%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:45 EST 2020

% Result     : Theorem 10.35s
% Output     : CNFRefutation 10.35s
% Verified   : 
% Statistics : Number of formulae       :  145 (1260 expanded)
%              Number of leaves         :   32 ( 434 expanded)
%              Depth                    :   15
%              Number of atoms          :  268 (2715 expanded)
%              Number of equality atoms :   74 ( 736 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(c_42,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_69,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_36,plain,
    ( k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_75,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_36])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_20,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_54,plain,(
    ! [A_28] :
      ( u1_struct_0(A_28) = k2_struct_0(A_28)
      | ~ l1_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_59,plain,(
    ! [A_29] :
      ( u1_struct_0(A_29) = k2_struct_0(A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_20,c_54])).

tff(c_63,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_59])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_64,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_32])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k3_subset_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_348,plain,(
    ! [B_60,A_61] :
      ( v1_tops_1(B_60,A_61)
      | k2_pre_topc(A_61,B_60) != k2_struct_0(A_61)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_370,plain,(
    ! [B_60] :
      ( v1_tops_1(B_60,'#skF_1')
      | k2_pre_topc('#skF_1',B_60) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_348])).

tff(c_386,plain,(
    ! [B_64] :
      ( v1_tops_1(B_64,'#skF_1')
      | k2_pre_topc('#skF_1',B_64) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_370])).

tff(c_414,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_386])).

tff(c_415,plain,(
    k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_414])).

tff(c_417,plain,(
    ! [A_65,B_66] :
      ( k2_pre_topc(A_65,B_66) = k2_struct_0(A_65)
      | ~ v1_tops_1(B_66,A_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_439,plain,(
    ! [B_66] :
      ( k2_pre_topc('#skF_1',B_66) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_66,'#skF_1')
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_417])).

tff(c_476,plain,(
    ! [B_69] :
      ( k2_pre_topc('#skF_1',B_69) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_69,'#skF_1')
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_439])).

tff(c_498,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_476])).

tff(c_510,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_415,c_498])).

tff(c_92,plain,(
    ! [A_38,B_39] :
      ( k3_subset_1(A_38,k3_subset_1(A_38,B_39)) = B_39
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_101,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_64,c_92])).

tff(c_792,plain,(
    ! [A_86,B_87] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_86),B_87),A_86)
      | ~ v2_tops_1(B_87,A_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_814,plain,(
    ! [B_87] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_87),'#skF_1')
      | ~ v2_tops_1(B_87,'#skF_1')
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_792])).

tff(c_848,plain,(
    ! [B_90] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_90),'#skF_1')
      | ~ v2_tops_1(B_90,'#skF_1')
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_63,c_814])).

tff(c_870,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_848])).

tff(c_878,plain,
    ( ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_510,c_870])).

tff(c_1196,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_878])).

tff(c_1199,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8,c_1196])).

tff(c_1206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1199])).

tff(c_1208,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_878])).

tff(c_446,plain,(
    ! [B_66] :
      ( k2_pre_topc('#skF_1',B_66) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_66,'#skF_1')
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_439])).

tff(c_1254,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1208,c_446])).

tff(c_1389,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1254])).

tff(c_377,plain,(
    ! [B_60] :
      ( v1_tops_1(B_60,'#skF_1')
      | k2_pre_topc('#skF_1',B_60) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_370])).

tff(c_1255,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1208,c_377])).

tff(c_1423,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1389,c_1255])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_114,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(A_40,B_41) = k3_subset_1(A_40,B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_170,plain,(
    ! [B_44,A_45] :
      ( k4_xboole_0(B_44,A_45) = k3_subset_1(B_44,A_45)
      | ~ r1_tarski(A_45,B_44) ) ),
    inference(resolution,[status(thm)],[c_14,c_114])).

tff(c_179,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = k3_subset_1(A_1,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_170])).

tff(c_184,plain,(
    ! [A_1] : k3_subset_1(A_1,k1_xboole_0) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_179])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1260,plain,(
    r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1208,c_12])).

tff(c_100,plain,(
    ! [B_10,A_9] :
      ( k3_subset_1(B_10,k3_subset_1(B_10,A_9)) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(resolution,[status(thm)],[c_14,c_92])).

tff(c_962,plain,(
    ! [A_94,B_95] :
      ( k3_subset_1(u1_struct_0(A_94),k2_pre_topc(A_94,k3_subset_1(u1_struct_0(A_94),B_95))) = k1_tops_1(A_94,B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10261,plain,(
    ! [A_259,A_260] :
      ( k3_subset_1(u1_struct_0(A_259),k2_pre_topc(A_259,A_260)) = k1_tops_1(A_259,k3_subset_1(u1_struct_0(A_259),A_260))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_259),A_260),k1_zfmisc_1(u1_struct_0(A_259)))
      | ~ l1_pre_topc(A_259)
      | ~ r1_tarski(A_260,u1_struct_0(A_259)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_962])).

tff(c_10333,plain,(
    ! [A_260] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',A_260)) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),A_260))
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),A_260),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_260,u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_10261])).

tff(c_11789,plain,(
    ! [A_280] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',A_280)) = k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),A_280))
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),A_280),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ r1_tarski(A_280,k2_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_34,c_63,c_63,c_63,c_10333])).

tff(c_11864,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))) = k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_11789])).

tff(c_11904,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1260,c_64,c_69,c_101,c_11864])).

tff(c_233,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1(k2_pre_topc(A_48,B_49),k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k3_subset_1(A_7,k3_subset_1(A_7,B_8)) = B_8
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1528,plain,(
    ! [A_108,B_109] :
      ( k3_subset_1(u1_struct_0(A_108),k3_subset_1(u1_struct_0(A_108),k2_pre_topc(A_108,B_109))) = k2_pre_topc(A_108,B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(resolution,[status(thm)],[c_233,c_10])).

tff(c_1582,plain,(
    ! [B_109] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_109))) = k2_pre_topc('#skF_1',B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_1528])).

tff(c_1600,plain,(
    ! [B_109] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_109))) = k2_pre_topc('#skF_1',B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_63,c_63,c_1582])).

tff(c_11965,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),k1_xboole_0)
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_11904,c_1600])).

tff(c_12034,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1208,c_184,c_11965])).

tff(c_12036,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1423,c_12034])).

tff(c_12038,plain,(
    v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_1254])).

tff(c_555,plain,(
    ! [B_72,A_73] :
      ( v2_tops_1(B_72,A_73)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_73),B_72),A_73)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_570,plain,(
    ! [B_72] :
      ( v2_tops_1(B_72,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_72),'#skF_1')
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_555])).

tff(c_576,plain,(
    ! [B_72] :
      ( v2_tops_1(B_72,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_72),'#skF_1')
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_63,c_570])).

tff(c_12041,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_12038,c_576])).

tff(c_12044,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_12041])).

tff(c_12046,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_12044])).

tff(c_12048,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_12061,plain,(
    ! [A_285,B_286] :
      ( k4_xboole_0(A_285,B_286) = k3_subset_1(A_285,B_286)
      | ~ m1_subset_1(B_286,k1_zfmisc_1(A_285)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12074,plain,(
    ! [B_287,A_288] :
      ( k4_xboole_0(B_287,A_288) = k3_subset_1(B_287,A_288)
      | ~ r1_tarski(A_288,B_287) ) ),
    inference(resolution,[status(thm)],[c_14,c_12061])).

tff(c_12080,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = k3_subset_1(A_1,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_12074])).

tff(c_12084,plain,(
    ! [A_1] : k3_subset_1(A_1,k1_xboole_0) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_12080])).

tff(c_12123,plain,(
    ! [A_294,B_295] :
      ( k3_subset_1(A_294,k3_subset_1(A_294,B_295)) = B_295
      | ~ m1_subset_1(B_295,k1_zfmisc_1(A_294)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12204,plain,(
    ! [B_301,A_302] :
      ( k3_subset_1(B_301,k3_subset_1(B_301,A_302)) = A_302
      | ~ r1_tarski(A_302,B_301) ) ),
    inference(resolution,[status(thm)],[c_14,c_12123])).

tff(c_12244,plain,(
    ! [A_1] :
      ( k3_subset_1(A_1,A_1) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12084,c_12204])).

tff(c_12264,plain,(
    ! [A_1] : k3_subset_1(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12244])).

tff(c_12047,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_12884,plain,(
    ! [A_341,B_342] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_341),B_342),A_341)
      | ~ v2_tops_1(B_342,A_341)
      | ~ m1_subset_1(B_342,k1_zfmisc_1(u1_struct_0(A_341)))
      | ~ l1_pre_topc(A_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_12906,plain,(
    ! [B_342] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_342),'#skF_1')
      | ~ v2_tops_1(B_342,'#skF_1')
      | ~ m1_subset_1(B_342,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_12884])).

tff(c_12913,plain,(
    ! [B_342] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_342),'#skF_1')
      | ~ v2_tops_1(B_342,'#skF_1')
      | ~ m1_subset_1(B_342,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_63,c_12906])).

tff(c_12442,plain,(
    ! [A_315,B_316] :
      ( k2_pre_topc(A_315,B_316) = k2_struct_0(A_315)
      | ~ v1_tops_1(B_316,A_315)
      | ~ m1_subset_1(B_316,k1_zfmisc_1(u1_struct_0(A_315)))
      | ~ l1_pre_topc(A_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12464,plain,(
    ! [B_316] :
      ( k2_pre_topc('#skF_1',B_316) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_316,'#skF_1')
      | ~ m1_subset_1(B_316,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_12442])).

tff(c_12480,plain,(
    ! [B_319] :
      ( k2_pre_topc('#skF_1',B_319) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_319,'#skF_1')
      | ~ m1_subset_1(B_319,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_12464])).

tff(c_12508,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_12480])).

tff(c_12509,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_12508])).

tff(c_12135,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_64,c_12123])).

tff(c_12940,plain,(
    ! [B_345] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_345),'#skF_1')
      | ~ v2_tops_1(B_345,'#skF_1')
      | ~ m1_subset_1(B_345,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_63,c_12906])).

tff(c_12958,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_12135,c_12940])).

tff(c_12967,plain,
    ( ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_12509,c_12958])).

tff(c_13332,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_12967])).

tff(c_13335,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8,c_13332])).

tff(c_13342,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_13335])).

tff(c_13344,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_12967])).

tff(c_12511,plain,(
    ! [B_320,A_321] :
      ( v1_tops_1(B_320,A_321)
      | k2_pre_topc(A_321,B_320) != k2_struct_0(A_321)
      | ~ m1_subset_1(B_320,k1_zfmisc_1(u1_struct_0(A_321)))
      | ~ l1_pre_topc(A_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12533,plain,(
    ! [B_320] :
      ( v1_tops_1(B_320,'#skF_1')
      | k2_pre_topc('#skF_1',B_320) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_320,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_12511])).

tff(c_12540,plain,(
    ! [B_320] :
      ( v1_tops_1(B_320,'#skF_1')
      | k2_pre_topc('#skF_1',B_320) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_320,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_12533])).

tff(c_13439,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_13344,c_12540])).

tff(c_13606,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_13439])).

tff(c_12471,plain,(
    ! [B_316] :
      ( k2_pre_topc('#skF_1',B_316) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_316,'#skF_1')
      | ~ m1_subset_1(B_316,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_12464])).

tff(c_13440,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_13344,c_12471])).

tff(c_13634,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_13606,c_13440])).

tff(c_13637,plain,
    ( ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_12913,c_13634])).

tff(c_13641,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_12047,c_13637])).

tff(c_13643,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_13439])).

tff(c_13058,plain,(
    ! [A_349,B_350] :
      ( k3_subset_1(u1_struct_0(A_349),k2_pre_topc(A_349,k3_subset_1(u1_struct_0(A_349),B_350))) = k1_tops_1(A_349,B_350)
      | ~ m1_subset_1(B_350,k1_zfmisc_1(u1_struct_0(A_349)))
      | ~ l1_pre_topc(A_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_13110,plain,(
    ! [B_350] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_350))) = k1_tops_1('#skF_1',B_350)
      | ~ m1_subset_1(B_350,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_13058])).

tff(c_13121,plain,(
    ! [B_350] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_350))) = k1_tops_1('#skF_1',B_350)
      | ~ m1_subset_1(B_350,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_63,c_63,c_13110])).

tff(c_13656,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_13643,c_13121])).

tff(c_13674,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_12264,c_13656])).

tff(c_13676,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12048,c_13674])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:53:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.35/3.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.35/3.65  
% 10.35/3.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.35/3.65  %$ v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 10.35/3.65  
% 10.35/3.65  %Foreground sorts:
% 10.35/3.65  
% 10.35/3.65  
% 10.35/3.65  %Background operators:
% 10.35/3.65  
% 10.35/3.65  
% 10.35/3.65  %Foreground operators:
% 10.35/3.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.35/3.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.35/3.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.35/3.65  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 10.35/3.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.35/3.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.35/3.65  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.35/3.65  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 10.35/3.65  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 10.35/3.65  tff('#skF_2', type, '#skF_2': $i).
% 10.35/3.65  tff('#skF_1', type, '#skF_1': $i).
% 10.35/3.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.35/3.65  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 10.35/3.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.35/3.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.35/3.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.35/3.65  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 10.35/3.65  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.35/3.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.35/3.65  
% 10.35/3.67  tff(f_94, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 10.35/3.67  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 10.35/3.67  tff(f_49, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 10.35/3.67  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 10.35/3.67  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 10.35/3.67  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 10.35/3.67  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 10.35/3.67  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 10.35/3.67  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.35/3.67  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.35/3.67  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 10.35/3.67  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 10.35/3.67  tff(f_55, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 10.35/3.67  tff(c_42, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.35/3.67  tff(c_69, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 10.35/3.67  tff(c_36, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.35/3.67  tff(c_75, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_36])).
% 10.35/3.67  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.35/3.67  tff(c_20, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.35/3.67  tff(c_54, plain, (![A_28]: (u1_struct_0(A_28)=k2_struct_0(A_28) | ~l1_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.35/3.67  tff(c_59, plain, (![A_29]: (u1_struct_0(A_29)=k2_struct_0(A_29) | ~l1_pre_topc(A_29))), inference(resolution, [status(thm)], [c_20, c_54])).
% 10.35/3.67  tff(c_63, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_59])).
% 10.35/3.67  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.35/3.67  tff(c_64, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_32])).
% 10.35/3.67  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(k3_subset_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.35/3.67  tff(c_348, plain, (![B_60, A_61]: (v1_tops_1(B_60, A_61) | k2_pre_topc(A_61, B_60)!=k2_struct_0(A_61) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.35/3.67  tff(c_370, plain, (![B_60]: (v1_tops_1(B_60, '#skF_1') | k2_pre_topc('#skF_1', B_60)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_60, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_348])).
% 10.35/3.67  tff(c_386, plain, (![B_64]: (v1_tops_1(B_64, '#skF_1') | k2_pre_topc('#skF_1', B_64)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_64, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_370])).
% 10.35/3.67  tff(c_414, plain, (v1_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_64, c_386])).
% 10.35/3.67  tff(c_415, plain, (k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_414])).
% 10.35/3.67  tff(c_417, plain, (![A_65, B_66]: (k2_pre_topc(A_65, B_66)=k2_struct_0(A_65) | ~v1_tops_1(B_66, A_65) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.35/3.67  tff(c_439, plain, (![B_66]: (k2_pre_topc('#skF_1', B_66)=k2_struct_0('#skF_1') | ~v1_tops_1(B_66, '#skF_1') | ~m1_subset_1(B_66, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_417])).
% 10.35/3.67  tff(c_476, plain, (![B_69]: (k2_pre_topc('#skF_1', B_69)=k2_struct_0('#skF_1') | ~v1_tops_1(B_69, '#skF_1') | ~m1_subset_1(B_69, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_439])).
% 10.35/3.67  tff(c_498, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_476])).
% 10.35/3.67  tff(c_510, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_415, c_498])).
% 10.35/3.67  tff(c_92, plain, (![A_38, B_39]: (k3_subset_1(A_38, k3_subset_1(A_38, B_39))=B_39 | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.35/3.67  tff(c_101, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_64, c_92])).
% 10.35/3.67  tff(c_792, plain, (![A_86, B_87]: (v1_tops_1(k3_subset_1(u1_struct_0(A_86), B_87), A_86) | ~v2_tops_1(B_87, A_86) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.35/3.67  tff(c_814, plain, (![B_87]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_87), '#skF_1') | ~v2_tops_1(B_87, '#skF_1') | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_792])).
% 10.35/3.67  tff(c_848, plain, (![B_90]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_90), '#skF_1') | ~v2_tops_1(B_90, '#skF_1') | ~m1_subset_1(B_90, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_63, c_814])).
% 10.35/3.67  tff(c_870, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_101, c_848])).
% 10.35/3.67  tff(c_878, plain, (~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_510, c_870])).
% 10.35/3.67  tff(c_1196, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_878])).
% 10.35/3.67  tff(c_1199, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8, c_1196])).
% 10.35/3.67  tff(c_1206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_1199])).
% 10.35/3.67  tff(c_1208, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_878])).
% 10.35/3.67  tff(c_446, plain, (![B_66]: (k2_pre_topc('#skF_1', B_66)=k2_struct_0('#skF_1') | ~v1_tops_1(B_66, '#skF_1') | ~m1_subset_1(B_66, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_439])).
% 10.35/3.67  tff(c_1254, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_1208, c_446])).
% 10.35/3.67  tff(c_1389, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_1254])).
% 10.35/3.67  tff(c_377, plain, (![B_60]: (v1_tops_1(B_60, '#skF_1') | k2_pre_topc('#skF_1', B_60)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_60, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_370])).
% 10.35/3.67  tff(c_1255, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1208, c_377])).
% 10.35/3.67  tff(c_1423, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1389, c_1255])).
% 10.35/3.67  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.35/3.67  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.35/3.67  tff(c_14, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.35/3.67  tff(c_114, plain, (![A_40, B_41]: (k4_xboole_0(A_40, B_41)=k3_subset_1(A_40, B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.35/3.67  tff(c_170, plain, (![B_44, A_45]: (k4_xboole_0(B_44, A_45)=k3_subset_1(B_44, A_45) | ~r1_tarski(A_45, B_44))), inference(resolution, [status(thm)], [c_14, c_114])).
% 10.35/3.67  tff(c_179, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=k3_subset_1(A_1, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_170])).
% 10.35/3.67  tff(c_184, plain, (![A_1]: (k3_subset_1(A_1, k1_xboole_0)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_179])).
% 10.35/3.67  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.35/3.67  tff(c_1260, plain, (r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1208, c_12])).
% 10.35/3.67  tff(c_100, plain, (![B_10, A_9]: (k3_subset_1(B_10, k3_subset_1(B_10, A_9))=A_9 | ~r1_tarski(A_9, B_10))), inference(resolution, [status(thm)], [c_14, c_92])).
% 10.35/3.67  tff(c_962, plain, (![A_94, B_95]: (k3_subset_1(u1_struct_0(A_94), k2_pre_topc(A_94, k3_subset_1(u1_struct_0(A_94), B_95)))=k1_tops_1(A_94, B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.35/3.67  tff(c_10261, plain, (![A_259, A_260]: (k3_subset_1(u1_struct_0(A_259), k2_pre_topc(A_259, A_260))=k1_tops_1(A_259, k3_subset_1(u1_struct_0(A_259), A_260)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_259), A_260), k1_zfmisc_1(u1_struct_0(A_259))) | ~l1_pre_topc(A_259) | ~r1_tarski(A_260, u1_struct_0(A_259)))), inference(superposition, [status(thm), theory('equality')], [c_100, c_962])).
% 10.35/3.67  tff(c_10333, plain, (![A_260]: (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', A_260))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), A_260)) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), A_260), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_260, u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_63, c_10261])).
% 10.35/3.67  tff(c_11789, plain, (![A_280]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', A_280))=k1_tops_1('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), A_280)) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), A_280), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~r1_tarski(A_280, k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_34, c_63, c_63, c_63, c_10333])).
% 10.35/3.67  tff(c_11864, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')))=k1_tops_1('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_11789])).
% 10.35/3.67  tff(c_11904, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1260, c_64, c_69, c_101, c_11864])).
% 10.35/3.67  tff(c_233, plain, (![A_48, B_49]: (m1_subset_1(k2_pre_topc(A_48, B_49), k1_zfmisc_1(u1_struct_0(A_48))) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.35/3.67  tff(c_10, plain, (![A_7, B_8]: (k3_subset_1(A_7, k3_subset_1(A_7, B_8))=B_8 | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.35/3.67  tff(c_1528, plain, (![A_108, B_109]: (k3_subset_1(u1_struct_0(A_108), k3_subset_1(u1_struct_0(A_108), k2_pre_topc(A_108, B_109)))=k2_pre_topc(A_108, B_109) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(resolution, [status(thm)], [c_233, c_10])).
% 10.35/3.67  tff(c_1582, plain, (![B_109]: (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', B_109)))=k2_pre_topc('#skF_1', B_109) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_1528])).
% 10.35/3.67  tff(c_1600, plain, (![B_109]: (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', B_109)))=k2_pre_topc('#skF_1', B_109) | ~m1_subset_1(B_109, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_63, c_63, c_1582])).
% 10.35/3.67  tff(c_11965, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), k1_xboole_0) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_11904, c_1600])).
% 10.35/3.67  tff(c_12034, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1208, c_184, c_11965])).
% 10.35/3.67  tff(c_12036, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1423, c_12034])).
% 10.35/3.67  tff(c_12038, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_1254])).
% 10.35/3.67  tff(c_555, plain, (![B_72, A_73]: (v2_tops_1(B_72, A_73) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_73), B_72), A_73) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.35/3.67  tff(c_570, plain, (![B_72]: (v2_tops_1(B_72, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_72), '#skF_1') | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_555])).
% 10.35/3.67  tff(c_576, plain, (![B_72]: (v2_tops_1(B_72, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_72), '#skF_1') | ~m1_subset_1(B_72, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_63, c_570])).
% 10.35/3.67  tff(c_12041, plain, (v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_12038, c_576])).
% 10.35/3.67  tff(c_12044, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_12041])).
% 10.35/3.67  tff(c_12046, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_12044])).
% 10.35/3.67  tff(c_12048, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 10.35/3.67  tff(c_12061, plain, (![A_285, B_286]: (k4_xboole_0(A_285, B_286)=k3_subset_1(A_285, B_286) | ~m1_subset_1(B_286, k1_zfmisc_1(A_285)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.35/3.67  tff(c_12074, plain, (![B_287, A_288]: (k4_xboole_0(B_287, A_288)=k3_subset_1(B_287, A_288) | ~r1_tarski(A_288, B_287))), inference(resolution, [status(thm)], [c_14, c_12061])).
% 10.35/3.67  tff(c_12080, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=k3_subset_1(A_1, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_12074])).
% 10.35/3.67  tff(c_12084, plain, (![A_1]: (k3_subset_1(A_1, k1_xboole_0)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_12080])).
% 10.35/3.67  tff(c_12123, plain, (![A_294, B_295]: (k3_subset_1(A_294, k3_subset_1(A_294, B_295))=B_295 | ~m1_subset_1(B_295, k1_zfmisc_1(A_294)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.35/3.67  tff(c_12204, plain, (![B_301, A_302]: (k3_subset_1(B_301, k3_subset_1(B_301, A_302))=A_302 | ~r1_tarski(A_302, B_301))), inference(resolution, [status(thm)], [c_14, c_12123])).
% 10.35/3.67  tff(c_12244, plain, (![A_1]: (k3_subset_1(A_1, A_1)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_1))), inference(superposition, [status(thm), theory('equality')], [c_12084, c_12204])).
% 10.35/3.67  tff(c_12264, plain, (![A_1]: (k3_subset_1(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12244])).
% 10.35/3.67  tff(c_12047, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 10.35/3.67  tff(c_12884, plain, (![A_341, B_342]: (v1_tops_1(k3_subset_1(u1_struct_0(A_341), B_342), A_341) | ~v2_tops_1(B_342, A_341) | ~m1_subset_1(B_342, k1_zfmisc_1(u1_struct_0(A_341))) | ~l1_pre_topc(A_341))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.35/3.67  tff(c_12906, plain, (![B_342]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_342), '#skF_1') | ~v2_tops_1(B_342, '#skF_1') | ~m1_subset_1(B_342, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_12884])).
% 10.35/3.67  tff(c_12913, plain, (![B_342]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_342), '#skF_1') | ~v2_tops_1(B_342, '#skF_1') | ~m1_subset_1(B_342, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_63, c_12906])).
% 10.35/3.67  tff(c_12442, plain, (![A_315, B_316]: (k2_pre_topc(A_315, B_316)=k2_struct_0(A_315) | ~v1_tops_1(B_316, A_315) | ~m1_subset_1(B_316, k1_zfmisc_1(u1_struct_0(A_315))) | ~l1_pre_topc(A_315))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.35/3.67  tff(c_12464, plain, (![B_316]: (k2_pre_topc('#skF_1', B_316)=k2_struct_0('#skF_1') | ~v1_tops_1(B_316, '#skF_1') | ~m1_subset_1(B_316, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_12442])).
% 10.35/3.67  tff(c_12480, plain, (![B_319]: (k2_pre_topc('#skF_1', B_319)=k2_struct_0('#skF_1') | ~v1_tops_1(B_319, '#skF_1') | ~m1_subset_1(B_319, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_12464])).
% 10.35/3.67  tff(c_12508, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_12480])).
% 10.35/3.67  tff(c_12509, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_12508])).
% 10.35/3.67  tff(c_12135, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_64, c_12123])).
% 10.35/3.67  tff(c_12940, plain, (![B_345]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_345), '#skF_1') | ~v2_tops_1(B_345, '#skF_1') | ~m1_subset_1(B_345, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_63, c_12906])).
% 10.35/3.67  tff(c_12958, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_12135, c_12940])).
% 10.35/3.67  tff(c_12967, plain, (~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_12509, c_12958])).
% 10.35/3.67  tff(c_13332, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_12967])).
% 10.35/3.67  tff(c_13335, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8, c_13332])).
% 10.35/3.67  tff(c_13342, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_13335])).
% 10.35/3.67  tff(c_13344, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_12967])).
% 10.35/3.67  tff(c_12511, plain, (![B_320, A_321]: (v1_tops_1(B_320, A_321) | k2_pre_topc(A_321, B_320)!=k2_struct_0(A_321) | ~m1_subset_1(B_320, k1_zfmisc_1(u1_struct_0(A_321))) | ~l1_pre_topc(A_321))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.35/3.67  tff(c_12533, plain, (![B_320]: (v1_tops_1(B_320, '#skF_1') | k2_pre_topc('#skF_1', B_320)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_320, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_12511])).
% 10.35/3.67  tff(c_12540, plain, (![B_320]: (v1_tops_1(B_320, '#skF_1') | k2_pre_topc('#skF_1', B_320)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_320, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_12533])).
% 10.35/3.67  tff(c_13439, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_13344, c_12540])).
% 10.35/3.67  tff(c_13606, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_13439])).
% 10.35/3.67  tff(c_12471, plain, (![B_316]: (k2_pre_topc('#skF_1', B_316)=k2_struct_0('#skF_1') | ~v1_tops_1(B_316, '#skF_1') | ~m1_subset_1(B_316, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_12464])).
% 10.35/3.67  tff(c_13440, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_13344, c_12471])).
% 10.35/3.67  tff(c_13634, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_13606, c_13440])).
% 10.35/3.67  tff(c_13637, plain, (~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_12913, c_13634])).
% 10.35/3.67  tff(c_13641, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_12047, c_13637])).
% 10.35/3.67  tff(c_13643, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_13439])).
% 10.35/3.67  tff(c_13058, plain, (![A_349, B_350]: (k3_subset_1(u1_struct_0(A_349), k2_pre_topc(A_349, k3_subset_1(u1_struct_0(A_349), B_350)))=k1_tops_1(A_349, B_350) | ~m1_subset_1(B_350, k1_zfmisc_1(u1_struct_0(A_349))) | ~l1_pre_topc(A_349))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.35/3.67  tff(c_13110, plain, (![B_350]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_350)))=k1_tops_1('#skF_1', B_350) | ~m1_subset_1(B_350, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_13058])).
% 10.35/3.67  tff(c_13121, plain, (![B_350]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_350)))=k1_tops_1('#skF_1', B_350) | ~m1_subset_1(B_350, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_63, c_63, c_13110])).
% 10.35/3.67  tff(c_13656, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_13643, c_13121])).
% 10.35/3.67  tff(c_13674, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_64, c_12264, c_13656])).
% 10.35/3.67  tff(c_13676, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12048, c_13674])).
% 10.35/3.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.35/3.67  
% 10.35/3.67  Inference rules
% 10.35/3.67  ----------------------
% 10.35/3.67  #Ref     : 0
% 10.35/3.67  #Sup     : 3234
% 10.35/3.67  #Fact    : 0
% 10.35/3.67  #Define  : 0
% 10.35/3.67  #Split   : 39
% 10.35/3.67  #Chain   : 0
% 10.35/3.67  #Close   : 0
% 10.35/3.67  
% 10.35/3.67  Ordering : KBO
% 10.35/3.67  
% 10.35/3.67  Simplification rules
% 10.35/3.67  ----------------------
% 10.35/3.67  #Subsume      : 683
% 10.35/3.67  #Demod        : 2594
% 10.35/3.67  #Tautology    : 747
% 10.35/3.67  #SimpNegUnit  : 313
% 10.35/3.67  #BackRed      : 6
% 10.35/3.67  
% 10.35/3.67  #Partial instantiations: 0
% 10.35/3.67  #Strategies tried      : 1
% 10.35/3.67  
% 10.35/3.67  Timing (in seconds)
% 10.35/3.67  ----------------------
% 10.35/3.68  Preprocessing        : 0.33
% 10.35/3.68  Parsing              : 0.18
% 10.35/3.68  CNF conversion       : 0.02
% 10.35/3.68  Main loop            : 2.54
% 10.35/3.68  Inferencing          : 0.70
% 10.35/3.68  Reduction            : 1.03
% 10.35/3.68  Demodulation         : 0.75
% 10.35/3.68  BG Simplification    : 0.09
% 10.35/3.68  Subsumption          : 0.57
% 10.35/3.68  Abstraction          : 0.11
% 10.35/3.68  MUC search           : 0.00
% 10.35/3.68  Cooper               : 0.00
% 10.35/3.68  Total                : 2.91
% 10.35/3.68  Index Insertion      : 0.00
% 10.35/3.68  Index Deletion       : 0.00
% 10.35/3.68  Index Matching       : 0.00
% 10.35/3.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
