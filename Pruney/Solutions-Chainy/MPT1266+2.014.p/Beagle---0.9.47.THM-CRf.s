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
% DateTime   : Thu Dec  3 10:21:45 EST 2020

% Result     : Theorem 8.54s
% Output     : CNFRefutation 8.88s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 885 expanded)
%              Number of leaves         :   37 ( 309 expanded)
%              Depth                    :   15
%              Number of atoms          :  252 (1887 expanded)
%              Number of equality atoms :   74 ( 519 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > v1_tops_1 > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

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

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

tff(f_31,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_49,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(c_46,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_96,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_40,plain,
    ( k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_124,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_40])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_24,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_108,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_113,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_24,c_108])).

tff(c_117,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_113])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_118,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_36])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k3_subset_1(A_9,B_10),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_366,plain,(
    ! [B_60,A_61] :
      ( v1_tops_1(B_60,A_61)
      | k2_pre_topc(A_61,B_60) != k2_struct_0(A_61)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_380,plain,(
    ! [B_60] :
      ( v1_tops_1(B_60,'#skF_1')
      | k2_pre_topc('#skF_1',B_60) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_366])).

tff(c_407,plain,(
    ! [B_64] :
      ( v1_tops_1(B_64,'#skF_1')
      | k2_pre_topc('#skF_1',B_64) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_380])).

tff(c_429,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_118,c_407])).

tff(c_433,plain,(
    k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_429])).

tff(c_333,plain,(
    ! [A_56,B_57] :
      ( k2_pre_topc(A_56,B_57) = k2_struct_0(A_56)
      | ~ v1_tops_1(B_57,A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_347,plain,(
    ! [B_57] :
      ( k2_pre_topc('#skF_1',B_57) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_57,'#skF_1')
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_333])).

tff(c_464,plain,(
    ! [B_68] :
      ( k2_pre_topc('#skF_1',B_68) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_68,'#skF_1')
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_347])).

tff(c_478,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_118,c_464])).

tff(c_490,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_433,c_478])).

tff(c_195,plain,(
    ! [A_46,B_47] :
      ( k3_subset_1(A_46,k3_subset_1(A_46,B_47)) = B_47
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_207,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_118,c_195])).

tff(c_435,plain,(
    ! [A_65,B_66] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_65),B_66),A_65)
      | ~ v2_tops_1(B_66,A_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_446,plain,(
    ! [B_66] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_66),'#skF_1')
      | ~ v2_tops_1(B_66,'#skF_1')
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_435])).

tff(c_655,plain,(
    ! [B_78] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_78),'#skF_1')
      | ~ v2_tops_1(B_78,'#skF_1')
      | ~ m1_subset_1(B_78,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_117,c_446])).

tff(c_668,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_655])).

tff(c_678,plain,
    ( ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_490,c_668])).

tff(c_685,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_678])).

tff(c_688,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_14,c_685])).

tff(c_692,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_688])).

tff(c_694,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_678])).

tff(c_389,plain,(
    ! [B_60] :
      ( v1_tops_1(B_60,'#skF_1')
      | k2_pre_topc('#skF_1',B_60) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_380])).

tff(c_762,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_694,c_389])).

tff(c_1034,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_762])).

tff(c_6,plain,(
    ! [A_4] : k1_subset_1(A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_5] : k2_subset_1(A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_13] : k3_subset_1(A_13,k1_subset_1(A_13)) = k2_subset_1(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_48,plain,(
    ! [A_13] : k3_subset_1(A_13,k1_subset_1(A_13)) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).

tff(c_49,plain,(
    ! [A_13] : k3_subset_1(A_13,k1_xboole_0) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_48])).

tff(c_26,plain,(
    ! [A_18,B_20] :
      ( k3_subset_1(u1_struct_0(A_18),k2_pre_topc(A_18,k3_subset_1(u1_struct_0(A_18),B_20))) = k1_tops_1(A_18,B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_218,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1(k2_pre_topc(A_48,B_49),k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( k3_subset_1(A_11,k3_subset_1(A_11,B_12)) = B_12
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_914,plain,(
    ! [A_83,B_84] :
      ( k3_subset_1(u1_struct_0(A_83),k3_subset_1(u1_struct_0(A_83),k2_pre_topc(A_83,B_84))) = k2_pre_topc(A_83,B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(resolution,[status(thm)],[c_218,c_16])).

tff(c_7137,plain,(
    ! [A_239,B_240] :
      ( k3_subset_1(u1_struct_0(A_239),k1_tops_1(A_239,B_240)) = k2_pre_topc(A_239,k3_subset_1(u1_struct_0(A_239),B_240))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_239),B_240),k1_zfmisc_1(u1_struct_0(A_239)))
      | ~ l1_pre_topc(A_239)
      | ~ m1_subset_1(B_240,k1_zfmisc_1(u1_struct_0(A_239)))
      | ~ l1_pre_topc(A_239) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_914])).

tff(c_7226,plain,(
    ! [A_241,B_242] :
      ( k3_subset_1(u1_struct_0(A_241),k1_tops_1(A_241,B_242)) = k2_pre_topc(A_241,k3_subset_1(u1_struct_0(A_241),B_242))
      | ~ l1_pre_topc(A_241)
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(A_241))) ) ),
    inference(resolution,[status(thm)],[c_14,c_7137])).

tff(c_7248,plain,(
    ! [B_242] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1',B_242)) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_242))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_242,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_7226])).

tff(c_7266,plain,(
    ! [B_243] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k1_tops_1('#skF_1',B_243)) = k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_243))
      | ~ m1_subset_1(B_243,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_117,c_117,c_7248])).

tff(c_7313,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_118,c_7266])).

tff(c_7344,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_96,c_7313])).

tff(c_7346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1034,c_7344])).

tff(c_7347,plain,(
    v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_762])).

tff(c_510,plain,(
    ! [B_70,A_71] :
      ( v2_tops_1(B_70,A_71)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_71),B_70),A_71)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_524,plain,(
    ! [B_70] :
      ( v2_tops_1(B_70,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_70),'#skF_1')
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_510])).

tff(c_533,plain,(
    ! [B_70] :
      ( v2_tops_1(B_70,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_70),'#skF_1')
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_117,c_524])).

tff(c_7351,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_7347,c_533])).

tff(c_7354,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_7351])).

tff(c_7356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_7354])).

tff(c_7357,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_7359,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_7361,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7357,c_7359])).

tff(c_7362,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_7372,plain,(
    ! [A_245] :
      ( u1_struct_0(A_245) = k2_struct_0(A_245)
      | ~ l1_struct_0(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_7377,plain,(
    ! [A_246] :
      ( u1_struct_0(A_246) = k2_struct_0(A_246)
      | ~ l1_pre_topc(A_246) ) ),
    inference(resolution,[status(thm)],[c_24,c_7372])).

tff(c_7381,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_7377])).

tff(c_7382,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7381,c_36])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_86,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k2_xboole_0(A_34,B_35)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_93,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_86])).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1(k2_subset_1(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_47,plain,(
    ! [A_8] : m1_subset_1(A_8,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12])).

tff(c_7387,plain,(
    ! [A_247,B_248] :
      ( k4_xboole_0(A_247,B_248) = k3_subset_1(A_247,B_248)
      | ~ m1_subset_1(B_248,k1_zfmisc_1(A_247)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_7393,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_subset_1(A_8,A_8) ),
    inference(resolution,[status(thm)],[c_47,c_7387])).

tff(c_7396,plain,(
    ! [A_8] : k3_subset_1(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_7393])).

tff(c_7755,plain,(
    ! [A_278,B_279] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_278),B_279),A_278)
      | ~ v2_tops_1(B_279,A_278)
      | ~ m1_subset_1(B_279,k1_zfmisc_1(u1_struct_0(A_278)))
      | ~ l1_pre_topc(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_7769,plain,(
    ! [B_279] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_279),'#skF_1')
      | ~ v2_tops_1(B_279,'#skF_1')
      | ~ m1_subset_1(B_279,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7381,c_7755])).

tff(c_7778,plain,(
    ! [B_279] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_279),'#skF_1')
      | ~ v2_tops_1(B_279,'#skF_1')
      | ~ m1_subset_1(B_279,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_7381,c_7769])).

tff(c_7575,plain,(
    ! [B_263,A_264] :
      ( v1_tops_1(B_263,A_264)
      | k2_pre_topc(A_264,B_263) != k2_struct_0(A_264)
      | ~ m1_subset_1(B_263,k1_zfmisc_1(u1_struct_0(A_264)))
      | ~ l1_pre_topc(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_7589,plain,(
    ! [B_263] :
      ( v1_tops_1(B_263,'#skF_1')
      | k2_pre_topc('#skF_1',B_263) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_263,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7381,c_7575])).

tff(c_7649,plain,(
    ! [B_271] :
      ( v1_tops_1(B_271,'#skF_1')
      | k2_pre_topc('#skF_1',B_271) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_271,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_7589])).

tff(c_7671,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_7382,c_7649])).

tff(c_7697,plain,(
    k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_7671])).

tff(c_7600,plain,(
    ! [A_265,B_266] :
      ( k2_pre_topc(A_265,B_266) = k2_struct_0(A_265)
      | ~ v1_tops_1(B_266,A_265)
      | ~ m1_subset_1(B_266,k1_zfmisc_1(u1_struct_0(A_265)))
      | ~ l1_pre_topc(A_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_7614,plain,(
    ! [B_266] :
      ( k2_pre_topc('#skF_1',B_266) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_266,'#skF_1')
      | ~ m1_subset_1(B_266,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7381,c_7600])).

tff(c_7698,plain,(
    ! [B_274] :
      ( k2_pre_topc('#skF_1',B_274) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_274,'#skF_1')
      | ~ m1_subset_1(B_274,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_7614])).

tff(c_7712,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_7382,c_7698])).

tff(c_7724,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_7697,c_7712])).

tff(c_7432,plain,(
    ! [A_252,B_253] :
      ( k3_subset_1(A_252,k3_subset_1(A_252,B_253)) = B_253
      | ~ m1_subset_1(B_253,k1_zfmisc_1(A_252)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_7440,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_7382,c_7432])).

tff(c_7882,plain,(
    ! [B_285] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_285),'#skF_1')
      | ~ v2_tops_1(B_285,'#skF_1')
      | ~ m1_subset_1(B_285,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_7381,c_7769])).

tff(c_7892,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_7440,c_7882])).

tff(c_7902,plain,
    ( ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_7724,c_7892])).

tff(c_7909,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_7902])).

tff(c_7965,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_14,c_7909])).

tff(c_7969,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7382,c_7965])).

tff(c_7971,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_7902])).

tff(c_7623,plain,(
    ! [B_266] :
      ( k2_pre_topc('#skF_1',B_266) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_266,'#skF_1')
      | ~ m1_subset_1(B_266,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_7614])).

tff(c_7985,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_7971,c_7623])).

tff(c_7993,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_7985])).

tff(c_7996,plain,
    ( ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_7778,c_7993])).

tff(c_8000,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7382,c_7357,c_7996])).

tff(c_8001,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_7985])).

tff(c_8039,plain,(
    ! [A_289,B_290] :
      ( k3_subset_1(u1_struct_0(A_289),k2_pre_topc(A_289,k3_subset_1(u1_struct_0(A_289),B_290))) = k1_tops_1(A_289,B_290)
      | ~ m1_subset_1(B_290,k1_zfmisc_1(u1_struct_0(A_289)))
      | ~ l1_pre_topc(A_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8077,plain,(
    ! [B_290] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_290))) = k1_tops_1('#skF_1',B_290)
      | ~ m1_subset_1(B_290,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7381,c_8039])).

tff(c_8397,plain,(
    ! [B_300] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_300))) = k1_tops_1('#skF_1',B_300)
      | ~ m1_subset_1(B_300,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_7381,c_7381,c_8077])).

tff(c_8433,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8001,c_8397])).

tff(c_8456,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7382,c_7396,c_8433])).

tff(c_8458,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7362,c_8456])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:37:41 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.54/2.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.54/2.98  
% 8.54/2.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.54/2.98  %$ v2_tops_1 > v1_tops_1 > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.54/2.98  
% 8.54/2.98  %Foreground sorts:
% 8.54/2.98  
% 8.54/2.98  
% 8.54/2.98  %Background operators:
% 8.54/2.98  
% 8.54/2.98  
% 8.54/2.98  %Foreground operators:
% 8.54/2.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.54/2.98  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.54/2.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.54/2.98  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 8.54/2.98  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.54/2.98  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.54/2.98  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 8.54/2.98  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.54/2.98  tff('#skF_2', type, '#skF_2': $i).
% 8.54/2.98  tff('#skF_1', type, '#skF_1': $i).
% 8.54/2.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.54/2.98  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.54/2.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.54/2.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.54/2.98  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 8.54/2.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.54/2.98  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.54/2.98  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 8.54/2.98  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 8.54/2.98  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.54/2.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.54/2.98  
% 8.88/3.00  tff(f_98, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 8.88/3.00  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 8.88/3.00  tff(f_53, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 8.88/3.00  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 8.88/3.00  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 8.88/3.00  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 8.88/3.00  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 8.88/3.00  tff(f_31, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 8.88/3.00  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 8.88/3.00  tff(f_49, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 8.88/3.00  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 8.88/3.00  tff(f_59, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 8.88/3.00  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 8.88/3.00  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 8.88/3.00  tff(f_39, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 8.88/3.00  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 8.88/3.00  tff(c_46, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.88/3.00  tff(c_96, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_46])).
% 8.88/3.00  tff(c_40, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.88/3.00  tff(c_124, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_40])).
% 8.88/3.00  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.88/3.00  tff(c_24, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.88/3.00  tff(c_108, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.88/3.00  tff(c_113, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_pre_topc(A_38))), inference(resolution, [status(thm)], [c_24, c_108])).
% 8.88/3.00  tff(c_117, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_113])).
% 8.88/3.00  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.88/3.00  tff(c_118, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_36])).
% 8.88/3.00  tff(c_14, plain, (![A_9, B_10]: (m1_subset_1(k3_subset_1(A_9, B_10), k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.88/3.00  tff(c_366, plain, (![B_60, A_61]: (v1_tops_1(B_60, A_61) | k2_pre_topc(A_61, B_60)!=k2_struct_0(A_61) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.88/3.00  tff(c_380, plain, (![B_60]: (v1_tops_1(B_60, '#skF_1') | k2_pre_topc('#skF_1', B_60)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_60, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_117, c_366])).
% 8.88/3.00  tff(c_407, plain, (![B_64]: (v1_tops_1(B_64, '#skF_1') | k2_pre_topc('#skF_1', B_64)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_64, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_380])).
% 8.88/3.00  tff(c_429, plain, (v1_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_118, c_407])).
% 8.88/3.00  tff(c_433, plain, (k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_429])).
% 8.88/3.00  tff(c_333, plain, (![A_56, B_57]: (k2_pre_topc(A_56, B_57)=k2_struct_0(A_56) | ~v1_tops_1(B_57, A_56) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.88/3.00  tff(c_347, plain, (![B_57]: (k2_pre_topc('#skF_1', B_57)=k2_struct_0('#skF_1') | ~v1_tops_1(B_57, '#skF_1') | ~m1_subset_1(B_57, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_117, c_333])).
% 8.88/3.00  tff(c_464, plain, (![B_68]: (k2_pre_topc('#skF_1', B_68)=k2_struct_0('#skF_1') | ~v1_tops_1(B_68, '#skF_1') | ~m1_subset_1(B_68, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_347])).
% 8.88/3.00  tff(c_478, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_118, c_464])).
% 8.88/3.00  tff(c_490, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_433, c_478])).
% 8.88/3.00  tff(c_195, plain, (![A_46, B_47]: (k3_subset_1(A_46, k3_subset_1(A_46, B_47))=B_47 | ~m1_subset_1(B_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.88/3.00  tff(c_207, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_118, c_195])).
% 8.88/3.00  tff(c_435, plain, (![A_65, B_66]: (v1_tops_1(k3_subset_1(u1_struct_0(A_65), B_66), A_65) | ~v2_tops_1(B_66, A_65) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.88/3.00  tff(c_446, plain, (![B_66]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_66), '#skF_1') | ~v2_tops_1(B_66, '#skF_1') | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_117, c_435])).
% 8.88/3.00  tff(c_655, plain, (![B_78]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_78), '#skF_1') | ~v2_tops_1(B_78, '#skF_1') | ~m1_subset_1(B_78, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_117, c_446])).
% 8.88/3.00  tff(c_668, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_207, c_655])).
% 8.88/3.00  tff(c_678, plain, (~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_490, c_668])).
% 8.88/3.00  tff(c_685, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_678])).
% 8.88/3.00  tff(c_688, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_685])).
% 8.88/3.00  tff(c_692, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_688])).
% 8.88/3.00  tff(c_694, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_678])).
% 8.88/3.00  tff(c_389, plain, (![B_60]: (v1_tops_1(B_60, '#skF_1') | k2_pre_topc('#skF_1', B_60)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_60, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_380])).
% 8.88/3.00  tff(c_762, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_694, c_389])).
% 8.88/3.00  tff(c_1034, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_762])).
% 8.88/3.00  tff(c_6, plain, (![A_4]: (k1_subset_1(A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.88/3.00  tff(c_8, plain, (![A_5]: (k2_subset_1(A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.88/3.00  tff(c_18, plain, (![A_13]: (k3_subset_1(A_13, k1_subset_1(A_13))=k2_subset_1(A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.88/3.00  tff(c_48, plain, (![A_13]: (k3_subset_1(A_13, k1_subset_1(A_13))=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 8.88/3.00  tff(c_49, plain, (![A_13]: (k3_subset_1(A_13, k1_xboole_0)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_48])).
% 8.88/3.00  tff(c_26, plain, (![A_18, B_20]: (k3_subset_1(u1_struct_0(A_18), k2_pre_topc(A_18, k3_subset_1(u1_struct_0(A_18), B_20)))=k1_tops_1(A_18, B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.88/3.00  tff(c_218, plain, (![A_48, B_49]: (m1_subset_1(k2_pre_topc(A_48, B_49), k1_zfmisc_1(u1_struct_0(A_48))) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.88/3.00  tff(c_16, plain, (![A_11, B_12]: (k3_subset_1(A_11, k3_subset_1(A_11, B_12))=B_12 | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.88/3.00  tff(c_914, plain, (![A_83, B_84]: (k3_subset_1(u1_struct_0(A_83), k3_subset_1(u1_struct_0(A_83), k2_pre_topc(A_83, B_84)))=k2_pre_topc(A_83, B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(resolution, [status(thm)], [c_218, c_16])).
% 8.88/3.00  tff(c_7137, plain, (![A_239, B_240]: (k3_subset_1(u1_struct_0(A_239), k1_tops_1(A_239, B_240))=k2_pre_topc(A_239, k3_subset_1(u1_struct_0(A_239), B_240)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_239), B_240), k1_zfmisc_1(u1_struct_0(A_239))) | ~l1_pre_topc(A_239) | ~m1_subset_1(B_240, k1_zfmisc_1(u1_struct_0(A_239))) | ~l1_pre_topc(A_239))), inference(superposition, [status(thm), theory('equality')], [c_26, c_914])).
% 8.88/3.00  tff(c_7226, plain, (![A_241, B_242]: (k3_subset_1(u1_struct_0(A_241), k1_tops_1(A_241, B_242))=k2_pre_topc(A_241, k3_subset_1(u1_struct_0(A_241), B_242)) | ~l1_pre_topc(A_241) | ~m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0(A_241))))), inference(resolution, [status(thm)], [c_14, c_7137])).
% 8.88/3.00  tff(c_7248, plain, (![B_242]: (k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', B_242))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_242)) | ~l1_pre_topc('#skF_1') | ~m1_subset_1(B_242, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_117, c_7226])).
% 8.88/3.00  tff(c_7266, plain, (![B_243]: (k3_subset_1(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', B_243))=k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_243)) | ~m1_subset_1(B_243, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_117, c_117, c_7248])).
% 8.88/3.00  tff(c_7313, plain, (k3_subset_1(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_118, c_7266])).
% 8.88/3.00  tff(c_7344, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_96, c_7313])).
% 8.88/3.00  tff(c_7346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1034, c_7344])).
% 8.88/3.00  tff(c_7347, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_762])).
% 8.88/3.00  tff(c_510, plain, (![B_70, A_71]: (v2_tops_1(B_70, A_71) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_71), B_70), A_71) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.88/3.00  tff(c_524, plain, (![B_70]: (v2_tops_1(B_70, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_70), '#skF_1') | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_117, c_510])).
% 8.88/3.00  tff(c_533, plain, (![B_70]: (v2_tops_1(B_70, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_70), '#skF_1') | ~m1_subset_1(B_70, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_117, c_524])).
% 8.88/3.00  tff(c_7351, plain, (v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_7347, c_533])).
% 8.88/3.00  tff(c_7354, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_7351])).
% 8.88/3.00  tff(c_7356, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_7354])).
% 8.88/3.00  tff(c_7357, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 8.88/3.00  tff(c_7359, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_40])).
% 8.88/3.00  tff(c_7361, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7357, c_7359])).
% 8.88/3.00  tff(c_7362, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 8.88/3.00  tff(c_7372, plain, (![A_245]: (u1_struct_0(A_245)=k2_struct_0(A_245) | ~l1_struct_0(A_245))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.88/3.00  tff(c_7377, plain, (![A_246]: (u1_struct_0(A_246)=k2_struct_0(A_246) | ~l1_pre_topc(A_246))), inference(resolution, [status(thm)], [c_24, c_7372])).
% 8.88/3.00  tff(c_7381, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_7377])).
% 8.88/3.00  tff(c_7382, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_7381, c_36])).
% 8.88/3.00  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.88/3.00  tff(c_86, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k2_xboole_0(A_34, B_35))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.88/3.00  tff(c_93, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_86])).
% 8.88/3.00  tff(c_12, plain, (![A_8]: (m1_subset_1(k2_subset_1(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.88/3.00  tff(c_47, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_12])).
% 8.88/3.00  tff(c_7387, plain, (![A_247, B_248]: (k4_xboole_0(A_247, B_248)=k3_subset_1(A_247, B_248) | ~m1_subset_1(B_248, k1_zfmisc_1(A_247)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.88/3.00  tff(c_7393, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_subset_1(A_8, A_8))), inference(resolution, [status(thm)], [c_47, c_7387])).
% 8.88/3.00  tff(c_7396, plain, (![A_8]: (k3_subset_1(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_93, c_7393])).
% 8.88/3.00  tff(c_7755, plain, (![A_278, B_279]: (v1_tops_1(k3_subset_1(u1_struct_0(A_278), B_279), A_278) | ~v2_tops_1(B_279, A_278) | ~m1_subset_1(B_279, k1_zfmisc_1(u1_struct_0(A_278))) | ~l1_pre_topc(A_278))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.88/3.00  tff(c_7769, plain, (![B_279]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_279), '#skF_1') | ~v2_tops_1(B_279, '#skF_1') | ~m1_subset_1(B_279, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_7381, c_7755])).
% 8.88/3.00  tff(c_7778, plain, (![B_279]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_279), '#skF_1') | ~v2_tops_1(B_279, '#skF_1') | ~m1_subset_1(B_279, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_7381, c_7769])).
% 8.88/3.00  tff(c_7575, plain, (![B_263, A_264]: (v1_tops_1(B_263, A_264) | k2_pre_topc(A_264, B_263)!=k2_struct_0(A_264) | ~m1_subset_1(B_263, k1_zfmisc_1(u1_struct_0(A_264))) | ~l1_pre_topc(A_264))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.88/3.00  tff(c_7589, plain, (![B_263]: (v1_tops_1(B_263, '#skF_1') | k2_pre_topc('#skF_1', B_263)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_263, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_7381, c_7575])).
% 8.88/3.00  tff(c_7649, plain, (![B_271]: (v1_tops_1(B_271, '#skF_1') | k2_pre_topc('#skF_1', B_271)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_271, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_7589])).
% 8.88/3.00  tff(c_7671, plain, (v1_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_7382, c_7649])).
% 8.88/3.00  tff(c_7697, plain, (k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_7671])).
% 8.88/3.00  tff(c_7600, plain, (![A_265, B_266]: (k2_pre_topc(A_265, B_266)=k2_struct_0(A_265) | ~v1_tops_1(B_266, A_265) | ~m1_subset_1(B_266, k1_zfmisc_1(u1_struct_0(A_265))) | ~l1_pre_topc(A_265))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.88/3.00  tff(c_7614, plain, (![B_266]: (k2_pre_topc('#skF_1', B_266)=k2_struct_0('#skF_1') | ~v1_tops_1(B_266, '#skF_1') | ~m1_subset_1(B_266, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_7381, c_7600])).
% 8.88/3.00  tff(c_7698, plain, (![B_274]: (k2_pre_topc('#skF_1', B_274)=k2_struct_0('#skF_1') | ~v1_tops_1(B_274, '#skF_1') | ~m1_subset_1(B_274, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_7614])).
% 8.88/3.00  tff(c_7712, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_7382, c_7698])).
% 8.88/3.00  tff(c_7724, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_7697, c_7712])).
% 8.88/3.00  tff(c_7432, plain, (![A_252, B_253]: (k3_subset_1(A_252, k3_subset_1(A_252, B_253))=B_253 | ~m1_subset_1(B_253, k1_zfmisc_1(A_252)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.88/3.00  tff(c_7440, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_7382, c_7432])).
% 8.88/3.00  tff(c_7882, plain, (![B_285]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_285), '#skF_1') | ~v2_tops_1(B_285, '#skF_1') | ~m1_subset_1(B_285, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_7381, c_7769])).
% 8.88/3.00  tff(c_7892, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_7440, c_7882])).
% 8.88/3.00  tff(c_7902, plain, (~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_7724, c_7892])).
% 8.88/3.00  tff(c_7909, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_7902])).
% 8.88/3.00  tff(c_7965, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_7909])).
% 8.88/3.00  tff(c_7969, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7382, c_7965])).
% 8.88/3.00  tff(c_7971, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_7902])).
% 8.88/3.00  tff(c_7623, plain, (![B_266]: (k2_pre_topc('#skF_1', B_266)=k2_struct_0('#skF_1') | ~v1_tops_1(B_266, '#skF_1') | ~m1_subset_1(B_266, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_7614])).
% 8.88/3.00  tff(c_7985, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_7971, c_7623])).
% 8.88/3.00  tff(c_7993, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_7985])).
% 8.88/3.00  tff(c_7996, plain, (~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_7778, c_7993])).
% 8.88/3.00  tff(c_8000, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7382, c_7357, c_7996])).
% 8.88/3.00  tff(c_8001, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_7985])).
% 8.88/3.00  tff(c_8039, plain, (![A_289, B_290]: (k3_subset_1(u1_struct_0(A_289), k2_pre_topc(A_289, k3_subset_1(u1_struct_0(A_289), B_290)))=k1_tops_1(A_289, B_290) | ~m1_subset_1(B_290, k1_zfmisc_1(u1_struct_0(A_289))) | ~l1_pre_topc(A_289))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.88/3.00  tff(c_8077, plain, (![B_290]: (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_290)))=k1_tops_1('#skF_1', B_290) | ~m1_subset_1(B_290, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_7381, c_8039])).
% 8.88/3.00  tff(c_8397, plain, (![B_300]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_300)))=k1_tops_1('#skF_1', B_300) | ~m1_subset_1(B_300, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_7381, c_7381, c_8077])).
% 8.88/3.00  tff(c_8433, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_8001, c_8397])).
% 8.88/3.00  tff(c_8456, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7382, c_7396, c_8433])).
% 8.88/3.00  tff(c_8458, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7362, c_8456])).
% 8.88/3.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.88/3.00  
% 8.88/3.00  Inference rules
% 8.88/3.00  ----------------------
% 8.88/3.00  #Ref     : 0
% 8.88/3.00  #Sup     : 2034
% 8.88/3.00  #Fact    : 0
% 8.88/3.00  #Define  : 0
% 8.88/3.00  #Split   : 37
% 8.88/3.00  #Chain   : 0
% 8.88/3.00  #Close   : 0
% 8.88/3.00  
% 8.88/3.00  Ordering : KBO
% 8.88/3.00  
% 8.88/3.00  Simplification rules
% 8.88/3.00  ----------------------
% 8.88/3.00  #Subsume      : 323
% 8.88/3.00  #Demod        : 1638
% 8.88/3.00  #Tautology    : 508
% 8.88/3.00  #SimpNegUnit  : 188
% 8.88/3.00  #BackRed      : 3
% 8.88/3.00  
% 8.88/3.00  #Partial instantiations: 0
% 8.88/3.00  #Strategies tried      : 1
% 8.88/3.00  
% 8.88/3.00  Timing (in seconds)
% 8.88/3.00  ----------------------
% 8.88/3.01  Preprocessing        : 0.32
% 8.88/3.01  Parsing              : 0.17
% 8.88/3.01  CNF conversion       : 0.02
% 8.88/3.01  Main loop            : 1.84
% 8.88/3.01  Inferencing          : 0.58
% 8.88/3.01  Reduction            : 0.67
% 8.88/3.01  Demodulation         : 0.47
% 8.88/3.01  BG Simplification    : 0.07
% 8.88/3.01  Subsumption          : 0.39
% 8.88/3.01  Abstraction          : 0.09
% 8.88/3.01  MUC search           : 0.00
% 8.88/3.01  Cooper               : 0.00
% 8.88/3.01  Total                : 2.21
% 8.88/3.01  Index Insertion      : 0.00
% 8.88/3.01  Index Deletion       : 0.00
% 8.88/3.01  Index Matching       : 0.00
% 8.88/3.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
