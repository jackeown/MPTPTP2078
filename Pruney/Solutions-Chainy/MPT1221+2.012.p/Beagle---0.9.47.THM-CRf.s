%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:25 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 446 expanded)
%              Number of leaves         :   29 ( 162 expanded)
%              Depth                    :   13
%              Number of atoms          :  156 ( 835 expanded)
%              Number of equality atoms :   50 ( 190 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > m1_subset_1 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(A),k2_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22,plain,(
    ! [A_21] :
      ( l1_struct_0(A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_36,plain,(
    ! [A_24] :
      ( u1_struct_0(A_24) = k2_struct_0(A_24)
      | ~ l1_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_41,plain,(
    ! [A_25] :
      ( u1_struct_0(A_25) = k2_struct_0(A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(resolution,[status(thm)],[c_22,c_36])).

tff(c_45,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_41])).

tff(c_28,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_70,plain,
    ( ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_28])).

tff(c_71,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_47,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_24])).

tff(c_34,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_87,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_34])).

tff(c_88,plain,(
    v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_87])).

tff(c_89,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k3_subset_1(A_29,B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_47,c_89])).

tff(c_2,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k4_xboole_0(A_1,B_2)) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_105,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_xboole_0(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_2])).

tff(c_109,plain,(
    ! [A_31,B_32] :
      ( k3_subset_1(A_31,k3_subset_1(A_31,B_32)) = B_32
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_117,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_47,c_109])).

tff(c_123,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k3_subset_1(A_33,B_34),k1_zfmisc_1(A_33))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k3_subset_1(A_3,B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_334,plain,(
    ! [A_50,B_51] :
      ( k4_xboole_0(A_50,k3_subset_1(A_50,B_51)) = k3_subset_1(A_50,k3_subset_1(A_50,B_51))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(resolution,[status(thm)],[c_123,c_4])).

tff(c_340,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_47,c_334])).

tff(c_347,plain,(
    k3_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_117,c_340])).

tff(c_55,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_64,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k3_xboole_0(A_1,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_55])).

tff(c_355,plain,(
    k3_xboole_0(k2_struct_0('#skF_1'),k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_64])).

tff(c_358,plain,(
    k3_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_100,c_355])).

tff(c_20,plain,(
    ! [A_20] :
      ( m1_subset_1(k2_struct_0(A_20),k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_51,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_20])).

tff(c_72,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_51])).

tff(c_75,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_72])).

tff(c_79,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_75])).

tff(c_80,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_51])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k3_subset_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_163,plain,(
    ! [A_37,B_38,C_39] :
      ( k9_subset_1(A_37,B_38,C_39) = k3_xboole_0(B_38,C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_532,plain,(
    ! [A_61,B_62,B_63] :
      ( k9_subset_1(A_61,B_62,k3_subset_1(A_61,B_63)) = k3_xboole_0(B_62,k3_subset_1(A_61,B_63))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_61)) ) ),
    inference(resolution,[status(thm)],[c_6,c_163])).

tff(c_543,plain,(
    ! [B_62] : k9_subset_1(k2_struct_0('#skF_1'),B_62,k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_xboole_0(B_62,k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_47,c_532])).

tff(c_404,plain,(
    ! [A_53,B_54,C_55] :
      ( k9_subset_1(A_53,B_54,k3_subset_1(A_53,C_55)) = k7_subset_1(A_53,B_54,C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(A_53))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_415,plain,(
    ! [B_54] :
      ( k9_subset_1(k2_struct_0('#skF_1'),B_54,k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k7_subset_1(k2_struct_0('#skF_1'),B_54,'#skF_2')
      | ~ m1_subset_1(B_54,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_47,c_404])).

tff(c_667,plain,(
    ! [B_70] :
      ( k3_xboole_0(B_70,k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k7_subset_1(k2_struct_0('#skF_1'),B_70,'#skF_2')
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_415])).

tff(c_674,plain,(
    k3_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_667])).

tff(c_680,plain,(
    k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_674])).

tff(c_328,plain,(
    ! [B_48,A_49] :
      ( v4_pre_topc(B_48,A_49)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_49),k2_struct_0(A_49),B_48),A_49)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_331,plain,(
    ! [B_48] :
      ( v4_pre_topc(B_48,'#skF_1')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_48),'#skF_1')
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_328])).

tff(c_333,plain,(
    ! [B_48] :
      ( v4_pre_topc(B_48,'#skF_1')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_48),'#skF_1')
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_45,c_331])).

tff(c_685,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_680,c_333])).

tff(c_689,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_88,c_685])).

tff(c_691,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_689])).

tff(c_692,plain,(
    ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_693,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_741,plain,(
    ! [A_75,B_76] :
      ( k4_xboole_0(A_75,B_76) = k3_subset_1(A_75,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_756,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_47,c_741])).

tff(c_761,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_xboole_0(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_756,c_2])).

tff(c_700,plain,(
    ! [A_71,B_72] :
      ( k3_subset_1(A_71,k3_subset_1(A_71,B_72)) = B_72
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_705,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_47,c_700])).

tff(c_947,plain,(
    ! [A_93,B_94] :
      ( k4_xboole_0(A_93,k3_subset_1(A_93,B_94)) = k3_subset_1(A_93,k3_subset_1(A_93,B_94))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_93)) ) ),
    inference(resolution,[status(thm)],[c_6,c_741])).

tff(c_953,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_47,c_947])).

tff(c_960,plain,(
    k3_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_761,c_705,c_953])).

tff(c_58,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k3_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,k4_xboole_0(A_27,B_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_2])).

tff(c_966,plain,(
    k3_xboole_0(k2_struct_0('#skF_1'),k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_58])).

tff(c_969,plain,(
    k3_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_756,c_756,c_966])).

tff(c_707,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_51])).

tff(c_714,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_707])).

tff(c_718,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_714])).

tff(c_719,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_51])).

tff(c_800,plain,(
    ! [A_79,B_80,C_81] :
      ( k9_subset_1(A_79,B_80,C_81) = k3_xboole_0(B_80,C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1148,plain,(
    ! [A_105,B_106,B_107] :
      ( k9_subset_1(A_105,B_106,k3_subset_1(A_105,B_107)) = k3_xboole_0(B_106,k3_subset_1(A_105,B_107))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(A_105)) ) ),
    inference(resolution,[status(thm)],[c_6,c_800])).

tff(c_1159,plain,(
    ! [B_106] : k9_subset_1(k2_struct_0('#skF_1'),B_106,k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_xboole_0(B_106,k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_47,c_1148])).

tff(c_1133,plain,(
    ! [A_102,B_103,C_104] :
      ( k9_subset_1(A_102,B_103,k3_subset_1(A_102,C_104)) = k7_subset_1(A_102,B_103,C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(A_102))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1144,plain,(
    ! [B_103] :
      ( k9_subset_1(k2_struct_0('#skF_1'),B_103,k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k7_subset_1(k2_struct_0('#skF_1'),B_103,'#skF_2')
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_47,c_1133])).

tff(c_1496,plain,(
    ! [B_122] :
      ( k3_xboole_0(B_122,k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k7_subset_1(k2_struct_0('#skF_1'),B_122,'#skF_2')
      | ~ m1_subset_1(B_122,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1159,c_1144])).

tff(c_1506,plain,(
    k3_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_719,c_1496])).

tff(c_1513,plain,(
    k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_969,c_1506])).

tff(c_831,plain,(
    ! [A_84,B_85] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(A_84),k2_struct_0(A_84),B_85),A_84)
      | ~ v4_pre_topc(B_85,A_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_834,plain,(
    ! [B_85] :
      ( v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_85),'#skF_1')
      | ~ v4_pre_topc(B_85,'#skF_1')
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_831])).

tff(c_836,plain,(
    ! [B_85] :
      ( v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_85),'#skF_1')
      | ~ v4_pre_topc(B_85,'#skF_1')
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_45,c_834])).

tff(c_1521,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1513,c_836])).

tff(c_1527,plain,(
    v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_693,c_1521])).

tff(c_1529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_692,c_1527])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:54:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.60  
% 3.46/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.60  %$ v4_pre_topc > v3_pre_topc > m1_subset_1 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.46/1.60  
% 3.46/1.60  %Foreground sorts:
% 3.46/1.60  
% 3.46/1.60  
% 3.46/1.60  %Background operators:
% 3.46/1.60  
% 3.46/1.60  
% 3.46/1.60  %Foreground operators:
% 3.46/1.60  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.46/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.46/1.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.46/1.60  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.46/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.46/1.60  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.46/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.46/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.46/1.60  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.46/1.60  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.46/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.46/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.46/1.60  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.46/1.60  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.46/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.46/1.60  
% 3.46/1.62  tff(f_81, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 3.46/1.62  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.46/1.62  tff(f_54, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.46/1.62  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.46/1.62  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.46/1.62  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.46/1.62  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.46/1.62  tff(f_67, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 3.46/1.62  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.46/1.62  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 3.46/1.62  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k7_subset_1(u1_struct_0(A), k2_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_pre_topc)).
% 3.46/1.62  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.46/1.62  tff(c_22, plain, (![A_21]: (l1_struct_0(A_21) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.46/1.62  tff(c_36, plain, (![A_24]: (u1_struct_0(A_24)=k2_struct_0(A_24) | ~l1_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.46/1.62  tff(c_41, plain, (![A_25]: (u1_struct_0(A_25)=k2_struct_0(A_25) | ~l1_pre_topc(A_25))), inference(resolution, [status(thm)], [c_22, c_36])).
% 3.46/1.62  tff(c_45, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_41])).
% 3.46/1.62  tff(c_28, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.46/1.62  tff(c_70, plain, (~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_28])).
% 3.46/1.62  tff(c_71, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_70])).
% 3.46/1.62  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.46/1.62  tff(c_47, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_24])).
% 3.46/1.62  tff(c_34, plain, (v4_pre_topc('#skF_2', '#skF_1') | v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.46/1.62  tff(c_87, plain, (v4_pre_topc('#skF_2', '#skF_1') | v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_34])).
% 3.46/1.62  tff(c_88, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_71, c_87])).
% 3.46/1.62  tff(c_89, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k3_subset_1(A_29, B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.46/1.62  tff(c_100, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_47, c_89])).
% 3.46/1.62  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k4_xboole_0(A_1, B_2))=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.46/1.62  tff(c_105, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_xboole_0(k2_struct_0('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_100, c_2])).
% 3.46/1.62  tff(c_109, plain, (![A_31, B_32]: (k3_subset_1(A_31, k3_subset_1(A_31, B_32))=B_32 | ~m1_subset_1(B_32, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.46/1.62  tff(c_117, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_47, c_109])).
% 3.46/1.62  tff(c_123, plain, (![A_33, B_34]: (m1_subset_1(k3_subset_1(A_33, B_34), k1_zfmisc_1(A_33)) | ~m1_subset_1(B_34, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.46/1.62  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k3_subset_1(A_3, B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.46/1.62  tff(c_334, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k3_subset_1(A_50, B_51))=k3_subset_1(A_50, k3_subset_1(A_50, B_51)) | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(resolution, [status(thm)], [c_123, c_4])).
% 3.46/1.62  tff(c_340, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_47, c_334])).
% 3.46/1.62  tff(c_347, plain, (k3_xboole_0(k2_struct_0('#skF_1'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_105, c_117, c_340])).
% 3.46/1.62  tff(c_55, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.46/1.62  tff(c_64, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k3_xboole_0(A_1, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_55])).
% 3.46/1.62  tff(c_355, plain, (k3_xboole_0(k2_struct_0('#skF_1'), k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2'))=k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_347, c_64])).
% 3.46/1.62  tff(c_358, plain, (k3_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_100, c_355])).
% 3.46/1.62  tff(c_20, plain, (![A_20]: (m1_subset_1(k2_struct_0(A_20), k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.46/1.62  tff(c_51, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_45, c_20])).
% 3.46/1.62  tff(c_72, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_51])).
% 3.46/1.62  tff(c_75, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_72])).
% 3.46/1.62  tff(c_79, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_75])).
% 3.46/1.62  tff(c_80, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_51])).
% 3.46/1.62  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(k3_subset_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.46/1.62  tff(c_163, plain, (![A_37, B_38, C_39]: (k9_subset_1(A_37, B_38, C_39)=k3_xboole_0(B_38, C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.46/1.62  tff(c_532, plain, (![A_61, B_62, B_63]: (k9_subset_1(A_61, B_62, k3_subset_1(A_61, B_63))=k3_xboole_0(B_62, k3_subset_1(A_61, B_63)) | ~m1_subset_1(B_63, k1_zfmisc_1(A_61)))), inference(resolution, [status(thm)], [c_6, c_163])).
% 3.46/1.62  tff(c_543, plain, (![B_62]: (k9_subset_1(k2_struct_0('#skF_1'), B_62, k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_xboole_0(B_62, k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')))), inference(resolution, [status(thm)], [c_47, c_532])).
% 3.46/1.62  tff(c_404, plain, (![A_53, B_54, C_55]: (k9_subset_1(A_53, B_54, k3_subset_1(A_53, C_55))=k7_subset_1(A_53, B_54, C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(A_53)) | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.46/1.62  tff(c_415, plain, (![B_54]: (k9_subset_1(k2_struct_0('#skF_1'), B_54, k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k7_subset_1(k2_struct_0('#skF_1'), B_54, '#skF_2') | ~m1_subset_1(B_54, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_47, c_404])).
% 3.46/1.62  tff(c_667, plain, (![B_70]: (k3_xboole_0(B_70, k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k7_subset_1(k2_struct_0('#skF_1'), B_70, '#skF_2') | ~m1_subset_1(B_70, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_543, c_415])).
% 3.46/1.62  tff(c_674, plain, (k3_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_80, c_667])).
% 3.46/1.62  tff(c_680, plain, (k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_358, c_674])).
% 3.46/1.62  tff(c_328, plain, (![B_48, A_49]: (v4_pre_topc(B_48, A_49) | ~v3_pre_topc(k7_subset_1(u1_struct_0(A_49), k2_struct_0(A_49), B_48), A_49) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.46/1.62  tff(c_331, plain, (![B_48]: (v4_pre_topc(B_48, '#skF_1') | ~v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_48), '#skF_1') | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_45, c_328])).
% 3.46/1.62  tff(c_333, plain, (![B_48]: (v4_pre_topc(B_48, '#skF_1') | ~v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_48), '#skF_1') | ~m1_subset_1(B_48, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_45, c_331])).
% 3.46/1.62  tff(c_685, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_680, c_333])).
% 3.46/1.62  tff(c_689, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_88, c_685])).
% 3.46/1.62  tff(c_691, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_689])).
% 3.46/1.62  tff(c_692, plain, (~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_70])).
% 3.46/1.62  tff(c_693, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_70])).
% 3.46/1.62  tff(c_741, plain, (![A_75, B_76]: (k4_xboole_0(A_75, B_76)=k3_subset_1(A_75, B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.46/1.62  tff(c_756, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_47, c_741])).
% 3.46/1.62  tff(c_761, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_xboole_0(k2_struct_0('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_756, c_2])).
% 3.46/1.62  tff(c_700, plain, (![A_71, B_72]: (k3_subset_1(A_71, k3_subset_1(A_71, B_72))=B_72 | ~m1_subset_1(B_72, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.46/1.62  tff(c_705, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_47, c_700])).
% 3.46/1.62  tff(c_947, plain, (![A_93, B_94]: (k4_xboole_0(A_93, k3_subset_1(A_93, B_94))=k3_subset_1(A_93, k3_subset_1(A_93, B_94)) | ~m1_subset_1(B_94, k1_zfmisc_1(A_93)))), inference(resolution, [status(thm)], [c_6, c_741])).
% 3.46/1.62  tff(c_953, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_47, c_947])).
% 3.46/1.62  tff(c_960, plain, (k3_xboole_0(k2_struct_0('#skF_1'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_761, c_705, c_953])).
% 3.46/1.62  tff(c_58, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k3_xboole_0(A_27, B_28))=k3_xboole_0(A_27, k4_xboole_0(A_27, B_28)))), inference(superposition, [status(thm), theory('equality')], [c_55, c_2])).
% 3.46/1.62  tff(c_966, plain, (k3_xboole_0(k2_struct_0('#skF_1'), k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2'))=k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_960, c_58])).
% 3.46/1.62  tff(c_969, plain, (k3_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_756, c_756, c_966])).
% 3.46/1.62  tff(c_707, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_51])).
% 3.46/1.62  tff(c_714, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_707])).
% 3.46/1.62  tff(c_718, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_714])).
% 3.46/1.62  tff(c_719, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_51])).
% 3.46/1.62  tff(c_800, plain, (![A_79, B_80, C_81]: (k9_subset_1(A_79, B_80, C_81)=k3_xboole_0(B_80, C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.46/1.62  tff(c_1148, plain, (![A_105, B_106, B_107]: (k9_subset_1(A_105, B_106, k3_subset_1(A_105, B_107))=k3_xboole_0(B_106, k3_subset_1(A_105, B_107)) | ~m1_subset_1(B_107, k1_zfmisc_1(A_105)))), inference(resolution, [status(thm)], [c_6, c_800])).
% 3.46/1.62  tff(c_1159, plain, (![B_106]: (k9_subset_1(k2_struct_0('#skF_1'), B_106, k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_xboole_0(B_106, k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')))), inference(resolution, [status(thm)], [c_47, c_1148])).
% 3.46/1.62  tff(c_1133, plain, (![A_102, B_103, C_104]: (k9_subset_1(A_102, B_103, k3_subset_1(A_102, C_104))=k7_subset_1(A_102, B_103, C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(A_102)) | ~m1_subset_1(B_103, k1_zfmisc_1(A_102)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.46/1.62  tff(c_1144, plain, (![B_103]: (k9_subset_1(k2_struct_0('#skF_1'), B_103, k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k7_subset_1(k2_struct_0('#skF_1'), B_103, '#skF_2') | ~m1_subset_1(B_103, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_47, c_1133])).
% 3.46/1.62  tff(c_1496, plain, (![B_122]: (k3_xboole_0(B_122, k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k7_subset_1(k2_struct_0('#skF_1'), B_122, '#skF_2') | ~m1_subset_1(B_122, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_1159, c_1144])).
% 3.46/1.62  tff(c_1506, plain, (k3_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_719, c_1496])).
% 3.46/1.62  tff(c_1513, plain, (k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_969, c_1506])).
% 3.46/1.62  tff(c_831, plain, (![A_84, B_85]: (v3_pre_topc(k7_subset_1(u1_struct_0(A_84), k2_struct_0(A_84), B_85), A_84) | ~v4_pre_topc(B_85, A_84) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.46/1.62  tff(c_834, plain, (![B_85]: (v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_85), '#skF_1') | ~v4_pre_topc(B_85, '#skF_1') | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_45, c_831])).
% 3.46/1.62  tff(c_836, plain, (![B_85]: (v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_85), '#skF_1') | ~v4_pre_topc(B_85, '#skF_1') | ~m1_subset_1(B_85, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_45, c_834])).
% 3.46/1.62  tff(c_1521, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1513, c_836])).
% 3.46/1.62  tff(c_1527, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_693, c_1521])).
% 3.46/1.62  tff(c_1529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_692, c_1527])).
% 3.46/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.62  
% 3.46/1.62  Inference rules
% 3.46/1.62  ----------------------
% 3.46/1.62  #Ref     : 0
% 3.46/1.62  #Sup     : 386
% 3.46/1.62  #Fact    : 0
% 3.46/1.62  #Define  : 0
% 3.46/1.62  #Split   : 6
% 3.46/1.62  #Chain   : 0
% 3.46/1.62  #Close   : 0
% 3.46/1.62  
% 3.46/1.62  Ordering : KBO
% 3.46/1.62  
% 3.46/1.62  Simplification rules
% 3.46/1.62  ----------------------
% 3.46/1.62  #Subsume      : 7
% 3.46/1.62  #Demod        : 340
% 3.46/1.62  #Tautology    : 225
% 3.46/1.62  #SimpNegUnit  : 5
% 3.46/1.62  #BackRed      : 7
% 3.46/1.62  
% 3.46/1.62  #Partial instantiations: 0
% 3.46/1.62  #Strategies tried      : 1
% 3.46/1.62  
% 3.46/1.62  Timing (in seconds)
% 3.46/1.62  ----------------------
% 3.46/1.63  Preprocessing        : 0.33
% 3.46/1.63  Parsing              : 0.18
% 3.46/1.63  CNF conversion       : 0.02
% 3.46/1.63  Main loop            : 0.49
% 3.46/1.63  Inferencing          : 0.18
% 3.46/1.63  Reduction            : 0.17
% 3.46/1.63  Demodulation         : 0.13
% 3.46/1.63  BG Simplification    : 0.03
% 3.46/1.63  Subsumption          : 0.07
% 3.46/1.63  Abstraction          : 0.03
% 3.46/1.63  MUC search           : 0.00
% 3.46/1.63  Cooper               : 0.00
% 3.46/1.63  Total                : 0.87
% 3.46/1.63  Index Insertion      : 0.00
% 3.46/1.63  Index Deletion       : 0.00
% 3.46/1.63  Index Matching       : 0.00
% 3.46/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
