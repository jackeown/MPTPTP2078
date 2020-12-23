%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:45 EST 2020

% Result     : Theorem 9.53s
% Output     : CNFRefutation 9.67s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 925 expanded)
%              Number of leaves         :   35 ( 323 expanded)
%              Depth                    :   15
%              Number of atoms          :  238 (1955 expanded)
%              Number of equality atoms :   70 ( 541 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > v1_tops_1 > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_77,axiom,(
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

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(c_44,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_83,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_38,plain,
    ( k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_94,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_38])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_22,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_73,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_78,plain,(
    ! [A_33] :
      ( u1_struct_0(A_33) = k2_struct_0(A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_22,c_73])).

tff(c_82,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_78])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_88,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_34])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k3_subset_1(A_9,B_10),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_428,plain,(
    ! [B_59,A_60] :
      ( v1_tops_1(B_59,A_60)
      | k2_pre_topc(A_60,B_59) != k2_struct_0(A_60)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_442,plain,(
    ! [B_59] :
      ( v1_tops_1(B_59,'#skF_1')
      | k2_pre_topc('#skF_1',B_59) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_59,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_428])).

tff(c_474,plain,(
    ! [B_62] :
      ( v1_tops_1(B_62,'#skF_1')
      | k2_pre_topc('#skF_1',B_62) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_442])).

tff(c_496,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_88,c_474])).

tff(c_499,plain,(
    k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_496])).

tff(c_501,plain,(
    ! [A_63,B_64] :
      ( k2_pre_topc(A_63,B_64) = k2_struct_0(A_63)
      | ~ v1_tops_1(B_64,A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_515,plain,(
    ! [B_64] :
      ( k2_pre_topc('#skF_1',B_64) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_64,'#skF_1')
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_501])).

tff(c_532,plain,(
    ! [B_66] :
      ( k2_pre_topc('#skF_1',B_66) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_66,'#skF_1')
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_515])).

tff(c_546,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_88,c_532])).

tff(c_558,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_499,c_546])).

tff(c_155,plain,(
    ! [A_40,B_41] :
      ( k3_subset_1(A_40,k3_subset_1(A_40,B_41)) = B_41
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_163,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_88,c_155])).

tff(c_586,plain,(
    ! [A_69,B_70] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_69),B_70),A_69)
      | ~ v2_tops_1(B_70,A_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_601,plain,(
    ! [B_70] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_70),'#skF_1')
      | ~ v2_tops_1(B_70,'#skF_1')
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_586])).

tff(c_626,plain,(
    ! [B_73] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_73),'#skF_1')
      | ~ v2_tops_1(B_73,'#skF_1')
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_82,c_601])).

tff(c_641,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_626])).

tff(c_648,plain,
    ( ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_558,c_641])).

tff(c_829,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_648])).

tff(c_832,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_14,c_829])).

tff(c_836,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_832])).

tff(c_838,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_648])).

tff(c_451,plain,(
    ! [B_59] :
      ( v1_tops_1(B_59,'#skF_1')
      | k2_pre_topc('#skF_1',B_59) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_59,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_442])).

tff(c_853,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_838,c_451])).

tff(c_1088,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_853])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_95,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k4_xboole_0(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_95])).

tff(c_113,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_110])).

tff(c_8,plain,(
    ! [A_5] : k2_subset_1(A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1(k2_subset_1(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_45,plain,(
    ! [A_8] : m1_subset_1(A_8,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12])).

tff(c_186,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(A_43,B_44) = k3_subset_1(A_43,B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_195,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_subset_1(A_8,A_8) ),
    inference(resolution,[status(thm)],[c_45,c_186])).

tff(c_199,plain,(
    ! [A_8] : k3_subset_1(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_195])).

tff(c_164,plain,(
    ! [A_8] : k3_subset_1(A_8,k3_subset_1(A_8,A_8)) = A_8 ),
    inference(resolution,[status(thm)],[c_45,c_155])).

tff(c_200,plain,(
    ! [A_8] : k3_subset_1(A_8,k1_xboole_0) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_164])).

tff(c_24,plain,(
    ! [A_17,B_19] :
      ( k3_subset_1(u1_struct_0(A_17),k2_pre_topc(A_17,k3_subset_1(u1_struct_0(A_17),B_19))) = k1_tops_1(A_17,B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_246,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1(k2_pre_topc(A_48,B_49),k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( k3_subset_1(A_11,k3_subset_1(A_11,B_12)) = B_12
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1191,plain,(
    ! [A_92,B_93] :
      ( k3_subset_1(u1_struct_0(A_92),k3_subset_1(u1_struct_0(A_92),k2_pre_topc(A_92,B_93))) = k2_pre_topc(A_92,B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_246,c_16])).

tff(c_7879,plain,(
    ! [A_235,B_236] :
      ( k3_subset_1(u1_struct_0(A_235),k1_tops_1(A_235,B_236)) = k2_pre_topc(A_235,k3_subset_1(u1_struct_0(A_235),B_236))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_235),B_236),k1_zfmisc_1(u1_struct_0(A_235)))
      | ~ l1_pre_topc(A_235)
      | ~ m1_subset_1(B_236,k1_zfmisc_1(u1_struct_0(A_235)))
      | ~ l1_pre_topc(A_235) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1191])).

tff(c_7958,plain,(
    ! [B_236] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1',B_236)) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_236))
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),B_236),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_236,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_7879])).

tff(c_8002,plain,(
    ! [B_238] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k1_tops_1('#skF_1',B_238)) = k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_238))
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),B_238),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_238,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_82,c_36,c_82,c_82,c_82,c_7958])).

tff(c_8056,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_838,c_8002])).

tff(c_8100,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_200,c_83,c_8056])).

tff(c_8102,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1088,c_8100])).

tff(c_8103,plain,(
    v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_853])).

tff(c_739,plain,(
    ! [B_78,A_79] :
      ( v2_tops_1(B_78,A_79)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_79),B_78),A_79)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_757,plain,(
    ! [B_78] :
      ( v2_tops_1(B_78,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_78),'#skF_1')
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_739])).

tff(c_764,plain,(
    ! [B_78] :
      ( v2_tops_1(B_78,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_78),'#skF_1')
      | ~ m1_subset_1(B_78,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_82,c_757])).

tff(c_8107,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8103,c_764])).

tff(c_8110,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_8107])).

tff(c_8112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_8110])).

tff(c_8114,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_8115,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_34])).

tff(c_8122,plain,(
    ! [A_239,B_240] : k4_xboole_0(A_239,k4_xboole_0(A_239,B_240)) = k3_xboole_0(A_239,B_240) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8137,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_8122])).

tff(c_8140,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8137])).

tff(c_8182,plain,(
    ! [A_245,B_246] :
      ( k4_xboole_0(A_245,B_246) = k3_subset_1(A_245,B_246)
      | ~ m1_subset_1(B_246,k1_zfmisc_1(A_245)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8191,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_subset_1(A_8,A_8) ),
    inference(resolution,[status(thm)],[c_45,c_8182])).

tff(c_8195,plain,(
    ! [A_8] : k3_subset_1(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8140,c_8191])).

tff(c_8113,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_8552,plain,(
    ! [A_271,B_272] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_271),B_272),A_271)
      | ~ v2_tops_1(B_272,A_271)
      | ~ m1_subset_1(B_272,k1_zfmisc_1(u1_struct_0(A_271)))
      | ~ l1_pre_topc(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_8563,plain,(
    ! [B_272] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_272),'#skF_1')
      | ~ v2_tops_1(B_272,'#skF_1')
      | ~ m1_subset_1(B_272,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_8552])).

tff(c_8569,plain,(
    ! [B_272] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_272),'#skF_1')
      | ~ v2_tops_1(B_272,'#skF_1')
      | ~ m1_subset_1(B_272,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_82,c_8563])).

tff(c_8395,plain,(
    ! [A_261,B_262] :
      ( k2_pre_topc(A_261,B_262) = k2_struct_0(A_261)
      | ~ v1_tops_1(B_262,A_261)
      | ~ m1_subset_1(B_262,k1_zfmisc_1(u1_struct_0(A_261)))
      | ~ l1_pre_topc(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8409,plain,(
    ! [B_262] :
      ( k2_pre_topc('#skF_1',B_262) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_262,'#skF_1')
      | ~ m1_subset_1(B_262,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_8395])).

tff(c_8441,plain,(
    ! [B_264] :
      ( k2_pre_topc('#skF_1',B_264) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_264,'#skF_1')
      | ~ m1_subset_1(B_264,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8409])).

tff(c_8463,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_8115,c_8441])).

tff(c_8466,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_8463])).

tff(c_8245,plain,(
    ! [A_250,B_251] :
      ( k3_subset_1(A_250,k3_subset_1(A_250,B_251)) = B_251
      | ~ m1_subset_1(B_251,k1_zfmisc_1(A_250)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8257,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8115,c_8245])).

tff(c_8588,plain,(
    ! [B_275] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_275),'#skF_1')
      | ~ v2_tops_1(B_275,'#skF_1')
      | ~ m1_subset_1(B_275,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_82,c_8563])).

tff(c_8591,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8257,c_8588])).

tff(c_8600,plain,
    ( ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_8466,c_8591])).

tff(c_8843,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_8600])).

tff(c_8846,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_14,c_8843])).

tff(c_8850,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8115,c_8846])).

tff(c_8852,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_8600])).

tff(c_8418,plain,(
    ! [B_262] :
      ( k2_pre_topc('#skF_1',B_262) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_262,'#skF_1')
      | ~ m1_subset_1(B_262,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8409])).

tff(c_8920,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_8852,c_8418])).

tff(c_9101,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_8920])).

tff(c_9104,plain,
    ( ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8569,c_9101])).

tff(c_9108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8115,c_8113,c_9104])).

tff(c_9109,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_8920])).

tff(c_8853,plain,(
    ! [A_288,B_289] :
      ( k3_subset_1(u1_struct_0(A_288),k2_pre_topc(A_288,k3_subset_1(u1_struct_0(A_288),B_289))) = k1_tops_1(A_288,B_289)
      | ~ m1_subset_1(B_289,k1_zfmisc_1(u1_struct_0(A_288)))
      | ~ l1_pre_topc(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8892,plain,(
    ! [B_289] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_289))) = k1_tops_1('#skF_1',B_289)
      | ~ m1_subset_1(B_289,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_8853])).

tff(c_8903,plain,(
    ! [B_289] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_289))) = k1_tops_1('#skF_1',B_289)
      | ~ m1_subset_1(B_289,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_82,c_82,c_8892])).

tff(c_9143,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_9109,c_8903])).

tff(c_9153,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8115,c_8195,c_9143])).

tff(c_9155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8114,c_9153])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:44:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.53/3.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.53/3.22  
% 9.53/3.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.53/3.22  %$ v2_tops_1 > v1_tops_1 > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 9.53/3.22  
% 9.53/3.22  %Foreground sorts:
% 9.53/3.22  
% 9.53/3.22  
% 9.53/3.22  %Background operators:
% 9.53/3.22  
% 9.53/3.22  
% 9.53/3.22  %Foreground operators:
% 9.53/3.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.53/3.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.53/3.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.53/3.22  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 9.53/3.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.53/3.22  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 9.53/3.22  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 9.53/3.22  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 9.53/3.22  tff('#skF_2', type, '#skF_2': $i).
% 9.53/3.22  tff('#skF_1', type, '#skF_1': $i).
% 9.53/3.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.53/3.22  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 9.53/3.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.53/3.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.53/3.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.53/3.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.53/3.22  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 9.53/3.22  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 9.53/3.22  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 9.53/3.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.53/3.22  
% 9.67/3.25  tff(f_96, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 9.67/3.25  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 9.67/3.25  tff(f_51, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 9.67/3.25  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 9.67/3.25  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 9.67/3.25  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 9.67/3.25  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 9.67/3.25  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 9.67/3.25  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 9.67/3.25  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.67/3.25  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 9.67/3.25  tff(f_39, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 9.67/3.25  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 9.67/3.25  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 9.67/3.25  tff(f_57, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 9.67/3.25  tff(c_44, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.67/3.25  tff(c_83, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_44])).
% 9.67/3.25  tff(c_38, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.67/3.25  tff(c_94, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_38])).
% 9.67/3.25  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.67/3.25  tff(c_22, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.67/3.25  tff(c_73, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.67/3.25  tff(c_78, plain, (![A_33]: (u1_struct_0(A_33)=k2_struct_0(A_33) | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_22, c_73])).
% 9.67/3.25  tff(c_82, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_78])).
% 9.67/3.25  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.67/3.25  tff(c_88, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_34])).
% 9.67/3.25  tff(c_14, plain, (![A_9, B_10]: (m1_subset_1(k3_subset_1(A_9, B_10), k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.67/3.25  tff(c_428, plain, (![B_59, A_60]: (v1_tops_1(B_59, A_60) | k2_pre_topc(A_60, B_59)!=k2_struct_0(A_60) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.67/3.25  tff(c_442, plain, (![B_59]: (v1_tops_1(B_59, '#skF_1') | k2_pre_topc('#skF_1', B_59)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_59, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_428])).
% 9.67/3.25  tff(c_474, plain, (![B_62]: (v1_tops_1(B_62, '#skF_1') | k2_pre_topc('#skF_1', B_62)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_62, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_442])).
% 9.67/3.25  tff(c_496, plain, (v1_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_88, c_474])).
% 9.67/3.25  tff(c_499, plain, (k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_496])).
% 9.67/3.25  tff(c_501, plain, (![A_63, B_64]: (k2_pre_topc(A_63, B_64)=k2_struct_0(A_63) | ~v1_tops_1(B_64, A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.67/3.25  tff(c_515, plain, (![B_64]: (k2_pre_topc('#skF_1', B_64)=k2_struct_0('#skF_1') | ~v1_tops_1(B_64, '#skF_1') | ~m1_subset_1(B_64, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_501])).
% 9.67/3.25  tff(c_532, plain, (![B_66]: (k2_pre_topc('#skF_1', B_66)=k2_struct_0('#skF_1') | ~v1_tops_1(B_66, '#skF_1') | ~m1_subset_1(B_66, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_515])).
% 9.67/3.25  tff(c_546, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_88, c_532])).
% 9.67/3.25  tff(c_558, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_499, c_546])).
% 9.67/3.25  tff(c_155, plain, (![A_40, B_41]: (k3_subset_1(A_40, k3_subset_1(A_40, B_41))=B_41 | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.67/3.25  tff(c_163, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_88, c_155])).
% 9.67/3.25  tff(c_586, plain, (![A_69, B_70]: (v1_tops_1(k3_subset_1(u1_struct_0(A_69), B_70), A_69) | ~v2_tops_1(B_70, A_69) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.67/3.25  tff(c_601, plain, (![B_70]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_70), '#skF_1') | ~v2_tops_1(B_70, '#skF_1') | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_586])).
% 9.67/3.25  tff(c_626, plain, (![B_73]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_73), '#skF_1') | ~v2_tops_1(B_73, '#skF_1') | ~m1_subset_1(B_73, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_82, c_601])).
% 9.67/3.25  tff(c_641, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_163, c_626])).
% 9.67/3.25  tff(c_648, plain, (~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_558, c_641])).
% 9.67/3.25  tff(c_829, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_648])).
% 9.67/3.25  tff(c_832, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_829])).
% 9.67/3.25  tff(c_836, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_832])).
% 9.67/3.25  tff(c_838, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_648])).
% 9.67/3.25  tff(c_451, plain, (![B_59]: (v1_tops_1(B_59, '#skF_1') | k2_pre_topc('#skF_1', B_59)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_59, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_442])).
% 9.67/3.25  tff(c_853, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_838, c_451])).
% 9.67/3.25  tff(c_1088, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_853])).
% 9.67/3.25  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.67/3.25  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.67/3.25  tff(c_95, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k4_xboole_0(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.67/3.25  tff(c_110, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_95])).
% 9.67/3.25  tff(c_113, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_110])).
% 9.67/3.25  tff(c_8, plain, (![A_5]: (k2_subset_1(A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.67/3.25  tff(c_12, plain, (![A_8]: (m1_subset_1(k2_subset_1(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.67/3.25  tff(c_45, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_12])).
% 9.67/3.25  tff(c_186, plain, (![A_43, B_44]: (k4_xboole_0(A_43, B_44)=k3_subset_1(A_43, B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.67/3.25  tff(c_195, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_subset_1(A_8, A_8))), inference(resolution, [status(thm)], [c_45, c_186])).
% 9.67/3.25  tff(c_199, plain, (![A_8]: (k3_subset_1(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_113, c_195])).
% 9.67/3.25  tff(c_164, plain, (![A_8]: (k3_subset_1(A_8, k3_subset_1(A_8, A_8))=A_8)), inference(resolution, [status(thm)], [c_45, c_155])).
% 9.67/3.25  tff(c_200, plain, (![A_8]: (k3_subset_1(A_8, k1_xboole_0)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_199, c_164])).
% 9.67/3.25  tff(c_24, plain, (![A_17, B_19]: (k3_subset_1(u1_struct_0(A_17), k2_pre_topc(A_17, k3_subset_1(u1_struct_0(A_17), B_19)))=k1_tops_1(A_17, B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.67/3.25  tff(c_246, plain, (![A_48, B_49]: (m1_subset_1(k2_pre_topc(A_48, B_49), k1_zfmisc_1(u1_struct_0(A_48))) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.67/3.25  tff(c_16, plain, (![A_11, B_12]: (k3_subset_1(A_11, k3_subset_1(A_11, B_12))=B_12 | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.67/3.25  tff(c_1191, plain, (![A_92, B_93]: (k3_subset_1(u1_struct_0(A_92), k3_subset_1(u1_struct_0(A_92), k2_pre_topc(A_92, B_93)))=k2_pre_topc(A_92, B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(resolution, [status(thm)], [c_246, c_16])).
% 9.67/3.25  tff(c_7879, plain, (![A_235, B_236]: (k3_subset_1(u1_struct_0(A_235), k1_tops_1(A_235, B_236))=k2_pre_topc(A_235, k3_subset_1(u1_struct_0(A_235), B_236)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_235), B_236), k1_zfmisc_1(u1_struct_0(A_235))) | ~l1_pre_topc(A_235) | ~m1_subset_1(B_236, k1_zfmisc_1(u1_struct_0(A_235))) | ~l1_pre_topc(A_235))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1191])).
% 9.67/3.25  tff(c_7958, plain, (![B_236]: (k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', B_236))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_236)) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), B_236), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1(B_236, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_7879])).
% 9.67/3.25  tff(c_8002, plain, (![B_238]: (k3_subset_1(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', B_238))=k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_238)) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), B_238), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_238, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_82, c_36, c_82, c_82, c_82, c_7958])).
% 9.67/3.25  tff(c_8056, plain, (k3_subset_1(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_838, c_8002])).
% 9.67/3.25  tff(c_8100, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_200, c_83, c_8056])).
% 9.67/3.25  tff(c_8102, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1088, c_8100])).
% 9.67/3.25  tff(c_8103, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_853])).
% 9.67/3.25  tff(c_739, plain, (![B_78, A_79]: (v2_tops_1(B_78, A_79) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_79), B_78), A_79) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.67/3.25  tff(c_757, plain, (![B_78]: (v2_tops_1(B_78, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_78), '#skF_1') | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_739])).
% 9.67/3.25  tff(c_764, plain, (![B_78]: (v2_tops_1(B_78, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_78), '#skF_1') | ~m1_subset_1(B_78, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_82, c_757])).
% 9.67/3.25  tff(c_8107, plain, (v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8103, c_764])).
% 9.67/3.25  tff(c_8110, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_8107])).
% 9.67/3.25  tff(c_8112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_8110])).
% 9.67/3.25  tff(c_8114, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 9.67/3.25  tff(c_8115, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_34])).
% 9.67/3.25  tff(c_8122, plain, (![A_239, B_240]: (k4_xboole_0(A_239, k4_xboole_0(A_239, B_240))=k3_xboole_0(A_239, B_240))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.67/3.25  tff(c_8137, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_8122])).
% 9.67/3.25  tff(c_8140, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8137])).
% 9.67/3.25  tff(c_8182, plain, (![A_245, B_246]: (k4_xboole_0(A_245, B_246)=k3_subset_1(A_245, B_246) | ~m1_subset_1(B_246, k1_zfmisc_1(A_245)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.67/3.25  tff(c_8191, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_subset_1(A_8, A_8))), inference(resolution, [status(thm)], [c_45, c_8182])).
% 9.67/3.25  tff(c_8195, plain, (![A_8]: (k3_subset_1(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8140, c_8191])).
% 9.67/3.25  tff(c_8113, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 9.67/3.25  tff(c_8552, plain, (![A_271, B_272]: (v1_tops_1(k3_subset_1(u1_struct_0(A_271), B_272), A_271) | ~v2_tops_1(B_272, A_271) | ~m1_subset_1(B_272, k1_zfmisc_1(u1_struct_0(A_271))) | ~l1_pre_topc(A_271))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.67/3.25  tff(c_8563, plain, (![B_272]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_272), '#skF_1') | ~v2_tops_1(B_272, '#skF_1') | ~m1_subset_1(B_272, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_8552])).
% 9.67/3.25  tff(c_8569, plain, (![B_272]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_272), '#skF_1') | ~v2_tops_1(B_272, '#skF_1') | ~m1_subset_1(B_272, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_82, c_8563])).
% 9.67/3.25  tff(c_8395, plain, (![A_261, B_262]: (k2_pre_topc(A_261, B_262)=k2_struct_0(A_261) | ~v1_tops_1(B_262, A_261) | ~m1_subset_1(B_262, k1_zfmisc_1(u1_struct_0(A_261))) | ~l1_pre_topc(A_261))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.67/3.25  tff(c_8409, plain, (![B_262]: (k2_pre_topc('#skF_1', B_262)=k2_struct_0('#skF_1') | ~v1_tops_1(B_262, '#skF_1') | ~m1_subset_1(B_262, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_8395])).
% 9.67/3.25  tff(c_8441, plain, (![B_264]: (k2_pre_topc('#skF_1', B_264)=k2_struct_0('#skF_1') | ~v1_tops_1(B_264, '#skF_1') | ~m1_subset_1(B_264, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_8409])).
% 9.67/3.25  tff(c_8463, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_8115, c_8441])).
% 9.67/3.25  tff(c_8466, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_8463])).
% 9.67/3.25  tff(c_8245, plain, (![A_250, B_251]: (k3_subset_1(A_250, k3_subset_1(A_250, B_251))=B_251 | ~m1_subset_1(B_251, k1_zfmisc_1(A_250)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.67/3.25  tff(c_8257, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_8115, c_8245])).
% 9.67/3.25  tff(c_8588, plain, (![B_275]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_275), '#skF_1') | ~v2_tops_1(B_275, '#skF_1') | ~m1_subset_1(B_275, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_82, c_8563])).
% 9.67/3.25  tff(c_8591, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_8257, c_8588])).
% 9.67/3.25  tff(c_8600, plain, (~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_8466, c_8591])).
% 9.67/3.25  tff(c_8843, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_8600])).
% 9.67/3.25  tff(c_8846, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_8843])).
% 9.67/3.25  tff(c_8850, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8115, c_8846])).
% 9.67/3.25  tff(c_8852, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_8600])).
% 9.67/3.25  tff(c_8418, plain, (![B_262]: (k2_pre_topc('#skF_1', B_262)=k2_struct_0('#skF_1') | ~v1_tops_1(B_262, '#skF_1') | ~m1_subset_1(B_262, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_8409])).
% 9.67/3.25  tff(c_8920, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_8852, c_8418])).
% 9.67/3.25  tff(c_9101, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_8920])).
% 9.67/3.25  tff(c_9104, plain, (~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8569, c_9101])).
% 9.67/3.25  tff(c_9108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8115, c_8113, c_9104])).
% 9.67/3.25  tff(c_9109, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_8920])).
% 9.67/3.25  tff(c_8853, plain, (![A_288, B_289]: (k3_subset_1(u1_struct_0(A_288), k2_pre_topc(A_288, k3_subset_1(u1_struct_0(A_288), B_289)))=k1_tops_1(A_288, B_289) | ~m1_subset_1(B_289, k1_zfmisc_1(u1_struct_0(A_288))) | ~l1_pre_topc(A_288))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.67/3.25  tff(c_8892, plain, (![B_289]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_289)))=k1_tops_1('#skF_1', B_289) | ~m1_subset_1(B_289, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_8853])).
% 9.67/3.25  tff(c_8903, plain, (![B_289]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_289)))=k1_tops_1('#skF_1', B_289) | ~m1_subset_1(B_289, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_82, c_82, c_8892])).
% 9.67/3.25  tff(c_9143, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_9109, c_8903])).
% 9.67/3.25  tff(c_9153, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8115, c_8195, c_9143])).
% 9.67/3.25  tff(c_9155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8114, c_9153])).
% 9.67/3.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.67/3.25  
% 9.67/3.25  Inference rules
% 9.67/3.25  ----------------------
% 9.67/3.25  #Ref     : 0
% 9.67/3.25  #Sup     : 2269
% 9.67/3.25  #Fact    : 0
% 9.67/3.25  #Define  : 0
% 9.67/3.25  #Split   : 33
% 9.67/3.25  #Chain   : 0
% 9.67/3.25  #Close   : 0
% 9.67/3.25  
% 9.67/3.25  Ordering : KBO
% 9.67/3.25  
% 9.67/3.25  Simplification rules
% 9.67/3.25  ----------------------
% 9.67/3.25  #Subsume      : 268
% 9.67/3.25  #Demod        : 2080
% 9.67/3.25  #Tautology    : 672
% 9.67/3.25  #SimpNegUnit  : 165
% 9.67/3.25  #BackRed      : 10
% 9.67/3.25  
% 9.67/3.25  #Partial instantiations: 0
% 9.67/3.25  #Strategies tried      : 1
% 9.67/3.25  
% 9.67/3.25  Timing (in seconds)
% 9.67/3.25  ----------------------
% 9.67/3.25  Preprocessing        : 0.33
% 9.67/3.25  Parsing              : 0.18
% 9.67/3.25  CNF conversion       : 0.02
% 9.67/3.25  Main loop            : 2.15
% 9.67/3.25  Inferencing          : 0.65
% 9.67/3.25  Reduction            : 0.84
% 9.67/3.25  Demodulation         : 0.62
% 9.67/3.25  BG Simplification    : 0.08
% 9.67/3.25  Subsumption          : 0.43
% 9.67/3.25  Abstraction          : 0.10
% 9.67/3.25  MUC search           : 0.00
% 9.67/3.25  Cooper               : 0.00
% 9.67/3.25  Total                : 2.53
% 9.67/3.25  Index Insertion      : 0.00
% 9.67/3.25  Index Deletion       : 0.00
% 9.67/3.25  Index Matching       : 0.00
% 9.67/3.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
