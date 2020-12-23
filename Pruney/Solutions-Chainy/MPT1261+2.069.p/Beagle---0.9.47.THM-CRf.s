%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:21 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 132 expanded)
%              Number of leaves         :   33 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :  116 ( 253 expanded)
%              Number of equality atoms :   54 (  91 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_60,axiom,(
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

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_35,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1608,plain,(
    ! [A_125,B_126,C_127] :
      ( k7_subset_1(A_125,B_126,C_127) = k4_xboole_0(B_126,C_127)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1611,plain,(
    ! [C_127] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_127) = k4_xboole_0('#skF_2',C_127) ),
    inference(resolution,[status(thm)],[c_28,c_1608])).

tff(c_34,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_160,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_720,plain,(
    ! [B_80,A_81] :
      ( v4_pre_topc(B_80,A_81)
      | k2_pre_topc(A_81,B_80) != B_80
      | ~ v2_pre_topc(A_81)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_726,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_720])).

tff(c_730,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_726])).

tff(c_731,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_730])).

tff(c_876,plain,(
    ! [A_86,B_87] :
      ( k4_subset_1(u1_struct_0(A_86),B_87,k2_tops_1(A_86,B_87)) = k2_pre_topc(A_86,B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_880,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_876])).

tff(c_884,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_880])).

tff(c_206,plain,(
    ! [A_47,B_48,C_49] :
      ( k7_subset_1(A_47,B_48,C_49) = k4_xboole_0(B_48,C_49)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_209,plain,(
    ! [C_49] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_49) = k4_xboole_0('#skF_2',C_49) ),
    inference(resolution,[status(thm)],[c_28,c_206])).

tff(c_40,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_247,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_40])).

tff(c_248,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_247])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(k3_xboole_0(A_5,B_6),k4_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_74,plain,(
    ! [A_33,B_34] : k3_tarski(k2_tarski(A_33,B_34)) = k2_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_104,plain,(
    ! [B_37,A_38] : k3_tarski(k2_tarski(B_37,A_38)) = k2_xboole_0(A_38,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_74])).

tff(c_10,plain,(
    ! [A_9,B_10] : k3_tarski(k2_tarski(A_9,B_10)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_110,plain,(
    ! [B_37,A_38] : k2_xboole_0(B_37,A_38) = k2_xboole_0(A_38,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_10])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_174,plain,(
    ! [A_43,B_44] : k2_xboole_0(A_43,k4_xboole_0(B_44,A_43)) = k2_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_183,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k3_xboole_0(A_3,B_4)) = k2_xboole_0(k4_xboole_0(A_3,B_4),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_174])).

tff(c_438,plain,(
    ! [A_63,B_64] : k2_xboole_0(k4_xboole_0(A_63,B_64),k3_xboole_0(A_63,B_64)) = k2_xboole_0(A_63,k4_xboole_0(A_63,B_64)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_183])).

tff(c_444,plain,(
    ! [A_63,B_64] : k2_xboole_0(k3_xboole_0(A_63,B_64),k4_xboole_0(A_63,B_64)) = k2_xboole_0(A_63,k4_xboole_0(A_63,B_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_110])).

tff(c_484,plain,(
    ! [A_65,B_66] : k2_xboole_0(A_65,k4_xboole_0(A_65,B_66)) = A_65 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_444])).

tff(c_503,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_484])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k2_tops_1(A_20,B_21),k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_607,plain,(
    ! [A_74,B_75,C_76] :
      ( k4_subset_1(A_74,B_75,C_76) = k2_xboole_0(B_75,C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(A_74))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1535,plain,(
    ! [A_115,B_116,B_117] :
      ( k4_subset_1(u1_struct_0(A_115),B_116,k2_tops_1(A_115,B_117)) = k2_xboole_0(B_116,k2_tops_1(A_115,B_117))
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(resolution,[status(thm)],[c_20,c_607])).

tff(c_1539,plain,(
    ! [B_117] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_117)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_117))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_1535])).

tff(c_1544,plain,(
    ! [B_118] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_118)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_118))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1539])).

tff(c_1551,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_1544])).

tff(c_1556,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_884,c_503,c_1551])).

tff(c_1558,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_731,c_1556])).

tff(c_1559,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1612,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1611,c_1559])).

tff(c_1560,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1649,plain,(
    ! [A_131,B_132] :
      ( k2_pre_topc(A_131,B_132) = B_132
      | ~ v4_pre_topc(B_132,A_131)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1652,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1649])).

tff(c_1655,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1560,c_1652])).

tff(c_2108,plain,(
    ! [A_172,B_173] :
      ( k7_subset_1(u1_struct_0(A_172),k2_pre_topc(A_172,B_173),k1_tops_1(A_172,B_173)) = k2_tops_1(A_172,B_173)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ l1_pre_topc(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2117,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1655,c_2108])).

tff(c_2121,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1611,c_2117])).

tff(c_2123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1612,c_2121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:16:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.96/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.68  
% 3.96/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.68  %$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.96/1.68  
% 3.96/1.68  %Foreground sorts:
% 3.96/1.68  
% 3.96/1.68  
% 3.96/1.68  %Background operators:
% 3.96/1.68  
% 3.96/1.68  
% 3.96/1.68  %Foreground operators:
% 3.96/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.96/1.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.96/1.68  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.96/1.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.96/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.96/1.68  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.96/1.68  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.96/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.96/1.68  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.96/1.68  tff('#skF_1', type, '#skF_1': $i).
% 3.96/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.96/1.68  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.96/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.96/1.68  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.96/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.96/1.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.96/1.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.96/1.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.96/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.96/1.68  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.96/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.96/1.68  
% 4.04/1.69  tff(f_100, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 4.04/1.69  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.04/1.69  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.04/1.69  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 4.04/1.69  tff(f_31, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.04/1.69  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.04/1.69  tff(f_35, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.04/1.69  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.04/1.69  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.04/1.69  tff(f_66, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 4.04/1.69  tff(f_41, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.04/1.69  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 4.04/1.69  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.04/1.69  tff(c_1608, plain, (![A_125, B_126, C_127]: (k7_subset_1(A_125, B_126, C_127)=k4_xboole_0(B_126, C_127) | ~m1_subset_1(B_126, k1_zfmisc_1(A_125)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.04/1.69  tff(c_1611, plain, (![C_127]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_127)=k4_xboole_0('#skF_2', C_127))), inference(resolution, [status(thm)], [c_28, c_1608])).
% 4.04/1.69  tff(c_34, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.04/1.69  tff(c_160, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_34])).
% 4.04/1.69  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.04/1.69  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.04/1.69  tff(c_720, plain, (![B_80, A_81]: (v4_pre_topc(B_80, A_81) | k2_pre_topc(A_81, B_80)!=B_80 | ~v2_pre_topc(A_81) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.04/1.69  tff(c_726, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_720])).
% 4.04/1.69  tff(c_730, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_726])).
% 4.04/1.69  tff(c_731, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_160, c_730])).
% 4.04/1.69  tff(c_876, plain, (![A_86, B_87]: (k4_subset_1(u1_struct_0(A_86), B_87, k2_tops_1(A_86, B_87))=k2_pre_topc(A_86, B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.04/1.69  tff(c_880, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_876])).
% 4.04/1.69  tff(c_884, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_880])).
% 4.04/1.69  tff(c_206, plain, (![A_47, B_48, C_49]: (k7_subset_1(A_47, B_48, C_49)=k4_xboole_0(B_48, C_49) | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.04/1.69  tff(c_209, plain, (![C_49]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_49)=k4_xboole_0('#skF_2', C_49))), inference(resolution, [status(thm)], [c_28, c_206])).
% 4.04/1.69  tff(c_40, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.04/1.69  tff(c_247, plain, (v4_pre_topc('#skF_2', '#skF_1') | k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_209, c_40])).
% 4.04/1.69  tff(c_248, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_160, c_247])).
% 4.04/1.69  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(k3_xboole_0(A_5, B_6), k4_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.04/1.69  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.04/1.69  tff(c_74, plain, (![A_33, B_34]: (k3_tarski(k2_tarski(A_33, B_34))=k2_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.04/1.69  tff(c_104, plain, (![B_37, A_38]: (k3_tarski(k2_tarski(B_37, A_38))=k2_xboole_0(A_38, B_37))), inference(superposition, [status(thm), theory('equality')], [c_8, c_74])).
% 4.04/1.69  tff(c_10, plain, (![A_9, B_10]: (k3_tarski(k2_tarski(A_9, B_10))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.04/1.69  tff(c_110, plain, (![B_37, A_38]: (k2_xboole_0(B_37, A_38)=k2_xboole_0(A_38, B_37))), inference(superposition, [status(thm), theory('equality')], [c_104, c_10])).
% 4.04/1.69  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.04/1.69  tff(c_174, plain, (![A_43, B_44]: (k2_xboole_0(A_43, k4_xboole_0(B_44, A_43))=k2_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.04/1.69  tff(c_183, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k3_xboole_0(A_3, B_4))=k2_xboole_0(k4_xboole_0(A_3, B_4), A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_174])).
% 4.04/1.69  tff(c_438, plain, (![A_63, B_64]: (k2_xboole_0(k4_xboole_0(A_63, B_64), k3_xboole_0(A_63, B_64))=k2_xboole_0(A_63, k4_xboole_0(A_63, B_64)))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_183])).
% 4.04/1.69  tff(c_444, plain, (![A_63, B_64]: (k2_xboole_0(k3_xboole_0(A_63, B_64), k4_xboole_0(A_63, B_64))=k2_xboole_0(A_63, k4_xboole_0(A_63, B_64)))), inference(superposition, [status(thm), theory('equality')], [c_438, c_110])).
% 4.04/1.69  tff(c_484, plain, (![A_65, B_66]: (k2_xboole_0(A_65, k4_xboole_0(A_65, B_66))=A_65)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_444])).
% 4.04/1.69  tff(c_503, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_248, c_484])).
% 4.04/1.69  tff(c_20, plain, (![A_20, B_21]: (m1_subset_1(k2_tops_1(A_20, B_21), k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.04/1.69  tff(c_607, plain, (![A_74, B_75, C_76]: (k4_subset_1(A_74, B_75, C_76)=k2_xboole_0(B_75, C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(A_74)) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.04/1.69  tff(c_1535, plain, (![A_115, B_116, B_117]: (k4_subset_1(u1_struct_0(A_115), B_116, k2_tops_1(A_115, B_117))=k2_xboole_0(B_116, k2_tops_1(A_115, B_117)) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(resolution, [status(thm)], [c_20, c_607])).
% 4.04/1.69  tff(c_1539, plain, (![B_117]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_117))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_117)) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_1535])).
% 4.04/1.69  tff(c_1544, plain, (![B_118]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_118))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_118)) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1539])).
% 4.04/1.69  tff(c_1551, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_1544])).
% 4.04/1.69  tff(c_1556, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_884, c_503, c_1551])).
% 4.04/1.69  tff(c_1558, plain, $false, inference(negUnitSimplification, [status(thm)], [c_731, c_1556])).
% 4.04/1.69  tff(c_1559, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_34])).
% 4.04/1.69  tff(c_1612, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1611, c_1559])).
% 4.04/1.69  tff(c_1560, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 4.04/1.69  tff(c_1649, plain, (![A_131, B_132]: (k2_pre_topc(A_131, B_132)=B_132 | ~v4_pre_topc(B_132, A_131) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.04/1.69  tff(c_1652, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_1649])).
% 4.04/1.69  tff(c_1655, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1560, c_1652])).
% 4.04/1.69  tff(c_2108, plain, (![A_172, B_173]: (k7_subset_1(u1_struct_0(A_172), k2_pre_topc(A_172, B_173), k1_tops_1(A_172, B_173))=k2_tops_1(A_172, B_173) | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0(A_172))) | ~l1_pre_topc(A_172))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.04/1.69  tff(c_2117, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1655, c_2108])).
% 4.04/1.69  tff(c_2121, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1611, c_2117])).
% 4.04/1.69  tff(c_2123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1612, c_2121])).
% 4.04/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.04/1.69  
% 4.04/1.69  Inference rules
% 4.04/1.69  ----------------------
% 4.04/1.69  #Ref     : 0
% 4.04/1.69  #Sup     : 556
% 4.04/1.69  #Fact    : 0
% 4.04/1.69  #Define  : 0
% 4.04/1.69  #Split   : 2
% 4.04/1.69  #Chain   : 0
% 4.04/1.69  #Close   : 0
% 4.04/1.69  
% 4.04/1.69  Ordering : KBO
% 4.04/1.69  
% 4.04/1.69  Simplification rules
% 4.04/1.69  ----------------------
% 4.04/1.69  #Subsume      : 2
% 4.04/1.69  #Demod        : 261
% 4.04/1.69  #Tautology    : 323
% 4.04/1.69  #SimpNegUnit  : 4
% 4.04/1.69  #BackRed      : 3
% 4.04/1.69  
% 4.04/1.70  #Partial instantiations: 0
% 4.04/1.70  #Strategies tried      : 1
% 4.04/1.70  
% 4.04/1.70  Timing (in seconds)
% 4.04/1.70  ----------------------
% 4.04/1.70  Preprocessing        : 0.32
% 4.04/1.70  Parsing              : 0.17
% 4.04/1.70  CNF conversion       : 0.02
% 4.04/1.70  Main loop            : 0.62
% 4.04/1.70  Inferencing          : 0.21
% 4.04/1.70  Reduction            : 0.24
% 4.04/1.70  Demodulation         : 0.19
% 4.04/1.70  BG Simplification    : 0.03
% 4.04/1.70  Subsumption          : 0.09
% 4.04/1.70  Abstraction          : 0.03
% 4.04/1.70  MUC search           : 0.00
% 4.04/1.70  Cooper               : 0.00
% 4.04/1.70  Total                : 0.97
% 4.04/1.70  Index Insertion      : 0.00
% 4.04/1.70  Index Deletion       : 0.00
% 4.04/1.70  Index Matching       : 0.00
% 4.04/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
