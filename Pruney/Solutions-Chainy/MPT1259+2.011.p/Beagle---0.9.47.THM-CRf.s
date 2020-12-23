%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:00 EST 2020

% Result     : Theorem 6.11s
% Output     : CNFRefutation 6.11s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 317 expanded)
%              Number of leaves         :   31 ( 127 expanded)
%              Depth                    :   11
%              Number of atoms          :  148 ( 834 expanded)
%              Number of equality atoms :   38 ( 146 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => k2_tops_1(A,k2_tops_1(A,k2_tops_1(A,B))) = k2_tops_1(A,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_tops_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_tops_1)).

tff(f_66,axiom,(
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

tff(f_51,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,k2_tops_1(A,k2_tops_1(A,B))) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l80_tops_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k2_tops_1(A_17,B_18),k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_602,plain,(
    ! [A_77,B_78] :
      ( v4_pre_topc(k2_tops_1(A_77,B_78),A_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_608,plain,
    ( v4_pre_topc(k2_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_602])).

tff(c_613,plain,(
    v4_pre_topc(k2_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_608])).

tff(c_373,plain,(
    ! [A_67,B_68] :
      ( m1_subset_1(k2_tops_1(A_67,B_68),k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    ! [A_14,B_16] :
      ( k2_pre_topc(A_14,B_16) = B_16
      | ~ v4_pre_topc(B_16,A_14)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4301,plain,(
    ! [A_148,B_149] :
      ( k2_pre_topc(A_148,k2_tops_1(A_148,B_149)) = k2_tops_1(A_148,B_149)
      | ~ v4_pre_topc(k2_tops_1(A_148,B_149),A_148)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ l1_pre_topc(A_148) ) ),
    inference(resolution,[status(thm)],[c_373,c_22])).

tff(c_4309,plain,
    ( k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_613,c_4301])).

tff(c_4317,plain,(
    k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_4309])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k2_pre_topc(A_12,B_13),k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_610,plain,(
    ! [A_12,B_13] :
      ( v4_pre_topc(k2_tops_1(A_12,k2_pre_topc(A_12,B_13)),A_12)
      | ~ v2_pre_topc(A_12)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(resolution,[status(thm)],[c_18,c_602])).

tff(c_4326,plain,
    ( v4_pre_topc(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),'#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4317,c_610])).

tff(c_4340,plain,
    ( v4_pre_topc(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),'#skF_1')
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_4326])).

tff(c_4346,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_4340])).

tff(c_4349,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_4346])).

tff(c_4353,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_4349])).

tff(c_4355,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_4340])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,B_32) = A_31
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_50,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_42])).

tff(c_60,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_60])).

tff(c_86,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k4_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_101,plain,(
    ! [B_2] : k4_xboole_0(B_2,k1_xboole_0) = k3_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_86])).

tff(c_104,plain,(
    ! [B_2] : k4_xboole_0(B_2,k1_xboole_0) = B_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_101])).

tff(c_206,plain,(
    ! [A_53,B_54] :
      ( m1_subset_1(k2_pre_topc(A_53,B_54),k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [A_9,B_10,C_11] :
      ( k7_subset_1(A_9,B_10,C_11) = k4_xboole_0(B_10,C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1750,plain,(
    ! [A_109,B_110,C_111] :
      ( k7_subset_1(u1_struct_0(A_109),k2_pre_topc(A_109,B_110),C_111) = k4_xboole_0(k2_pre_topc(A_109,B_110),C_111)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(resolution,[status(thm)],[c_206,c_16])).

tff(c_4878,plain,(
    ! [A_157,B_158,C_159] :
      ( k7_subset_1(u1_struct_0(A_157),k2_pre_topc(A_157,k2_tops_1(A_157,B_158)),C_159) = k4_xboole_0(k2_pre_topc(A_157,k2_tops_1(A_157,B_158)),C_159)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ l1_pre_topc(A_157) ) ),
    inference(resolution,[status(thm)],[c_24,c_1750])).

tff(c_832,plain,(
    ! [A_87,B_88] :
      ( k1_tops_1(A_87,k2_tops_1(A_87,k2_tops_1(A_87,B_88))) = k1_xboole_0
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_838,plain,
    ( k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_832])).

tff(c_843,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_838])).

tff(c_977,plain,(
    ! [A_93,B_94] :
      ( k7_subset_1(u1_struct_0(A_93),k2_pre_topc(A_93,B_94),k1_tops_1(A_93,B_94)) = k2_tops_1(A_93,B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_986,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k1_xboole_0) = k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_843,c_977])).

tff(c_990,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k1_xboole_0) = k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_986])).

tff(c_1490,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_990])).

tff(c_1493,plain,
    ( ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_1490])).

tff(c_1496,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1493])).

tff(c_1499,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_1496])).

tff(c_1503,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_1499])).

tff(c_1504,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k1_xboole_0) = k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_990])).

tff(c_4884,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k1_xboole_0) = k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4878,c_1504])).

tff(c_4907,plain,(
    k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4355,c_104,c_4884])).

tff(c_32,plain,(
    k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) != k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_4920,plain,(
    k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) != k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4907,c_32])).

tff(c_6463,plain,(
    ! [A_178,B_179] :
      ( k2_pre_topc(A_178,k2_tops_1(A_178,k2_pre_topc(A_178,B_179))) = k2_tops_1(A_178,k2_pre_topc(A_178,B_179))
      | ~ m1_subset_1(k2_pre_topc(A_178,B_179),k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ v2_pre_topc(A_178)
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ l1_pre_topc(A_178) ) ),
    inference(resolution,[status(thm)],[c_610,c_4301])).

tff(c_6469,plain,
    ( k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')))) = k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4317,c_6463])).

tff(c_6478,plain,(
    k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4355,c_38,c_4355,c_4317,c_4317,c_6469])).

tff(c_6480,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4920,c_6478])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:36:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.11/2.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.11/2.28  
% 6.11/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.11/2.28  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 6.11/2.28  
% 6.11/2.28  %Foreground sorts:
% 6.11/2.28  
% 6.11/2.28  
% 6.11/2.28  %Background operators:
% 6.11/2.28  
% 6.11/2.28  
% 6.11/2.28  %Foreground operators:
% 6.11/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.11/2.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.11/2.28  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 6.11/2.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.11/2.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.11/2.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.11/2.28  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.11/2.28  tff('#skF_2', type, '#skF_2': $i).
% 6.11/2.28  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 6.11/2.28  tff('#skF_1', type, '#skF_1': $i).
% 6.11/2.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.11/2.28  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.11/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.11/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.11/2.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.11/2.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.11/2.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.11/2.28  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.11/2.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.11/2.28  
% 6.11/2.30  tff(f_106, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, k2_tops_1(A, k2_tops_1(A, B))) = k2_tops_1(A, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_tops_1)).
% 6.11/2.30  tff(f_72, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 6.11/2.30  tff(f_80, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_tops_1)).
% 6.11/2.30  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 6.11/2.30  tff(f_51, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 6.11/2.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.11/2.30  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.11/2.30  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.11/2.30  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.11/2.30  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 6.11/2.30  tff(f_96, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, k2_tops_1(A, k2_tops_1(A, B))) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l80_tops_1)).
% 6.11/2.30  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 6.11/2.30  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.11/2.30  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.11/2.30  tff(c_24, plain, (![A_17, B_18]: (m1_subset_1(k2_tops_1(A_17, B_18), k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.11/2.30  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.11/2.30  tff(c_602, plain, (![A_77, B_78]: (v4_pre_topc(k2_tops_1(A_77, B_78), A_77) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.11/2.30  tff(c_608, plain, (v4_pre_topc(k2_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_602])).
% 6.11/2.30  tff(c_613, plain, (v4_pre_topc(k2_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_608])).
% 6.11/2.30  tff(c_373, plain, (![A_67, B_68]: (m1_subset_1(k2_tops_1(A_67, B_68), k1_zfmisc_1(u1_struct_0(A_67))) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.11/2.30  tff(c_22, plain, (![A_14, B_16]: (k2_pre_topc(A_14, B_16)=B_16 | ~v4_pre_topc(B_16, A_14) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.11/2.30  tff(c_4301, plain, (![A_148, B_149]: (k2_pre_topc(A_148, k2_tops_1(A_148, B_149))=k2_tops_1(A_148, B_149) | ~v4_pre_topc(k2_tops_1(A_148, B_149), A_148) | ~m1_subset_1(B_149, k1_zfmisc_1(u1_struct_0(A_148))) | ~l1_pre_topc(A_148))), inference(resolution, [status(thm)], [c_373, c_22])).
% 6.11/2.30  tff(c_4309, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_613, c_4301])).
% 6.11/2.30  tff(c_4317, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_4309])).
% 6.11/2.30  tff(c_18, plain, (![A_12, B_13]: (m1_subset_1(k2_pre_topc(A_12, B_13), k1_zfmisc_1(u1_struct_0(A_12))) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.11/2.30  tff(c_610, plain, (![A_12, B_13]: (v4_pre_topc(k2_tops_1(A_12, k2_pre_topc(A_12, B_13)), A_12) | ~v2_pre_topc(A_12) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(resolution, [status(thm)], [c_18, c_602])).
% 6.11/2.30  tff(c_4326, plain, (v4_pre_topc(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4317, c_610])).
% 6.11/2.30  tff(c_4340, plain, (v4_pre_topc(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), '#skF_1') | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_4326])).
% 6.11/2.30  tff(c_4346, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_4340])).
% 6.11/2.30  tff(c_4349, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_4346])).
% 6.11/2.30  tff(c_4353, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_4349])).
% 6.11/2.30  tff(c_4355, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_4340])).
% 6.11/2.30  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.11/2.30  tff(c_42, plain, (![A_31, B_32]: (k3_xboole_0(A_31, B_32)=A_31 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.11/2.30  tff(c_50, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_42])).
% 6.11/2.30  tff(c_60, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.11/2.30  tff(c_68, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_60])).
% 6.11/2.30  tff(c_86, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k4_xboole_0(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.11/2.30  tff(c_101, plain, (![B_2]: (k4_xboole_0(B_2, k1_xboole_0)=k3_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_68, c_86])).
% 6.11/2.30  tff(c_104, plain, (![B_2]: (k4_xboole_0(B_2, k1_xboole_0)=B_2)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_101])).
% 6.11/2.30  tff(c_206, plain, (![A_53, B_54]: (m1_subset_1(k2_pre_topc(A_53, B_54), k1_zfmisc_1(u1_struct_0(A_53))) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.11/2.30  tff(c_16, plain, (![A_9, B_10, C_11]: (k7_subset_1(A_9, B_10, C_11)=k4_xboole_0(B_10, C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.11/2.30  tff(c_1750, plain, (![A_109, B_110, C_111]: (k7_subset_1(u1_struct_0(A_109), k2_pre_topc(A_109, B_110), C_111)=k4_xboole_0(k2_pre_topc(A_109, B_110), C_111) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(resolution, [status(thm)], [c_206, c_16])).
% 6.11/2.30  tff(c_4878, plain, (![A_157, B_158, C_159]: (k7_subset_1(u1_struct_0(A_157), k2_pre_topc(A_157, k2_tops_1(A_157, B_158)), C_159)=k4_xboole_0(k2_pre_topc(A_157, k2_tops_1(A_157, B_158)), C_159) | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0(A_157))) | ~l1_pre_topc(A_157))), inference(resolution, [status(thm)], [c_24, c_1750])).
% 6.11/2.30  tff(c_832, plain, (![A_87, B_88]: (k1_tops_1(A_87, k2_tops_1(A_87, k2_tops_1(A_87, B_88)))=k1_xboole_0 | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87) | ~v2_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.11/2.30  tff(c_838, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k1_xboole_0 | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_832])).
% 6.11/2.30  tff(c_843, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_838])).
% 6.11/2.30  tff(c_977, plain, (![A_93, B_94]: (k7_subset_1(u1_struct_0(A_93), k2_pre_topc(A_93, B_94), k1_tops_1(A_93, B_94))=k2_tops_1(A_93, B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.11/2.30  tff(c_986, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k1_xboole_0)=k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_843, c_977])).
% 6.11/2.30  tff(c_990, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k1_xboole_0)=k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_986])).
% 6.11/2.30  tff(c_1490, plain, (~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_990])).
% 6.11/2.30  tff(c_1493, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_1490])).
% 6.11/2.30  tff(c_1496, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1493])).
% 6.11/2.30  tff(c_1499, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_1496])).
% 6.11/2.30  tff(c_1503, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_1499])).
% 6.11/2.30  tff(c_1504, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k1_xboole_0)=k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_990])).
% 6.11/2.30  tff(c_4884, plain, (k4_xboole_0(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k1_xboole_0)=k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4878, c_1504])).
% 6.11/2.30  tff(c_4907, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4355, c_104, c_4884])).
% 6.11/2.30  tff(c_32, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))!=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.11/2.30  tff(c_4920, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))!=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4907, c_32])).
% 6.11/2.30  tff(c_6463, plain, (![A_178, B_179]: (k2_pre_topc(A_178, k2_tops_1(A_178, k2_pre_topc(A_178, B_179)))=k2_tops_1(A_178, k2_pre_topc(A_178, B_179)) | ~m1_subset_1(k2_pre_topc(A_178, B_179), k1_zfmisc_1(u1_struct_0(A_178))) | ~v2_pre_topc(A_178) | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0(A_178))) | ~l1_pre_topc(A_178))), inference(resolution, [status(thm)], [c_610, c_4301])).
% 6.11/2.30  tff(c_6469, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))))=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_pre_topc('#skF_1') | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4317, c_6463])).
% 6.11/2.30  tff(c_6478, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4355, c_38, c_4355, c_4317, c_4317, c_6469])).
% 6.11/2.30  tff(c_6480, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4920, c_6478])).
% 6.11/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.11/2.30  
% 6.11/2.30  Inference rules
% 6.11/2.30  ----------------------
% 6.11/2.30  #Ref     : 0
% 6.11/2.30  #Sup     : 1593
% 6.11/2.30  #Fact    : 0
% 6.11/2.30  #Define  : 0
% 6.11/2.30  #Split   : 8
% 6.11/2.30  #Chain   : 0
% 6.11/2.30  #Close   : 0
% 6.11/2.30  
% 6.11/2.30  Ordering : KBO
% 6.11/2.30  
% 6.11/2.30  Simplification rules
% 6.11/2.30  ----------------------
% 6.11/2.30  #Subsume      : 314
% 6.11/2.30  #Demod        : 2391
% 6.11/2.30  #Tautology    : 907
% 6.11/2.30  #SimpNegUnit  : 2
% 6.11/2.30  #BackRed      : 6
% 6.11/2.30  
% 6.11/2.30  #Partial instantiations: 0
% 6.11/2.30  #Strategies tried      : 1
% 6.11/2.30  
% 6.11/2.30  Timing (in seconds)
% 6.11/2.30  ----------------------
% 6.39/2.30  Preprocessing        : 0.33
% 6.39/2.30  Parsing              : 0.19
% 6.39/2.30  CNF conversion       : 0.02
% 6.39/2.30  Main loop            : 1.14
% 6.39/2.30  Inferencing          : 0.35
% 6.39/2.30  Reduction            : 0.46
% 6.39/2.30  Demodulation         : 0.36
% 6.39/2.30  BG Simplification    : 0.05
% 6.39/2.30  Subsumption          : 0.24
% 6.39/2.30  Abstraction          : 0.07
% 6.39/2.30  MUC search           : 0.00
% 6.39/2.30  Cooper               : 0.00
% 6.39/2.30  Total                : 1.51
% 6.39/2.30  Index Insertion      : 0.00
% 6.39/2.30  Index Deletion       : 0.00
% 6.39/2.30  Index Matching       : 0.00
% 6.39/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
