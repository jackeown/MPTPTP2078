%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:00 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 235 expanded)
%              Number of leaves         :   27 (  96 expanded)
%              Depth                    :   15
%              Number of atoms          :  127 ( 567 expanded)
%              Number of equality atoms :   34 ( 130 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => k2_tops_1(A,k2_tops_1(A,k2_tops_1(A,B))) = k2_tops_1(A,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_tops_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_tops_1)).

tff(f_50,axiom,(
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

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,k2_tops_1(A,k2_tops_1(A,B))) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l80_tops_1)).

tff(c_22,plain,(
    k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) != k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k2_tops_1(A_11,B_12),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_86,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k2_tops_1(A_33,B_34),k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_5,B_6,C_7] :
      ( k7_subset_1(A_5,B_6,C_7) = k4_xboole_0(B_6,C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_157,plain,(
    ! [A_47,B_48,C_49] :
      ( k7_subset_1(u1_struct_0(A_47),k2_tops_1(A_47,B_48),C_49) = k4_xboole_0(k2_tops_1(A_47,B_48),C_49)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_86,c_8])).

tff(c_161,plain,(
    ! [C_49] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),C_49) = k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),C_49)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_157])).

tff(c_165,plain,(
    ! [C_49] : k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),C_49) = k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),C_49) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_161])).

tff(c_80,plain,(
    ! [A_31,B_32] :
      ( v4_pre_topc(k2_tops_1(A_31,B_32),A_31)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_82,plain,
    ( v4_pre_topc(k2_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_80])).

tff(c_85,plain,(
    v4_pre_topc(k2_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_82])).

tff(c_93,plain,(
    ! [A_35,B_36] :
      ( k2_pre_topc(A_35,B_36) = B_36
      | ~ v4_pre_topc(B_36,A_35)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_175,plain,(
    ! [A_51,B_52] :
      ( k2_pre_topc(A_51,k2_tops_1(A_51,B_52)) = k2_tops_1(A_51,B_52)
      | ~ v4_pre_topc(k2_tops_1(A_51,B_52),A_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_14,c_93])).

tff(c_179,plain,
    ( k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_85,c_175])).

tff(c_183,plain,(
    k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_179])).

tff(c_18,plain,(
    ! [A_15,B_17] :
      ( k7_subset_1(u1_struct_0(A_15),k2_pre_topc(A_15,B_17),k1_tops_1(A_15,B_17)) = k2_tops_1(A_15,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_187,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_18])).

tff(c_191,plain,
    ( k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_165,c_187])).

tff(c_193,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_191])).

tff(c_196,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_193])).

tff(c_200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_196])).

tff(c_202,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( v4_pre_topc(k2_tops_1(A_13,B_14),A_13)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_260,plain,
    ( v4_pre_topc(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_202,c_16])).

tff(c_277,plain,(
    v4_pre_topc(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_260])).

tff(c_118,plain,(
    ! [A_41,B_42] :
      ( k1_tops_1(A_41,k2_tops_1(A_41,k2_tops_1(A_41,B_42))) = k1_xboole_0
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_122,plain,
    ( k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_118])).

tff(c_126,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_122])).

tff(c_131,plain,(
    ! [A_43,B_44] :
      ( k7_subset_1(u1_struct_0(A_43),k2_pre_topc(A_43,B_44),k1_tops_1(A_43,B_44)) = k2_tops_1(A_43,B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_140,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k1_xboole_0) = k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_131])).

tff(c_144,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k1_xboole_0) = k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_140])).

tff(c_203,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_242,plain,
    ( ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_203])).

tff(c_246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_202,c_242])).

tff(c_248,plain,(
    m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_12,plain,(
    ! [A_8,B_10] :
      ( k2_pre_topc(A_8,B_10) = B_10
      | ~ v4_pre_topc(B_10,A_8)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_294,plain,
    ( k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ v4_pre_topc(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_248,c_12])).

tff(c_310,plain,(
    k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_277,c_294])).

tff(c_247,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k1_xboole_0) = k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_366,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_xboole_0) = k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_247])).

tff(c_162,plain,(
    ! [A_11,B_12,C_49] :
      ( k7_subset_1(u1_struct_0(A_11),k2_tops_1(A_11,k2_tops_1(A_11,B_12)),C_49) = k4_xboole_0(k2_tops_1(A_11,k2_tops_1(A_11,B_12)),C_49)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_157])).

tff(c_425,plain,
    ( k4_xboole_0(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_xboole_0) = k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_162])).

tff(c_438,plain,(
    k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_6,c_425])).

tff(c_440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_438])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:57:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.32  
% 2.22/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.32  %$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.22/1.32  
% 2.22/1.32  %Foreground sorts:
% 2.22/1.32  
% 2.22/1.32  
% 2.22/1.32  %Background operators:
% 2.22/1.32  
% 2.22/1.32  
% 2.22/1.32  %Foreground operators:
% 2.22/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.22/1.32  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.22/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.22/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.22/1.32  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.22/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.32  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.22/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.32  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.22/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.22/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.22/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.22/1.32  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.22/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.32  
% 2.22/1.34  tff(f_90, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, k2_tops_1(A, k2_tops_1(A, B))) = k2_tops_1(A, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_tops_1)).
% 2.22/1.34  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.22/1.34  tff(f_56, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 2.22/1.34  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.22/1.34  tff(f_64, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_tops_1)).
% 2.22/1.34  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.22/1.34  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 2.22/1.34  tff(f_80, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, k2_tops_1(A, k2_tops_1(A, B))) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l80_tops_1)).
% 2.22/1.34  tff(c_22, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))!=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.22/1.34  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.22/1.34  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.22/1.34  tff(c_6, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.22/1.34  tff(c_28, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.22/1.34  tff(c_14, plain, (![A_11, B_12]: (m1_subset_1(k2_tops_1(A_11, B_12), k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.22/1.34  tff(c_86, plain, (![A_33, B_34]: (m1_subset_1(k2_tops_1(A_33, B_34), k1_zfmisc_1(u1_struct_0(A_33))) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.22/1.34  tff(c_8, plain, (![A_5, B_6, C_7]: (k7_subset_1(A_5, B_6, C_7)=k4_xboole_0(B_6, C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.22/1.34  tff(c_157, plain, (![A_47, B_48, C_49]: (k7_subset_1(u1_struct_0(A_47), k2_tops_1(A_47, B_48), C_49)=k4_xboole_0(k2_tops_1(A_47, B_48), C_49) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_86, c_8])).
% 2.22/1.34  tff(c_161, plain, (![C_49]: (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), C_49)=k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), C_49) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_157])).
% 2.22/1.34  tff(c_165, plain, (![C_49]: (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), C_49)=k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), C_49))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_161])).
% 2.22/1.34  tff(c_80, plain, (![A_31, B_32]: (v4_pre_topc(k2_tops_1(A_31, B_32), A_31) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.22/1.34  tff(c_82, plain, (v4_pre_topc(k2_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_80])).
% 2.22/1.34  tff(c_85, plain, (v4_pre_topc(k2_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_82])).
% 2.22/1.34  tff(c_93, plain, (![A_35, B_36]: (k2_pre_topc(A_35, B_36)=B_36 | ~v4_pre_topc(B_36, A_35) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.22/1.34  tff(c_175, plain, (![A_51, B_52]: (k2_pre_topc(A_51, k2_tops_1(A_51, B_52))=k2_tops_1(A_51, B_52) | ~v4_pre_topc(k2_tops_1(A_51, B_52), A_51) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_14, c_93])).
% 2.22/1.34  tff(c_179, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_85, c_175])).
% 2.22/1.34  tff(c_183, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_179])).
% 2.22/1.34  tff(c_18, plain, (![A_15, B_17]: (k7_subset_1(u1_struct_0(A_15), k2_pre_topc(A_15, B_17), k1_tops_1(A_15, B_17))=k2_tops_1(A_15, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.22/1.34  tff(c_187, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_183, c_18])).
% 2.22/1.34  tff(c_191, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_165, c_187])).
% 2.22/1.34  tff(c_193, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_191])).
% 2.22/1.34  tff(c_196, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_193])).
% 2.22/1.34  tff(c_200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_196])).
% 2.22/1.34  tff(c_202, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_191])).
% 2.22/1.34  tff(c_16, plain, (![A_13, B_14]: (v4_pre_topc(k2_tops_1(A_13, B_14), A_13) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13) | ~v2_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.22/1.34  tff(c_260, plain, (v4_pre_topc(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_202, c_16])).
% 2.22/1.34  tff(c_277, plain, (v4_pre_topc(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_260])).
% 2.22/1.34  tff(c_118, plain, (![A_41, B_42]: (k1_tops_1(A_41, k2_tops_1(A_41, k2_tops_1(A_41, B_42)))=k1_xboole_0 | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.22/1.34  tff(c_122, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k1_xboole_0 | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_118])).
% 2.22/1.34  tff(c_126, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_122])).
% 2.22/1.34  tff(c_131, plain, (![A_43, B_44]: (k7_subset_1(u1_struct_0(A_43), k2_pre_topc(A_43, B_44), k1_tops_1(A_43, B_44))=k2_tops_1(A_43, B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.22/1.34  tff(c_140, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k1_xboole_0)=k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_126, c_131])).
% 2.22/1.34  tff(c_144, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k1_xboole_0)=k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_140])).
% 2.22/1.34  tff(c_203, plain, (~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_144])).
% 2.22/1.34  tff(c_242, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_203])).
% 2.22/1.34  tff(c_246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_202, c_242])).
% 2.22/1.34  tff(c_248, plain, (m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_144])).
% 2.22/1.34  tff(c_12, plain, (![A_8, B_10]: (k2_pre_topc(A_8, B_10)=B_10 | ~v4_pre_topc(B_10, A_8) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.22/1.34  tff(c_294, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | ~v4_pre_topc(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_248, c_12])).
% 2.22/1.34  tff(c_310, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_277, c_294])).
% 2.22/1.34  tff(c_247, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k1_xboole_0)=k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_144])).
% 2.22/1.34  tff(c_366, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_xboole_0)=k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_310, c_247])).
% 2.22/1.34  tff(c_162, plain, (![A_11, B_12, C_49]: (k7_subset_1(u1_struct_0(A_11), k2_tops_1(A_11, k2_tops_1(A_11, B_12)), C_49)=k4_xboole_0(k2_tops_1(A_11, k2_tops_1(A_11, B_12)), C_49) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(resolution, [status(thm)], [c_14, c_157])).
% 2.22/1.34  tff(c_425, plain, (k4_xboole_0(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_xboole_0)=k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_366, c_162])).
% 2.22/1.34  tff(c_438, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_6, c_425])).
% 2.22/1.34  tff(c_440, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_438])).
% 2.22/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.34  
% 2.22/1.34  Inference rules
% 2.22/1.34  ----------------------
% 2.22/1.34  #Ref     : 0
% 2.22/1.34  #Sup     : 93
% 2.22/1.34  #Fact    : 0
% 2.22/1.34  #Define  : 0
% 2.22/1.34  #Split   : 3
% 2.22/1.34  #Chain   : 0
% 2.22/1.34  #Close   : 0
% 2.22/1.34  
% 2.22/1.34  Ordering : KBO
% 2.22/1.34  
% 2.22/1.34  Simplification rules
% 2.22/1.34  ----------------------
% 2.22/1.34  #Subsume      : 1
% 2.22/1.34  #Demod        : 89
% 2.22/1.34  #Tautology    : 52
% 2.22/1.34  #SimpNegUnit  : 2
% 2.22/1.34  #BackRed      : 1
% 2.22/1.34  
% 2.22/1.34  #Partial instantiations: 0
% 2.22/1.34  #Strategies tried      : 1
% 2.22/1.34  
% 2.22/1.34  Timing (in seconds)
% 2.22/1.34  ----------------------
% 2.22/1.35  Preprocessing        : 0.31
% 2.22/1.35  Parsing              : 0.17
% 2.22/1.35  CNF conversion       : 0.02
% 2.22/1.35  Main loop            : 0.24
% 2.22/1.35  Inferencing          : 0.09
% 2.22/1.35  Reduction            : 0.08
% 2.22/1.35  Demodulation         : 0.06
% 2.22/1.35  BG Simplification    : 0.01
% 2.22/1.35  Subsumption          : 0.04
% 2.22/1.35  Abstraction          : 0.02
% 2.22/1.35  MUC search           : 0.00
% 2.22/1.35  Cooper               : 0.00
% 2.22/1.35  Total                : 0.59
% 2.22/1.35  Index Insertion      : 0.00
% 2.22/1.35  Index Deletion       : 0.00
% 2.22/1.35  Index Matching       : 0.00
% 2.22/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
