%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:28 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 443 expanded)
%              Number of leaves         :   47 ( 170 expanded)
%              Depth                    :   15
%              Number of atoms          :  139 (1200 expanded)
%              Number of equality atoms :   20 ( 235 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_102,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_46,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_6,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [A_4] : r1_tarski('#skF_3',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_42,plain,(
    ! [A_50] :
      ( v4_pre_topc(k2_struct_0(A_50),A_50)
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_38,plain,(
    ! [A_48] :
      ( l1_struct_0(A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_100,plain,(
    ! [A_72] :
      ( u1_struct_0(A_72) = k2_struct_0(A_72)
      | ~ l1_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_115,plain,(
    ! [A_75] :
      ( u1_struct_0(A_75) = k2_struct_0(A_75)
      | ~ l1_pre_topc(A_75) ) ),
    inference(resolution,[status(thm)],[c_38,c_100])).

tff(c_119,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_115])).

tff(c_133,plain,(
    ! [A_77] :
      ( ~ v1_xboole_0(u1_struct_0(A_77))
      | ~ l1_struct_0(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_136,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_133])).

tff(c_137,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_136])).

tff(c_138,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_141,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_138])).

tff(c_145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_141])).

tff(c_146,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_50,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_121,plain,(
    m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_50])).

tff(c_30,plain,(
    ! [A_40,B_41] :
      ( r2_hidden(A_40,B_41)
      | v1_xboole_0(B_41)
      | ~ m1_subset_1(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_44,plain,(
    ! [A_51] :
      ( v3_pre_topc(k2_struct_0(A_51),A_51)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_26,plain,(
    ! [A_37] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_65,plain,(
    ! [A_37] : m1_subset_1('#skF_3',k1_zfmisc_1(A_37)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_26])).

tff(c_8,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_67,plain,(
    ! [A_5] : k5_xboole_0(A_5,'#skF_3') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_69,plain,(
    ! [A_3] : k3_xboole_0(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_4])).

tff(c_162,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k3_xboole_0(A_80,B_81)) = k4_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_171,plain,(
    ! [A_3] : k5_xboole_0(A_3,'#skF_3') = k4_xboole_0(A_3,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_162])).

tff(c_174,plain,(
    ! [A_3] : k4_xboole_0(A_3,'#skF_3') = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_171])).

tff(c_508,plain,(
    ! [A_137,B_138] :
      ( k4_xboole_0(A_137,B_138) = k3_subset_1(A_137,B_138)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_137)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_514,plain,(
    ! [A_37] : k4_xboole_0(A_37,'#skF_3') = k3_subset_1(A_37,'#skF_3') ),
    inference(resolution,[status(thm)],[c_65,c_508])).

tff(c_518,plain,(
    ! [A_139] : k3_subset_1(A_139,'#skF_3') = A_139 ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_514])).

tff(c_24,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(k3_subset_1(A_35,B_36),k1_zfmisc_1(A_35))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_524,plain,(
    ! [A_139] :
      ( m1_subset_1(A_139,k1_zfmisc_1(A_139))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_139)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_24])).

tff(c_530,plain,(
    ! [A_139] : m1_subset_1(A_139,k1_zfmisc_1(A_139)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_524])).

tff(c_64,plain,(
    ! [D_63] :
      ( v3_pre_topc(D_63,'#skF_1')
      | ~ r2_hidden(D_63,'#skF_3')
      | ~ m1_subset_1(D_63,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_561,plain,(
    ! [D_143] :
      ( v3_pre_topc(D_143,'#skF_1')
      | ~ r2_hidden(D_143,'#skF_3')
      | ~ m1_subset_1(D_143,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_64])).

tff(c_574,plain,
    ( v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_530,c_561])).

tff(c_602,plain,(
    ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_574])).

tff(c_532,plain,(
    ! [A_140] : m1_subset_1(A_140,k1_zfmisc_1(A_140)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_524])).

tff(c_58,plain,(
    ! [D_63] :
      ( r2_hidden(D_63,'#skF_3')
      | ~ r2_hidden('#skF_2',D_63)
      | ~ v4_pre_topc(D_63,'#skF_1')
      | ~ v3_pre_topc(D_63,'#skF_1')
      | ~ m1_subset_1(D_63,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_475,plain,(
    ! [D_63] :
      ( r2_hidden(D_63,'#skF_3')
      | ~ r2_hidden('#skF_2',D_63)
      | ~ v4_pre_topc(D_63,'#skF_1')
      | ~ v3_pre_topc(D_63,'#skF_1')
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_58])).

tff(c_552,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),'#skF_3')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_532,c_475])).

tff(c_637,plain,
    ( ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_602,c_552])).

tff(c_638,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_637])).

tff(c_641,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_638])).

tff(c_645,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_641])).

tff(c_646,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_637])).

tff(c_648,plain,(
    ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_646])).

tff(c_651,plain,
    ( v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_648])).

tff(c_654,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_651])).

tff(c_656,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_654])).

tff(c_657,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_646])).

tff(c_679,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_657])).

tff(c_683,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_679])).

tff(c_685,plain,(
    r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_574])).

tff(c_34,plain,(
    ! [B_46,A_45] :
      ( ~ r1_tarski(B_46,A_45)
      | ~ r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_693,plain,(
    ~ r1_tarski('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_685,c_34])).

tff(c_699,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_693])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.48  
% 3.02/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.48  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.02/1.48  
% 3.02/1.48  %Foreground sorts:
% 3.02/1.48  
% 3.02/1.48  
% 3.02/1.48  %Background operators:
% 3.02/1.48  
% 3.02/1.48  
% 3.02/1.48  %Foreground operators:
% 3.02/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.02/1.48  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.02/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.02/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.02/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.02/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.02/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.02/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.02/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.02/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.02/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.02/1.48  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.02/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.02/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.02/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.02/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.02/1.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.02/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.02/1.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.02/1.48  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.02/1.48  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.02/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.02/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.02/1.48  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.02/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.02/1.48  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.02/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.02/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.02/1.48  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.02/1.48  
% 3.20/1.50  tff(f_130, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 3.20/1.50  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.20/1.50  tff(f_96, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 3.20/1.50  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.20/1.50  tff(f_78, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.20/1.50  tff(f_90, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.20/1.50  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.20/1.50  tff(f_102, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 3.20/1.50  tff(f_55, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.20/1.50  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.20/1.50  tff(f_29, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.20/1.50  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.20/1.50  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.20/1.50  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.20/1.50  tff(f_74, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.20/1.50  tff(c_46, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.20/1.50  tff(c_6, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.50  tff(c_68, plain, (![A_4]: (r1_tarski('#skF_3', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6])).
% 3.20/1.50  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.20/1.50  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.20/1.50  tff(c_42, plain, (![A_50]: (v4_pre_topc(k2_struct_0(A_50), A_50) | ~l1_pre_topc(A_50) | ~v2_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.20/1.50  tff(c_38, plain, (![A_48]: (l1_struct_0(A_48) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.20/1.50  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.20/1.50  tff(c_100, plain, (![A_72]: (u1_struct_0(A_72)=k2_struct_0(A_72) | ~l1_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.20/1.50  tff(c_115, plain, (![A_75]: (u1_struct_0(A_75)=k2_struct_0(A_75) | ~l1_pre_topc(A_75))), inference(resolution, [status(thm)], [c_38, c_100])).
% 3.20/1.50  tff(c_119, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_115])).
% 3.20/1.50  tff(c_133, plain, (![A_77]: (~v1_xboole_0(u1_struct_0(A_77)) | ~l1_struct_0(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.20/1.50  tff(c_136, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_119, c_133])).
% 3.20/1.50  tff(c_137, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_136])).
% 3.20/1.50  tff(c_138, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_137])).
% 3.20/1.50  tff(c_141, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_138])).
% 3.20/1.50  tff(c_145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_141])).
% 3.20/1.50  tff(c_146, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_137])).
% 3.20/1.50  tff(c_50, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.20/1.50  tff(c_121, plain, (m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_50])).
% 3.20/1.50  tff(c_30, plain, (![A_40, B_41]: (r2_hidden(A_40, B_41) | v1_xboole_0(B_41) | ~m1_subset_1(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.20/1.50  tff(c_44, plain, (![A_51]: (v3_pre_topc(k2_struct_0(A_51), A_51) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.20/1.50  tff(c_26, plain, (![A_37]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.20/1.50  tff(c_65, plain, (![A_37]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_26])).
% 3.20/1.50  tff(c_8, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.20/1.50  tff(c_67, plain, (![A_5]: (k5_xboole_0(A_5, '#skF_3')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8])).
% 3.20/1.50  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.20/1.50  tff(c_69, plain, (![A_3]: (k3_xboole_0(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_4])).
% 3.20/1.50  tff(c_162, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k3_xboole_0(A_80, B_81))=k4_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.20/1.50  tff(c_171, plain, (![A_3]: (k5_xboole_0(A_3, '#skF_3')=k4_xboole_0(A_3, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_69, c_162])).
% 3.20/1.50  tff(c_174, plain, (![A_3]: (k4_xboole_0(A_3, '#skF_3')=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_67, c_171])).
% 3.20/1.50  tff(c_508, plain, (![A_137, B_138]: (k4_xboole_0(A_137, B_138)=k3_subset_1(A_137, B_138) | ~m1_subset_1(B_138, k1_zfmisc_1(A_137)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.20/1.50  tff(c_514, plain, (![A_37]: (k4_xboole_0(A_37, '#skF_3')=k3_subset_1(A_37, '#skF_3'))), inference(resolution, [status(thm)], [c_65, c_508])).
% 3.20/1.50  tff(c_518, plain, (![A_139]: (k3_subset_1(A_139, '#skF_3')=A_139)), inference(demodulation, [status(thm), theory('equality')], [c_174, c_514])).
% 3.20/1.50  tff(c_24, plain, (![A_35, B_36]: (m1_subset_1(k3_subset_1(A_35, B_36), k1_zfmisc_1(A_35)) | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.20/1.50  tff(c_524, plain, (![A_139]: (m1_subset_1(A_139, k1_zfmisc_1(A_139)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_139)))), inference(superposition, [status(thm), theory('equality')], [c_518, c_24])).
% 3.20/1.50  tff(c_530, plain, (![A_139]: (m1_subset_1(A_139, k1_zfmisc_1(A_139)))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_524])).
% 3.20/1.50  tff(c_64, plain, (![D_63]: (v3_pre_topc(D_63, '#skF_1') | ~r2_hidden(D_63, '#skF_3') | ~m1_subset_1(D_63, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.20/1.50  tff(c_561, plain, (![D_143]: (v3_pre_topc(D_143, '#skF_1') | ~r2_hidden(D_143, '#skF_3') | ~m1_subset_1(D_143, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_64])).
% 3.20/1.50  tff(c_574, plain, (v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_530, c_561])).
% 3.20/1.50  tff(c_602, plain, (~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_574])).
% 3.20/1.50  tff(c_532, plain, (![A_140]: (m1_subset_1(A_140, k1_zfmisc_1(A_140)))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_524])).
% 3.20/1.50  tff(c_58, plain, (![D_63]: (r2_hidden(D_63, '#skF_3') | ~r2_hidden('#skF_2', D_63) | ~v4_pre_topc(D_63, '#skF_1') | ~v3_pre_topc(D_63, '#skF_1') | ~m1_subset_1(D_63, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.20/1.50  tff(c_475, plain, (![D_63]: (r2_hidden(D_63, '#skF_3') | ~r2_hidden('#skF_2', D_63) | ~v4_pre_topc(D_63, '#skF_1') | ~v3_pre_topc(D_63, '#skF_1') | ~m1_subset_1(D_63, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_58])).
% 3.20/1.50  tff(c_552, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_532, c_475])).
% 3.20/1.50  tff(c_637, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_602, c_552])).
% 3.20/1.50  tff(c_638, plain, (~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_637])).
% 3.20/1.50  tff(c_641, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_638])).
% 3.20/1.50  tff(c_645, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_641])).
% 3.20/1.50  tff(c_646, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_637])).
% 3.20/1.50  tff(c_648, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_646])).
% 3.20/1.50  tff(c_651, plain, (v1_xboole_0(k2_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_648])).
% 3.20/1.50  tff(c_654, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_651])).
% 3.20/1.50  tff(c_656, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_654])).
% 3.20/1.50  tff(c_657, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_646])).
% 3.20/1.50  tff(c_679, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_657])).
% 3.20/1.50  tff(c_683, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_679])).
% 3.20/1.50  tff(c_685, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_574])).
% 3.20/1.50  tff(c_34, plain, (![B_46, A_45]: (~r1_tarski(B_46, A_45) | ~r2_hidden(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.20/1.50  tff(c_693, plain, (~r1_tarski('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_685, c_34])).
% 3.20/1.50  tff(c_699, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_693])).
% 3.20/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.50  
% 3.20/1.50  Inference rules
% 3.20/1.50  ----------------------
% 3.20/1.50  #Ref     : 0
% 3.20/1.50  #Sup     : 122
% 3.20/1.50  #Fact    : 0
% 3.20/1.50  #Define  : 0
% 3.20/1.50  #Split   : 12
% 3.20/1.50  #Chain   : 0
% 3.20/1.50  #Close   : 0
% 3.20/1.50  
% 3.20/1.50  Ordering : KBO
% 3.20/1.50  
% 3.20/1.50  Simplification rules
% 3.20/1.50  ----------------------
% 3.20/1.50  #Subsume      : 13
% 3.20/1.50  #Demod        : 47
% 3.20/1.50  #Tautology    : 55
% 3.20/1.50  #SimpNegUnit  : 10
% 3.20/1.50  #BackRed      : 2
% 3.20/1.50  
% 3.20/1.50  #Partial instantiations: 0
% 3.20/1.50  #Strategies tried      : 1
% 3.20/1.50  
% 3.20/1.50  Timing (in seconds)
% 3.20/1.50  ----------------------
% 3.20/1.50  Preprocessing        : 0.36
% 3.20/1.50  Parsing              : 0.19
% 3.20/1.50  CNF conversion       : 0.02
% 3.20/1.50  Main loop            : 0.33
% 3.20/1.50  Inferencing          : 0.12
% 3.20/1.50  Reduction            : 0.11
% 3.20/1.50  Demodulation         : 0.07
% 3.20/1.50  BG Simplification    : 0.02
% 3.20/1.50  Subsumption          : 0.05
% 3.20/1.50  Abstraction          : 0.02
% 3.20/1.50  MUC search           : 0.00
% 3.20/1.50  Cooper               : 0.00
% 3.20/1.50  Total                : 0.73
% 3.20/1.50  Index Insertion      : 0.00
% 3.20/1.50  Index Deletion       : 0.00
% 3.20/1.50  Index Matching       : 0.00
% 3.20/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
