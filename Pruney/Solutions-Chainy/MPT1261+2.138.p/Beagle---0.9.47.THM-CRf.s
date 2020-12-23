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
% DateTime   : Thu Dec  3 10:21:31 EST 2020

% Result     : Theorem 5.83s
% Output     : CNFRefutation 5.83s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 133 expanded)
%              Number of leaves         :   36 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  126 ( 256 expanded)
%              Number of equality atoms :   60 (  90 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_76,axiom,(
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

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_41,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6310,plain,(
    ! [A_205,B_206,C_207] :
      ( k7_subset_1(A_205,B_206,C_207) = k4_xboole_0(B_206,C_207)
      | ~ m1_subset_1(B_206,k1_zfmisc_1(A_205)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6313,plain,(
    ! [C_207] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_207) = k4_xboole_0('#skF_2',C_207) ),
    inference(resolution,[status(thm)],[c_40,c_6310])).

tff(c_46,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_114,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1444,plain,(
    ! [B_105,A_106] :
      ( v4_pre_topc(B_105,A_106)
      | k2_pre_topc(A_106,B_105) != B_105
      | ~ v2_pre_topc(A_106)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1450,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1444])).

tff(c_1454,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_1450])).

tff(c_1455,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_1454])).

tff(c_1783,plain,(
    ! [A_113,B_114] :
      ( k4_subset_1(u1_struct_0(A_113),B_114,k2_tops_1(A_113,B_114)) = k2_pre_topc(A_113,B_114)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1787,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1783])).

tff(c_1791,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1787])).

tff(c_392,plain,(
    ! [A_64,B_65,C_66] :
      ( k7_subset_1(A_64,B_65,C_66) = k4_xboole_0(B_65,C_66)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_399,plain,(
    ! [C_67] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_67) = k4_xboole_0('#skF_2',C_67) ),
    inference(resolution,[status(thm)],[c_40,c_392])).

tff(c_52,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_223,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_52])).

tff(c_405,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_223])).

tff(c_16,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_98,plain,(
    ! [A_42,B_43] :
      ( k4_xboole_0(A_42,B_43) = k1_xboole_0
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_106,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_98])).

tff(c_22,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_228,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k4_xboole_0(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_24,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_231,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = k3_xboole_0(A_58,k4_xboole_0(A_58,B_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_24])).

tff(c_250,plain,(
    ! [A_58,B_59] : k3_xboole_0(A_58,k4_xboole_0(A_58,B_59)) = k4_xboole_0(A_58,B_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_231])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_133,plain,(
    ! [A_48,B_49] : k4_xboole_0(A_48,k3_xboole_0(A_48,B_49)) = k4_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_602,plain,(
    ! [B_77,A_78] : k4_xboole_0(B_77,k3_xboole_0(A_78,B_77)) = k4_xboole_0(B_77,A_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_133])).

tff(c_634,plain,(
    ! [A_58,B_59] : k4_xboole_0(k4_xboole_0(A_58,B_59),k4_xboole_0(A_58,B_59)) = k4_xboole_0(k4_xboole_0(A_58,B_59),A_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_602])).

tff(c_731,plain,(
    ! [A_81,B_82] : k4_xboole_0(k4_xboole_0(A_81,B_82),A_81) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_634])).

tff(c_20,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_752,plain,(
    ! [A_81,B_82] : k2_xboole_0(A_81,k4_xboole_0(A_81,B_82)) = k2_xboole_0(A_81,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_731,c_20])).

tff(c_893,plain,(
    ! [A_85,B_86] : k2_xboole_0(A_85,k4_xboole_0(A_85,B_86)) = A_85 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_752])).

tff(c_909,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_893])).

tff(c_34,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(k2_tops_1(A_27,B_28),k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1126,plain,(
    ! [A_95,B_96,C_97] :
      ( k4_subset_1(A_95,B_96,C_97) = k2_xboole_0(B_96,C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(A_95))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5811,plain,(
    ! [A_180,B_181,B_182] :
      ( k4_subset_1(u1_struct_0(A_180),B_181,k2_tops_1(A_180,B_182)) = k2_xboole_0(B_181,k2_tops_1(A_180,B_182))
      | ~ m1_subset_1(B_181,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ m1_subset_1(B_182,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ l1_pre_topc(A_180) ) ),
    inference(resolution,[status(thm)],[c_34,c_1126])).

tff(c_5815,plain,(
    ! [B_182] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_182)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_182))
      | ~ m1_subset_1(B_182,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_5811])).

tff(c_6017,plain,(
    ! [B_185] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_185)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_185))
      | ~ m1_subset_1(B_185,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_5815])).

tff(c_6024,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_6017])).

tff(c_6029,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1791,c_909,c_6024])).

tff(c_6031,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1455,c_6029])).

tff(c_6032,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_6621,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6313,c_6032])).

tff(c_6033,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_6804,plain,(
    ! [A_228,B_229] :
      ( k2_pre_topc(A_228,B_229) = B_229
      | ~ v4_pre_topc(B_229,A_228)
      | ~ m1_subset_1(B_229,k1_zfmisc_1(u1_struct_0(A_228)))
      | ~ l1_pre_topc(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6810,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_6804])).

tff(c_6814,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6033,c_6810])).

tff(c_8147,plain,(
    ! [A_265,B_266] :
      ( k7_subset_1(u1_struct_0(A_265),k2_pre_topc(A_265,B_266),k1_tops_1(A_265,B_266)) = k2_tops_1(A_265,B_266)
      | ~ m1_subset_1(B_266,k1_zfmisc_1(u1_struct_0(A_265)))
      | ~ l1_pre_topc(A_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8156,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6814,c_8147])).

tff(c_8160,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_6313,c_8156])).

tff(c_8162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6621,c_8160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:26:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.83/2.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.83/2.24  
% 5.83/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.83/2.24  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.83/2.24  
% 5.83/2.24  %Foreground sorts:
% 5.83/2.24  
% 5.83/2.24  
% 5.83/2.24  %Background operators:
% 5.83/2.24  
% 5.83/2.24  
% 5.83/2.24  %Foreground operators:
% 5.83/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.83/2.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.83/2.24  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.83/2.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.83/2.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.83/2.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.83/2.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.83/2.24  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.83/2.24  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.83/2.24  tff('#skF_2', type, '#skF_2': $i).
% 5.83/2.24  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.83/2.24  tff('#skF_1', type, '#skF_1': $i).
% 5.83/2.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.83/2.24  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.83/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.83/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.83/2.24  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.83/2.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.83/2.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.83/2.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.83/2.24  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.83/2.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.83/2.24  
% 5.83/2.26  tff(f_108, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 5.83/2.26  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.83/2.26  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.83/2.26  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 5.83/2.26  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 5.83/2.26  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.83/2.26  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.83/2.26  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.83/2.26  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.83/2.26  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.83/2.26  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.83/2.26  tff(f_82, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.83/2.26  tff(f_57, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.83/2.26  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 5.83/2.26  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.83/2.26  tff(c_6310, plain, (![A_205, B_206, C_207]: (k7_subset_1(A_205, B_206, C_207)=k4_xboole_0(B_206, C_207) | ~m1_subset_1(B_206, k1_zfmisc_1(A_205)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.83/2.26  tff(c_6313, plain, (![C_207]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_207)=k4_xboole_0('#skF_2', C_207))), inference(resolution, [status(thm)], [c_40, c_6310])).
% 5.83/2.26  tff(c_46, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.83/2.26  tff(c_114, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 5.83/2.26  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.83/2.26  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.83/2.26  tff(c_1444, plain, (![B_105, A_106]: (v4_pre_topc(B_105, A_106) | k2_pre_topc(A_106, B_105)!=B_105 | ~v2_pre_topc(A_106) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.83/2.26  tff(c_1450, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1444])).
% 5.83/2.26  tff(c_1454, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_1450])).
% 5.83/2.26  tff(c_1455, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_114, c_1454])).
% 5.83/2.26  tff(c_1783, plain, (![A_113, B_114]: (k4_subset_1(u1_struct_0(A_113), B_114, k2_tops_1(A_113, B_114))=k2_pre_topc(A_113, B_114) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.83/2.26  tff(c_1787, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1783])).
% 5.83/2.26  tff(c_1791, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1787])).
% 5.83/2.26  tff(c_392, plain, (![A_64, B_65, C_66]: (k7_subset_1(A_64, B_65, C_66)=k4_xboole_0(B_65, C_66) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.83/2.26  tff(c_399, plain, (![C_67]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_67)=k4_xboole_0('#skF_2', C_67))), inference(resolution, [status(thm)], [c_40, c_392])).
% 5.83/2.26  tff(c_52, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.83/2.26  tff(c_223, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_114, c_52])).
% 5.83/2.26  tff(c_405, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_399, c_223])).
% 5.83/2.26  tff(c_16, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.83/2.26  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.83/2.26  tff(c_98, plain, (![A_42, B_43]: (k4_xboole_0(A_42, B_43)=k1_xboole_0 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.83/2.26  tff(c_106, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_98])).
% 5.83/2.26  tff(c_22, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.83/2.26  tff(c_228, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k4_xboole_0(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.83/2.26  tff(c_24, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.83/2.26  tff(c_231, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k3_xboole_0(A_58, B_59))=k3_xboole_0(A_58, k4_xboole_0(A_58, B_59)))), inference(superposition, [status(thm), theory('equality')], [c_228, c_24])).
% 5.83/2.26  tff(c_250, plain, (![A_58, B_59]: (k3_xboole_0(A_58, k4_xboole_0(A_58, B_59))=k4_xboole_0(A_58, B_59))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_231])).
% 5.83/2.26  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.83/2.26  tff(c_133, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k3_xboole_0(A_48, B_49))=k4_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.83/2.26  tff(c_602, plain, (![B_77, A_78]: (k4_xboole_0(B_77, k3_xboole_0(A_78, B_77))=k4_xboole_0(B_77, A_78))), inference(superposition, [status(thm), theory('equality')], [c_2, c_133])).
% 5.83/2.26  tff(c_634, plain, (![A_58, B_59]: (k4_xboole_0(k4_xboole_0(A_58, B_59), k4_xboole_0(A_58, B_59))=k4_xboole_0(k4_xboole_0(A_58, B_59), A_58))), inference(superposition, [status(thm), theory('equality')], [c_250, c_602])).
% 5.83/2.26  tff(c_731, plain, (![A_81, B_82]: (k4_xboole_0(k4_xboole_0(A_81, B_82), A_81)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_106, c_634])).
% 5.83/2.26  tff(c_20, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.83/2.26  tff(c_752, plain, (![A_81, B_82]: (k2_xboole_0(A_81, k4_xboole_0(A_81, B_82))=k2_xboole_0(A_81, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_731, c_20])).
% 5.83/2.26  tff(c_893, plain, (![A_85, B_86]: (k2_xboole_0(A_85, k4_xboole_0(A_85, B_86))=A_85)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_752])).
% 5.83/2.26  tff(c_909, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_405, c_893])).
% 5.83/2.26  tff(c_34, plain, (![A_27, B_28]: (m1_subset_1(k2_tops_1(A_27, B_28), k1_zfmisc_1(u1_struct_0(A_27))) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.83/2.26  tff(c_1126, plain, (![A_95, B_96, C_97]: (k4_subset_1(A_95, B_96, C_97)=k2_xboole_0(B_96, C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(A_95)) | ~m1_subset_1(B_96, k1_zfmisc_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.83/2.26  tff(c_5811, plain, (![A_180, B_181, B_182]: (k4_subset_1(u1_struct_0(A_180), B_181, k2_tops_1(A_180, B_182))=k2_xboole_0(B_181, k2_tops_1(A_180, B_182)) | ~m1_subset_1(B_181, k1_zfmisc_1(u1_struct_0(A_180))) | ~m1_subset_1(B_182, k1_zfmisc_1(u1_struct_0(A_180))) | ~l1_pre_topc(A_180))), inference(resolution, [status(thm)], [c_34, c_1126])).
% 5.83/2.26  tff(c_5815, plain, (![B_182]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_182))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_182)) | ~m1_subset_1(B_182, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_5811])).
% 5.83/2.26  tff(c_6017, plain, (![B_185]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_185))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_185)) | ~m1_subset_1(B_185, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_5815])).
% 5.83/2.26  tff(c_6024, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_6017])).
% 5.83/2.26  tff(c_6029, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1791, c_909, c_6024])).
% 5.83/2.26  tff(c_6031, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1455, c_6029])).
% 5.83/2.26  tff(c_6032, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 5.83/2.26  tff(c_6621, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6313, c_6032])).
% 5.83/2.26  tff(c_6033, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 5.83/2.26  tff(c_6804, plain, (![A_228, B_229]: (k2_pre_topc(A_228, B_229)=B_229 | ~v4_pre_topc(B_229, A_228) | ~m1_subset_1(B_229, k1_zfmisc_1(u1_struct_0(A_228))) | ~l1_pre_topc(A_228))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.83/2.26  tff(c_6810, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_6804])).
% 5.83/2.26  tff(c_6814, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_6033, c_6810])).
% 5.83/2.26  tff(c_8147, plain, (![A_265, B_266]: (k7_subset_1(u1_struct_0(A_265), k2_pre_topc(A_265, B_266), k1_tops_1(A_265, B_266))=k2_tops_1(A_265, B_266) | ~m1_subset_1(B_266, k1_zfmisc_1(u1_struct_0(A_265))) | ~l1_pre_topc(A_265))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.83/2.26  tff(c_8156, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6814, c_8147])).
% 5.83/2.26  tff(c_8160, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_6313, c_8156])).
% 5.83/2.26  tff(c_8162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6621, c_8160])).
% 5.83/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.83/2.26  
% 5.83/2.26  Inference rules
% 5.83/2.26  ----------------------
% 5.83/2.26  #Ref     : 0
% 5.83/2.26  #Sup     : 1973
% 5.83/2.26  #Fact    : 0
% 5.83/2.26  #Define  : 0
% 5.83/2.26  #Split   : 5
% 5.83/2.26  #Chain   : 0
% 5.83/2.26  #Close   : 0
% 5.83/2.26  
% 5.83/2.26  Ordering : KBO
% 5.83/2.26  
% 5.83/2.26  Simplification rules
% 5.83/2.26  ----------------------
% 5.83/2.26  #Subsume      : 218
% 5.83/2.26  #Demod        : 2922
% 5.83/2.26  #Tautology    : 1539
% 5.83/2.26  #SimpNegUnit  : 8
% 5.83/2.26  #BackRed      : 1
% 5.83/2.26  
% 5.83/2.26  #Partial instantiations: 0
% 5.83/2.26  #Strategies tried      : 1
% 5.83/2.26  
% 5.83/2.26  Timing (in seconds)
% 5.83/2.26  ----------------------
% 5.83/2.26  Preprocessing        : 0.34
% 5.83/2.26  Parsing              : 0.18
% 5.83/2.26  CNF conversion       : 0.02
% 5.83/2.26  Main loop            : 1.17
% 5.83/2.26  Inferencing          : 0.33
% 5.83/2.26  Reduction            : 0.61
% 5.83/2.26  Demodulation         : 0.52
% 5.83/2.26  BG Simplification    : 0.03
% 5.83/2.26  Subsumption          : 0.14
% 5.83/2.26  Abstraction          : 0.06
% 5.83/2.26  MUC search           : 0.00
% 5.83/2.26  Cooper               : 0.00
% 5.83/2.26  Total                : 1.54
% 5.83/2.26  Index Insertion      : 0.00
% 5.83/2.26  Index Deletion       : 0.00
% 5.83/2.26  Index Matching       : 0.00
% 5.83/2.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
