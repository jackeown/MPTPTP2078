%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:32 EST 2020

% Result     : Theorem 5.63s
% Output     : CNFRefutation 5.63s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 144 expanded)
%              Number of leaves         :   40 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :  132 ( 265 expanded)
%              Number of equality atoms :   65 (  96 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_74,axiom,(
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

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_7007,plain,(
    ! [A_220,B_221,C_222] :
      ( k7_subset_1(A_220,B_221,C_222) = k4_xboole_0(B_221,C_222)
      | ~ m1_subset_1(B_221,k1_zfmisc_1(A_220)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7010,plain,(
    ! [C_222] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_222) = k4_xboole_0('#skF_2',C_222) ),
    inference(resolution,[status(thm)],[c_38,c_7007])).

tff(c_44,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_112,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1286,plain,(
    ! [B_105,A_106] :
      ( v4_pre_topc(B_105,A_106)
      | k2_pre_topc(A_106,B_105) != B_105
      | ~ v2_pre_topc(A_106)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1292,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1286])).

tff(c_1296,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_1292])).

tff(c_1297,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_1296])).

tff(c_1605,plain,(
    ! [A_115,B_116] :
      ( k4_subset_1(u1_struct_0(A_115),B_116,k2_tops_1(A_115,B_116)) = k2_pre_topc(A_115,B_116)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1609,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1605])).

tff(c_1613,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1609])).

tff(c_329,plain,(
    ! [A_68,B_69,C_70] :
      ( k7_subset_1(A_68,B_69,C_70) = k4_xboole_0(B_69,C_70)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_400,plain,(
    ! [C_73] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_73) = k4_xboole_0('#skF_2',C_73) ),
    inference(resolution,[status(thm)],[c_38,c_329])).

tff(c_50,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_235,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_50])).

tff(c_406,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_235])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_144,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(A_53,B_54) = k1_xboole_0
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_156,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k2_xboole_0(A_16,B_17)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_144])).

tff(c_99,plain,(
    ! [A_46,B_47] :
      ( k3_xboole_0(A_46,B_47) = A_46
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_111,plain,(
    ! [A_16,B_17] : k3_xboole_0(A_16,k2_xboole_0(A_16,B_17)) = A_16 ),
    inference(resolution,[status(thm)],[c_20,c_99])).

tff(c_240,plain,(
    ! [A_61,B_62] : k5_xboole_0(A_61,k3_xboole_0(A_61,B_62)) = k4_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_249,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k2_xboole_0(A_16,B_17)) = k5_xboole_0(A_16,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_240])).

tff(c_261,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_249])).

tff(c_16,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_297,plain,(
    ! [A_66,B_67] : k4_xboole_0(A_66,k4_xboole_0(A_66,B_67)) = k3_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_309,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,k4_xboole_0(A_14,B_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_297])).

tff(c_974,plain,(
    ! [A_95,B_96] : k3_xboole_0(A_95,k4_xboole_0(A_95,B_96)) = k4_xboole_0(A_95,B_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_309])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_255,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_240])).

tff(c_980,plain,(
    ! [A_95,B_96] : k5_xboole_0(k4_xboole_0(A_95,B_96),k4_xboole_0(A_95,B_96)) = k4_xboole_0(k4_xboole_0(A_95,B_96),A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_974,c_255])).

tff(c_1067,plain,(
    ! [A_97,B_98] : k4_xboole_0(k4_xboole_0(A_97,B_98),A_97) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_980])).

tff(c_14,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1085,plain,(
    ! [A_97,B_98] : k2_xboole_0(A_97,k4_xboole_0(A_97,B_98)) = k2_xboole_0(A_97,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1067,c_14])).

tff(c_1152,plain,(
    ! [A_102,B_103] : k2_xboole_0(A_102,k4_xboole_0(A_102,B_103)) = A_102 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1085])).

tff(c_1186,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_1152])).

tff(c_32,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(k2_tops_1(A_29,B_30),k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1144,plain,(
    ! [A_99,B_100,C_101] :
      ( k4_subset_1(A_99,B_100,C_101) = k2_xboole_0(B_100,C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(A_99))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6121,plain,(
    ! [A_187,B_188,B_189] :
      ( k4_subset_1(u1_struct_0(A_187),B_188,k2_tops_1(A_187,B_189)) = k2_xboole_0(B_188,k2_tops_1(A_187,B_189))
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0(A_187)))
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_187)))
      | ~ l1_pre_topc(A_187) ) ),
    inference(resolution,[status(thm)],[c_32,c_1144])).

tff(c_6125,plain,(
    ! [B_189] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_189)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_189))
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_6121])).

tff(c_6569,plain,(
    ! [B_194] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_194)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_194))
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6125])).

tff(c_6576,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_6569])).

tff(c_6581,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1613,c_1186,c_6576])).

tff(c_6583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1297,c_6581])).

tff(c_6584,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_7012,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7010,c_6584])).

tff(c_6585,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_7242,plain,(
    ! [A_232,B_233] :
      ( k2_pre_topc(A_232,B_233) = B_233
      | ~ v4_pre_topc(B_233,A_232)
      | ~ m1_subset_1(B_233,k1_zfmisc_1(u1_struct_0(A_232)))
      | ~ l1_pre_topc(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_7245,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_7242])).

tff(c_7248,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6585,c_7245])).

tff(c_8787,plain,(
    ! [A_273,B_274] :
      ( k7_subset_1(u1_struct_0(A_273),k2_pre_topc(A_273,B_274),k1_tops_1(A_273,B_274)) = k2_tops_1(A_273,B_274)
      | ~ m1_subset_1(B_274,k1_zfmisc_1(u1_struct_0(A_273)))
      | ~ l1_pre_topc(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8796,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7248,c_8787])).

tff(c_8800,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_7010,c_8796])).

tff(c_8802,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7012,c_8800])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:04:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.63/2.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.63/2.18  
% 5.63/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.63/2.18  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.63/2.18  
% 5.63/2.18  %Foreground sorts:
% 5.63/2.18  
% 5.63/2.18  
% 5.63/2.18  %Background operators:
% 5.63/2.18  
% 5.63/2.18  
% 5.63/2.18  %Foreground operators:
% 5.63/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.63/2.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.63/2.18  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.63/2.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.63/2.18  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.63/2.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.63/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.63/2.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.63/2.18  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.63/2.18  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.63/2.18  tff('#skF_2', type, '#skF_2': $i).
% 5.63/2.18  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.63/2.18  tff('#skF_1', type, '#skF_1': $i).
% 5.63/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.63/2.18  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.63/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.63/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.63/2.18  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.63/2.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.63/2.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.63/2.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.63/2.18  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.63/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.63/2.18  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.63/2.18  
% 5.63/2.20  tff(f_106, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 5.63/2.20  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.63/2.20  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.63/2.20  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 5.63/2.20  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 5.63/2.20  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.63/2.20  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.63/2.20  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.63/2.20  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.63/2.20  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.63/2.20  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.63/2.20  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.63/2.20  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.63/2.20  tff(f_80, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.63/2.20  tff(f_53, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.63/2.20  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 5.63/2.20  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.63/2.20  tff(c_7007, plain, (![A_220, B_221, C_222]: (k7_subset_1(A_220, B_221, C_222)=k4_xboole_0(B_221, C_222) | ~m1_subset_1(B_221, k1_zfmisc_1(A_220)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.63/2.20  tff(c_7010, plain, (![C_222]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_222)=k4_xboole_0('#skF_2', C_222))), inference(resolution, [status(thm)], [c_38, c_7007])).
% 5.63/2.20  tff(c_44, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.63/2.20  tff(c_112, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 5.63/2.20  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.63/2.20  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.63/2.20  tff(c_1286, plain, (![B_105, A_106]: (v4_pre_topc(B_105, A_106) | k2_pre_topc(A_106, B_105)!=B_105 | ~v2_pre_topc(A_106) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.63/2.20  tff(c_1292, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1286])).
% 5.63/2.20  tff(c_1296, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_1292])).
% 5.63/2.20  tff(c_1297, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_112, c_1296])).
% 5.63/2.20  tff(c_1605, plain, (![A_115, B_116]: (k4_subset_1(u1_struct_0(A_115), B_116, k2_tops_1(A_115, B_116))=k2_pre_topc(A_115, B_116) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.63/2.20  tff(c_1609, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1605])).
% 5.63/2.20  tff(c_1613, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1609])).
% 5.63/2.20  tff(c_329, plain, (![A_68, B_69, C_70]: (k7_subset_1(A_68, B_69, C_70)=k4_xboole_0(B_69, C_70) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.63/2.20  tff(c_400, plain, (![C_73]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_73)=k4_xboole_0('#skF_2', C_73))), inference(resolution, [status(thm)], [c_38, c_329])).
% 5.63/2.20  tff(c_50, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.63/2.20  tff(c_235, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_112, c_50])).
% 5.63/2.20  tff(c_406, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_400, c_235])).
% 5.63/2.20  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.63/2.20  tff(c_20, plain, (![A_16, B_17]: (r1_tarski(A_16, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.63/2.20  tff(c_144, plain, (![A_53, B_54]: (k4_xboole_0(A_53, B_54)=k1_xboole_0 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.63/2.20  tff(c_156, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k2_xboole_0(A_16, B_17))=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_144])).
% 5.63/2.20  tff(c_99, plain, (![A_46, B_47]: (k3_xboole_0(A_46, B_47)=A_46 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.63/2.20  tff(c_111, plain, (![A_16, B_17]: (k3_xboole_0(A_16, k2_xboole_0(A_16, B_17))=A_16)), inference(resolution, [status(thm)], [c_20, c_99])).
% 5.63/2.20  tff(c_240, plain, (![A_61, B_62]: (k5_xboole_0(A_61, k3_xboole_0(A_61, B_62))=k4_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.63/2.20  tff(c_249, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k2_xboole_0(A_16, B_17))=k5_xboole_0(A_16, A_16))), inference(superposition, [status(thm), theory('equality')], [c_111, c_240])).
% 5.63/2.20  tff(c_261, plain, (![A_16]: (k5_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_156, c_249])).
% 5.63/2.20  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.63/2.20  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.63/2.20  tff(c_297, plain, (![A_66, B_67]: (k4_xboole_0(A_66, k4_xboole_0(A_66, B_67))=k3_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.63/2.20  tff(c_309, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k3_xboole_0(A_14, k4_xboole_0(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_297])).
% 5.63/2.20  tff(c_974, plain, (![A_95, B_96]: (k3_xboole_0(A_95, k4_xboole_0(A_95, B_96))=k4_xboole_0(A_95, B_96))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_309])).
% 5.63/2.20  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.63/2.20  tff(c_255, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_240])).
% 5.63/2.20  tff(c_980, plain, (![A_95, B_96]: (k5_xboole_0(k4_xboole_0(A_95, B_96), k4_xboole_0(A_95, B_96))=k4_xboole_0(k4_xboole_0(A_95, B_96), A_95))), inference(superposition, [status(thm), theory('equality')], [c_974, c_255])).
% 5.63/2.20  tff(c_1067, plain, (![A_97, B_98]: (k4_xboole_0(k4_xboole_0(A_97, B_98), A_97)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_261, c_980])).
% 5.63/2.20  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.63/2.20  tff(c_1085, plain, (![A_97, B_98]: (k2_xboole_0(A_97, k4_xboole_0(A_97, B_98))=k2_xboole_0(A_97, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1067, c_14])).
% 5.63/2.20  tff(c_1152, plain, (![A_102, B_103]: (k2_xboole_0(A_102, k4_xboole_0(A_102, B_103))=A_102)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1085])).
% 5.63/2.20  tff(c_1186, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_406, c_1152])).
% 5.63/2.20  tff(c_32, plain, (![A_29, B_30]: (m1_subset_1(k2_tops_1(A_29, B_30), k1_zfmisc_1(u1_struct_0(A_29))) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.63/2.20  tff(c_1144, plain, (![A_99, B_100, C_101]: (k4_subset_1(A_99, B_100, C_101)=k2_xboole_0(B_100, C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(A_99)) | ~m1_subset_1(B_100, k1_zfmisc_1(A_99)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.63/2.20  tff(c_6121, plain, (![A_187, B_188, B_189]: (k4_subset_1(u1_struct_0(A_187), B_188, k2_tops_1(A_187, B_189))=k2_xboole_0(B_188, k2_tops_1(A_187, B_189)) | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0(A_187))) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_187))) | ~l1_pre_topc(A_187))), inference(resolution, [status(thm)], [c_32, c_1144])).
% 5.63/2.20  tff(c_6125, plain, (![B_189]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_189))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_189)) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_6121])).
% 5.63/2.20  tff(c_6569, plain, (![B_194]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_194))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_194)) | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6125])).
% 5.63/2.20  tff(c_6576, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_6569])).
% 5.63/2.20  tff(c_6581, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1613, c_1186, c_6576])).
% 5.63/2.20  tff(c_6583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1297, c_6581])).
% 5.63/2.20  tff(c_6584, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 5.63/2.20  tff(c_7012, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7010, c_6584])).
% 5.63/2.20  tff(c_6585, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 5.63/2.20  tff(c_7242, plain, (![A_232, B_233]: (k2_pre_topc(A_232, B_233)=B_233 | ~v4_pre_topc(B_233, A_232) | ~m1_subset_1(B_233, k1_zfmisc_1(u1_struct_0(A_232))) | ~l1_pre_topc(A_232))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.63/2.20  tff(c_7245, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_7242])).
% 5.63/2.20  tff(c_7248, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6585, c_7245])).
% 5.63/2.20  tff(c_8787, plain, (![A_273, B_274]: (k7_subset_1(u1_struct_0(A_273), k2_pre_topc(A_273, B_274), k1_tops_1(A_273, B_274))=k2_tops_1(A_273, B_274) | ~m1_subset_1(B_274, k1_zfmisc_1(u1_struct_0(A_273))) | ~l1_pre_topc(A_273))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.63/2.20  tff(c_8796, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7248, c_8787])).
% 5.63/2.20  tff(c_8800, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_7010, c_8796])).
% 5.63/2.20  tff(c_8802, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7012, c_8800])).
% 5.63/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.63/2.20  
% 5.63/2.20  Inference rules
% 5.63/2.20  ----------------------
% 5.63/2.20  #Ref     : 0
% 5.63/2.20  #Sup     : 2132
% 5.63/2.20  #Fact    : 0
% 5.63/2.20  #Define  : 0
% 5.63/2.20  #Split   : 4
% 5.63/2.20  #Chain   : 0
% 5.63/2.20  #Close   : 0
% 5.63/2.20  
% 5.63/2.20  Ordering : KBO
% 5.63/2.20  
% 5.63/2.20  Simplification rules
% 5.63/2.20  ----------------------
% 5.63/2.20  #Subsume      : 197
% 5.63/2.20  #Demod        : 3043
% 5.63/2.20  #Tautology    : 1684
% 5.63/2.20  #SimpNegUnit  : 5
% 5.63/2.20  #BackRed      : 1
% 5.63/2.20  
% 5.63/2.20  #Partial instantiations: 0
% 5.63/2.20  #Strategies tried      : 1
% 5.63/2.20  
% 5.63/2.20  Timing (in seconds)
% 5.63/2.20  ----------------------
% 5.63/2.20  Preprocessing        : 0.32
% 5.63/2.20  Parsing              : 0.17
% 5.63/2.20  CNF conversion       : 0.02
% 5.63/2.20  Main loop            : 1.10
% 5.63/2.20  Inferencing          : 0.32
% 5.63/2.20  Reduction            : 0.57
% 5.63/2.20  Demodulation         : 0.48
% 5.63/2.20  BG Simplification    : 0.03
% 5.63/2.20  Subsumption          : 0.13
% 5.63/2.20  Abstraction          : 0.06
% 5.63/2.20  MUC search           : 0.00
% 5.63/2.20  Cooper               : 0.00
% 5.63/2.20  Total                : 1.46
% 5.63/2.20  Index Insertion      : 0.00
% 5.63/2.20  Index Deletion       : 0.00
% 5.63/2.20  Index Matching       : 0.00
% 5.63/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
