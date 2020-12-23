%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:13 EST 2020

% Result     : Theorem 7.11s
% Output     : CNFRefutation 7.39s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 225 expanded)
%              Number of leaves         :   46 (  93 expanded)
%              Depth                    :   13
%              Number of atoms          :  174 ( 389 expanded)
%              Number of equality atoms :   84 ( 147 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_96,axiom,(
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

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_55,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_77,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_47,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_118,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_9669,plain,(
    ! [A_356,B_357,C_358] :
      ( k7_subset_1(A_356,B_357,C_358) = k4_xboole_0(B_357,C_358)
      | ~ m1_subset_1(B_357,k1_zfmisc_1(A_356)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_9675,plain,(
    ! [C_358] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_358) = k4_xboole_0('#skF_2',C_358) ),
    inference(resolution,[status(thm)],[c_52,c_9669])).

tff(c_64,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_116,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_58,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_220,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_56,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3247,plain,(
    ! [B_174,A_175] :
      ( v4_pre_topc(B_174,A_175)
      | k2_pre_topc(A_175,B_174) != B_174
      | ~ v2_pre_topc(A_175)
      | ~ m1_subset_1(B_174,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ l1_pre_topc(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3254,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_3247])).

tff(c_3258,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_3254])).

tff(c_3259,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_3258])).

tff(c_1566,plain,(
    ! [A_137,B_138,C_139] :
      ( k7_subset_1(A_137,B_138,C_139) = k4_xboole_0(B_138,C_139)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_137)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1650,plain,(
    ! [C_143] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_143) = k4_xboole_0('#skF_2',C_143) ),
    inference(resolution,[status(thm)],[c_52,c_1566])).

tff(c_1662,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_1650])).

tff(c_18,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2184,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1662,c_18])).

tff(c_20,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_24,plain,(
    ! [B_19,A_18] : k2_tarski(B_19,A_18) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_122,plain,(
    ! [A_59,B_60] : k1_setfam_1(k2_tarski(A_59,B_60)) = k3_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_221,plain,(
    ! [B_69,A_70] : k1_setfam_1(k2_tarski(B_69,A_70)) = k3_xboole_0(A_70,B_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_122])).

tff(c_36,plain,(
    ! [A_32,B_33] : k1_setfam_1(k2_tarski(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_244,plain,(
    ! [B_71,A_72] : k3_xboole_0(B_71,A_72) = k3_xboole_0(A_72,B_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_36])).

tff(c_16,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_137,plain,(
    ! [A_61,B_62] :
      ( k3_xboole_0(A_61,B_62) = A_61
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_157,plain,(
    ! [A_12] : k3_xboole_0(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_137])).

tff(c_260,plain,(
    ! [B_71] : k3_xboole_0(B_71,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_157])).

tff(c_468,plain,(
    ! [A_83,B_84] : k5_xboole_0(A_83,k3_xboole_0(A_83,B_84)) = k4_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_485,plain,(
    ! [B_71] : k5_xboole_0(B_71,k1_xboole_0) = k4_xboole_0(B_71,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_468])).

tff(c_505,plain,(
    ! [B_71] : k5_xboole_0(B_71,k1_xboole_0) = B_71 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_485])).

tff(c_40,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(A_34,k1_zfmisc_1(B_35))
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1316,plain,(
    ! [A_127,B_128] :
      ( k4_xboole_0(A_127,B_128) = k3_subset_1(A_127,B_128)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(A_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4274,plain,(
    ! [B_192,A_193] :
      ( k4_xboole_0(B_192,A_193) = k3_subset_1(B_192,A_193)
      | ~ r1_tarski(A_193,B_192) ) ),
    inference(resolution,[status(thm)],[c_40,c_1316])).

tff(c_4361,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = k3_subset_1(A_12,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_4274])).

tff(c_4395,plain,(
    ! [A_12] : k3_subset_1(A_12,k1_xboole_0) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_4361])).

tff(c_975,plain,(
    ! [A_109,B_110] :
      ( k3_subset_1(A_109,k3_subset_1(A_109,B_110)) = B_110
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5882,plain,(
    ! [B_220,A_221] :
      ( k3_subset_1(B_220,k3_subset_1(B_220,A_221)) = A_221
      | ~ r1_tarski(A_221,B_220) ) ),
    inference(resolution,[status(thm)],[c_40,c_975])).

tff(c_5906,plain,(
    ! [A_12] :
      ( k3_subset_1(A_12,A_12) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4395,c_5882])).

tff(c_5925,plain,(
    ! [A_12] : k3_subset_1(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_5906])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2200,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_2184,c_14])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_227,plain,(
    ! [B_69,A_70] : k3_xboole_0(B_69,A_70) = k3_xboole_0(A_70,B_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_36])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_156,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_137])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1779,plain,(
    ! [A_146,B_147] : k3_xboole_0(k3_xboole_0(A_146,B_147),A_146) = k3_xboole_0(A_146,B_147) ),
    inference(resolution,[status(thm)],[c_10,c_137])).

tff(c_155,plain,(
    ! [A_5,B_6] : k3_xboole_0(k3_xboole_0(A_5,B_6),A_5) = k3_xboole_0(A_5,B_6) ),
    inference(resolution,[status(thm)],[c_10,c_137])).

tff(c_1782,plain,(
    ! [A_146,B_147] : k3_xboole_0(k3_xboole_0(A_146,B_147),k3_xboole_0(A_146,B_147)) = k3_xboole_0(k3_xboole_0(A_146,B_147),A_146) ),
    inference(superposition,[status(thm),theory(equality)],[c_1779,c_155])).

tff(c_1924,plain,(
    ! [A_150,B_151] : k3_xboole_0(A_150,k3_xboole_0(A_150,B_151)) = k3_xboole_0(A_150,B_151) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_156,c_1782])).

tff(c_1979,plain,(
    ! [A_150,B_151] : k5_xboole_0(A_150,k3_xboole_0(A_150,B_151)) = k4_xboole_0(A_150,k3_xboole_0(A_150,B_151)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1924,c_8])).

tff(c_2039,plain,(
    ! [A_150,B_151] : k4_xboole_0(A_150,k3_xboole_0(A_150,B_151)) = k4_xboole_0(A_150,B_151) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1979])).

tff(c_4355,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k3_subset_1(A_5,k3_xboole_0(A_5,B_6)) ),
    inference(resolution,[status(thm)],[c_10,c_4274])).

tff(c_4392,plain,(
    ! [A_5,B_6] : k3_subset_1(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2039,c_4355])).

tff(c_6652,plain,(
    k3_subset_1(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2200,c_4392])).

tff(c_6737,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5925,c_6652])).

tff(c_22,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6909,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6737,c_22])).

tff(c_6923,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_6909])).

tff(c_117,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_121,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_117])).

tff(c_733,plain,(
    ! [A_93,C_94,B_95] :
      ( r1_tarski(A_93,C_94)
      | ~ r1_tarski(B_95,C_94)
      | ~ r1_tarski(A_93,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_750,plain,(
    ! [A_93] :
      ( r1_tarski(A_93,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_93,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_121,c_733])).

tff(c_2693,plain,(
    ! [A_165,B_166,C_167] :
      ( k4_subset_1(A_165,B_166,C_167) = k2_xboole_0(B_166,C_167)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(A_165))
      | ~ m1_subset_1(B_166,k1_zfmisc_1(A_165)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6638,plain,(
    ! [B_240,B_241,A_242] :
      ( k4_subset_1(B_240,B_241,A_242) = k2_xboole_0(B_241,A_242)
      | ~ m1_subset_1(B_241,k1_zfmisc_1(B_240))
      | ~ r1_tarski(A_242,B_240) ) ),
    inference(resolution,[status(thm)],[c_40,c_2693])).

tff(c_6765,plain,(
    ! [A_243] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_243) = k2_xboole_0('#skF_2',A_243)
      | ~ r1_tarski(A_243,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_52,c_6638])).

tff(c_7459,plain,(
    ! [A_250] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_250) = k2_xboole_0('#skF_2',A_250)
      | ~ r1_tarski(A_250,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_750,c_6765])).

tff(c_3409,plain,(
    ! [A_180,B_181] :
      ( k4_subset_1(u1_struct_0(A_180),B_181,k2_tops_1(A_180,B_181)) = k2_pre_topc(A_180,B_181)
      | ~ m1_subset_1(B_181,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ l1_pre_topc(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_3414,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_3409])).

tff(c_3418,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3414])).

tff(c_7474,plain,
    ( k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7459,c_3418])).

tff(c_7497,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2184,c_6923,c_7474])).

tff(c_7499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3259,c_7497])).

tff(c_7500,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_7827,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_7500])).

tff(c_7828,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_7919,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7828,c_58])).

tff(c_9679,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9675,c_7919])).

tff(c_10727,plain,(
    ! [A_378,B_379] :
      ( k2_pre_topc(A_378,B_379) = B_379
      | ~ v4_pre_topc(B_379,A_378)
      | ~ m1_subset_1(B_379,k1_zfmisc_1(u1_struct_0(A_378)))
      | ~ l1_pre_topc(A_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_10734,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_10727])).

tff(c_10738,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_7828,c_10734])).

tff(c_11564,plain,(
    ! [A_397,B_398] :
      ( k7_subset_1(u1_struct_0(A_397),k2_pre_topc(A_397,B_398),k1_tops_1(A_397,B_398)) = k2_tops_1(A_397,B_398)
      | ~ m1_subset_1(B_398,k1_zfmisc_1(u1_struct_0(A_397)))
      | ~ l1_pre_topc(A_397) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_11573,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10738,c_11564])).

tff(c_11577,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_9675,c_11573])).

tff(c_11579,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9679,c_11577])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:38:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.11/2.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.11/2.59  
% 7.11/2.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.11/2.59  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 7.11/2.59  
% 7.11/2.59  %Foreground sorts:
% 7.11/2.59  
% 7.11/2.59  
% 7.11/2.59  %Background operators:
% 7.11/2.59  
% 7.11/2.59  
% 7.11/2.59  %Foreground operators:
% 7.11/2.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.11/2.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.11/2.59  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 7.11/2.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.11/2.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.11/2.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.11/2.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.11/2.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.11/2.59  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 7.11/2.59  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.11/2.59  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.11/2.59  tff('#skF_2', type, '#skF_2': $i).
% 7.11/2.59  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 7.11/2.59  tff('#skF_1', type, '#skF_1': $i).
% 7.11/2.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.11/2.59  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.11/2.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.11/2.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.11/2.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.11/2.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.11/2.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.11/2.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.11/2.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.11/2.59  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.11/2.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.11/2.59  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.11/2.59  
% 7.39/2.63  tff(f_130, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 7.39/2.63  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 7.39/2.63  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 7.39/2.63  tff(f_49, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.39/2.63  tff(f_51, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.39/2.63  tff(f_55, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.39/2.63  tff(f_77, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 7.39/2.63  tff(f_47, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.39/2.63  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.39/2.63  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.39/2.63  tff(f_81, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.39/2.63  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 7.39/2.63  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 7.39/2.63  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.39/2.63  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.39/2.63  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.39/2.63  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.39/2.63  tff(f_71, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 7.39/2.63  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 7.39/2.63  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 7.39/2.63  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.39/2.63  tff(c_9669, plain, (![A_356, B_357, C_358]: (k7_subset_1(A_356, B_357, C_358)=k4_xboole_0(B_357, C_358) | ~m1_subset_1(B_357, k1_zfmisc_1(A_356)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.39/2.63  tff(c_9675, plain, (![C_358]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_358)=k4_xboole_0('#skF_2', C_358))), inference(resolution, [status(thm)], [c_52, c_9669])).
% 7.39/2.63  tff(c_64, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.39/2.63  tff(c_116, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_64])).
% 7.39/2.63  tff(c_58, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.39/2.63  tff(c_220, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_58])).
% 7.39/2.63  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.39/2.63  tff(c_56, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.39/2.63  tff(c_3247, plain, (![B_174, A_175]: (v4_pre_topc(B_174, A_175) | k2_pre_topc(A_175, B_174)!=B_174 | ~v2_pre_topc(A_175) | ~m1_subset_1(B_174, k1_zfmisc_1(u1_struct_0(A_175))) | ~l1_pre_topc(A_175))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.39/2.63  tff(c_3254, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_3247])).
% 7.39/2.63  tff(c_3258, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_3254])).
% 7.39/2.63  tff(c_3259, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_220, c_3258])).
% 7.39/2.63  tff(c_1566, plain, (![A_137, B_138, C_139]: (k7_subset_1(A_137, B_138, C_139)=k4_xboole_0(B_138, C_139) | ~m1_subset_1(B_138, k1_zfmisc_1(A_137)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.39/2.63  tff(c_1650, plain, (![C_143]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_143)=k4_xboole_0('#skF_2', C_143))), inference(resolution, [status(thm)], [c_52, c_1566])).
% 7.39/2.63  tff(c_1662, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_116, c_1650])).
% 7.39/2.63  tff(c_18, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.39/2.63  tff(c_2184, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1662, c_18])).
% 7.39/2.63  tff(c_20, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.39/2.63  tff(c_24, plain, (![B_19, A_18]: (k2_tarski(B_19, A_18)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.39/2.63  tff(c_122, plain, (![A_59, B_60]: (k1_setfam_1(k2_tarski(A_59, B_60))=k3_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.39/2.63  tff(c_221, plain, (![B_69, A_70]: (k1_setfam_1(k2_tarski(B_69, A_70))=k3_xboole_0(A_70, B_69))), inference(superposition, [status(thm), theory('equality')], [c_24, c_122])).
% 7.39/2.63  tff(c_36, plain, (![A_32, B_33]: (k1_setfam_1(k2_tarski(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.39/2.63  tff(c_244, plain, (![B_71, A_72]: (k3_xboole_0(B_71, A_72)=k3_xboole_0(A_72, B_71))), inference(superposition, [status(thm), theory('equality')], [c_221, c_36])).
% 7.39/2.63  tff(c_16, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.39/2.63  tff(c_137, plain, (![A_61, B_62]: (k3_xboole_0(A_61, B_62)=A_61 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.39/2.63  tff(c_157, plain, (![A_12]: (k3_xboole_0(k1_xboole_0, A_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_137])).
% 7.39/2.63  tff(c_260, plain, (![B_71]: (k3_xboole_0(B_71, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_244, c_157])).
% 7.39/2.63  tff(c_468, plain, (![A_83, B_84]: (k5_xboole_0(A_83, k3_xboole_0(A_83, B_84))=k4_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.39/2.63  tff(c_485, plain, (![B_71]: (k5_xboole_0(B_71, k1_xboole_0)=k4_xboole_0(B_71, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_260, c_468])).
% 7.39/2.63  tff(c_505, plain, (![B_71]: (k5_xboole_0(B_71, k1_xboole_0)=B_71)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_485])).
% 7.39/2.63  tff(c_40, plain, (![A_34, B_35]: (m1_subset_1(A_34, k1_zfmisc_1(B_35)) | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.39/2.63  tff(c_1316, plain, (![A_127, B_128]: (k4_xboole_0(A_127, B_128)=k3_subset_1(A_127, B_128) | ~m1_subset_1(B_128, k1_zfmisc_1(A_127)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.39/2.63  tff(c_4274, plain, (![B_192, A_193]: (k4_xboole_0(B_192, A_193)=k3_subset_1(B_192, A_193) | ~r1_tarski(A_193, B_192))), inference(resolution, [status(thm)], [c_40, c_1316])).
% 7.39/2.63  tff(c_4361, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=k3_subset_1(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_4274])).
% 7.39/2.63  tff(c_4395, plain, (![A_12]: (k3_subset_1(A_12, k1_xboole_0)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_4361])).
% 7.39/2.63  tff(c_975, plain, (![A_109, B_110]: (k3_subset_1(A_109, k3_subset_1(A_109, B_110))=B_110 | ~m1_subset_1(B_110, k1_zfmisc_1(A_109)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.39/2.63  tff(c_5882, plain, (![B_220, A_221]: (k3_subset_1(B_220, k3_subset_1(B_220, A_221))=A_221 | ~r1_tarski(A_221, B_220))), inference(resolution, [status(thm)], [c_40, c_975])).
% 7.39/2.63  tff(c_5906, plain, (![A_12]: (k3_subset_1(A_12, A_12)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_12))), inference(superposition, [status(thm), theory('equality')], [c_4395, c_5882])).
% 7.39/2.63  tff(c_5925, plain, (![A_12]: (k3_subset_1(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_5906])).
% 7.39/2.63  tff(c_14, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.39/2.63  tff(c_2200, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_2184, c_14])).
% 7.39/2.63  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.39/2.63  tff(c_227, plain, (![B_69, A_70]: (k3_xboole_0(B_69, A_70)=k3_xboole_0(A_70, B_69))), inference(superposition, [status(thm), theory('equality')], [c_221, c_36])).
% 7.39/2.63  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.39/2.63  tff(c_156, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_137])).
% 7.39/2.63  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.39/2.63  tff(c_1779, plain, (![A_146, B_147]: (k3_xboole_0(k3_xboole_0(A_146, B_147), A_146)=k3_xboole_0(A_146, B_147))), inference(resolution, [status(thm)], [c_10, c_137])).
% 7.39/2.63  tff(c_155, plain, (![A_5, B_6]: (k3_xboole_0(k3_xboole_0(A_5, B_6), A_5)=k3_xboole_0(A_5, B_6))), inference(resolution, [status(thm)], [c_10, c_137])).
% 7.39/2.63  tff(c_1782, plain, (![A_146, B_147]: (k3_xboole_0(k3_xboole_0(A_146, B_147), k3_xboole_0(A_146, B_147))=k3_xboole_0(k3_xboole_0(A_146, B_147), A_146))), inference(superposition, [status(thm), theory('equality')], [c_1779, c_155])).
% 7.39/2.63  tff(c_1924, plain, (![A_150, B_151]: (k3_xboole_0(A_150, k3_xboole_0(A_150, B_151))=k3_xboole_0(A_150, B_151))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_156, c_1782])).
% 7.39/2.63  tff(c_1979, plain, (![A_150, B_151]: (k5_xboole_0(A_150, k3_xboole_0(A_150, B_151))=k4_xboole_0(A_150, k3_xboole_0(A_150, B_151)))), inference(superposition, [status(thm), theory('equality')], [c_1924, c_8])).
% 7.39/2.63  tff(c_2039, plain, (![A_150, B_151]: (k4_xboole_0(A_150, k3_xboole_0(A_150, B_151))=k4_xboole_0(A_150, B_151))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1979])).
% 7.39/2.63  tff(c_4355, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k3_subset_1(A_5, k3_xboole_0(A_5, B_6)))), inference(resolution, [status(thm)], [c_10, c_4274])).
% 7.39/2.63  tff(c_4392, plain, (![A_5, B_6]: (k3_subset_1(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_2039, c_4355])).
% 7.39/2.63  tff(c_6652, plain, (k3_subset_1(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2200, c_4392])).
% 7.39/2.63  tff(c_6737, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5925, c_6652])).
% 7.39/2.63  tff(c_22, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.39/2.63  tff(c_6909, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6737, c_22])).
% 7.39/2.63  tff(c_6923, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_505, c_6909])).
% 7.39/2.63  tff(c_117, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~m1_subset_1(A_57, k1_zfmisc_1(B_58)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.39/2.63  tff(c_121, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_117])).
% 7.39/2.63  tff(c_733, plain, (![A_93, C_94, B_95]: (r1_tarski(A_93, C_94) | ~r1_tarski(B_95, C_94) | ~r1_tarski(A_93, B_95))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.39/2.63  tff(c_750, plain, (![A_93]: (r1_tarski(A_93, u1_struct_0('#skF_1')) | ~r1_tarski(A_93, '#skF_2'))), inference(resolution, [status(thm)], [c_121, c_733])).
% 7.39/2.63  tff(c_2693, plain, (![A_165, B_166, C_167]: (k4_subset_1(A_165, B_166, C_167)=k2_xboole_0(B_166, C_167) | ~m1_subset_1(C_167, k1_zfmisc_1(A_165)) | ~m1_subset_1(B_166, k1_zfmisc_1(A_165)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.39/2.63  tff(c_6638, plain, (![B_240, B_241, A_242]: (k4_subset_1(B_240, B_241, A_242)=k2_xboole_0(B_241, A_242) | ~m1_subset_1(B_241, k1_zfmisc_1(B_240)) | ~r1_tarski(A_242, B_240))), inference(resolution, [status(thm)], [c_40, c_2693])).
% 7.39/2.63  tff(c_6765, plain, (![A_243]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_243)=k2_xboole_0('#skF_2', A_243) | ~r1_tarski(A_243, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_52, c_6638])).
% 7.39/2.63  tff(c_7459, plain, (![A_250]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_250)=k2_xboole_0('#skF_2', A_250) | ~r1_tarski(A_250, '#skF_2'))), inference(resolution, [status(thm)], [c_750, c_6765])).
% 7.39/2.63  tff(c_3409, plain, (![A_180, B_181]: (k4_subset_1(u1_struct_0(A_180), B_181, k2_tops_1(A_180, B_181))=k2_pre_topc(A_180, B_181) | ~m1_subset_1(B_181, k1_zfmisc_1(u1_struct_0(A_180))) | ~l1_pre_topc(A_180))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.39/2.63  tff(c_3414, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_3409])).
% 7.39/2.63  tff(c_3418, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3414])).
% 7.39/2.63  tff(c_7474, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7459, c_3418])).
% 7.39/2.63  tff(c_7497, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2184, c_6923, c_7474])).
% 7.39/2.63  tff(c_7499, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3259, c_7497])).
% 7.39/2.63  tff(c_7500, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 7.39/2.63  tff(c_7827, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_7500])).
% 7.39/2.63  tff(c_7828, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 7.39/2.63  tff(c_7919, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7828, c_58])).
% 7.39/2.63  tff(c_9679, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9675, c_7919])).
% 7.39/2.63  tff(c_10727, plain, (![A_378, B_379]: (k2_pre_topc(A_378, B_379)=B_379 | ~v4_pre_topc(B_379, A_378) | ~m1_subset_1(B_379, k1_zfmisc_1(u1_struct_0(A_378))) | ~l1_pre_topc(A_378))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.39/2.63  tff(c_10734, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_10727])).
% 7.39/2.63  tff(c_10738, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_7828, c_10734])).
% 7.39/2.63  tff(c_11564, plain, (![A_397, B_398]: (k7_subset_1(u1_struct_0(A_397), k2_pre_topc(A_397, B_398), k1_tops_1(A_397, B_398))=k2_tops_1(A_397, B_398) | ~m1_subset_1(B_398, k1_zfmisc_1(u1_struct_0(A_397))) | ~l1_pre_topc(A_397))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.39/2.63  tff(c_11573, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10738, c_11564])).
% 7.39/2.63  tff(c_11577, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_9675, c_11573])).
% 7.39/2.63  tff(c_11579, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9679, c_11577])).
% 7.39/2.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.39/2.63  
% 7.39/2.63  Inference rules
% 7.39/2.63  ----------------------
% 7.39/2.63  #Ref     : 0
% 7.39/2.63  #Sup     : 2736
% 7.39/2.63  #Fact    : 0
% 7.39/2.63  #Define  : 0
% 7.39/2.63  #Split   : 4
% 7.39/2.63  #Chain   : 0
% 7.39/2.63  #Close   : 0
% 7.39/2.63  
% 7.39/2.63  Ordering : KBO
% 7.39/2.63  
% 7.39/2.63  Simplification rules
% 7.39/2.63  ----------------------
% 7.39/2.63  #Subsume      : 162
% 7.39/2.63  #Demod        : 2095
% 7.39/2.63  #Tautology    : 1772
% 7.39/2.63  #SimpNegUnit  : 5
% 7.39/2.63  #BackRed      : 23
% 7.39/2.63  
% 7.39/2.63  #Partial instantiations: 0
% 7.39/2.63  #Strategies tried      : 1
% 7.39/2.63  
% 7.39/2.63  Timing (in seconds)
% 7.39/2.63  ----------------------
% 7.39/2.63  Preprocessing        : 0.36
% 7.39/2.63  Parsing              : 0.20
% 7.39/2.63  CNF conversion       : 0.02
% 7.39/2.63  Main loop            : 1.41
% 7.39/2.63  Inferencing          : 0.39
% 7.39/2.63  Reduction            : 0.65
% 7.39/2.63  Demodulation         : 0.52
% 7.39/2.63  BG Simplification    : 0.05
% 7.39/2.63  Subsumption          : 0.22
% 7.39/2.63  Abstraction          : 0.07
% 7.39/2.63  MUC search           : 0.00
% 7.39/2.63  Cooper               : 0.00
% 7.39/2.63  Total                : 1.84
% 7.39/2.63  Index Insertion      : 0.00
% 7.39/2.63  Index Deletion       : 0.00
% 7.39/2.63  Index Matching       : 0.00
% 7.39/2.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
