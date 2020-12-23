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
% DateTime   : Thu Dec  3 10:21:31 EST 2020

% Result     : Theorem 4.78s
% Output     : CNFRefutation 5.13s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 183 expanded)
%              Number of leaves         :   44 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :  150 ( 330 expanded)
%              Number of equality atoms :   73 ( 124 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_86,axiom,(
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

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_65,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_43,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_3066,plain,(
    ! [A_252,B_253,C_254] :
      ( k7_subset_1(A_252,B_253,C_254) = k4_xboole_0(B_253,C_254)
      | ~ m1_subset_1(B_253,k1_zfmisc_1(A_252)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3073,plain,(
    ! [C_254] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_254) = k4_xboole_0('#skF_2',C_254) ),
    inference(resolution,[status(thm)],[c_44,c_3066])).

tff(c_56,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_232,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_50,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_342,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1063,plain,(
    ! [B_119,A_120] :
      ( v4_pre_topc(B_119,A_120)
      | k2_pre_topc(A_120,B_119) != B_119
      | ~ v2_pre_topc(A_120)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1069,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1063])).

tff(c_1081,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_1069])).

tff(c_1082,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_342,c_1081])).

tff(c_1189,plain,(
    ! [A_126,B_127] :
      ( k4_subset_1(u1_struct_0(A_126),B_127,k2_tops_1(A_126,B_127)) = k2_pre_topc(A_126,B_127)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1193,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1189])).

tff(c_1203,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1193])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    ! [A_25] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_174,plain,(
    ! [A_60,B_61] :
      ( k4_xboole_0(A_60,B_61) = k3_subset_1(A_60,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_180,plain,(
    ! [A_25] : k4_xboole_0(A_25,k1_xboole_0) = k3_subset_1(A_25,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_28,c_174])).

tff(c_186,plain,(
    ! [A_25] : k3_subset_1(A_25,k1_xboole_0) = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_180])).

tff(c_419,plain,(
    ! [A_82,B_83] :
      ( k3_subset_1(A_82,k3_subset_1(A_82,B_83)) = B_83
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_423,plain,(
    ! [A_25] : k3_subset_1(A_25,k3_subset_1(A_25,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_419])).

tff(c_428,plain,(
    ! [A_25] : k3_subset_1(A_25,A_25) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_423])).

tff(c_16,plain,(
    ! [A_13] : k2_subset_1(A_13) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_16] : m1_subset_1(k2_subset_1(A_16),k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_57,plain,(
    ! [A_16] : m1_subset_1(A_16,k1_zfmisc_1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20])).

tff(c_187,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_subset_1(A_16,A_16) ),
    inference(resolution,[status(thm)],[c_57,c_174])).

tff(c_87,plain,(
    ! [A_48,B_49] : r1_tarski(k4_xboole_0(A_48,B_49),A_48) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_90,plain,(
    ! [A_12] : r1_tarski(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_87])).

tff(c_125,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = A_53
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_132,plain,(
    ! [A_12] : k3_xboole_0(A_12,A_12) = A_12 ),
    inference(resolution,[status(thm)],[c_90,c_125])).

tff(c_156,plain,(
    ! [A_58,B_59] : k5_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = k4_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_165,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k4_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_156])).

tff(c_233,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k3_subset_1(A_12,A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_165])).

tff(c_432,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_233])).

tff(c_700,plain,(
    ! [A_93,B_94,C_95] :
      ( k7_subset_1(A_93,B_94,C_95) = k4_xboole_0(B_94,C_95)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_714,plain,(
    ! [C_96] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_96) = k4_xboole_0('#skF_2',C_96) ),
    inference(resolution,[status(thm)],[c_44,c_700])).

tff(c_726,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_714])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_257,plain,(
    ! [A_66,B_67] : k3_xboole_0(k4_xboole_0(A_66,B_67),A_66) = k4_xboole_0(A_66,B_67) ),
    inference(resolution,[status(thm)],[c_10,c_125])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_266,plain,(
    ! [A_66,B_67] : k3_xboole_0(A_66,k4_xboole_0(A_66,B_67)) = k4_xboole_0(A_66,B_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_2])).

tff(c_778,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_726,c_266])).

tff(c_790,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_726,c_778])).

tff(c_168,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_156])).

tff(c_872,plain,(
    k5_xboole_0(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_790,c_168])).

tff(c_878,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_872])).

tff(c_12,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_889,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_878,c_12])).

tff(c_897,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_889])).

tff(c_36,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(k2_tops_1(A_32,B_33),k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_994,plain,(
    ! [A_112,B_113,C_114] :
      ( k4_subset_1(A_112,B_113,C_114) = k2_xboole_0(B_113,C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(A_112))
      | ~ m1_subset_1(B_113,k1_zfmisc_1(A_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2227,plain,(
    ! [A_205,B_206,B_207] :
      ( k4_subset_1(u1_struct_0(A_205),B_206,k2_tops_1(A_205,B_207)) = k2_xboole_0(B_206,k2_tops_1(A_205,B_207))
      | ~ m1_subset_1(B_206,k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ l1_pre_topc(A_205) ) ),
    inference(resolution,[status(thm)],[c_36,c_994])).

tff(c_2231,plain,(
    ! [B_207] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_207)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_207))
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_2227])).

tff(c_2244,plain,(
    ! [B_208] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_208)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_208))
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2231])).

tff(c_2251,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_2244])).

tff(c_2264,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1203,c_897,c_2251])).

tff(c_2266,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1082,c_2264])).

tff(c_2267,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2537,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_2267])).

tff(c_2538,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2561,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2538,c_50])).

tff(c_3103,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3073,c_2561])).

tff(c_3234,plain,(
    ! [A_266,B_267] :
      ( k2_pre_topc(A_266,B_267) = B_267
      | ~ v4_pre_topc(B_267,A_266)
      | ~ m1_subset_1(B_267,k1_zfmisc_1(u1_struct_0(A_266)))
      | ~ l1_pre_topc(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3237,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_3234])).

tff(c_3248,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2538,c_3237])).

tff(c_3580,plain,(
    ! [A_298,B_299] :
      ( k7_subset_1(u1_struct_0(A_298),k2_pre_topc(A_298,B_299),k1_tops_1(A_298,B_299)) = k2_tops_1(A_298,B_299)
      | ~ m1_subset_1(B_299,k1_zfmisc_1(u1_struct_0(A_298)))
      | ~ l1_pre_topc(A_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3589,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3248,c_3580])).

tff(c_3593,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_3073,c_3589])).

tff(c_3595,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3103,c_3593])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:08:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.78/1.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.13/1.94  
% 5.13/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.13/1.94  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.13/1.94  
% 5.13/1.94  %Foreground sorts:
% 5.13/1.94  
% 5.13/1.94  
% 5.13/1.94  %Background operators:
% 5.13/1.94  
% 5.13/1.94  
% 5.13/1.94  %Foreground operators:
% 5.13/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.13/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.13/1.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.13/1.94  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.13/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.13/1.94  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.13/1.94  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.13/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.13/1.94  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.13/1.94  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.13/1.94  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.13/1.94  tff('#skF_2', type, '#skF_2': $i).
% 5.13/1.94  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.13/1.94  tff('#skF_1', type, '#skF_1': $i).
% 5.13/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.13/1.94  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.13/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.13/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.13/1.94  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.13/1.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.13/1.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.13/1.94  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.13/1.94  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.13/1.94  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.13/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.13/1.94  
% 5.13/1.96  tff(f_126, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 5.13/1.96  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.13/1.96  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.13/1.96  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 5.13/1.96  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 5.13/1.96  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.13/1.96  tff(f_65, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.13/1.96  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.13/1.96  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 5.13/1.96  tff(f_43, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.13/1.96  tff(f_49, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.13/1.96  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.13/1.96  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.13/1.96  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.13/1.96  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.13/1.96  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.13/1.96  tff(f_92, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.13/1.96  tff(f_59, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.13/1.96  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 5.13/1.96  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.13/1.96  tff(c_3066, plain, (![A_252, B_253, C_254]: (k7_subset_1(A_252, B_253, C_254)=k4_xboole_0(B_253, C_254) | ~m1_subset_1(B_253, k1_zfmisc_1(A_252)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.13/1.96  tff(c_3073, plain, (![C_254]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_254)=k4_xboole_0('#skF_2', C_254))), inference(resolution, [status(thm)], [c_44, c_3066])).
% 5.13/1.96  tff(c_56, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.13/1.96  tff(c_232, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_56])).
% 5.13/1.96  tff(c_50, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.13/1.96  tff(c_342, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 5.13/1.96  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.13/1.96  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.13/1.96  tff(c_1063, plain, (![B_119, A_120]: (v4_pre_topc(B_119, A_120) | k2_pre_topc(A_120, B_119)!=B_119 | ~v2_pre_topc(A_120) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.13/1.96  tff(c_1069, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1063])).
% 5.13/1.96  tff(c_1081, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_1069])).
% 5.13/1.96  tff(c_1082, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_342, c_1081])).
% 5.13/1.96  tff(c_1189, plain, (![A_126, B_127]: (k4_subset_1(u1_struct_0(A_126), B_127, k2_tops_1(A_126, B_127))=k2_pre_topc(A_126, B_127) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.13/1.96  tff(c_1193, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1189])).
% 5.13/1.96  tff(c_1203, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1193])).
% 5.13/1.96  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.13/1.96  tff(c_14, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.13/1.96  tff(c_28, plain, (![A_25]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.13/1.96  tff(c_174, plain, (![A_60, B_61]: (k4_xboole_0(A_60, B_61)=k3_subset_1(A_60, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.13/1.96  tff(c_180, plain, (![A_25]: (k4_xboole_0(A_25, k1_xboole_0)=k3_subset_1(A_25, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_174])).
% 5.13/1.96  tff(c_186, plain, (![A_25]: (k3_subset_1(A_25, k1_xboole_0)=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_180])).
% 5.13/1.96  tff(c_419, plain, (![A_82, B_83]: (k3_subset_1(A_82, k3_subset_1(A_82, B_83))=B_83 | ~m1_subset_1(B_83, k1_zfmisc_1(A_82)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.13/1.96  tff(c_423, plain, (![A_25]: (k3_subset_1(A_25, k3_subset_1(A_25, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_419])).
% 5.13/1.96  tff(c_428, plain, (![A_25]: (k3_subset_1(A_25, A_25)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_186, c_423])).
% 5.13/1.96  tff(c_16, plain, (![A_13]: (k2_subset_1(A_13)=A_13)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.13/1.96  tff(c_20, plain, (![A_16]: (m1_subset_1(k2_subset_1(A_16), k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.13/1.96  tff(c_57, plain, (![A_16]: (m1_subset_1(A_16, k1_zfmisc_1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20])).
% 5.13/1.96  tff(c_187, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_subset_1(A_16, A_16))), inference(resolution, [status(thm)], [c_57, c_174])).
% 5.13/1.96  tff(c_87, plain, (![A_48, B_49]: (r1_tarski(k4_xboole_0(A_48, B_49), A_48))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.13/1.96  tff(c_90, plain, (![A_12]: (r1_tarski(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_14, c_87])).
% 5.13/1.96  tff(c_125, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=A_53 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.13/1.96  tff(c_132, plain, (![A_12]: (k3_xboole_0(A_12, A_12)=A_12)), inference(resolution, [status(thm)], [c_90, c_125])).
% 5.13/1.96  tff(c_156, plain, (![A_58, B_59]: (k5_xboole_0(A_58, k3_xboole_0(A_58, B_59))=k4_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.13/1.96  tff(c_165, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k4_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_132, c_156])).
% 5.13/1.96  tff(c_233, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k3_subset_1(A_12, A_12))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_165])).
% 5.13/1.96  tff(c_432, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_428, c_233])).
% 5.13/1.96  tff(c_700, plain, (![A_93, B_94, C_95]: (k7_subset_1(A_93, B_94, C_95)=k4_xboole_0(B_94, C_95) | ~m1_subset_1(B_94, k1_zfmisc_1(A_93)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.13/1.96  tff(c_714, plain, (![C_96]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_96)=k4_xboole_0('#skF_2', C_96))), inference(resolution, [status(thm)], [c_44, c_700])).
% 5.13/1.96  tff(c_726, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_232, c_714])).
% 5.13/1.96  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.13/1.96  tff(c_257, plain, (![A_66, B_67]: (k3_xboole_0(k4_xboole_0(A_66, B_67), A_66)=k4_xboole_0(A_66, B_67))), inference(resolution, [status(thm)], [c_10, c_125])).
% 5.13/1.96  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.13/1.96  tff(c_266, plain, (![A_66, B_67]: (k3_xboole_0(A_66, k4_xboole_0(A_66, B_67))=k4_xboole_0(A_66, B_67))), inference(superposition, [status(thm), theory('equality')], [c_257, c_2])).
% 5.13/1.96  tff(c_778, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_726, c_266])).
% 5.13/1.96  tff(c_790, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_726, c_778])).
% 5.13/1.96  tff(c_168, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_156])).
% 5.13/1.96  tff(c_872, plain, (k5_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_790, c_168])).
% 5.13/1.96  tff(c_878, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_432, c_872])).
% 5.13/1.96  tff(c_12, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.13/1.96  tff(c_889, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_878, c_12])).
% 5.13/1.96  tff(c_897, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_889])).
% 5.13/1.96  tff(c_36, plain, (![A_32, B_33]: (m1_subset_1(k2_tops_1(A_32, B_33), k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.13/1.96  tff(c_994, plain, (![A_112, B_113, C_114]: (k4_subset_1(A_112, B_113, C_114)=k2_xboole_0(B_113, C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(A_112)) | ~m1_subset_1(B_113, k1_zfmisc_1(A_112)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.13/1.96  tff(c_2227, plain, (![A_205, B_206, B_207]: (k4_subset_1(u1_struct_0(A_205), B_206, k2_tops_1(A_205, B_207))=k2_xboole_0(B_206, k2_tops_1(A_205, B_207)) | ~m1_subset_1(B_206, k1_zfmisc_1(u1_struct_0(A_205))) | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0(A_205))) | ~l1_pre_topc(A_205))), inference(resolution, [status(thm)], [c_36, c_994])).
% 5.13/1.96  tff(c_2231, plain, (![B_207]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_207))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_207)) | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_2227])).
% 5.13/1.96  tff(c_2244, plain, (![B_208]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_208))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_208)) | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2231])).
% 5.13/1.96  tff(c_2251, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_2244])).
% 5.13/1.96  tff(c_2264, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1203, c_897, c_2251])).
% 5.13/1.96  tff(c_2266, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1082, c_2264])).
% 5.13/1.96  tff(c_2267, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 5.13/1.96  tff(c_2537, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_232, c_2267])).
% 5.13/1.96  tff(c_2538, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 5.13/1.96  tff(c_2561, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2538, c_50])).
% 5.13/1.96  tff(c_3103, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3073, c_2561])).
% 5.13/1.96  tff(c_3234, plain, (![A_266, B_267]: (k2_pre_topc(A_266, B_267)=B_267 | ~v4_pre_topc(B_267, A_266) | ~m1_subset_1(B_267, k1_zfmisc_1(u1_struct_0(A_266))) | ~l1_pre_topc(A_266))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.13/1.96  tff(c_3237, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_3234])).
% 5.13/1.96  tff(c_3248, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2538, c_3237])).
% 5.13/1.96  tff(c_3580, plain, (![A_298, B_299]: (k7_subset_1(u1_struct_0(A_298), k2_pre_topc(A_298, B_299), k1_tops_1(A_298, B_299))=k2_tops_1(A_298, B_299) | ~m1_subset_1(B_299, k1_zfmisc_1(u1_struct_0(A_298))) | ~l1_pre_topc(A_298))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.13/1.96  tff(c_3589, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3248, c_3580])).
% 5.13/1.96  tff(c_3593, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_3073, c_3589])).
% 5.13/1.96  tff(c_3595, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3103, c_3593])).
% 5.13/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.13/1.96  
% 5.13/1.96  Inference rules
% 5.13/1.96  ----------------------
% 5.13/1.96  #Ref     : 0
% 5.13/1.96  #Sup     : 875
% 5.13/1.96  #Fact    : 0
% 5.13/1.96  #Define  : 0
% 5.13/1.96  #Split   : 3
% 5.13/1.96  #Chain   : 0
% 5.13/1.96  #Close   : 0
% 5.13/1.96  
% 5.13/1.96  Ordering : KBO
% 5.13/1.96  
% 5.13/1.96  Simplification rules
% 5.13/1.96  ----------------------
% 5.13/1.96  #Subsume      : 27
% 5.13/1.96  #Demod        : 489
% 5.13/1.96  #Tautology    : 626
% 5.13/1.96  #SimpNegUnit  : 3
% 5.13/1.96  #BackRed      : 16
% 5.13/1.96  
% 5.13/1.96  #Partial instantiations: 0
% 5.13/1.96  #Strategies tried      : 1
% 5.13/1.96  
% 5.13/1.96  Timing (in seconds)
% 5.13/1.96  ----------------------
% 5.13/1.96  Preprocessing        : 0.34
% 5.13/1.96  Parsing              : 0.18
% 5.13/1.96  CNF conversion       : 0.02
% 5.13/1.96  Main loop            : 0.83
% 5.13/1.96  Inferencing          : 0.31
% 5.13/1.96  Reduction            : 0.31
% 5.13/1.96  Demodulation         : 0.24
% 5.13/1.96  BG Simplification    : 0.03
% 5.13/1.96  Subsumption          : 0.13
% 5.13/1.96  Abstraction          : 0.04
% 5.13/1.96  MUC search           : 0.00
% 5.13/1.96  Cooper               : 0.00
% 5.13/1.96  Total                : 1.21
% 5.13/1.96  Index Insertion      : 0.00
% 5.13/1.96  Index Deletion       : 0.00
% 5.13/1.96  Index Matching       : 0.00
% 5.13/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
