%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:18 EST 2020

% Result     : Theorem 4.82s
% Output     : CNFRefutation 5.19s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 181 expanded)
%              Number of leaves         :   41 (  79 expanded)
%              Depth                    :   10
%              Number of atoms          :  136 ( 322 expanded)
%              Number of equality atoms :   61 ( 113 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_49,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_41,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_35,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2543,plain,(
    ! [A_220,B_221,C_222] :
      ( k7_subset_1(A_220,B_221,C_222) = k4_xboole_0(B_221,C_222)
      | ~ m1_subset_1(B_221,k1_zfmisc_1(A_220)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2552,plain,(
    ! [C_222] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_222) = k4_xboole_0('#skF_2',C_222) ),
    inference(resolution,[status(thm)],[c_38,c_2543])).

tff(c_44,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_135,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_982,plain,(
    ! [B_101,A_102] :
      ( v4_pre_topc(B_101,A_102)
      | k2_pre_topc(A_102,B_101) != B_101
      | ~ v2_pre_topc(A_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_996,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_982])).

tff(c_1002,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_996])).

tff(c_1003,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_1002])).

tff(c_524,plain,(
    ! [A_73,B_74,C_75] :
      ( k7_subset_1(A_73,B_74,C_75) = k4_xboole_0(B_74,C_75)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_534,plain,(
    ! [C_76] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_76) = k4_xboole_0('#skF_2',C_76) ),
    inference(resolution,[status(thm)],[c_38,c_524])).

tff(c_50,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_264,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_50])).

tff(c_540,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_534,c_264])).

tff(c_18,plain,(
    ! [A_17,B_18] : k6_subset_1(A_17,B_18) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_12,B_13] : m1_subset_1(k6_subset_1(A_12,B_13),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_51,plain,(
    ! [A_12,B_13] : m1_subset_1(k4_xboole_0(A_12,B_13),k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_14])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k3_subset_1(A_10,B_11),k1_zfmisc_1(A_10))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_942,plain,(
    ! [A_97,B_98,C_99] :
      ( k4_subset_1(A_97,B_98,C_99) = k2_xboole_0(B_98,C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(A_97))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1239,plain,(
    ! [A_137,B_138,B_139] :
      ( k4_subset_1(A_137,B_138,k3_subset_1(A_137,B_139)) = k2_xboole_0(B_138,k3_subset_1(A_137,B_139))
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_137))
      | ~ m1_subset_1(B_139,k1_zfmisc_1(A_137)) ) ),
    inference(resolution,[status(thm)],[c_12,c_942])).

tff(c_1281,plain,(
    ! [A_144,B_145,B_146] :
      ( k4_subset_1(A_144,k4_xboole_0(A_144,B_145),k3_subset_1(A_144,B_146)) = k2_xboole_0(k4_xboole_0(A_144,B_145),k3_subset_1(A_144,B_146))
      | ~ m1_subset_1(B_146,k1_zfmisc_1(A_144)) ) ),
    inference(resolution,[status(thm)],[c_51,c_1239])).

tff(c_10,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    ! [A_22,B_23] :
      ( k4_subset_1(A_22,B_23,k3_subset_1(A_22,B_23)) = k2_subset_1(A_22)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_561,plain,(
    ! [A_77,B_78] :
      ( k4_subset_1(A_77,B_78,k3_subset_1(A_77,B_78)) = A_77
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_22])).

tff(c_572,plain,(
    ! [A_12,B_13] : k4_subset_1(A_12,k4_xboole_0(A_12,B_13),k3_subset_1(A_12,k4_xboole_0(A_12,B_13))) = A_12 ),
    inference(resolution,[status(thm)],[c_51,c_561])).

tff(c_1288,plain,(
    ! [A_144,B_145] :
      ( k2_xboole_0(k4_xboole_0(A_144,B_145),k3_subset_1(A_144,k4_xboole_0(A_144,B_145))) = A_144
      | ~ m1_subset_1(k4_xboole_0(A_144,B_145),k1_zfmisc_1(A_144)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1281,c_572])).

tff(c_1300,plain,(
    ! [A_144,B_145] : k2_xboole_0(k4_xboole_0(A_144,B_145),k3_subset_1(A_144,k4_xboole_0(A_144,B_145))) = A_144 ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_1288])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_120,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_192,plain,(
    ! [B_55,A_56] : k3_tarski(k2_tarski(B_55,A_56)) = k2_xboole_0(A_56,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_120])).

tff(c_8,plain,(
    ! [A_7,B_8] : k3_tarski(k2_tarski(A_7,B_8)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_198,plain,(
    ! [B_55,A_56] : k2_xboole_0(B_55,A_56) = k2_xboole_0(A_56,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_8])).

tff(c_1305,plain,(
    ! [A_147,B_148] : k2_xboole_0(k4_xboole_0(A_147,B_148),k3_subset_1(A_147,k4_xboole_0(A_147,B_148))) = A_147 ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_1288])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1338,plain,(
    ! [A_147,B_148] : k2_xboole_0(k4_xboole_0(A_147,B_148),k3_subset_1(A_147,k4_xboole_0(A_147,B_148))) = k2_xboole_0(k4_xboole_0(A_147,B_148),A_147) ),
    inference(superposition,[status(thm),theory(equality)],[c_1305,c_4])).

tff(c_1463,plain,(
    ! [A_153,B_154] : k2_xboole_0(A_153,k4_xboole_0(A_153,B_154)) = A_153 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1300,c_198,c_1338])).

tff(c_1496,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_1463])).

tff(c_1091,plain,(
    ! [A_113,B_114] :
      ( k4_subset_1(u1_struct_0(A_113),B_114,k2_tops_1(A_113,B_114)) = k2_pre_topc(A_113,B_114)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1101,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1091])).

tff(c_1107,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1101])).

tff(c_30,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(k2_tops_1(A_29,B_30),k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2182,plain,(
    ! [A_192,B_193,B_194] :
      ( k4_subset_1(u1_struct_0(A_192),B_193,k2_tops_1(A_192,B_194)) = k2_xboole_0(B_193,k2_tops_1(A_192,B_194))
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ l1_pre_topc(A_192) ) ),
    inference(resolution,[status(thm)],[c_30,c_942])).

tff(c_2192,plain,(
    ! [B_194] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_194)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_194))
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_2182])).

tff(c_2204,plain,(
    ! [B_197] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_197)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_197))
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2192])).

tff(c_2219,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_2204])).

tff(c_2226,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1496,c_1107,c_2219])).

tff(c_2228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1003,c_2226])).

tff(c_2229,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2553,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2552,c_2229])).

tff(c_2230,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2941,plain,(
    ! [A_234,B_235] :
      ( k2_pre_topc(A_234,B_235) = B_235
      | ~ v4_pre_topc(B_235,A_234)
      | ~ m1_subset_1(B_235,k1_zfmisc_1(u1_struct_0(A_234)))
      | ~ l1_pre_topc(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2955,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_2941])).

tff(c_2961,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2230,c_2955])).

tff(c_3180,plain,(
    ! [A_273,B_274] :
      ( k7_subset_1(u1_struct_0(A_273),k2_pre_topc(A_273,B_274),k1_tops_1(A_273,B_274)) = k2_tops_1(A_273,B_274)
      | ~ m1_subset_1(B_274,k1_zfmisc_1(u1_struct_0(A_273)))
      | ~ l1_pre_topc(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3189,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2961,c_3180])).

tff(c_3193,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_2552,c_3189])).

tff(c_3195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2553,c_3193])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.82/1.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/2.00  
% 4.82/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/2.00  %$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 4.82/2.00  
% 4.82/2.00  %Foreground sorts:
% 4.82/2.00  
% 4.82/2.00  
% 4.82/2.00  %Background operators:
% 4.82/2.00  
% 4.82/2.00  
% 4.82/2.00  %Foreground operators:
% 4.82/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.82/2.00  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.82/2.00  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.82/2.00  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.82/2.00  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.82/2.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.82/2.00  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.82/2.00  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.82/2.00  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.82/2.00  tff('#skF_2', type, '#skF_2': $i).
% 4.82/2.00  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.82/2.00  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 4.82/2.00  tff('#skF_1', type, '#skF_1': $i).
% 4.82/2.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.82/2.00  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.82/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.82/2.00  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.82/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.82/2.00  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.82/2.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.82/2.00  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.82/2.00  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.82/2.00  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.82/2.00  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.82/2.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.82/2.00  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.82/2.00  
% 5.19/2.02  tff(f_114, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 5.19/2.02  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.19/2.02  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.19/2.02  tff(f_49, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 5.19/2.02  tff(f_41, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 5.19/2.02  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.19/2.02  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.19/2.02  tff(f_35, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 5.19/2.02  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 5.19/2.02  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.19/2.02  tff(f_33, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.19/2.02  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 5.19/2.02  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 5.19/2.02  tff(f_80, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.19/2.02  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 5.19/2.02  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.19/2.02  tff(c_2543, plain, (![A_220, B_221, C_222]: (k7_subset_1(A_220, B_221, C_222)=k4_xboole_0(B_221, C_222) | ~m1_subset_1(B_221, k1_zfmisc_1(A_220)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.19/2.02  tff(c_2552, plain, (![C_222]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_222)=k4_xboole_0('#skF_2', C_222))), inference(resolution, [status(thm)], [c_38, c_2543])).
% 5.19/2.02  tff(c_44, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.19/2.02  tff(c_135, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 5.19/2.02  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.19/2.02  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.19/2.02  tff(c_982, plain, (![B_101, A_102]: (v4_pre_topc(B_101, A_102) | k2_pre_topc(A_102, B_101)!=B_101 | ~v2_pre_topc(A_102) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.19/2.02  tff(c_996, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_982])).
% 5.19/2.02  tff(c_1002, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_996])).
% 5.19/2.02  tff(c_1003, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_135, c_1002])).
% 5.19/2.02  tff(c_524, plain, (![A_73, B_74, C_75]: (k7_subset_1(A_73, B_74, C_75)=k4_xboole_0(B_74, C_75) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.19/2.02  tff(c_534, plain, (![C_76]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_76)=k4_xboole_0('#skF_2', C_76))), inference(resolution, [status(thm)], [c_38, c_524])).
% 5.19/2.02  tff(c_50, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.19/2.02  tff(c_264, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_135, c_50])).
% 5.19/2.02  tff(c_540, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_534, c_264])).
% 5.19/2.02  tff(c_18, plain, (![A_17, B_18]: (k6_subset_1(A_17, B_18)=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.19/2.02  tff(c_14, plain, (![A_12, B_13]: (m1_subset_1(k6_subset_1(A_12, B_13), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.19/2.02  tff(c_51, plain, (![A_12, B_13]: (m1_subset_1(k4_xboole_0(A_12, B_13), k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_14])).
% 5.19/2.02  tff(c_12, plain, (![A_10, B_11]: (m1_subset_1(k3_subset_1(A_10, B_11), k1_zfmisc_1(A_10)) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.19/2.02  tff(c_942, plain, (![A_97, B_98, C_99]: (k4_subset_1(A_97, B_98, C_99)=k2_xboole_0(B_98, C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(A_97)) | ~m1_subset_1(B_98, k1_zfmisc_1(A_97)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.19/2.02  tff(c_1239, plain, (![A_137, B_138, B_139]: (k4_subset_1(A_137, B_138, k3_subset_1(A_137, B_139))=k2_xboole_0(B_138, k3_subset_1(A_137, B_139)) | ~m1_subset_1(B_138, k1_zfmisc_1(A_137)) | ~m1_subset_1(B_139, k1_zfmisc_1(A_137)))), inference(resolution, [status(thm)], [c_12, c_942])).
% 5.19/2.02  tff(c_1281, plain, (![A_144, B_145, B_146]: (k4_subset_1(A_144, k4_xboole_0(A_144, B_145), k3_subset_1(A_144, B_146))=k2_xboole_0(k4_xboole_0(A_144, B_145), k3_subset_1(A_144, B_146)) | ~m1_subset_1(B_146, k1_zfmisc_1(A_144)))), inference(resolution, [status(thm)], [c_51, c_1239])).
% 5.19/2.02  tff(c_10, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.19/2.02  tff(c_22, plain, (![A_22, B_23]: (k4_subset_1(A_22, B_23, k3_subset_1(A_22, B_23))=k2_subset_1(A_22) | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.19/2.02  tff(c_561, plain, (![A_77, B_78]: (k4_subset_1(A_77, B_78, k3_subset_1(A_77, B_78))=A_77 | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_22])).
% 5.19/2.02  tff(c_572, plain, (![A_12, B_13]: (k4_subset_1(A_12, k4_xboole_0(A_12, B_13), k3_subset_1(A_12, k4_xboole_0(A_12, B_13)))=A_12)), inference(resolution, [status(thm)], [c_51, c_561])).
% 5.19/2.02  tff(c_1288, plain, (![A_144, B_145]: (k2_xboole_0(k4_xboole_0(A_144, B_145), k3_subset_1(A_144, k4_xboole_0(A_144, B_145)))=A_144 | ~m1_subset_1(k4_xboole_0(A_144, B_145), k1_zfmisc_1(A_144)))), inference(superposition, [status(thm), theory('equality')], [c_1281, c_572])).
% 5.19/2.02  tff(c_1300, plain, (![A_144, B_145]: (k2_xboole_0(k4_xboole_0(A_144, B_145), k3_subset_1(A_144, k4_xboole_0(A_144, B_145)))=A_144)), inference(demodulation, [status(thm), theory('equality')], [c_51, c_1288])).
% 5.19/2.02  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.19/2.02  tff(c_120, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.19/2.02  tff(c_192, plain, (![B_55, A_56]: (k3_tarski(k2_tarski(B_55, A_56))=k2_xboole_0(A_56, B_55))), inference(superposition, [status(thm), theory('equality')], [c_6, c_120])).
% 5.19/2.02  tff(c_8, plain, (![A_7, B_8]: (k3_tarski(k2_tarski(A_7, B_8))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.19/2.02  tff(c_198, plain, (![B_55, A_56]: (k2_xboole_0(B_55, A_56)=k2_xboole_0(A_56, B_55))), inference(superposition, [status(thm), theory('equality')], [c_192, c_8])).
% 5.19/2.02  tff(c_1305, plain, (![A_147, B_148]: (k2_xboole_0(k4_xboole_0(A_147, B_148), k3_subset_1(A_147, k4_xboole_0(A_147, B_148)))=A_147)), inference(demodulation, [status(thm), theory('equality')], [c_51, c_1288])).
% 5.19/2.02  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.19/2.02  tff(c_1338, plain, (![A_147, B_148]: (k2_xboole_0(k4_xboole_0(A_147, B_148), k3_subset_1(A_147, k4_xboole_0(A_147, B_148)))=k2_xboole_0(k4_xboole_0(A_147, B_148), A_147))), inference(superposition, [status(thm), theory('equality')], [c_1305, c_4])).
% 5.19/2.02  tff(c_1463, plain, (![A_153, B_154]: (k2_xboole_0(A_153, k4_xboole_0(A_153, B_154))=A_153)), inference(demodulation, [status(thm), theory('equality')], [c_1300, c_198, c_1338])).
% 5.19/2.02  tff(c_1496, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_540, c_1463])).
% 5.19/2.02  tff(c_1091, plain, (![A_113, B_114]: (k4_subset_1(u1_struct_0(A_113), B_114, k2_tops_1(A_113, B_114))=k2_pre_topc(A_113, B_114) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.19/2.02  tff(c_1101, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1091])).
% 5.19/2.02  tff(c_1107, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1101])).
% 5.19/2.02  tff(c_30, plain, (![A_29, B_30]: (m1_subset_1(k2_tops_1(A_29, B_30), k1_zfmisc_1(u1_struct_0(A_29))) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.19/2.02  tff(c_2182, plain, (![A_192, B_193, B_194]: (k4_subset_1(u1_struct_0(A_192), B_193, k2_tops_1(A_192, B_194))=k2_xboole_0(B_193, k2_tops_1(A_192, B_194)) | ~m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0(A_192))) | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0(A_192))) | ~l1_pre_topc(A_192))), inference(resolution, [status(thm)], [c_30, c_942])).
% 5.19/2.02  tff(c_2192, plain, (![B_194]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_194))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_194)) | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_2182])).
% 5.19/2.02  tff(c_2204, plain, (![B_197]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_197))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_197)) | ~m1_subset_1(B_197, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2192])).
% 5.19/2.02  tff(c_2219, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_2204])).
% 5.19/2.02  tff(c_2226, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1496, c_1107, c_2219])).
% 5.19/2.02  tff(c_2228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1003, c_2226])).
% 5.19/2.02  tff(c_2229, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 5.19/2.02  tff(c_2553, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2552, c_2229])).
% 5.19/2.02  tff(c_2230, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 5.19/2.02  tff(c_2941, plain, (![A_234, B_235]: (k2_pre_topc(A_234, B_235)=B_235 | ~v4_pre_topc(B_235, A_234) | ~m1_subset_1(B_235, k1_zfmisc_1(u1_struct_0(A_234))) | ~l1_pre_topc(A_234))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.19/2.02  tff(c_2955, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_2941])).
% 5.19/2.02  tff(c_2961, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2230, c_2955])).
% 5.19/2.02  tff(c_3180, plain, (![A_273, B_274]: (k7_subset_1(u1_struct_0(A_273), k2_pre_topc(A_273, B_274), k1_tops_1(A_273, B_274))=k2_tops_1(A_273, B_274) | ~m1_subset_1(B_274, k1_zfmisc_1(u1_struct_0(A_273))) | ~l1_pre_topc(A_273))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.19/2.02  tff(c_3189, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2961, c_3180])).
% 5.19/2.02  tff(c_3193, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_2552, c_3189])).
% 5.19/2.02  tff(c_3195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2553, c_3193])).
% 5.19/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.19/2.02  
% 5.19/2.02  Inference rules
% 5.19/2.02  ----------------------
% 5.19/2.02  #Ref     : 0
% 5.19/2.02  #Sup     : 769
% 5.19/2.02  #Fact    : 0
% 5.19/2.02  #Define  : 0
% 5.19/2.02  #Split   : 2
% 5.19/2.02  #Chain   : 0
% 5.19/2.02  #Close   : 0
% 5.19/2.02  
% 5.19/2.02  Ordering : KBO
% 5.19/2.02  
% 5.19/2.02  Simplification rules
% 5.19/2.02  ----------------------
% 5.19/2.02  #Subsume      : 71
% 5.19/2.02  #Demod        : 919
% 5.19/2.02  #Tautology    : 554
% 5.19/2.02  #SimpNegUnit  : 4
% 5.19/2.02  #BackRed      : 6
% 5.19/2.02  
% 5.19/2.02  #Partial instantiations: 0
% 5.19/2.02  #Strategies tried      : 1
% 5.19/2.02  
% 5.19/2.02  Timing (in seconds)
% 5.19/2.02  ----------------------
% 5.19/2.02  Preprocessing        : 0.35
% 5.19/2.02  Parsing              : 0.19
% 5.19/2.02  CNF conversion       : 0.02
% 5.19/2.02  Main loop            : 0.84
% 5.19/2.02  Inferencing          : 0.27
% 5.19/2.02  Reduction            : 0.38
% 5.19/2.02  Demodulation         : 0.32
% 5.19/2.02  BG Simplification    : 0.03
% 5.19/2.02  Subsumption          : 0.11
% 5.19/2.02  Abstraction          : 0.05
% 5.19/2.02  MUC search           : 0.00
% 5.19/2.02  Cooper               : 0.00
% 5.19/2.02  Total                : 1.23
% 5.19/2.02  Index Insertion      : 0.00
% 5.19/2.02  Index Deletion       : 0.00
% 5.19/2.02  Index Matching       : 0.00
% 5.19/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
