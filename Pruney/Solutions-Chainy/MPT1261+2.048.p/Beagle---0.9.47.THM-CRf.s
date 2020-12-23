%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:18 EST 2020

% Result     : Theorem 8.73s
% Output     : CNFRefutation 8.91s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 227 expanded)
%              Number of leaves         :   46 (  95 expanded)
%              Depth                    :   12
%              Number of atoms          :  151 ( 361 expanded)
%              Number of equality atoms :   78 ( 162 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_150,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_109,axiom,(
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

tff(f_138,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_90,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_124,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_14083,plain,(
    ! [A_437,B_438,C_439] :
      ( k7_subset_1(A_437,B_438,C_439) = k4_xboole_0(B_438,C_439)
      | ~ m1_subset_1(B_438,k1_zfmisc_1(A_437)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_14095,plain,(
    ! [C_439] : k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',C_439) = k4_xboole_0('#skF_4',C_439) ),
    inference(resolution,[status(thm)],[c_70,c_14083])).

tff(c_82,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k1_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_140,plain,(
    k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k1_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_76,plain,
    ( k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k1_tops_1('#skF_3','#skF_4')) != k2_tops_1('#skF_3','#skF_4')
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_232,plain,(
    ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_72,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_74,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_3248,plain,(
    ! [B_191,A_192] :
      ( v4_pre_topc(B_191,A_192)
      | k2_pre_topc(A_192,B_191) != B_191
      | ~ v2_pre_topc(A_192)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ l1_pre_topc(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_3281,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_3248])).

tff(c_3306,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_74,c_3281])).

tff(c_3307,plain,(
    k2_pre_topc('#skF_3','#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_3306])).

tff(c_4972,plain,(
    ! [A_222,B_223] :
      ( k4_subset_1(u1_struct_0(A_222),B_223,k2_tops_1(A_222,B_223)) = k2_pre_topc(A_222,B_223)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ l1_pre_topc(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_4995,plain,
    ( k4_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3','#skF_4')) = k2_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_4972])).

tff(c_5019,plain,(
    k4_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3','#skF_4')) = k2_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4995])).

tff(c_2157,plain,(
    ! [A_155,B_156,C_157] :
      ( k7_subset_1(A_155,B_156,C_157) = k4_xboole_0(B_156,C_157)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(A_155)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2167,plain,(
    ! [C_158] : k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',C_158) = k4_xboole_0('#skF_4',C_158) ),
    inference(resolution,[status(thm)],[c_70,c_2157])).

tff(c_2173,plain,(
    k4_xboole_0('#skF_4',k1_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2167,c_140])).

tff(c_30,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_166,plain,(
    ! [A_75,B_76] :
      ( k3_xboole_0(A_75,B_76) = A_75
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_196,plain,(
    ! [A_79] : k3_xboole_0(k1_xboole_0,A_79) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_166])).

tff(c_22,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_233,plain,(
    ! [A_81] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_22])).

tff(c_20,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_184,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k4_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_193,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_184])).

tff(c_239,plain,(
    ! [A_81] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_193])).

tff(c_250,plain,(
    ! [A_81] : k4_xboole_0(k1_xboole_0,A_81) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_239])).

tff(c_289,plain,(
    ! [A_83,B_84] : k5_xboole_0(A_83,k4_xboole_0(B_84,A_83)) = k2_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_298,plain,(
    ! [A_81] : k5_xboole_0(A_81,k1_xboole_0) = k2_xboole_0(A_81,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_289])).

tff(c_36,plain,(
    ! [B_22,A_21] : k2_tarski(B_22,A_21) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_141,plain,(
    ! [A_69,B_70] : k1_setfam_1(k2_tarski(A_69,B_70)) = k3_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_424,plain,(
    ! [B_92,A_93] : k1_setfam_1(k2_tarski(B_92,A_93)) = k3_xboole_0(A_93,B_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_141])).

tff(c_52,plain,(
    ! [A_42,B_43] : k1_setfam_1(k2_tarski(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_447,plain,(
    ! [B_94,A_95] : k3_xboole_0(B_94,A_95) = k3_xboole_0(A_95,B_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_52])).

tff(c_183,plain,(
    ! [A_13] : k3_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_166])).

tff(c_500,plain,(
    ! [B_96] : k3_xboole_0(B_96,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_183])).

tff(c_514,plain,(
    ! [B_96] : k5_xboole_0(B_96,k1_xboole_0) = k4_xboole_0(B_96,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_500,c_22])).

tff(c_540,plain,(
    ! [B_96] : k2_xboole_0(B_96,k1_xboole_0) = B_96 ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_30,c_514])).

tff(c_560,plain,(
    ! [A_81] : k5_xboole_0(A_81,k1_xboole_0) = A_81 ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_298])).

tff(c_463,plain,(
    ! [B_94] : k3_xboole_0(B_94,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_183])).

tff(c_603,plain,(
    ! [A_103,B_104] : k4_xboole_0(A_103,k4_xboole_0(A_103,B_104)) = k3_xboole_0(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_644,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_603])).

tff(c_651,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_644])).

tff(c_654,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_193])).

tff(c_28,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_846,plain,(
    ! [A_118,B_119] : k3_xboole_0(k4_xboole_0(A_118,B_119),A_118) = k4_xboole_0(A_118,B_119) ),
    inference(resolution,[status(thm)],[c_28,c_166])).

tff(c_868,plain,(
    ! [A_118,B_119] : k5_xboole_0(k4_xboole_0(A_118,B_119),k4_xboole_0(A_118,B_119)) = k4_xboole_0(k4_xboole_0(A_118,B_119),A_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_846,c_22])).

tff(c_911,plain,(
    ! [A_120,B_121] : k4_xboole_0(k4_xboole_0(A_120,B_121),A_120) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_868])).

tff(c_34,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_931,plain,(
    ! [A_120,B_121] : k2_xboole_0(A_120,k4_xboole_0(A_120,B_121)) = k5_xboole_0(A_120,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_911,c_34])).

tff(c_967,plain,(
    ! [A_120,B_121] : k2_xboole_0(A_120,k4_xboole_0(A_120,B_121)) = A_120 ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_931])).

tff(c_2188,plain,(
    k2_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2173,c_967])).

tff(c_2507,plain,(
    ! [A_168,B_169,C_170] :
      ( m1_subset_1(k7_subset_1(A_168,B_169,C_170),k1_zfmisc_1(A_168))
      | ~ m1_subset_1(B_169,k1_zfmisc_1(A_168)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2523,plain,
    ( m1_subset_1(k2_tops_1('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_2507])).

tff(c_2531,plain,(
    m1_subset_1(k2_tops_1('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2523])).

tff(c_54,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2545,plain,(
    r1_tarski(k2_tops_1('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2531,c_54])).

tff(c_56,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1(A_44,k1_zfmisc_1(B_45))
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3046,plain,(
    ! [A_185,B_186,C_187] :
      ( k4_subset_1(A_185,B_186,C_187) = k2_xboole_0(B_186,C_187)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(A_185))
      | ~ m1_subset_1(B_186,k1_zfmisc_1(A_185)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_11337,plain,(
    ! [B_323,B_324,A_325] :
      ( k4_subset_1(B_323,B_324,A_325) = k2_xboole_0(B_324,A_325)
      | ~ m1_subset_1(B_324,k1_zfmisc_1(B_323))
      | ~ r1_tarski(A_325,B_323) ) ),
    inference(resolution,[status(thm)],[c_56,c_3046])).

tff(c_11394,plain,(
    ! [A_326] :
      ( k4_subset_1(u1_struct_0('#skF_3'),'#skF_4',A_326) = k2_xboole_0('#skF_4',A_326)
      | ~ r1_tarski(A_326,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_70,c_11337])).

tff(c_11417,plain,(
    k4_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_2545,c_11394])).

tff(c_11455,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5019,c_2188,c_11417])).

tff(c_11457,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3307,c_11455])).

tff(c_11458,plain,(
    k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k1_tops_1('#skF_3','#skF_4')) != k2_tops_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_11637,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_11458])).

tff(c_11638,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_11728,plain,(
    k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k1_tops_1('#skF_3','#skF_4')) != k2_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11638,c_76])).

tff(c_14096,plain,(
    k4_xboole_0('#skF_4',k1_tops_1('#skF_3','#skF_4')) != k2_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14095,c_11728])).

tff(c_14260,plain,(
    ! [A_445,B_446] :
      ( k2_pre_topc(A_445,B_446) = B_446
      | ~ v4_pre_topc(B_446,A_445)
      | ~ m1_subset_1(B_446,k1_zfmisc_1(u1_struct_0(A_445)))
      | ~ l1_pre_topc(A_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_14281,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_14260])).

tff(c_14293,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_11638,c_14281])).

tff(c_16991,plain,(
    ! [A_516,B_517] :
      ( k7_subset_1(u1_struct_0(A_516),k2_pre_topc(A_516,B_517),k1_tops_1(A_516,B_517)) = k2_tops_1(A_516,B_517)
      | ~ m1_subset_1(B_517,k1_zfmisc_1(u1_struct_0(A_516)))
      | ~ l1_pre_topc(A_516) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_17003,plain,
    ( k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k1_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14293,c_16991])).

tff(c_17007,plain,(
    k4_xboole_0('#skF_4',k1_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_14095,c_17003])).

tff(c_17009,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14096,c_17007])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:29:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.73/3.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.73/3.21  
% 8.73/3.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.73/3.21  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 8.73/3.21  
% 8.73/3.21  %Foreground sorts:
% 8.73/3.21  
% 8.73/3.21  
% 8.73/3.21  %Background operators:
% 8.73/3.21  
% 8.73/3.21  
% 8.73/3.21  %Foreground operators:
% 8.73/3.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.73/3.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.73/3.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.73/3.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.73/3.21  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 8.73/3.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.73/3.21  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.73/3.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.73/3.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.73/3.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.73/3.21  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.73/3.21  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.73/3.21  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.73/3.21  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 8.73/3.21  tff('#skF_3', type, '#skF_3': $i).
% 8.73/3.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.73/3.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.73/3.21  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.73/3.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.73/3.21  tff('#skF_4', type, '#skF_4': $i).
% 8.73/3.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.73/3.21  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.73/3.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.73/3.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.73/3.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.73/3.21  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.73/3.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.73/3.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.73/3.21  
% 8.91/3.23  tff(f_150, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 8.91/3.23  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 8.91/3.23  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 8.91/3.23  tff(f_138, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 8.91/3.23  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.91/3.23  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.91/3.23  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.91/3.23  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.91/3.23  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.91/3.23  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.91/3.23  tff(f_55, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.91/3.23  tff(f_90, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 8.91/3.23  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.91/3.23  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.91/3.23  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 8.91/3.23  tff(f_94, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.91/3.23  tff(f_84, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 8.91/3.23  tff(f_124, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 8.91/3.23  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 8.91/3.23  tff(c_14083, plain, (![A_437, B_438, C_439]: (k7_subset_1(A_437, B_438, C_439)=k4_xboole_0(B_438, C_439) | ~m1_subset_1(B_438, k1_zfmisc_1(A_437)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.91/3.23  tff(c_14095, plain, (![C_439]: (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', C_439)=k4_xboole_0('#skF_4', C_439))), inference(resolution, [status(thm)], [c_70, c_14083])).
% 8.91/3.23  tff(c_82, plain, (v4_pre_topc('#skF_4', '#skF_3') | k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_150])).
% 8.91/3.23  tff(c_140, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_82])).
% 8.91/3.23  tff(c_76, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k1_tops_1('#skF_3', '#skF_4'))!=k2_tops_1('#skF_3', '#skF_4') | ~v4_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 8.91/3.23  tff(c_232, plain, (~v4_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_76])).
% 8.91/3.23  tff(c_72, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 8.91/3.23  tff(c_74, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 8.91/3.23  tff(c_3248, plain, (![B_191, A_192]: (v4_pre_topc(B_191, A_192) | k2_pre_topc(A_192, B_191)!=B_191 | ~v2_pre_topc(A_192) | ~m1_subset_1(B_191, k1_zfmisc_1(u1_struct_0(A_192))) | ~l1_pre_topc(A_192))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.91/3.23  tff(c_3281, plain, (v4_pre_topc('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!='#skF_4' | ~v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_70, c_3248])).
% 8.91/3.23  tff(c_3306, plain, (v4_pre_topc('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_74, c_3281])).
% 8.91/3.23  tff(c_3307, plain, (k2_pre_topc('#skF_3', '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_232, c_3306])).
% 8.91/3.23  tff(c_4972, plain, (![A_222, B_223]: (k4_subset_1(u1_struct_0(A_222), B_223, k2_tops_1(A_222, B_223))=k2_pre_topc(A_222, B_223) | ~m1_subset_1(B_223, k1_zfmisc_1(u1_struct_0(A_222))) | ~l1_pre_topc(A_222))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.91/3.23  tff(c_4995, plain, (k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k2_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_70, c_4972])).
% 8.91/3.23  tff(c_5019, plain, (k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k2_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4995])).
% 8.91/3.23  tff(c_2157, plain, (![A_155, B_156, C_157]: (k7_subset_1(A_155, B_156, C_157)=k4_xboole_0(B_156, C_157) | ~m1_subset_1(B_156, k1_zfmisc_1(A_155)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.91/3.23  tff(c_2167, plain, (![C_158]: (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', C_158)=k4_xboole_0('#skF_4', C_158))), inference(resolution, [status(thm)], [c_70, c_2157])).
% 8.91/3.23  tff(c_2173, plain, (k4_xboole_0('#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2167, c_140])).
% 8.91/3.23  tff(c_30, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.91/3.23  tff(c_26, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.91/3.23  tff(c_166, plain, (![A_75, B_76]: (k3_xboole_0(A_75, B_76)=A_75 | ~r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.91/3.23  tff(c_196, plain, (![A_79]: (k3_xboole_0(k1_xboole_0, A_79)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_166])).
% 8.91/3.23  tff(c_22, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.91/3.23  tff(c_233, plain, (![A_81]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_81))), inference(superposition, [status(thm), theory('equality')], [c_196, c_22])).
% 8.91/3.23  tff(c_20, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.91/3.23  tff(c_184, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k4_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.91/3.23  tff(c_193, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_20, c_184])).
% 8.91/3.23  tff(c_239, plain, (![A_81]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_81))), inference(superposition, [status(thm), theory('equality')], [c_233, c_193])).
% 8.91/3.23  tff(c_250, plain, (![A_81]: (k4_xboole_0(k1_xboole_0, A_81)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_239])).
% 8.91/3.23  tff(c_289, plain, (![A_83, B_84]: (k5_xboole_0(A_83, k4_xboole_0(B_84, A_83))=k2_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.91/3.23  tff(c_298, plain, (![A_81]: (k5_xboole_0(A_81, k1_xboole_0)=k2_xboole_0(A_81, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_250, c_289])).
% 8.91/3.23  tff(c_36, plain, (![B_22, A_21]: (k2_tarski(B_22, A_21)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.91/3.23  tff(c_141, plain, (![A_69, B_70]: (k1_setfam_1(k2_tarski(A_69, B_70))=k3_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.91/3.23  tff(c_424, plain, (![B_92, A_93]: (k1_setfam_1(k2_tarski(B_92, A_93))=k3_xboole_0(A_93, B_92))), inference(superposition, [status(thm), theory('equality')], [c_36, c_141])).
% 8.91/3.23  tff(c_52, plain, (![A_42, B_43]: (k1_setfam_1(k2_tarski(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.91/3.23  tff(c_447, plain, (![B_94, A_95]: (k3_xboole_0(B_94, A_95)=k3_xboole_0(A_95, B_94))), inference(superposition, [status(thm), theory('equality')], [c_424, c_52])).
% 8.91/3.23  tff(c_183, plain, (![A_13]: (k3_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_166])).
% 8.91/3.23  tff(c_500, plain, (![B_96]: (k3_xboole_0(B_96, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_447, c_183])).
% 8.91/3.23  tff(c_514, plain, (![B_96]: (k5_xboole_0(B_96, k1_xboole_0)=k4_xboole_0(B_96, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_500, c_22])).
% 8.91/3.23  tff(c_540, plain, (![B_96]: (k2_xboole_0(B_96, k1_xboole_0)=B_96)), inference(demodulation, [status(thm), theory('equality')], [c_298, c_30, c_514])).
% 8.91/3.23  tff(c_560, plain, (![A_81]: (k5_xboole_0(A_81, k1_xboole_0)=A_81)), inference(demodulation, [status(thm), theory('equality')], [c_540, c_298])).
% 8.91/3.23  tff(c_463, plain, (![B_94]: (k3_xboole_0(B_94, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_447, c_183])).
% 8.91/3.23  tff(c_603, plain, (![A_103, B_104]: (k4_xboole_0(A_103, k4_xboole_0(A_103, B_104))=k3_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.91/3.23  tff(c_644, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_603])).
% 8.91/3.23  tff(c_651, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_463, c_644])).
% 8.91/3.23  tff(c_654, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_651, c_193])).
% 8.91/3.23  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.91/3.23  tff(c_846, plain, (![A_118, B_119]: (k3_xboole_0(k4_xboole_0(A_118, B_119), A_118)=k4_xboole_0(A_118, B_119))), inference(resolution, [status(thm)], [c_28, c_166])).
% 8.91/3.23  tff(c_868, plain, (![A_118, B_119]: (k5_xboole_0(k4_xboole_0(A_118, B_119), k4_xboole_0(A_118, B_119))=k4_xboole_0(k4_xboole_0(A_118, B_119), A_118))), inference(superposition, [status(thm), theory('equality')], [c_846, c_22])).
% 8.91/3.23  tff(c_911, plain, (![A_120, B_121]: (k4_xboole_0(k4_xboole_0(A_120, B_121), A_120)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_654, c_868])).
% 8.91/3.23  tff(c_34, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k4_xboole_0(B_20, A_19))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.91/3.23  tff(c_931, plain, (![A_120, B_121]: (k2_xboole_0(A_120, k4_xboole_0(A_120, B_121))=k5_xboole_0(A_120, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_911, c_34])).
% 8.91/3.23  tff(c_967, plain, (![A_120, B_121]: (k2_xboole_0(A_120, k4_xboole_0(A_120, B_121))=A_120)), inference(demodulation, [status(thm), theory('equality')], [c_560, c_931])).
% 8.91/3.23  tff(c_2188, plain, (k2_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2173, c_967])).
% 8.91/3.23  tff(c_2507, plain, (![A_168, B_169, C_170]: (m1_subset_1(k7_subset_1(A_168, B_169, C_170), k1_zfmisc_1(A_168)) | ~m1_subset_1(B_169, k1_zfmisc_1(A_168)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.91/3.23  tff(c_2523, plain, (m1_subset_1(k2_tops_1('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_140, c_2507])).
% 8.91/3.23  tff(c_2531, plain, (m1_subset_1(k2_tops_1('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2523])).
% 8.91/3.23  tff(c_54, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~m1_subset_1(A_44, k1_zfmisc_1(B_45)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.91/3.23  tff(c_2545, plain, (r1_tarski(k2_tops_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_2531, c_54])).
% 8.91/3.23  tff(c_56, plain, (![A_44, B_45]: (m1_subset_1(A_44, k1_zfmisc_1(B_45)) | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.91/3.23  tff(c_3046, plain, (![A_185, B_186, C_187]: (k4_subset_1(A_185, B_186, C_187)=k2_xboole_0(B_186, C_187) | ~m1_subset_1(C_187, k1_zfmisc_1(A_185)) | ~m1_subset_1(B_186, k1_zfmisc_1(A_185)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.91/3.23  tff(c_11337, plain, (![B_323, B_324, A_325]: (k4_subset_1(B_323, B_324, A_325)=k2_xboole_0(B_324, A_325) | ~m1_subset_1(B_324, k1_zfmisc_1(B_323)) | ~r1_tarski(A_325, B_323))), inference(resolution, [status(thm)], [c_56, c_3046])).
% 8.91/3.23  tff(c_11394, plain, (![A_326]: (k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', A_326)=k2_xboole_0('#skF_4', A_326) | ~r1_tarski(A_326, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_70, c_11337])).
% 8.91/3.23  tff(c_11417, plain, (k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_2545, c_11394])).
% 8.91/3.23  tff(c_11455, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5019, c_2188, c_11417])).
% 8.91/3.23  tff(c_11457, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3307, c_11455])).
% 8.91/3.23  tff(c_11458, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k1_tops_1('#skF_3', '#skF_4'))!=k2_tops_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_76])).
% 8.91/3.23  tff(c_11637, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_11458])).
% 8.91/3.23  tff(c_11638, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_82])).
% 8.91/3.23  tff(c_11728, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k1_tops_1('#skF_3', '#skF_4'))!=k2_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11638, c_76])).
% 8.91/3.23  tff(c_14096, plain, (k4_xboole_0('#skF_4', k1_tops_1('#skF_3', '#skF_4'))!=k2_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14095, c_11728])).
% 8.91/3.23  tff(c_14260, plain, (![A_445, B_446]: (k2_pre_topc(A_445, B_446)=B_446 | ~v4_pre_topc(B_446, A_445) | ~m1_subset_1(B_446, k1_zfmisc_1(u1_struct_0(A_445))) | ~l1_pre_topc(A_445))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.91/3.23  tff(c_14281, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_70, c_14260])).
% 8.91/3.23  tff(c_14293, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_11638, c_14281])).
% 8.91/3.23  tff(c_16991, plain, (![A_516, B_517]: (k7_subset_1(u1_struct_0(A_516), k2_pre_topc(A_516, B_517), k1_tops_1(A_516, B_517))=k2_tops_1(A_516, B_517) | ~m1_subset_1(B_517, k1_zfmisc_1(u1_struct_0(A_516))) | ~l1_pre_topc(A_516))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.91/3.23  tff(c_17003, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14293, c_16991])).
% 8.91/3.23  tff(c_17007, plain, (k4_xboole_0('#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_14095, c_17003])).
% 8.91/3.23  tff(c_17009, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14096, c_17007])).
% 8.91/3.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.91/3.23  
% 8.91/3.23  Inference rules
% 8.91/3.23  ----------------------
% 8.91/3.23  #Ref     : 0
% 8.91/3.23  #Sup     : 4134
% 8.91/3.23  #Fact    : 0
% 8.91/3.23  #Define  : 0
% 8.91/3.23  #Split   : 4
% 8.91/3.23  #Chain   : 0
% 8.91/3.23  #Close   : 0
% 8.91/3.23  
% 8.91/3.23  Ordering : KBO
% 8.91/3.23  
% 8.91/3.23  Simplification rules
% 8.91/3.23  ----------------------
% 8.91/3.23  #Subsume      : 214
% 8.91/3.23  #Demod        : 4354
% 8.91/3.23  #Tautology    : 2823
% 8.91/3.23  #SimpNegUnit  : 6
% 8.91/3.23  #BackRed      : 7
% 8.91/3.23  
% 8.91/3.23  #Partial instantiations: 0
% 8.91/3.23  #Strategies tried      : 1
% 8.91/3.23  
% 8.91/3.23  Timing (in seconds)
% 8.91/3.23  ----------------------
% 8.91/3.23  Preprocessing        : 0.36
% 8.91/3.23  Parsing              : 0.19
% 8.91/3.23  CNF conversion       : 0.03
% 8.91/3.23  Main loop            : 2.09
% 8.91/3.23  Inferencing          : 0.54
% 8.91/3.24  Reduction            : 1.01
% 8.91/3.24  Demodulation         : 0.84
% 8.91/3.24  BG Simplification    : 0.06
% 8.91/3.24  Subsumption          : 0.35
% 8.91/3.24  Abstraction          : 0.09
% 8.91/3.24  MUC search           : 0.00
% 8.91/3.24  Cooper               : 0.00
% 8.91/3.24  Total                : 2.49
% 8.91/3.24  Index Insertion      : 0.00
% 8.91/3.24  Index Deletion       : 0.00
% 8.91/3.24  Index Matching       : 0.00
% 8.91/3.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
