%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:17 EST 2020

% Result     : Theorem 23.44s
% Output     : CNFRefutation 23.44s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 185 expanded)
%              Number of leaves         :   42 (  80 expanded)
%              Depth                    :   10
%              Number of atoms          :  140 ( 326 expanded)
%              Number of equality atoms :   65 ( 117 expanded)
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

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_55,axiom,(
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

tff(f_51,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_43,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_37,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_35,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_36500,plain,(
    ! [A_331,B_332,C_333] :
      ( k7_subset_1(A_331,B_332,C_333) = k4_xboole_0(B_332,C_333)
      | ~ m1_subset_1(B_332,k1_zfmisc_1(A_331)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_36509,plain,(
    ! [C_333] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_333) = k4_xboole_0('#skF_2',C_333) ),
    inference(resolution,[status(thm)],[c_40,c_36500])).

tff(c_46,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_131,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3020,plain,(
    ! [B_118,A_119] :
      ( v4_pre_topc(B_118,A_119)
      | k2_pre_topc(A_119,B_118) != B_118
      | ~ v2_pre_topc(A_119)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3034,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_3020])).

tff(c_3040,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_3034])).

tff(c_3041,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_3040])).

tff(c_468,plain,(
    ! [A_76,B_77,C_78] :
      ( k7_subset_1(A_76,B_77,C_78) = k4_xboole_0(B_77,C_78)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_478,plain,(
    ! [C_79] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_79) = k4_xboole_0('#skF_2',C_79) ),
    inference(resolution,[status(thm)],[c_40,c_468])).

tff(c_52,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_274,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_52])).

tff(c_484,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_478,c_274])).

tff(c_20,plain,(
    ! [A_20,B_21] : k6_subset_1(A_20,B_21) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [A_15,B_16] : m1_subset_1(k6_subset_1(A_15,B_16),k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_53,plain,(
    ! [A_15,B_16] : m1_subset_1(k4_xboole_0(A_15,B_16),k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k3_subset_1(A_13,B_14),k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2973,plain,(
    ! [A_114,B_115,C_116] :
      ( k4_subset_1(A_114,B_115,C_116) = k2_xboole_0(B_115,C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(A_114))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(A_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_19811,plain,(
    ! [A_234,B_235,B_236] :
      ( k4_subset_1(A_234,B_235,k3_subset_1(A_234,B_236)) = k2_xboole_0(B_235,k3_subset_1(A_234,B_236))
      | ~ m1_subset_1(B_235,k1_zfmisc_1(A_234))
      | ~ m1_subset_1(B_236,k1_zfmisc_1(A_234)) ) ),
    inference(resolution,[status(thm)],[c_14,c_2973])).

tff(c_34668,plain,(
    ! [A_291,B_292,B_293] :
      ( k4_subset_1(A_291,k4_xboole_0(A_291,B_292),k3_subset_1(A_291,B_293)) = k2_xboole_0(k4_xboole_0(A_291,B_292),k3_subset_1(A_291,B_293))
      | ~ m1_subset_1(B_293,k1_zfmisc_1(A_291)) ) ),
    inference(resolution,[status(thm)],[c_53,c_19811])).

tff(c_12,plain,(
    ! [A_12] : k2_subset_1(A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ! [A_25,B_26] :
      ( k4_subset_1(A_25,B_26,k3_subset_1(A_25,B_26)) = k2_subset_1(A_25)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_505,plain,(
    ! [A_80,B_81] :
      ( k4_subset_1(A_80,B_81,k3_subset_1(A_80,B_81)) = A_80
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_80)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_24])).

tff(c_516,plain,(
    ! [A_15,B_16] : k4_subset_1(A_15,k4_xboole_0(A_15,B_16),k3_subset_1(A_15,k4_xboole_0(A_15,B_16))) = A_15 ),
    inference(resolution,[status(thm)],[c_53,c_505])).

tff(c_34675,plain,(
    ! [A_291,B_292] :
      ( k2_xboole_0(k4_xboole_0(A_291,B_292),k3_subset_1(A_291,k4_xboole_0(A_291,B_292))) = A_291
      | ~ m1_subset_1(k4_xboole_0(A_291,B_292),k1_zfmisc_1(A_291)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34668,c_516])).

tff(c_34687,plain,(
    ! [A_291,B_292] : k2_xboole_0(k4_xboole_0(A_291,B_292),k3_subset_1(A_291,k4_xboole_0(A_291,B_292))) = A_291 ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_34675])).

tff(c_8,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_132,plain,(
    ! [A_53,B_54] : k3_tarski(k2_tarski(A_53,B_54)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_218,plain,(
    ! [B_61,A_62] : k3_tarski(k2_tarski(B_61,A_62)) = k2_xboole_0(A_62,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_132])).

tff(c_10,plain,(
    ! [A_10,B_11] : k3_tarski(k2_tarski(A_10,B_11)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_224,plain,(
    ! [B_61,A_62] : k2_xboole_0(B_61,A_62) = k2_xboole_0(A_62,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_10])).

tff(c_34692,plain,(
    ! [A_294,B_295] : k2_xboole_0(k4_xboole_0(A_294,B_295),k3_subset_1(A_294,k4_xboole_0(A_294,B_295))) = A_294 ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_34675])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_310,plain,(
    ! [A_69,B_70,C_71] : k2_xboole_0(k2_xboole_0(A_69,B_70),C_71) = k2_xboole_0(A_69,k2_xboole_0(B_70,C_71)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_349,plain,(
    ! [A_1,C_71] : k2_xboole_0(A_1,k2_xboole_0(A_1,C_71)) = k2_xboole_0(A_1,C_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_310])).

tff(c_34866,plain,(
    ! [A_294,B_295] : k2_xboole_0(k4_xboole_0(A_294,B_295),k3_subset_1(A_294,k4_xboole_0(A_294,B_295))) = k2_xboole_0(k4_xboole_0(A_294,B_295),A_294) ),
    inference(superposition,[status(thm),theory(equality)],[c_34692,c_349])).

tff(c_34923,plain,(
    ! [A_296,B_297] : k2_xboole_0(A_296,k4_xboole_0(A_296,B_297)) = A_296 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34687,c_224,c_34866])).

tff(c_35182,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_484,c_34923])).

tff(c_3368,plain,(
    ! [A_124,B_125] :
      ( k4_subset_1(u1_struct_0(A_124),B_125,k2_tops_1(A_124,B_125)) = k2_pre_topc(A_124,B_125)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3378,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_3368])).

tff(c_3384,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3378])).

tff(c_32,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(k2_tops_1(A_32,B_33),k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28716,plain,(
    ! [A_268,B_269,B_270] :
      ( k4_subset_1(u1_struct_0(A_268),B_269,k2_tops_1(A_268,B_270)) = k2_xboole_0(B_269,k2_tops_1(A_268,B_270))
      | ~ m1_subset_1(B_269,k1_zfmisc_1(u1_struct_0(A_268)))
      | ~ m1_subset_1(B_270,k1_zfmisc_1(u1_struct_0(A_268)))
      | ~ l1_pre_topc(A_268) ) ),
    inference(resolution,[status(thm)],[c_32,c_2973])).

tff(c_28726,plain,(
    ! [B_270] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_270)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_270))
      | ~ m1_subset_1(B_270,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_28716])).

tff(c_28736,plain,(
    ! [B_271] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_271)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_271))
      | ~ m1_subset_1(B_271,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_28726])).

tff(c_28751,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_28736])).

tff(c_28758,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3384,c_28751])).

tff(c_35680,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35182,c_28758])).

tff(c_35682,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3041,c_35680])).

tff(c_35683,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_36510,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36509,c_35683])).

tff(c_35684,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_36662,plain,(
    ! [A_337,B_338] :
      ( k2_pre_topc(A_337,B_338) = B_338
      | ~ v4_pre_topc(B_338,A_337)
      | ~ m1_subset_1(B_338,k1_zfmisc_1(u1_struct_0(A_337)))
      | ~ l1_pre_topc(A_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36673,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_36662])).

tff(c_36678,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_35684,c_36673])).

tff(c_39549,plain,(
    ! [A_376,B_377] :
      ( k7_subset_1(u1_struct_0(A_376),k2_pre_topc(A_376,B_377),k1_tops_1(A_376,B_377)) = k2_tops_1(A_376,B_377)
      | ~ m1_subset_1(B_377,k1_zfmisc_1(u1_struct_0(A_376)))
      | ~ l1_pre_topc(A_376) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_39558,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_36678,c_39549])).

tff(c_39562,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36509,c_39558])).

tff(c_39564,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36510,c_39562])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n020.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 15:37:52 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.44/14.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.44/14.71  
% 23.44/14.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.44/14.72  %$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 23.44/14.72  
% 23.44/14.72  %Foreground sorts:
% 23.44/14.72  
% 23.44/14.72  
% 23.44/14.72  %Background operators:
% 23.44/14.72  
% 23.44/14.72  
% 23.44/14.72  %Foreground operators:
% 23.44/14.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.44/14.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 23.44/14.72  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 23.44/14.72  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 23.44/14.72  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 23.44/14.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 23.44/14.72  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 23.44/14.72  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 23.44/14.72  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 23.44/14.72  tff('#skF_2', type, '#skF_2': $i).
% 23.44/14.72  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 23.44/14.72  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 23.44/14.72  tff('#skF_1', type, '#skF_1': $i).
% 23.44/14.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 23.44/14.72  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 23.44/14.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.44/14.72  tff(k3_tarski, type, k3_tarski: $i > $i).
% 23.44/14.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.44/14.72  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 23.44/14.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 23.44/14.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 23.44/14.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 23.44/14.72  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 23.44/14.72  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 23.44/14.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 23.44/14.72  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 23.44/14.72  
% 23.44/14.73  tff(f_116, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 23.44/14.73  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 23.44/14.73  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 23.44/14.73  tff(f_51, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 23.44/14.73  tff(f_43, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 23.44/14.73  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 23.44/14.73  tff(f_49, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 23.44/14.73  tff(f_37, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 23.44/14.73  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 23.44/14.73  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 23.44/14.73  tff(f_35, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 23.44/14.73  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 23.44/14.73  tff(f_31, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 23.44/14.73  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 23.44/14.73  tff(f_82, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 23.44/14.73  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 23.44/14.73  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 23.44/14.73  tff(c_36500, plain, (![A_331, B_332, C_333]: (k7_subset_1(A_331, B_332, C_333)=k4_xboole_0(B_332, C_333) | ~m1_subset_1(B_332, k1_zfmisc_1(A_331)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 23.44/14.73  tff(c_36509, plain, (![C_333]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_333)=k4_xboole_0('#skF_2', C_333))), inference(resolution, [status(thm)], [c_40, c_36500])).
% 23.44/14.73  tff(c_46, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 23.44/14.73  tff(c_131, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 23.44/14.73  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 23.44/14.73  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 23.44/14.73  tff(c_3020, plain, (![B_118, A_119]: (v4_pre_topc(B_118, A_119) | k2_pre_topc(A_119, B_118)!=B_118 | ~v2_pre_topc(A_119) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_76])).
% 23.44/14.73  tff(c_3034, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_3020])).
% 23.44/14.73  tff(c_3040, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_3034])).
% 23.44/14.73  tff(c_3041, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_131, c_3040])).
% 23.44/14.73  tff(c_468, plain, (![A_76, B_77, C_78]: (k7_subset_1(A_76, B_77, C_78)=k4_xboole_0(B_77, C_78) | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 23.44/14.73  tff(c_478, plain, (![C_79]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_79)=k4_xboole_0('#skF_2', C_79))), inference(resolution, [status(thm)], [c_40, c_468])).
% 23.44/14.73  tff(c_52, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 23.44/14.73  tff(c_274, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_131, c_52])).
% 23.44/14.73  tff(c_484, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_478, c_274])).
% 23.44/14.73  tff(c_20, plain, (![A_20, B_21]: (k6_subset_1(A_20, B_21)=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_51])).
% 23.44/14.73  tff(c_16, plain, (![A_15, B_16]: (m1_subset_1(k6_subset_1(A_15, B_16), k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 23.44/14.73  tff(c_53, plain, (![A_15, B_16]: (m1_subset_1(k4_xboole_0(A_15, B_16), k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16])).
% 23.44/14.73  tff(c_14, plain, (![A_13, B_14]: (m1_subset_1(k3_subset_1(A_13, B_14), k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 23.44/14.73  tff(c_2973, plain, (![A_114, B_115, C_116]: (k4_subset_1(A_114, B_115, C_116)=k2_xboole_0(B_115, C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(A_114)) | ~m1_subset_1(B_115, k1_zfmisc_1(A_114)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 23.44/14.73  tff(c_19811, plain, (![A_234, B_235, B_236]: (k4_subset_1(A_234, B_235, k3_subset_1(A_234, B_236))=k2_xboole_0(B_235, k3_subset_1(A_234, B_236)) | ~m1_subset_1(B_235, k1_zfmisc_1(A_234)) | ~m1_subset_1(B_236, k1_zfmisc_1(A_234)))), inference(resolution, [status(thm)], [c_14, c_2973])).
% 23.44/14.73  tff(c_34668, plain, (![A_291, B_292, B_293]: (k4_subset_1(A_291, k4_xboole_0(A_291, B_292), k3_subset_1(A_291, B_293))=k2_xboole_0(k4_xboole_0(A_291, B_292), k3_subset_1(A_291, B_293)) | ~m1_subset_1(B_293, k1_zfmisc_1(A_291)))), inference(resolution, [status(thm)], [c_53, c_19811])).
% 23.44/14.73  tff(c_12, plain, (![A_12]: (k2_subset_1(A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_37])).
% 23.44/14.73  tff(c_24, plain, (![A_25, B_26]: (k4_subset_1(A_25, B_26, k3_subset_1(A_25, B_26))=k2_subset_1(A_25) | ~m1_subset_1(B_26, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 23.44/14.73  tff(c_505, plain, (![A_80, B_81]: (k4_subset_1(A_80, B_81, k3_subset_1(A_80, B_81))=A_80 | ~m1_subset_1(B_81, k1_zfmisc_1(A_80)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_24])).
% 23.44/14.73  tff(c_516, plain, (![A_15, B_16]: (k4_subset_1(A_15, k4_xboole_0(A_15, B_16), k3_subset_1(A_15, k4_xboole_0(A_15, B_16)))=A_15)), inference(resolution, [status(thm)], [c_53, c_505])).
% 23.44/14.73  tff(c_34675, plain, (![A_291, B_292]: (k2_xboole_0(k4_xboole_0(A_291, B_292), k3_subset_1(A_291, k4_xboole_0(A_291, B_292)))=A_291 | ~m1_subset_1(k4_xboole_0(A_291, B_292), k1_zfmisc_1(A_291)))), inference(superposition, [status(thm), theory('equality')], [c_34668, c_516])).
% 23.44/14.73  tff(c_34687, plain, (![A_291, B_292]: (k2_xboole_0(k4_xboole_0(A_291, B_292), k3_subset_1(A_291, k4_xboole_0(A_291, B_292)))=A_291)), inference(demodulation, [status(thm), theory('equality')], [c_53, c_34675])).
% 23.44/14.73  tff(c_8, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 23.44/14.73  tff(c_132, plain, (![A_53, B_54]: (k3_tarski(k2_tarski(A_53, B_54))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_35])).
% 23.44/14.73  tff(c_218, plain, (![B_61, A_62]: (k3_tarski(k2_tarski(B_61, A_62))=k2_xboole_0(A_62, B_61))), inference(superposition, [status(thm), theory('equality')], [c_8, c_132])).
% 23.44/14.73  tff(c_10, plain, (![A_10, B_11]: (k3_tarski(k2_tarski(A_10, B_11))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 23.44/14.73  tff(c_224, plain, (![B_61, A_62]: (k2_xboole_0(B_61, A_62)=k2_xboole_0(A_62, B_61))), inference(superposition, [status(thm), theory('equality')], [c_218, c_10])).
% 23.44/14.73  tff(c_34692, plain, (![A_294, B_295]: (k2_xboole_0(k4_xboole_0(A_294, B_295), k3_subset_1(A_294, k4_xboole_0(A_294, B_295)))=A_294)), inference(demodulation, [status(thm), theory('equality')], [c_53, c_34675])).
% 23.44/14.73  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 23.44/14.73  tff(c_310, plain, (![A_69, B_70, C_71]: (k2_xboole_0(k2_xboole_0(A_69, B_70), C_71)=k2_xboole_0(A_69, k2_xboole_0(B_70, C_71)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 23.44/14.73  tff(c_349, plain, (![A_1, C_71]: (k2_xboole_0(A_1, k2_xboole_0(A_1, C_71))=k2_xboole_0(A_1, C_71))), inference(superposition, [status(thm), theory('equality')], [c_2, c_310])).
% 23.44/14.73  tff(c_34866, plain, (![A_294, B_295]: (k2_xboole_0(k4_xboole_0(A_294, B_295), k3_subset_1(A_294, k4_xboole_0(A_294, B_295)))=k2_xboole_0(k4_xboole_0(A_294, B_295), A_294))), inference(superposition, [status(thm), theory('equality')], [c_34692, c_349])).
% 23.44/14.73  tff(c_34923, plain, (![A_296, B_297]: (k2_xboole_0(A_296, k4_xboole_0(A_296, B_297))=A_296)), inference(demodulation, [status(thm), theory('equality')], [c_34687, c_224, c_34866])).
% 23.44/14.73  tff(c_35182, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_484, c_34923])).
% 23.44/14.73  tff(c_3368, plain, (![A_124, B_125]: (k4_subset_1(u1_struct_0(A_124), B_125, k2_tops_1(A_124, B_125))=k2_pre_topc(A_124, B_125) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_104])).
% 23.44/14.73  tff(c_3378, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_3368])).
% 23.44/14.73  tff(c_3384, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3378])).
% 23.44/14.73  tff(c_32, plain, (![A_32, B_33]: (m1_subset_1(k2_tops_1(A_32, B_33), k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_82])).
% 23.44/14.73  tff(c_28716, plain, (![A_268, B_269, B_270]: (k4_subset_1(u1_struct_0(A_268), B_269, k2_tops_1(A_268, B_270))=k2_xboole_0(B_269, k2_tops_1(A_268, B_270)) | ~m1_subset_1(B_269, k1_zfmisc_1(u1_struct_0(A_268))) | ~m1_subset_1(B_270, k1_zfmisc_1(u1_struct_0(A_268))) | ~l1_pre_topc(A_268))), inference(resolution, [status(thm)], [c_32, c_2973])).
% 23.44/14.73  tff(c_28726, plain, (![B_270]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_270))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_270)) | ~m1_subset_1(B_270, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_28716])).
% 23.44/14.73  tff(c_28736, plain, (![B_271]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_271))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_271)) | ~m1_subset_1(B_271, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_28726])).
% 23.44/14.73  tff(c_28751, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_28736])).
% 23.44/14.73  tff(c_28758, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3384, c_28751])).
% 23.44/14.73  tff(c_35680, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_35182, c_28758])).
% 23.44/14.73  tff(c_35682, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3041, c_35680])).
% 23.44/14.73  tff(c_35683, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 23.44/14.73  tff(c_36510, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36509, c_35683])).
% 23.44/14.73  tff(c_35684, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 23.44/14.73  tff(c_36662, plain, (![A_337, B_338]: (k2_pre_topc(A_337, B_338)=B_338 | ~v4_pre_topc(B_338, A_337) | ~m1_subset_1(B_338, k1_zfmisc_1(u1_struct_0(A_337))) | ~l1_pre_topc(A_337))), inference(cnfTransformation, [status(thm)], [f_76])).
% 23.44/14.73  tff(c_36673, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_36662])).
% 23.44/14.73  tff(c_36678, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_35684, c_36673])).
% 23.44/14.73  tff(c_39549, plain, (![A_376, B_377]: (k7_subset_1(u1_struct_0(A_376), k2_pre_topc(A_376, B_377), k1_tops_1(A_376, B_377))=k2_tops_1(A_376, B_377) | ~m1_subset_1(B_377, k1_zfmisc_1(u1_struct_0(A_376))) | ~l1_pre_topc(A_376))), inference(cnfTransformation, [status(thm)], [f_97])).
% 23.44/14.73  tff(c_39558, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_36678, c_39549])).
% 23.44/14.73  tff(c_39562, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36509, c_39558])).
% 23.44/14.73  tff(c_39564, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36510, c_39562])).
% 23.44/14.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.44/14.73  
% 23.44/14.73  Inference rules
% 23.44/14.73  ----------------------
% 23.44/14.73  #Ref     : 0
% 23.44/14.73  #Sup     : 9699
% 23.44/14.73  #Fact    : 0
% 23.44/14.73  #Define  : 0
% 23.44/14.73  #Split   : 2
% 23.44/14.73  #Chain   : 0
% 23.44/14.73  #Close   : 0
% 23.44/14.73  
% 23.44/14.73  Ordering : KBO
% 23.44/14.73  
% 23.44/14.73  Simplification rules
% 23.44/14.73  ----------------------
% 23.44/14.73  #Subsume      : 1557
% 23.44/14.73  #Demod        : 19262
% 23.44/14.73  #Tautology    : 2901
% 23.44/14.73  #SimpNegUnit  : 4
% 23.44/14.73  #BackRed      : 3
% 23.44/14.73  
% 23.44/14.73  #Partial instantiations: 0
% 23.44/14.73  #Strategies tried      : 1
% 23.44/14.73  
% 23.44/14.73  Timing (in seconds)
% 23.44/14.73  ----------------------
% 23.44/14.74  Preprocessing        : 0.33
% 23.44/14.74  Parsing              : 0.18
% 23.44/14.74  CNF conversion       : 0.02
% 23.44/14.74  Main loop            : 13.59
% 23.44/14.74  Inferencing          : 1.13
% 23.44/14.74  Reduction            : 11.09
% 23.44/14.74  Demodulation         : 10.72
% 23.44/14.74  BG Simplification    : 0.19
% 23.44/14.74  Subsumption          : 0.94
% 23.44/14.74  Abstraction          : 0.40
% 23.44/14.74  MUC search           : 0.00
% 23.44/14.74  Cooper               : 0.00
% 23.44/14.74  Total                : 13.95
% 23.44/14.74  Index Insertion      : 0.00
% 23.44/14.74  Index Deletion       : 0.00
% 23.44/14.74  Index Matching       : 0.00
% 23.44/14.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
