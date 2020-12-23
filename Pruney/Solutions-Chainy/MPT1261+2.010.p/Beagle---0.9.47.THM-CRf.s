%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:12 EST 2020

% Result     : Theorem 8.71s
% Output     : CNFRefutation 8.71s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 185 expanded)
%              Number of leaves         :   43 (  79 expanded)
%              Depth                    :   12
%              Number of atoms          :  150 ( 305 expanded)
%              Number of equality atoms :   76 ( 129 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_131,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_90,axiom,(
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

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_71,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_119,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_13616,plain,(
    ! [A_360,B_361,C_362] :
      ( k7_subset_1(A_360,B_361,C_362) = k4_xboole_0(B_361,C_362)
      | ~ m1_subset_1(B_361,k1_zfmisc_1(A_360)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_13622,plain,(
    ! [C_362] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_362) = k4_xboole_0('#skF_2',C_362) ),
    inference(resolution,[status(thm)],[c_52,c_13616])).

tff(c_58,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_124,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_56,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2753,plain,(
    ! [B_145,A_146] :
      ( v4_pre_topc(B_145,A_146)
      | k2_pre_topc(A_146,B_145) != B_145
      | ~ v2_pre_topc(A_146)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2763,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_2753])).

tff(c_2768,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_2763])).

tff(c_2769,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_2768])).

tff(c_3343,plain,(
    ! [A_152,B_153] :
      ( k4_subset_1(u1_struct_0(A_152),B_153,k2_tops_1(A_152,B_153)) = k2_pre_topc(A_152,B_153)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_pre_topc(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3350,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_3343])).

tff(c_3355,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3350])).

tff(c_1172,plain,(
    ! [A_109,B_110,C_111] :
      ( k7_subset_1(A_109,B_110,C_111) = k4_xboole_0(B_110,C_111)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1186,plain,(
    ! [C_112] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_112) = k4_xboole_0('#skF_2',C_112) ),
    inference(resolution,[status(thm)],[c_52,c_1172])).

tff(c_64,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_212,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_64])).

tff(c_1192,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1186,c_212])).

tff(c_18,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [B_18,A_17] : k2_tarski(B_18,A_17) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_174,plain,(
    ! [A_63,B_64] : k1_setfam_1(k2_tarski(A_63,B_64)) = k3_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_189,plain,(
    ! [B_65,A_66] : k1_setfam_1(k2_tarski(B_65,A_66)) = k3_xboole_0(A_66,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_174])).

tff(c_34,plain,(
    ! [A_29,B_30] : k1_setfam_1(k2_tarski(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_217,plain,(
    ! [B_67,A_68] : k3_xboole_0(B_67,A_68) = k3_xboole_0(A_68,B_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_34])).

tff(c_14,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_125,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_138,plain,(
    ! [A_9] : k3_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_125])).

tff(c_233,plain,(
    ! [B_67] : k3_xboole_0(B_67,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_138])).

tff(c_310,plain,(
    ! [A_70,B_71] : k5_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k4_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_319,plain,(
    ! [B_67] : k5_xboole_0(B_67,k1_xboole_0) = k4_xboole_0(B_67,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_310])).

tff(c_337,plain,(
    ! [B_67] : k5_xboole_0(B_67,k1_xboole_0) = B_67 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_319])).

tff(c_515,plain,(
    ! [A_82,B_83] : k4_xboole_0(A_82,k4_xboole_0(A_82,B_83)) = k3_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_550,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_515])).

tff(c_557,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_550])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_334,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_310])).

tff(c_560,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_334])).

tff(c_16,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_752,plain,(
    ! [A_93,B_94] : k3_xboole_0(k4_xboole_0(A_93,B_94),A_93) = k4_xboole_0(A_93,B_94) ),
    inference(resolution,[status(thm)],[c_16,c_125])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_764,plain,(
    ! [A_93,B_94] : k5_xboole_0(k4_xboole_0(A_93,B_94),k4_xboole_0(A_93,B_94)) = k4_xboole_0(k4_xboole_0(A_93,B_94),A_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_752,c_10])).

tff(c_817,plain,(
    ! [A_95,B_96] : k4_xboole_0(k4_xboole_0(A_95,B_96),A_95) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_764])).

tff(c_22,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_831,plain,(
    ! [A_95,B_96] : k2_xboole_0(A_95,k4_xboole_0(A_95,B_96)) = k5_xboole_0(A_95,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_817,c_22])).

tff(c_867,plain,(
    ! [A_95,B_96] : k2_xboole_0(A_95,k4_xboole_0(A_95,B_96)) = A_95 ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_831])).

tff(c_1231,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1192,c_867])).

tff(c_44,plain,(
    ! [A_36,B_37] :
      ( m1_subset_1(k2_tops_1(A_36,B_37),k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2252,plain,(
    ! [A_133,B_134,C_135] :
      ( k4_subset_1(A_133,B_134,C_135) = k2_xboole_0(B_134,C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(A_133))
      | ~ m1_subset_1(B_134,k1_zfmisc_1(A_133)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12041,plain,(
    ! [A_293,B_294,B_295] :
      ( k4_subset_1(u1_struct_0(A_293),B_294,k2_tops_1(A_293,B_295)) = k2_xboole_0(B_294,k2_tops_1(A_293,B_295))
      | ~ m1_subset_1(B_294,k1_zfmisc_1(u1_struct_0(A_293)))
      | ~ m1_subset_1(B_295,k1_zfmisc_1(u1_struct_0(A_293)))
      | ~ l1_pre_topc(A_293) ) ),
    inference(resolution,[status(thm)],[c_44,c_2252])).

tff(c_12048,plain,(
    ! [B_295] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_295)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_295))
      | ~ m1_subset_1(B_295,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_52,c_12041])).

tff(c_12057,plain,(
    ! [B_296] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_296)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_296))
      | ~ m1_subset_1(B_296,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_12048])).

tff(c_12068,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_12057])).

tff(c_12074,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3355,c_1231,c_12068])).

tff(c_12076,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2769,c_12074])).

tff(c_12077,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_13623,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13622,c_12077])).

tff(c_12128,plain,(
    ! [A_304,B_305] : k1_setfam_1(k2_tarski(A_304,B_305)) = k3_xboole_0(A_304,B_305) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12143,plain,(
    ! [B_306,A_307] : k1_setfam_1(k2_tarski(B_306,A_307)) = k3_xboole_0(A_307,B_306) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_12128])).

tff(c_12149,plain,(
    ! [B_306,A_307] : k3_xboole_0(B_306,A_307) = k3_xboole_0(A_307,B_306) ),
    inference(superposition,[status(thm),theory(equality)],[c_12143,c_34])).

tff(c_12078,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_14613,plain,(
    ! [A_384,B_385] :
      ( r1_tarski(k2_tops_1(A_384,B_385),B_385)
      | ~ v4_pre_topc(B_385,A_384)
      | ~ m1_subset_1(B_385,k1_zfmisc_1(u1_struct_0(A_384)))
      | ~ l1_pre_topc(A_384) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_14620,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_14613])).

tff(c_14625,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_12078,c_14620])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14632,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_14625,c_12])).

tff(c_14694,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12149,c_14632])).

tff(c_15250,plain,(
    ! [A_395,B_396] :
      ( k7_subset_1(u1_struct_0(A_395),B_396,k2_tops_1(A_395,B_396)) = k1_tops_1(A_395,B_396)
      | ~ m1_subset_1(B_396,k1_zfmisc_1(u1_struct_0(A_395)))
      | ~ l1_pre_topc(A_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_15257,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_15250])).

tff(c_15262,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_13622,c_15257])).

tff(c_20,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_15281,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15262,c_20])).

tff(c_15293,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14694,c_15281])).

tff(c_15295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13623,c_15293])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:57:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.71/3.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.71/3.11  
% 8.71/3.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.71/3.12  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.71/3.12  
% 8.71/3.12  %Foreground sorts:
% 8.71/3.12  
% 8.71/3.12  
% 8.71/3.12  %Background operators:
% 8.71/3.12  
% 8.71/3.12  
% 8.71/3.12  %Foreground operators:
% 8.71/3.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.71/3.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.71/3.12  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 8.71/3.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.71/3.12  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.71/3.12  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.71/3.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.71/3.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.71/3.12  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.71/3.12  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.71/3.12  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.71/3.12  tff('#skF_2', type, '#skF_2': $i).
% 8.71/3.12  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 8.71/3.12  tff('#skF_1', type, '#skF_1': $i).
% 8.71/3.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.71/3.12  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.71/3.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.71/3.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.71/3.12  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.71/3.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.71/3.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.71/3.12  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.71/3.12  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.71/3.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.71/3.12  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.71/3.12  
% 8.71/3.13  tff(f_131, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 8.71/3.13  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 8.71/3.13  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 8.71/3.13  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 8.71/3.13  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 8.71/3.13  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.71/3.13  tff(f_71, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 8.71/3.13  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.71/3.13  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.71/3.13  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.71/3.13  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.71/3.13  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.71/3.13  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.71/3.13  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.71/3.13  tff(f_96, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 8.71/3.13  tff(f_65, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 8.71/3.13  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 8.71/3.13  tff(f_119, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 8.71/3.13  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.71/3.13  tff(c_13616, plain, (![A_360, B_361, C_362]: (k7_subset_1(A_360, B_361, C_362)=k4_xboole_0(B_361, C_362) | ~m1_subset_1(B_361, k1_zfmisc_1(A_360)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.71/3.13  tff(c_13622, plain, (![C_362]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_362)=k4_xboole_0('#skF_2', C_362))), inference(resolution, [status(thm)], [c_52, c_13616])).
% 8.71/3.13  tff(c_58, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.71/3.13  tff(c_124, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_58])).
% 8.71/3.13  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.71/3.13  tff(c_56, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.71/3.13  tff(c_2753, plain, (![B_145, A_146]: (v4_pre_topc(B_145, A_146) | k2_pre_topc(A_146, B_145)!=B_145 | ~v2_pre_topc(A_146) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_pre_topc(A_146))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.71/3.13  tff(c_2763, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_2753])).
% 8.71/3.13  tff(c_2768, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_2763])).
% 8.71/3.13  tff(c_2769, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_124, c_2768])).
% 8.71/3.13  tff(c_3343, plain, (![A_152, B_153]: (k4_subset_1(u1_struct_0(A_152), B_153, k2_tops_1(A_152, B_153))=k2_pre_topc(A_152, B_153) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_pre_topc(A_152))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.71/3.13  tff(c_3350, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_3343])).
% 8.71/3.13  tff(c_3355, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3350])).
% 8.71/3.13  tff(c_1172, plain, (![A_109, B_110, C_111]: (k7_subset_1(A_109, B_110, C_111)=k4_xboole_0(B_110, C_111) | ~m1_subset_1(B_110, k1_zfmisc_1(A_109)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.71/3.13  tff(c_1186, plain, (![C_112]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_112)=k4_xboole_0('#skF_2', C_112))), inference(resolution, [status(thm)], [c_52, c_1172])).
% 8.71/3.13  tff(c_64, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.71/3.13  tff(c_212, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_124, c_64])).
% 8.71/3.13  tff(c_1192, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1186, c_212])).
% 8.71/3.13  tff(c_18, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.71/3.13  tff(c_24, plain, (![B_18, A_17]: (k2_tarski(B_18, A_17)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.71/3.13  tff(c_174, plain, (![A_63, B_64]: (k1_setfam_1(k2_tarski(A_63, B_64))=k3_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.71/3.13  tff(c_189, plain, (![B_65, A_66]: (k1_setfam_1(k2_tarski(B_65, A_66))=k3_xboole_0(A_66, B_65))), inference(superposition, [status(thm), theory('equality')], [c_24, c_174])).
% 8.71/3.13  tff(c_34, plain, (![A_29, B_30]: (k1_setfam_1(k2_tarski(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.71/3.13  tff(c_217, plain, (![B_67, A_68]: (k3_xboole_0(B_67, A_68)=k3_xboole_0(A_68, B_67))), inference(superposition, [status(thm), theory('equality')], [c_189, c_34])).
% 8.71/3.13  tff(c_14, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.71/3.13  tff(c_125, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=A_56 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.71/3.13  tff(c_138, plain, (![A_9]: (k3_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_125])).
% 8.71/3.13  tff(c_233, plain, (![B_67]: (k3_xboole_0(B_67, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_217, c_138])).
% 8.71/3.13  tff(c_310, plain, (![A_70, B_71]: (k5_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k4_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.71/3.13  tff(c_319, plain, (![B_67]: (k5_xboole_0(B_67, k1_xboole_0)=k4_xboole_0(B_67, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_233, c_310])).
% 8.71/3.13  tff(c_337, plain, (![B_67]: (k5_xboole_0(B_67, k1_xboole_0)=B_67)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_319])).
% 8.71/3.13  tff(c_515, plain, (![A_82, B_83]: (k4_xboole_0(A_82, k4_xboole_0(A_82, B_83))=k3_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.71/3.13  tff(c_550, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_515])).
% 8.71/3.13  tff(c_557, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_233, c_550])).
% 8.71/3.13  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.71/3.13  tff(c_334, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_310])).
% 8.71/3.13  tff(c_560, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_557, c_334])).
% 8.71/3.13  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.71/3.13  tff(c_752, plain, (![A_93, B_94]: (k3_xboole_0(k4_xboole_0(A_93, B_94), A_93)=k4_xboole_0(A_93, B_94))), inference(resolution, [status(thm)], [c_16, c_125])).
% 8.71/3.13  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.71/3.13  tff(c_764, plain, (![A_93, B_94]: (k5_xboole_0(k4_xboole_0(A_93, B_94), k4_xboole_0(A_93, B_94))=k4_xboole_0(k4_xboole_0(A_93, B_94), A_93))), inference(superposition, [status(thm), theory('equality')], [c_752, c_10])).
% 8.71/3.13  tff(c_817, plain, (![A_95, B_96]: (k4_xboole_0(k4_xboole_0(A_95, B_96), A_95)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_560, c_764])).
% 8.71/3.13  tff(c_22, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.71/3.13  tff(c_831, plain, (![A_95, B_96]: (k2_xboole_0(A_95, k4_xboole_0(A_95, B_96))=k5_xboole_0(A_95, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_817, c_22])).
% 8.71/3.13  tff(c_867, plain, (![A_95, B_96]: (k2_xboole_0(A_95, k4_xboole_0(A_95, B_96))=A_95)), inference(demodulation, [status(thm), theory('equality')], [c_337, c_831])).
% 8.71/3.13  tff(c_1231, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1192, c_867])).
% 8.71/3.13  tff(c_44, plain, (![A_36, B_37]: (m1_subset_1(k2_tops_1(A_36, B_37), k1_zfmisc_1(u1_struct_0(A_36))) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.71/3.13  tff(c_2252, plain, (![A_133, B_134, C_135]: (k4_subset_1(A_133, B_134, C_135)=k2_xboole_0(B_134, C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(A_133)) | ~m1_subset_1(B_134, k1_zfmisc_1(A_133)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.71/3.13  tff(c_12041, plain, (![A_293, B_294, B_295]: (k4_subset_1(u1_struct_0(A_293), B_294, k2_tops_1(A_293, B_295))=k2_xboole_0(B_294, k2_tops_1(A_293, B_295)) | ~m1_subset_1(B_294, k1_zfmisc_1(u1_struct_0(A_293))) | ~m1_subset_1(B_295, k1_zfmisc_1(u1_struct_0(A_293))) | ~l1_pre_topc(A_293))), inference(resolution, [status(thm)], [c_44, c_2252])).
% 8.71/3.13  tff(c_12048, plain, (![B_295]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_295))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_295)) | ~m1_subset_1(B_295, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_12041])).
% 8.71/3.13  tff(c_12057, plain, (![B_296]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_296))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_296)) | ~m1_subset_1(B_296, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_12048])).
% 8.71/3.13  tff(c_12068, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_12057])).
% 8.71/3.13  tff(c_12074, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3355, c_1231, c_12068])).
% 8.71/3.13  tff(c_12076, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2769, c_12074])).
% 8.71/3.13  tff(c_12077, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 8.71/3.13  tff(c_13623, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13622, c_12077])).
% 8.71/3.13  tff(c_12128, plain, (![A_304, B_305]: (k1_setfam_1(k2_tarski(A_304, B_305))=k3_xboole_0(A_304, B_305))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.71/3.13  tff(c_12143, plain, (![B_306, A_307]: (k1_setfam_1(k2_tarski(B_306, A_307))=k3_xboole_0(A_307, B_306))), inference(superposition, [status(thm), theory('equality')], [c_24, c_12128])).
% 8.71/3.13  tff(c_12149, plain, (![B_306, A_307]: (k3_xboole_0(B_306, A_307)=k3_xboole_0(A_307, B_306))), inference(superposition, [status(thm), theory('equality')], [c_12143, c_34])).
% 8.71/3.13  tff(c_12078, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 8.71/3.13  tff(c_14613, plain, (![A_384, B_385]: (r1_tarski(k2_tops_1(A_384, B_385), B_385) | ~v4_pre_topc(B_385, A_384) | ~m1_subset_1(B_385, k1_zfmisc_1(u1_struct_0(A_384))) | ~l1_pre_topc(A_384))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.71/3.13  tff(c_14620, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_14613])).
% 8.71/3.13  tff(c_14625, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_12078, c_14620])).
% 8.71/3.13  tff(c_12, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.71/3.13  tff(c_14632, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_14625, c_12])).
% 8.71/3.13  tff(c_14694, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12149, c_14632])).
% 8.71/3.13  tff(c_15250, plain, (![A_395, B_396]: (k7_subset_1(u1_struct_0(A_395), B_396, k2_tops_1(A_395, B_396))=k1_tops_1(A_395, B_396) | ~m1_subset_1(B_396, k1_zfmisc_1(u1_struct_0(A_395))) | ~l1_pre_topc(A_395))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.71/3.13  tff(c_15257, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_15250])).
% 8.71/3.13  tff(c_15262, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_13622, c_15257])).
% 8.71/3.13  tff(c_20, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.71/3.13  tff(c_15281, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_15262, c_20])).
% 8.71/3.13  tff(c_15293, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14694, c_15281])).
% 8.71/3.13  tff(c_15295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13623, c_15293])).
% 8.71/3.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.71/3.13  
% 8.71/3.13  Inference rules
% 8.71/3.13  ----------------------
% 8.71/3.13  #Ref     : 0
% 8.71/3.13  #Sup     : 3732
% 8.71/3.13  #Fact    : 0
% 8.71/3.13  #Define  : 0
% 8.71/3.13  #Split   : 8
% 8.71/3.13  #Chain   : 0
% 8.71/3.13  #Close   : 0
% 8.71/3.13  
% 8.71/3.13  Ordering : KBO
% 8.71/3.13  
% 8.71/3.13  Simplification rules
% 8.71/3.13  ----------------------
% 8.71/3.13  #Subsume      : 223
% 8.71/3.13  #Demod        : 5576
% 8.71/3.13  #Tautology    : 3001
% 8.71/3.13  #SimpNegUnit  : 6
% 8.71/3.13  #BackRed      : 5
% 8.71/3.13  
% 8.71/3.13  #Partial instantiations: 0
% 8.71/3.13  #Strategies tried      : 1
% 8.71/3.13  
% 8.71/3.13  Timing (in seconds)
% 8.71/3.13  ----------------------
% 8.71/3.14  Preprocessing        : 0.36
% 8.71/3.14  Parsing              : 0.19
% 8.71/3.14  CNF conversion       : 0.02
% 8.71/3.14  Main loop            : 2.01
% 8.71/3.14  Inferencing          : 0.50
% 8.71/3.14  Reduction            : 1.10
% 8.71/3.14  Demodulation         : 0.95
% 8.71/3.14  BG Simplification    : 0.05
% 8.71/3.14  Subsumption          : 0.27
% 8.71/3.14  Abstraction          : 0.09
% 8.71/3.14  MUC search           : 0.00
% 8.71/3.14  Cooper               : 0.00
% 8.71/3.14  Total                : 2.40
% 8.71/3.14  Index Insertion      : 0.00
% 8.71/3.14  Index Deletion       : 0.00
% 8.71/3.14  Index Matching       : 0.00
% 8.71/3.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
