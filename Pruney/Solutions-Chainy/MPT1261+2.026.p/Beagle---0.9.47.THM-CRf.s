%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:15 EST 2020

% Result     : Theorem 12.60s
% Output     : CNFRefutation 12.60s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 239 expanded)
%              Number of leaves         :   51 ( 100 expanded)
%              Depth                    :   14
%              Number of atoms          :  184 ( 456 expanded)
%              Number of equality atoms :   71 ( 140 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k3_zfmisc_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

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

tff(f_170,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_122,axiom,(
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

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_55,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_91,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_tarski(A,k3_zfmisc_1(A,B,C))
          & ~ r1_tarski(A,k3_zfmisc_1(B,C,A))
          & ~ r1_tarski(A,k3_zfmisc_1(C,A,B)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_mcart_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_142,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_151,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_158,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_81,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_69,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(c_70,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_34556,plain,(
    ! [A_725,B_726,C_727] :
      ( k7_subset_1(A_725,B_726,C_727) = k4_xboole_0(B_726,C_727)
      | ~ m1_subset_1(B_726,k1_zfmisc_1(A_725)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_34571,plain,(
    ! [C_727] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_727) = k4_xboole_0('#skF_2',C_727) ),
    inference(resolution,[status(thm)],[c_70,c_34556])).

tff(c_76,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_264,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_72,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_74,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_3402,plain,(
    ! [B_253,A_254] :
      ( v4_pre_topc(B_253,A_254)
      | k2_pre_topc(A_254,B_253) != B_253
      | ~ v2_pre_topc(A_254)
      | ~ m1_subset_1(B_253,k1_zfmisc_1(u1_struct_0(A_254)))
      | ~ l1_pre_topc(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_3431,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_3402])).

tff(c_3443,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_74,c_3431])).

tff(c_3444,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_264,c_3443])).

tff(c_2096,plain,(
    ! [A_198,B_199,C_200] :
      ( k7_subset_1(A_198,B_199,C_200) = k4_xboole_0(B_199,C_200)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(A_198)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2125,plain,(
    ! [C_203] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_203) = k4_xboole_0('#skF_2',C_203) ),
    inference(resolution,[status(thm)],[c_70,c_2096])).

tff(c_82,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_155,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_2131,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2125,c_155])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [B_24,A_23] : k2_tarski(B_24,A_23) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_172,plain,(
    ! [A_87,B_88] : k1_setfam_1(k2_tarski(A_87,B_88)) = k3_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_202,plain,(
    ! [A_91,B_92] : k1_setfam_1(k2_tarski(A_91,B_92)) = k3_xboole_0(B_92,A_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_172])).

tff(c_44,plain,(
    ! [A_46,B_47] : k1_setfam_1(k2_tarski(A_46,B_47)) = k3_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_208,plain,(
    ! [B_92,A_91] : k3_xboole_0(B_92,A_91) = k3_xboole_0(A_91,B_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_44])).

tff(c_12,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1733,plain,(
    ! [A_183,B_184,C_185] :
      ( r1_tarski(k4_xboole_0(A_183,B_184),C_185)
      | ~ r1_tarski(A_183,k2_xboole_0(B_184,C_185)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1149,plain,(
    ! [A_160,B_161,C_162] :
      ( r1_tarski(A_160,k2_xboole_0(B_161,C_162))
      | ~ r1_tarski(k4_xboole_0(A_160,B_161),C_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1183,plain,(
    ! [A_163,B_164] : r1_tarski(A_163,k2_xboole_0(B_164,A_163)) ),
    inference(resolution,[status(thm)],[c_12,c_1149])).

tff(c_1289,plain,(
    ! [A_167] : r1_tarski(k1_xboole_0,A_167) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1183])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1314,plain,(
    ! [A_6,A_167] :
      ( r1_tarski(A_6,A_167)
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1289,c_8])).

tff(c_1736,plain,(
    ! [A_183,B_184,A_167] :
      ( r1_tarski(k4_xboole_0(A_183,B_184),A_167)
      | ~ r1_tarski(A_183,k2_xboole_0(B_184,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1733,c_1314])).

tff(c_7280,plain,(
    ! [A_359,B_360,A_361] :
      ( r1_tarski(k4_xboole_0(A_359,B_360),A_361)
      | ~ r1_tarski(A_359,B_360) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1736])).

tff(c_54,plain,(
    ! [A_50,B_51,C_52] :
      ( ~ r1_tarski(A_50,k3_zfmisc_1(A_50,B_51,C_52))
      | k1_xboole_0 = A_50 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_7375,plain,(
    ! [A_362,B_363] :
      ( k4_xboole_0(A_362,B_363) = k1_xboole_0
      | ~ r1_tarski(A_362,B_363) ) ),
    inference(resolution,[status(thm)],[c_7280,c_54])).

tff(c_8206,plain,(
    ! [A_366,B_367] : k4_xboole_0(k4_xboole_0(A_366,B_367),A_366) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_7375])).

tff(c_18,plain,(
    ! [A_19,B_20] : k2_xboole_0(k3_xboole_0(A_19,B_20),k4_xboole_0(A_19,B_20)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8308,plain,(
    ! [A_366,B_367] : k2_xboole_0(k3_xboole_0(k4_xboole_0(A_366,B_367),A_366),k1_xboole_0) = k4_xboole_0(A_366,B_367) ),
    inference(superposition,[status(thm),theory(equality)],[c_8206,c_18])).

tff(c_30856,plain,(
    ! [A_565,B_566] : k3_xboole_0(A_565,k4_xboole_0(A_565,B_566)) = k4_xboole_0(A_565,B_566) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_208,c_8308])).

tff(c_10,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_31354,plain,(
    ! [A_567,B_568] : k2_xboole_0(A_567,k4_xboole_0(A_567,B_568)) = A_567 ),
    inference(superposition,[status(thm),theory(equality)],[c_30856,c_10])).

tff(c_31732,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2131,c_31354])).

tff(c_2641,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2131,c_12])).

tff(c_3869,plain,(
    ! [A_270,B_271] :
      ( k4_subset_1(u1_struct_0(A_270),B_271,k2_tops_1(A_270,B_271)) = k2_pre_topc(A_270,B_271)
      | ~ m1_subset_1(B_271,k1_zfmisc_1(u1_struct_0(A_270)))
      | ~ l1_pre_topc(A_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_3892,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_3869])).

tff(c_3907,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3892])).

tff(c_157,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(A_83,B_84)
      | ~ m1_subset_1(A_83,k1_zfmisc_1(B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_166,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_157])).

tff(c_682,plain,(
    ! [A_124,C_125,B_126] :
      ( r1_tarski(A_124,C_125)
      | ~ r1_tarski(B_126,C_125)
      | ~ r1_tarski(A_124,B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_690,plain,(
    ! [A_124] :
      ( r1_tarski(A_124,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_124,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_166,c_682])).

tff(c_48,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1(A_48,k1_zfmisc_1(B_49))
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2704,plain,(
    ! [A_224,B_225,C_226] :
      ( k4_subset_1(A_224,B_225,C_226) = k2_xboole_0(B_225,C_226)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(A_224))
      | ~ m1_subset_1(B_225,k1_zfmisc_1(A_224)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10386,plain,(
    ! [B_387,B_388,A_389] :
      ( k4_subset_1(B_387,B_388,A_389) = k2_xboole_0(B_388,A_389)
      | ~ m1_subset_1(B_388,k1_zfmisc_1(B_387))
      | ~ r1_tarski(A_389,B_387) ) ),
    inference(resolution,[status(thm)],[c_48,c_2704])).

tff(c_10426,plain,(
    ! [A_390] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_390) = k2_xboole_0('#skF_2',A_390)
      | ~ r1_tarski(A_390,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_70,c_10386])).

tff(c_11667,plain,(
    ! [A_400] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_400) = k2_xboole_0('#skF_2',A_400)
      | ~ r1_tarski(A_400,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_690,c_10426])).

tff(c_11699,plain,
    ( k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3907,c_11667])).

tff(c_11721,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2641,c_11699])).

tff(c_31866,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31732,c_11721])).

tff(c_31868,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3444,c_31866])).

tff(c_31869,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_32123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31869,c_155])).

tff(c_32124,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_32243,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32124,c_76])).

tff(c_34692,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34571,c_32243])).

tff(c_35184,plain,(
    ! [A_750,B_751] :
      ( r1_tarski(k2_tops_1(A_750,B_751),B_751)
      | ~ v4_pre_topc(B_751,A_750)
      | ~ m1_subset_1(B_751,k1_zfmisc_1(u1_struct_0(A_750)))
      | ~ l1_pre_topc(A_750) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_35203,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_35184])).

tff(c_35212,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_32124,c_35203])).

tff(c_36085,plain,(
    ! [A_789,B_790] :
      ( k7_subset_1(u1_struct_0(A_789),B_790,k2_tops_1(A_789,B_790)) = k1_tops_1(A_789,B_790)
      | ~ m1_subset_1(B_790,k1_zfmisc_1(u1_struct_0(A_789)))
      | ~ l1_pre_topc(A_789) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_36108,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_36085])).

tff(c_36125,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_34571,c_36108])).

tff(c_34305,plain,(
    ! [A_718,B_719] :
      ( k4_xboole_0(A_718,B_719) = k3_subset_1(A_718,B_719)
      | ~ m1_subset_1(B_719,k1_zfmisc_1(A_718)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_36273,plain,(
    ! [B_794,A_795] :
      ( k4_xboole_0(B_794,A_795) = k3_subset_1(B_794,A_795)
      | ~ r1_tarski(A_795,B_794) ) ),
    inference(resolution,[status(thm)],[c_48,c_34305])).

tff(c_36321,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_35212,c_36273])).

tff(c_36431,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36125,c_36321])).

tff(c_33265,plain,(
    ! [A_665,B_666] :
      ( k3_subset_1(A_665,k3_subset_1(A_665,B_666)) = B_666
      | ~ m1_subset_1(B_666,k1_zfmisc_1(A_665)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_33275,plain,(
    ! [B_49,A_48] :
      ( k3_subset_1(B_49,k3_subset_1(B_49,A_48)) = A_48
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_48,c_33265])).

tff(c_36779,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_36431,c_33275])).

tff(c_36786,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35212,c_36779])).

tff(c_38,plain,(
    ! [A_39,B_40] : k6_subset_1(A_39,B_40) = k4_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,(
    ! [A_32,B_33] : m1_subset_1(k6_subset_1(A_32,B_33),k1_zfmisc_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_83,plain,(
    ! [A_32,B_33] : m1_subset_1(k4_xboole_0(A_32,B_33),k1_zfmisc_1(A_32)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32])).

tff(c_39536,plain,(
    ! [A_853,B_854] : k4_xboole_0(A_853,k4_xboole_0(A_853,B_854)) = k3_subset_1(A_853,k4_xboole_0(A_853,B_854)) ),
    inference(resolution,[status(thm)],[c_83,c_34305])).

tff(c_39667,plain,(
    k3_subset_1('#skF_2',k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36125,c_39536])).

tff(c_39700,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36786,c_36125,c_39667])).

tff(c_39702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34692,c_39700])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:10:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.60/5.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.60/5.98  
% 12.60/5.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.60/5.98  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k3_zfmisc_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 12.60/5.98  
% 12.60/5.98  %Foreground sorts:
% 12.60/5.98  
% 12.60/5.98  
% 12.60/5.98  %Background operators:
% 12.60/5.98  
% 12.60/5.98  
% 12.60/5.98  %Foreground operators:
% 12.60/5.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.60/5.98  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.60/5.98  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 12.60/5.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.60/5.98  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.60/5.98  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.60/5.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.60/5.98  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.60/5.98  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 12.60/5.98  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 12.60/5.98  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 12.60/5.98  tff('#skF_2', type, '#skF_2': $i).
% 12.60/5.98  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 12.60/5.98  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 12.60/5.98  tff('#skF_1', type, '#skF_1': $i).
% 12.60/5.98  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 12.60/5.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.60/5.98  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 12.60/5.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.60/5.98  tff(k3_tarski, type, k3_tarski: $i > $i).
% 12.60/5.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.60/5.98  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 12.60/5.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.60/5.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.60/5.98  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.60/5.98  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 12.60/5.98  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 12.60/5.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.60/5.98  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 12.60/5.98  
% 12.60/6.01  tff(f_170, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 12.60/6.01  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 12.60/6.01  tff(f_122, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 12.60/6.01  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 12.60/6.01  tff(f_55, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 12.60/6.01  tff(f_91, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 12.60/6.01  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 12.60/6.01  tff(f_45, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 12.60/6.01  tff(f_49, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 12.60/6.01  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 12.60/6.01  tff(f_107, axiom, (![A, B, C]: (~((~r1_tarski(A, k3_zfmisc_1(A, B, C)) & ~r1_tarski(A, k3_zfmisc_1(B, C, A))) & ~r1_tarski(A, k3_zfmisc_1(C, A, B))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_mcart_1)).
% 12.60/6.01  tff(f_51, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 12.60/6.01  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 12.60/6.01  tff(f_142, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 12.60/6.01  tff(f_95, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 12.60/6.01  tff(f_79, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 12.60/6.01  tff(f_151, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 12.60/6.01  tff(f_158, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 12.60/6.01  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 12.60/6.01  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 12.60/6.01  tff(f_81, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 12.60/6.01  tff(f_69, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 12.60/6.01  tff(c_70, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 12.60/6.01  tff(c_34556, plain, (![A_725, B_726, C_727]: (k7_subset_1(A_725, B_726, C_727)=k4_xboole_0(B_726, C_727) | ~m1_subset_1(B_726, k1_zfmisc_1(A_725)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.60/6.01  tff(c_34571, plain, (![C_727]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_727)=k4_xboole_0('#skF_2', C_727))), inference(resolution, [status(thm)], [c_70, c_34556])).
% 12.60/6.01  tff(c_76, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 12.60/6.01  tff(c_264, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_76])).
% 12.60/6.01  tff(c_72, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 12.60/6.01  tff(c_74, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 12.60/6.01  tff(c_3402, plain, (![B_253, A_254]: (v4_pre_topc(B_253, A_254) | k2_pre_topc(A_254, B_253)!=B_253 | ~v2_pre_topc(A_254) | ~m1_subset_1(B_253, k1_zfmisc_1(u1_struct_0(A_254))) | ~l1_pre_topc(A_254))), inference(cnfTransformation, [status(thm)], [f_122])).
% 12.60/6.01  tff(c_3431, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_70, c_3402])).
% 12.60/6.01  tff(c_3443, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_74, c_3431])).
% 12.60/6.01  tff(c_3444, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_264, c_3443])).
% 12.60/6.01  tff(c_2096, plain, (![A_198, B_199, C_200]: (k7_subset_1(A_198, B_199, C_200)=k4_xboole_0(B_199, C_200) | ~m1_subset_1(B_199, k1_zfmisc_1(A_198)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.60/6.01  tff(c_2125, plain, (![C_203]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_203)=k4_xboole_0('#skF_2', C_203))), inference(resolution, [status(thm)], [c_70, c_2096])).
% 12.60/6.01  tff(c_82, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 12.60/6.01  tff(c_155, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_82])).
% 12.60/6.01  tff(c_2131, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2125, c_155])).
% 12.60/6.01  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.60/6.01  tff(c_22, plain, (![B_24, A_23]: (k2_tarski(B_24, A_23)=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.60/6.01  tff(c_172, plain, (![A_87, B_88]: (k1_setfam_1(k2_tarski(A_87, B_88))=k3_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.60/6.01  tff(c_202, plain, (![A_91, B_92]: (k1_setfam_1(k2_tarski(A_91, B_92))=k3_xboole_0(B_92, A_91))), inference(superposition, [status(thm), theory('equality')], [c_22, c_172])).
% 12.60/6.01  tff(c_44, plain, (![A_46, B_47]: (k1_setfam_1(k2_tarski(A_46, B_47))=k3_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.60/6.01  tff(c_208, plain, (![B_92, A_91]: (k3_xboole_0(B_92, A_91)=k3_xboole_0(A_91, B_92))), inference(superposition, [status(thm), theory('equality')], [c_202, c_44])).
% 12.60/6.01  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.60/6.01  tff(c_1733, plain, (![A_183, B_184, C_185]: (r1_tarski(k4_xboole_0(A_183, B_184), C_185) | ~r1_tarski(A_183, k2_xboole_0(B_184, C_185)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.60/6.01  tff(c_1149, plain, (![A_160, B_161, C_162]: (r1_tarski(A_160, k2_xboole_0(B_161, C_162)) | ~r1_tarski(k4_xboole_0(A_160, B_161), C_162))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.60/6.01  tff(c_1183, plain, (![A_163, B_164]: (r1_tarski(A_163, k2_xboole_0(B_164, A_163)))), inference(resolution, [status(thm)], [c_12, c_1149])).
% 12.60/6.01  tff(c_1289, plain, (![A_167]: (r1_tarski(k1_xboole_0, A_167))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1183])).
% 12.60/6.01  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.60/6.01  tff(c_1314, plain, (![A_6, A_167]: (r1_tarski(A_6, A_167) | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_1289, c_8])).
% 12.60/6.01  tff(c_1736, plain, (![A_183, B_184, A_167]: (r1_tarski(k4_xboole_0(A_183, B_184), A_167) | ~r1_tarski(A_183, k2_xboole_0(B_184, k1_xboole_0)))), inference(resolution, [status(thm)], [c_1733, c_1314])).
% 12.60/6.01  tff(c_7280, plain, (![A_359, B_360, A_361]: (r1_tarski(k4_xboole_0(A_359, B_360), A_361) | ~r1_tarski(A_359, B_360))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1736])).
% 12.60/6.01  tff(c_54, plain, (![A_50, B_51, C_52]: (~r1_tarski(A_50, k3_zfmisc_1(A_50, B_51, C_52)) | k1_xboole_0=A_50)), inference(cnfTransformation, [status(thm)], [f_107])).
% 12.60/6.01  tff(c_7375, plain, (![A_362, B_363]: (k4_xboole_0(A_362, B_363)=k1_xboole_0 | ~r1_tarski(A_362, B_363))), inference(resolution, [status(thm)], [c_7280, c_54])).
% 12.60/6.01  tff(c_8206, plain, (![A_366, B_367]: (k4_xboole_0(k4_xboole_0(A_366, B_367), A_366)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_7375])).
% 12.60/6.01  tff(c_18, plain, (![A_19, B_20]: (k2_xboole_0(k3_xboole_0(A_19, B_20), k4_xboole_0(A_19, B_20))=A_19)), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.60/6.01  tff(c_8308, plain, (![A_366, B_367]: (k2_xboole_0(k3_xboole_0(k4_xboole_0(A_366, B_367), A_366), k1_xboole_0)=k4_xboole_0(A_366, B_367))), inference(superposition, [status(thm), theory('equality')], [c_8206, c_18])).
% 12.60/6.01  tff(c_30856, plain, (![A_565, B_566]: (k3_xboole_0(A_565, k4_xboole_0(A_565, B_566))=k4_xboole_0(A_565, B_566))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_208, c_8308])).
% 12.60/6.01  tff(c_10, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k3_xboole_0(A_9, B_10))=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.60/6.01  tff(c_31354, plain, (![A_567, B_568]: (k2_xboole_0(A_567, k4_xboole_0(A_567, B_568))=A_567)), inference(superposition, [status(thm), theory('equality')], [c_30856, c_10])).
% 12.60/6.01  tff(c_31732, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2131, c_31354])).
% 12.60/6.01  tff(c_2641, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2131, c_12])).
% 12.60/6.01  tff(c_3869, plain, (![A_270, B_271]: (k4_subset_1(u1_struct_0(A_270), B_271, k2_tops_1(A_270, B_271))=k2_pre_topc(A_270, B_271) | ~m1_subset_1(B_271, k1_zfmisc_1(u1_struct_0(A_270))) | ~l1_pre_topc(A_270))), inference(cnfTransformation, [status(thm)], [f_142])).
% 12.60/6.01  tff(c_3892, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_70, c_3869])).
% 12.60/6.01  tff(c_3907, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3892])).
% 12.60/6.01  tff(c_157, plain, (![A_83, B_84]: (r1_tarski(A_83, B_84) | ~m1_subset_1(A_83, k1_zfmisc_1(B_84)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.60/6.01  tff(c_166, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_157])).
% 12.60/6.01  tff(c_682, plain, (![A_124, C_125, B_126]: (r1_tarski(A_124, C_125) | ~r1_tarski(B_126, C_125) | ~r1_tarski(A_124, B_126))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.60/6.01  tff(c_690, plain, (![A_124]: (r1_tarski(A_124, u1_struct_0('#skF_1')) | ~r1_tarski(A_124, '#skF_2'))), inference(resolution, [status(thm)], [c_166, c_682])).
% 12.60/6.01  tff(c_48, plain, (![A_48, B_49]: (m1_subset_1(A_48, k1_zfmisc_1(B_49)) | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.60/6.01  tff(c_2704, plain, (![A_224, B_225, C_226]: (k4_subset_1(A_224, B_225, C_226)=k2_xboole_0(B_225, C_226) | ~m1_subset_1(C_226, k1_zfmisc_1(A_224)) | ~m1_subset_1(B_225, k1_zfmisc_1(A_224)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.60/6.01  tff(c_10386, plain, (![B_387, B_388, A_389]: (k4_subset_1(B_387, B_388, A_389)=k2_xboole_0(B_388, A_389) | ~m1_subset_1(B_388, k1_zfmisc_1(B_387)) | ~r1_tarski(A_389, B_387))), inference(resolution, [status(thm)], [c_48, c_2704])).
% 12.60/6.01  tff(c_10426, plain, (![A_390]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_390)=k2_xboole_0('#skF_2', A_390) | ~r1_tarski(A_390, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_70, c_10386])).
% 12.60/6.01  tff(c_11667, plain, (![A_400]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_400)=k2_xboole_0('#skF_2', A_400) | ~r1_tarski(A_400, '#skF_2'))), inference(resolution, [status(thm)], [c_690, c_10426])).
% 12.60/6.01  tff(c_11699, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3907, c_11667])).
% 12.60/6.01  tff(c_11721, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2641, c_11699])).
% 12.60/6.01  tff(c_31866, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_31732, c_11721])).
% 12.60/6.01  tff(c_31868, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3444, c_31866])).
% 12.60/6.01  tff(c_31869, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_76])).
% 12.60/6.01  tff(c_32123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31869, c_155])).
% 12.60/6.01  tff(c_32124, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_82])).
% 12.60/6.01  tff(c_32243, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32124, c_76])).
% 12.60/6.01  tff(c_34692, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34571, c_32243])).
% 12.60/6.01  tff(c_35184, plain, (![A_750, B_751]: (r1_tarski(k2_tops_1(A_750, B_751), B_751) | ~v4_pre_topc(B_751, A_750) | ~m1_subset_1(B_751, k1_zfmisc_1(u1_struct_0(A_750))) | ~l1_pre_topc(A_750))), inference(cnfTransformation, [status(thm)], [f_151])).
% 12.60/6.01  tff(c_35203, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_70, c_35184])).
% 12.60/6.01  tff(c_35212, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_32124, c_35203])).
% 12.60/6.01  tff(c_36085, plain, (![A_789, B_790]: (k7_subset_1(u1_struct_0(A_789), B_790, k2_tops_1(A_789, B_790))=k1_tops_1(A_789, B_790) | ~m1_subset_1(B_790, k1_zfmisc_1(u1_struct_0(A_789))) | ~l1_pre_topc(A_789))), inference(cnfTransformation, [status(thm)], [f_158])).
% 12.60/6.01  tff(c_36108, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_70, c_36085])).
% 12.60/6.01  tff(c_36125, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_34571, c_36108])).
% 12.60/6.01  tff(c_34305, plain, (![A_718, B_719]: (k4_xboole_0(A_718, B_719)=k3_subset_1(A_718, B_719) | ~m1_subset_1(B_719, k1_zfmisc_1(A_718)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.60/6.01  tff(c_36273, plain, (![B_794, A_795]: (k4_xboole_0(B_794, A_795)=k3_subset_1(B_794, A_795) | ~r1_tarski(A_795, B_794))), inference(resolution, [status(thm)], [c_48, c_34305])).
% 12.60/6.01  tff(c_36321, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_35212, c_36273])).
% 12.60/6.01  tff(c_36431, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36125, c_36321])).
% 12.60/6.01  tff(c_33265, plain, (![A_665, B_666]: (k3_subset_1(A_665, k3_subset_1(A_665, B_666))=B_666 | ~m1_subset_1(B_666, k1_zfmisc_1(A_665)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.60/6.01  tff(c_33275, plain, (![B_49, A_48]: (k3_subset_1(B_49, k3_subset_1(B_49, A_48))=A_48 | ~r1_tarski(A_48, B_49))), inference(resolution, [status(thm)], [c_48, c_33265])).
% 12.60/6.01  tff(c_36779, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_36431, c_33275])).
% 12.60/6.01  tff(c_36786, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_35212, c_36779])).
% 12.60/6.01  tff(c_38, plain, (![A_39, B_40]: (k6_subset_1(A_39, B_40)=k4_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_81])).
% 12.60/6.01  tff(c_32, plain, (![A_32, B_33]: (m1_subset_1(k6_subset_1(A_32, B_33), k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 12.60/6.01  tff(c_83, plain, (![A_32, B_33]: (m1_subset_1(k4_xboole_0(A_32, B_33), k1_zfmisc_1(A_32)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32])).
% 12.60/6.01  tff(c_39536, plain, (![A_853, B_854]: (k4_xboole_0(A_853, k4_xboole_0(A_853, B_854))=k3_subset_1(A_853, k4_xboole_0(A_853, B_854)))), inference(resolution, [status(thm)], [c_83, c_34305])).
% 12.60/6.01  tff(c_39667, plain, (k3_subset_1('#skF_2', k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_36125, c_39536])).
% 12.60/6.01  tff(c_39700, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36786, c_36125, c_39667])).
% 12.60/6.01  tff(c_39702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34692, c_39700])).
% 12.60/6.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.60/6.01  
% 12.60/6.01  Inference rules
% 12.60/6.01  ----------------------
% 12.60/6.01  #Ref     : 0
% 12.60/6.01  #Sup     : 9765
% 12.60/6.01  #Fact    : 0
% 12.60/6.01  #Define  : 0
% 12.60/6.01  #Split   : 3
% 12.60/6.01  #Chain   : 0
% 12.60/6.01  #Close   : 0
% 12.60/6.01  
% 12.60/6.01  Ordering : KBO
% 12.60/6.01  
% 12.60/6.01  Simplification rules
% 12.60/6.01  ----------------------
% 12.60/6.01  #Subsume      : 284
% 12.60/6.01  #Demod        : 9390
% 12.60/6.01  #Tautology    : 6728
% 12.60/6.01  #SimpNegUnit  : 7
% 12.60/6.01  #BackRed      : 28
% 12.60/6.01  
% 12.60/6.01  #Partial instantiations: 0
% 12.60/6.01  #Strategies tried      : 1
% 12.60/6.01  
% 12.60/6.01  Timing (in seconds)
% 12.60/6.01  ----------------------
% 12.60/6.01  Preprocessing        : 0.37
% 12.60/6.01  Parsing              : 0.19
% 12.60/6.01  CNF conversion       : 0.03
% 12.60/6.01  Main loop            : 4.79
% 12.60/6.01  Inferencing          : 0.86
% 12.60/6.01  Reduction            : 2.67
% 12.60/6.01  Demodulation         : 2.31
% 12.60/6.01  BG Simplification    : 0.09
% 12.60/6.01  Subsumption          : 0.91
% 12.60/6.01  Abstraction          : 0.15
% 12.60/6.01  MUC search           : 0.00
% 12.60/6.01  Cooper               : 0.00
% 12.60/6.01  Total                : 5.21
% 12.60/6.01  Index Insertion      : 0.00
% 12.60/6.01  Index Deletion       : 0.00
% 12.60/6.01  Index Matching       : 0.00
% 12.60/6.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
