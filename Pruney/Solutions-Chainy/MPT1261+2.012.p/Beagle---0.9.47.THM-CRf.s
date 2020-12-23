%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:13 EST 2020

% Result     : Theorem 8.94s
% Output     : CNFRefutation 8.94s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 354 expanded)
%              Number of leaves         :   48 ( 137 expanded)
%              Depth                    :   16
%              Number of atoms          :  198 ( 611 expanded)
%              Number of equality atoms :   98 ( 235 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_135,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_100,axiom,(
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

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_75,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_73,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_116,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_5241,plain,(
    ! [A_285,B_286,C_287] :
      ( k7_subset_1(A_285,B_286,C_287) = k4_xboole_0(B_286,C_287)
      | ~ m1_subset_1(B_286,k1_zfmisc_1(A_285)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_5249,plain,(
    ! [C_287] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_287) = k4_xboole_0('#skF_2',C_287) ),
    inference(resolution,[status(thm)],[c_52,c_5241])).

tff(c_58,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_124,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_56,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1891,plain,(
    ! [B_156,A_157] :
      ( v4_pre_topc(B_156,A_157)
      | k2_pre_topc(A_157,B_156) != B_156
      | ~ v2_pre_topc(A_157)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ l1_pre_topc(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1914,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_1891])).

tff(c_1935,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_1914])).

tff(c_1936,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_1935])).

tff(c_14,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_134,plain,(
    ! [A_61,B_62] : k1_setfam_1(k2_tarski(A_61,B_62)) = k3_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_198,plain,(
    ! [A_69,B_70] : k1_setfam_1(k2_tarski(A_69,B_70)) = k3_xboole_0(B_70,A_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_134])).

tff(c_34,plain,(
    ! [A_31,B_32] : k1_setfam_1(k2_tarski(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_221,plain,(
    ! [B_71,A_72] : k3_xboole_0(B_71,A_72) = k3_xboole_0(A_72,B_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_34])).

tff(c_32,plain,(
    ! [A_30] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_149,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(A_63,B_64)
      | ~ m1_subset_1(A_63,k1_zfmisc_1(B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_158,plain,(
    ! [A_65] : r1_tarski(k1_xboole_0,A_65) ),
    inference(resolution,[status(thm)],[c_32,c_149])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_162,plain,(
    ! [A_65] : k3_xboole_0(k1_xboole_0,A_65) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_158,c_10])).

tff(c_237,plain,(
    ! [B_71] : k3_xboole_0(B_71,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_162])).

tff(c_313,plain,(
    ! [A_74,B_75] : k5_xboole_0(A_74,k3_xboole_0(A_74,B_75)) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_322,plain,(
    ! [B_71] : k5_xboole_0(B_71,k1_xboole_0) = k4_xboole_0(B_71,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_313])).

tff(c_340,plain,(
    ! [B_71] : k5_xboole_0(B_71,k1_xboole_0) = B_71 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_322])).

tff(c_204,plain,(
    ! [B_70,A_69] : k3_xboole_0(B_70,A_69) = k3_xboole_0(A_69,B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_34])).

tff(c_325,plain,(
    ! [A_69,B_70] : k5_xboole_0(A_69,k3_xboole_0(B_70,A_69)) = k4_xboole_0(A_69,B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_313])).

tff(c_64,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_193,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_64])).

tff(c_838,plain,(
    ! [A_112,B_113,C_114] :
      ( k7_subset_1(A_112,B_113,C_114) = k4_xboole_0(B_113,C_114)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(A_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_857,plain,(
    ! [C_117] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_117) = k4_xboole_0('#skF_2',C_117) ),
    inference(resolution,[status(thm)],[c_52,c_838])).

tff(c_869,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_857])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_115,plain,(
    ! [A_58,B_59] :
      ( k3_xboole_0(A_58,B_59) = A_58
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_122,plain,(
    ! [A_7,B_8] : k3_xboole_0(k4_xboole_0(A_7,B_8),A_7) = k4_xboole_0(A_7,B_8) ),
    inference(resolution,[status(thm)],[c_12,c_115])).

tff(c_911,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_869,c_122])).

tff(c_922,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_869,c_204,c_911])).

tff(c_787,plain,(
    ! [A_108,B_109] :
      ( k4_xboole_0(A_108,B_109) = k3_subset_1(A_108,B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(A_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_796,plain,(
    ! [A_30] : k4_xboole_0(A_30,k1_xboole_0) = k3_subset_1(A_30,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_787])).

tff(c_800,plain,(
    ! [A_30] : k3_subset_1(A_30,k1_xboole_0) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_796])).

tff(c_690,plain,(
    ! [A_98,B_99] :
      ( k3_subset_1(A_98,k3_subset_1(A_98,B_99)) = B_99
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_699,plain,(
    ! [A_30] : k3_subset_1(A_30,k3_subset_1(A_30,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_690])).

tff(c_801,plain,(
    ! [A_30] : k3_subset_1(A_30,A_30) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_699])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(A_33,k1_zfmisc_1(B_34))
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_995,plain,(
    ! [B_121,A_122] :
      ( k4_xboole_0(B_121,A_122) = k3_subset_1(B_121,A_122)
      | ~ r1_tarski(A_122,B_121) ) ),
    inference(resolution,[status(thm)],[c_38,c_787])).

tff(c_1013,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k3_subset_1(B_2,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_995])).

tff(c_1023,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_801,c_1013])).

tff(c_123,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_115])).

tff(c_337,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_313])).

tff(c_1026,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1023,c_337])).

tff(c_1143,plain,(
    ! [A_126,B_127,C_128] :
      ( k9_subset_1(A_126,B_127,C_128) = k3_xboole_0(B_127,C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(A_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1174,plain,(
    ! [B_131] : k9_subset_1(u1_struct_0('#skF_1'),B_131,'#skF_2') = k3_xboole_0(B_131,'#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_1143])).

tff(c_22,plain,(
    ! [A_16,B_17,C_18] :
      ( m1_subset_1(k9_subset_1(A_16,B_17,C_18),k1_zfmisc_1(A_16))
      | ~ m1_subset_1(C_18,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1180,plain,(
    ! [B_131] :
      ( m1_subset_1(k3_xboole_0(B_131,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1174,c_22])).

tff(c_1188,plain,(
    ! [B_132] : m1_subset_1(k3_xboole_0(B_132,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1180])).

tff(c_36,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1232,plain,(
    ! [B_133] : r1_tarski(k3_xboole_0(B_133,'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1188,c_36])).

tff(c_1745,plain,(
    ! [B_153] : k3_xboole_0(k3_xboole_0(B_153,'#skF_2'),u1_struct_0('#skF_1')) = k3_xboole_0(B_153,'#skF_2') ),
    inference(resolution,[status(thm)],[c_1232,c_10])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1754,plain,(
    ! [B_153] : k5_xboole_0(k3_xboole_0(B_153,'#skF_2'),k3_xboole_0(B_153,'#skF_2')) = k4_xboole_0(k3_xboole_0(B_153,'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1745,c_8])).

tff(c_1800,plain,(
    ! [B_154] : k4_xboole_0(k3_xboole_0(B_154,'#skF_2'),u1_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1026,c_1754])).

tff(c_1829,plain,(
    ! [A_69] : k4_xboole_0(k3_xboole_0('#skF_2',A_69),u1_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_1800])).

tff(c_3212,plain,(
    ! [A_197] : k3_xboole_0(k3_xboole_0('#skF_2',A_197),u1_struct_0('#skF_1')) = k3_xboole_0(A_197,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_1745])).

tff(c_3231,plain,(
    ! [A_197] : k5_xboole_0(k3_xboole_0('#skF_2',A_197),k3_xboole_0(A_197,'#skF_2')) = k4_xboole_0(k3_xboole_0('#skF_2',A_197),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3212,c_8])).

tff(c_3319,plain,(
    ! [A_200] : k5_xboole_0(k3_xboole_0('#skF_2',A_200),k3_xboole_0(A_200,'#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1829,c_3231])).

tff(c_3344,plain,(
    k5_xboole_0(k2_tops_1('#skF_1','#skF_2'),k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_922,c_3319])).

tff(c_3396,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_204,c_3344])).

tff(c_16,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3464,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3396,c_16])).

tff(c_3473,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_3464])).

tff(c_2106,plain,(
    ! [A_161,B_162] :
      ( k4_subset_1(u1_struct_0(A_161),B_162,k2_tops_1(A_161,B_162)) = k2_pre_topc(A_161,B_162)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ l1_pre_topc(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2122,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_2106])).

tff(c_2142,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2122])).

tff(c_917,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_869,c_12])).

tff(c_930,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_917,c_10])).

tff(c_1242,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_930,c_1232])).

tff(c_1638,plain,(
    ! [A_145,B_146,C_147] :
      ( k4_subset_1(A_145,B_146,C_147) = k2_xboole_0(B_146,C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(A_145))
      | ~ m1_subset_1(B_146,k1_zfmisc_1(A_145)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4043,plain,(
    ! [B_220,B_221,A_222] :
      ( k4_subset_1(B_220,B_221,A_222) = k2_xboole_0(B_221,A_222)
      | ~ m1_subset_1(B_221,k1_zfmisc_1(B_220))
      | ~ r1_tarski(A_222,B_220) ) ),
    inference(resolution,[status(thm)],[c_38,c_1638])).

tff(c_4216,plain,(
    ! [A_225] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_225) = k2_xboole_0('#skF_2',A_225)
      | ~ r1_tarski(A_225,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_52,c_4043])).

tff(c_4234,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1242,c_4216])).

tff(c_4268,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3473,c_2142,c_4234])).

tff(c_4270,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1936,c_4268])).

tff(c_4271,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_5304,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5249,c_4271])).

tff(c_4272,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_6330,plain,(
    ! [A_340,B_341] :
      ( r1_tarski(k2_tops_1(A_340,B_341),B_341)
      | ~ v4_pre_topc(B_341,A_340)
      | ~ m1_subset_1(B_341,k1_zfmisc_1(u1_struct_0(A_340)))
      | ~ l1_pre_topc(A_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_6346,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_6330])).

tff(c_6366,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4272,c_6346])).

tff(c_6847,plain,(
    ! [A_348,B_349] :
      ( k7_subset_1(u1_struct_0(A_348),B_349,k2_tops_1(A_348,B_349)) = k1_tops_1(A_348,B_349)
      | ~ m1_subset_1(B_349,k1_zfmisc_1(u1_struct_0(A_348)))
      | ~ l1_pre_topc(A_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_6865,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_6847])).

tff(c_6888,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_5249,c_6865])).

tff(c_4900,plain,(
    ! [A_265,B_266] :
      ( k4_xboole_0(A_265,B_266) = k3_subset_1(A_265,B_266)
      | ~ m1_subset_1(B_266,k1_zfmisc_1(A_265)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4910,plain,(
    ! [B_34,A_33] :
      ( k4_xboole_0(B_34,A_33) = k3_subset_1(B_34,A_33)
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(resolution,[status(thm)],[c_38,c_4900])).

tff(c_6382,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6366,c_4910])).

tff(c_14622,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6888,c_6382])).

tff(c_4800,plain,(
    ! [A_258,B_259] :
      ( k3_subset_1(A_258,k3_subset_1(A_258,B_259)) = B_259
      | ~ m1_subset_1(B_259,k1_zfmisc_1(A_258)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4807,plain,(
    ! [B_34,A_33] :
      ( k3_subset_1(B_34,k3_subset_1(B_34,A_33)) = A_33
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(resolution,[status(thm)],[c_38,c_4800])).

tff(c_14626,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14622,c_4807])).

tff(c_14630,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6366,c_14626])).

tff(c_6939,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6888,c_12])).

tff(c_6994,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6939,c_4910])).

tff(c_15389,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14630,c_6994])).

tff(c_15390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5304,c_15389])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:01:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.94/3.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.94/3.46  
% 8.94/3.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.94/3.47  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.94/3.47  
% 8.94/3.47  %Foreground sorts:
% 8.94/3.47  
% 8.94/3.47  
% 8.94/3.47  %Background operators:
% 8.94/3.47  
% 8.94/3.47  
% 8.94/3.47  %Foreground operators:
% 8.94/3.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.94/3.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.94/3.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.94/3.47  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 8.94/3.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.94/3.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.94/3.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.94/3.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.94/3.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.94/3.47  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.94/3.47  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.94/3.47  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.94/3.47  tff('#skF_2', type, '#skF_2': $i).
% 8.94/3.47  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 8.94/3.47  tff('#skF_1', type, '#skF_1': $i).
% 8.94/3.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.94/3.47  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.94/3.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.94/3.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.94/3.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.94/3.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.94/3.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.94/3.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.94/3.47  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.94/3.47  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.94/3.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.94/3.47  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.94/3.47  
% 8.94/3.49  tff(f_135, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 8.94/3.49  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 8.94/3.49  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 8.94/3.49  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.94/3.49  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.94/3.49  tff(f_75, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 8.94/3.49  tff(f_73, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 8.94/3.49  tff(f_79, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.94/3.49  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.94/3.49  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.94/3.49  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.94/3.49  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 8.94/3.49  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 8.94/3.49  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.94/3.49  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 8.94/3.49  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 8.94/3.49  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.94/3.49  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 8.94/3.49  tff(f_63, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 8.94/3.49  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 8.94/3.49  tff(f_123, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 8.94/3.49  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.94/3.49  tff(c_5241, plain, (![A_285, B_286, C_287]: (k7_subset_1(A_285, B_286, C_287)=k4_xboole_0(B_286, C_287) | ~m1_subset_1(B_286, k1_zfmisc_1(A_285)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.94/3.49  tff(c_5249, plain, (![C_287]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_287)=k4_xboole_0('#skF_2', C_287))), inference(resolution, [status(thm)], [c_52, c_5241])).
% 8.94/3.49  tff(c_58, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.94/3.49  tff(c_124, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_58])).
% 8.94/3.49  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.94/3.49  tff(c_56, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.94/3.49  tff(c_1891, plain, (![B_156, A_157]: (v4_pre_topc(B_156, A_157) | k2_pre_topc(A_157, B_156)!=B_156 | ~v2_pre_topc(A_157) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0(A_157))) | ~l1_pre_topc(A_157))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.94/3.49  tff(c_1914, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_1891])).
% 8.94/3.49  tff(c_1935, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_1914])).
% 8.94/3.49  tff(c_1936, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_124, c_1935])).
% 8.94/3.49  tff(c_14, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.94/3.49  tff(c_18, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.94/3.49  tff(c_134, plain, (![A_61, B_62]: (k1_setfam_1(k2_tarski(A_61, B_62))=k3_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.94/3.49  tff(c_198, plain, (![A_69, B_70]: (k1_setfam_1(k2_tarski(A_69, B_70))=k3_xboole_0(B_70, A_69))), inference(superposition, [status(thm), theory('equality')], [c_18, c_134])).
% 8.94/3.49  tff(c_34, plain, (![A_31, B_32]: (k1_setfam_1(k2_tarski(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.94/3.49  tff(c_221, plain, (![B_71, A_72]: (k3_xboole_0(B_71, A_72)=k3_xboole_0(A_72, B_71))), inference(superposition, [status(thm), theory('equality')], [c_198, c_34])).
% 8.94/3.49  tff(c_32, plain, (![A_30]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.94/3.49  tff(c_149, plain, (![A_63, B_64]: (r1_tarski(A_63, B_64) | ~m1_subset_1(A_63, k1_zfmisc_1(B_64)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.94/3.49  tff(c_158, plain, (![A_65]: (r1_tarski(k1_xboole_0, A_65))), inference(resolution, [status(thm)], [c_32, c_149])).
% 8.94/3.49  tff(c_10, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.94/3.49  tff(c_162, plain, (![A_65]: (k3_xboole_0(k1_xboole_0, A_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_158, c_10])).
% 8.94/3.49  tff(c_237, plain, (![B_71]: (k3_xboole_0(B_71, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_221, c_162])).
% 8.94/3.49  tff(c_313, plain, (![A_74, B_75]: (k5_xboole_0(A_74, k3_xboole_0(A_74, B_75))=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.94/3.49  tff(c_322, plain, (![B_71]: (k5_xboole_0(B_71, k1_xboole_0)=k4_xboole_0(B_71, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_237, c_313])).
% 8.94/3.49  tff(c_340, plain, (![B_71]: (k5_xboole_0(B_71, k1_xboole_0)=B_71)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_322])).
% 8.94/3.49  tff(c_204, plain, (![B_70, A_69]: (k3_xboole_0(B_70, A_69)=k3_xboole_0(A_69, B_70))), inference(superposition, [status(thm), theory('equality')], [c_198, c_34])).
% 8.94/3.49  tff(c_325, plain, (![A_69, B_70]: (k5_xboole_0(A_69, k3_xboole_0(B_70, A_69))=k4_xboole_0(A_69, B_70))), inference(superposition, [status(thm), theory('equality')], [c_204, c_313])).
% 8.94/3.49  tff(c_64, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.94/3.49  tff(c_193, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_124, c_64])).
% 8.94/3.49  tff(c_838, plain, (![A_112, B_113, C_114]: (k7_subset_1(A_112, B_113, C_114)=k4_xboole_0(B_113, C_114) | ~m1_subset_1(B_113, k1_zfmisc_1(A_112)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.94/3.49  tff(c_857, plain, (![C_117]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_117)=k4_xboole_0('#skF_2', C_117))), inference(resolution, [status(thm)], [c_52, c_838])).
% 8.94/3.49  tff(c_869, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_193, c_857])).
% 8.94/3.49  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.94/3.49  tff(c_115, plain, (![A_58, B_59]: (k3_xboole_0(A_58, B_59)=A_58 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.94/3.49  tff(c_122, plain, (![A_7, B_8]: (k3_xboole_0(k4_xboole_0(A_7, B_8), A_7)=k4_xboole_0(A_7, B_8))), inference(resolution, [status(thm)], [c_12, c_115])).
% 8.94/3.49  tff(c_911, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_869, c_122])).
% 8.94/3.49  tff(c_922, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_869, c_204, c_911])).
% 8.94/3.49  tff(c_787, plain, (![A_108, B_109]: (k4_xboole_0(A_108, B_109)=k3_subset_1(A_108, B_109) | ~m1_subset_1(B_109, k1_zfmisc_1(A_108)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.94/3.49  tff(c_796, plain, (![A_30]: (k4_xboole_0(A_30, k1_xboole_0)=k3_subset_1(A_30, k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_787])).
% 8.94/3.49  tff(c_800, plain, (![A_30]: (k3_subset_1(A_30, k1_xboole_0)=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_796])).
% 8.94/3.49  tff(c_690, plain, (![A_98, B_99]: (k3_subset_1(A_98, k3_subset_1(A_98, B_99))=B_99 | ~m1_subset_1(B_99, k1_zfmisc_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.94/3.49  tff(c_699, plain, (![A_30]: (k3_subset_1(A_30, k3_subset_1(A_30, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_690])).
% 8.94/3.49  tff(c_801, plain, (![A_30]: (k3_subset_1(A_30, A_30)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_800, c_699])).
% 8.94/3.49  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.94/3.49  tff(c_38, plain, (![A_33, B_34]: (m1_subset_1(A_33, k1_zfmisc_1(B_34)) | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.94/3.49  tff(c_995, plain, (![B_121, A_122]: (k4_xboole_0(B_121, A_122)=k3_subset_1(B_121, A_122) | ~r1_tarski(A_122, B_121))), inference(resolution, [status(thm)], [c_38, c_787])).
% 8.94/3.49  tff(c_1013, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k3_subset_1(B_2, B_2))), inference(resolution, [status(thm)], [c_6, c_995])).
% 8.94/3.49  tff(c_1023, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_801, c_1013])).
% 8.94/3.49  tff(c_123, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_115])).
% 8.94/3.49  tff(c_337, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_123, c_313])).
% 8.94/3.49  tff(c_1026, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1023, c_337])).
% 8.94/3.49  tff(c_1143, plain, (![A_126, B_127, C_128]: (k9_subset_1(A_126, B_127, C_128)=k3_xboole_0(B_127, C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(A_126)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.94/3.49  tff(c_1174, plain, (![B_131]: (k9_subset_1(u1_struct_0('#skF_1'), B_131, '#skF_2')=k3_xboole_0(B_131, '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_1143])).
% 8.94/3.49  tff(c_22, plain, (![A_16, B_17, C_18]: (m1_subset_1(k9_subset_1(A_16, B_17, C_18), k1_zfmisc_1(A_16)) | ~m1_subset_1(C_18, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.94/3.49  tff(c_1180, plain, (![B_131]: (m1_subset_1(k3_xboole_0(B_131, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_1174, c_22])).
% 8.94/3.49  tff(c_1188, plain, (![B_132]: (m1_subset_1(k3_xboole_0(B_132, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1180])).
% 8.94/3.49  tff(c_36, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~m1_subset_1(A_33, k1_zfmisc_1(B_34)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.94/3.49  tff(c_1232, plain, (![B_133]: (r1_tarski(k3_xboole_0(B_133, '#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1188, c_36])).
% 8.94/3.49  tff(c_1745, plain, (![B_153]: (k3_xboole_0(k3_xboole_0(B_153, '#skF_2'), u1_struct_0('#skF_1'))=k3_xboole_0(B_153, '#skF_2'))), inference(resolution, [status(thm)], [c_1232, c_10])).
% 8.94/3.49  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.94/3.49  tff(c_1754, plain, (![B_153]: (k5_xboole_0(k3_xboole_0(B_153, '#skF_2'), k3_xboole_0(B_153, '#skF_2'))=k4_xboole_0(k3_xboole_0(B_153, '#skF_2'), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1745, c_8])).
% 8.94/3.49  tff(c_1800, plain, (![B_154]: (k4_xboole_0(k3_xboole_0(B_154, '#skF_2'), u1_struct_0('#skF_1'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1026, c_1754])).
% 8.94/3.49  tff(c_1829, plain, (![A_69]: (k4_xboole_0(k3_xboole_0('#skF_2', A_69), u1_struct_0('#skF_1'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_204, c_1800])).
% 8.94/3.49  tff(c_3212, plain, (![A_197]: (k3_xboole_0(k3_xboole_0('#skF_2', A_197), u1_struct_0('#skF_1'))=k3_xboole_0(A_197, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_204, c_1745])).
% 8.94/3.49  tff(c_3231, plain, (![A_197]: (k5_xboole_0(k3_xboole_0('#skF_2', A_197), k3_xboole_0(A_197, '#skF_2'))=k4_xboole_0(k3_xboole_0('#skF_2', A_197), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_3212, c_8])).
% 8.94/3.49  tff(c_3319, plain, (![A_200]: (k5_xboole_0(k3_xboole_0('#skF_2', A_200), k3_xboole_0(A_200, '#skF_2'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1829, c_3231])).
% 8.94/3.49  tff(c_3344, plain, (k5_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_922, c_3319])).
% 8.94/3.49  tff(c_3396, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_325, c_204, c_3344])).
% 8.94/3.49  tff(c_16, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.94/3.49  tff(c_3464, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3396, c_16])).
% 8.94/3.49  tff(c_3473, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_340, c_3464])).
% 8.94/3.49  tff(c_2106, plain, (![A_161, B_162]: (k4_subset_1(u1_struct_0(A_161), B_162, k2_tops_1(A_161, B_162))=k2_pre_topc(A_161, B_162) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0(A_161))) | ~l1_pre_topc(A_161))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.94/3.49  tff(c_2122, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_2106])).
% 8.94/3.49  tff(c_2142, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2122])).
% 8.94/3.49  tff(c_917, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_869, c_12])).
% 8.94/3.49  tff(c_930, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_917, c_10])).
% 8.94/3.49  tff(c_1242, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_930, c_1232])).
% 8.94/3.49  tff(c_1638, plain, (![A_145, B_146, C_147]: (k4_subset_1(A_145, B_146, C_147)=k2_xboole_0(B_146, C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(A_145)) | ~m1_subset_1(B_146, k1_zfmisc_1(A_145)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.94/3.49  tff(c_4043, plain, (![B_220, B_221, A_222]: (k4_subset_1(B_220, B_221, A_222)=k2_xboole_0(B_221, A_222) | ~m1_subset_1(B_221, k1_zfmisc_1(B_220)) | ~r1_tarski(A_222, B_220))), inference(resolution, [status(thm)], [c_38, c_1638])).
% 8.94/3.49  tff(c_4216, plain, (![A_225]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_225)=k2_xboole_0('#skF_2', A_225) | ~r1_tarski(A_225, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_52, c_4043])).
% 8.94/3.49  tff(c_4234, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1242, c_4216])).
% 8.94/3.49  tff(c_4268, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3473, c_2142, c_4234])).
% 8.94/3.49  tff(c_4270, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1936, c_4268])).
% 8.94/3.49  tff(c_4271, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 8.94/3.49  tff(c_5304, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5249, c_4271])).
% 8.94/3.49  tff(c_4272, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 8.94/3.49  tff(c_6330, plain, (![A_340, B_341]: (r1_tarski(k2_tops_1(A_340, B_341), B_341) | ~v4_pre_topc(B_341, A_340) | ~m1_subset_1(B_341, k1_zfmisc_1(u1_struct_0(A_340))) | ~l1_pre_topc(A_340))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.94/3.49  tff(c_6346, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_6330])).
% 8.94/3.49  tff(c_6366, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4272, c_6346])).
% 8.94/3.49  tff(c_6847, plain, (![A_348, B_349]: (k7_subset_1(u1_struct_0(A_348), B_349, k2_tops_1(A_348, B_349))=k1_tops_1(A_348, B_349) | ~m1_subset_1(B_349, k1_zfmisc_1(u1_struct_0(A_348))) | ~l1_pre_topc(A_348))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.94/3.49  tff(c_6865, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_6847])).
% 8.94/3.49  tff(c_6888, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_5249, c_6865])).
% 8.94/3.49  tff(c_4900, plain, (![A_265, B_266]: (k4_xboole_0(A_265, B_266)=k3_subset_1(A_265, B_266) | ~m1_subset_1(B_266, k1_zfmisc_1(A_265)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.94/3.49  tff(c_4910, plain, (![B_34, A_33]: (k4_xboole_0(B_34, A_33)=k3_subset_1(B_34, A_33) | ~r1_tarski(A_33, B_34))), inference(resolution, [status(thm)], [c_38, c_4900])).
% 8.94/3.49  tff(c_6382, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_6366, c_4910])).
% 8.94/3.49  tff(c_14622, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6888, c_6382])).
% 8.94/3.49  tff(c_4800, plain, (![A_258, B_259]: (k3_subset_1(A_258, k3_subset_1(A_258, B_259))=B_259 | ~m1_subset_1(B_259, k1_zfmisc_1(A_258)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.94/3.49  tff(c_4807, plain, (![B_34, A_33]: (k3_subset_1(B_34, k3_subset_1(B_34, A_33))=A_33 | ~r1_tarski(A_33, B_34))), inference(resolution, [status(thm)], [c_38, c_4800])).
% 8.94/3.49  tff(c_14626, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14622, c_4807])).
% 8.94/3.49  tff(c_14630, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6366, c_14626])).
% 8.94/3.49  tff(c_6939, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6888, c_12])).
% 8.94/3.49  tff(c_6994, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_6939, c_4910])).
% 8.94/3.49  tff(c_15389, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14630, c_6994])).
% 8.94/3.49  tff(c_15390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5304, c_15389])).
% 8.94/3.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.94/3.49  
% 8.94/3.49  Inference rules
% 8.94/3.49  ----------------------
% 8.94/3.49  #Ref     : 0
% 8.94/3.49  #Sup     : 3763
% 8.94/3.49  #Fact    : 0
% 8.94/3.49  #Define  : 0
% 8.94/3.49  #Split   : 7
% 8.94/3.49  #Chain   : 0
% 8.94/3.49  #Close   : 0
% 8.94/3.49  
% 8.94/3.49  Ordering : KBO
% 8.94/3.49  
% 8.94/3.49  Simplification rules
% 8.94/3.49  ----------------------
% 8.94/3.49  #Subsume      : 118
% 8.94/3.49  #Demod        : 3067
% 8.94/3.49  #Tautology    : 1999
% 8.94/3.49  #SimpNegUnit  : 5
% 8.94/3.49  #BackRed      : 18
% 8.94/3.49  
% 8.94/3.49  #Partial instantiations: 0
% 8.94/3.49  #Strategies tried      : 1
% 8.94/3.49  
% 8.94/3.49  Timing (in seconds)
% 8.94/3.49  ----------------------
% 8.94/3.49  Preprocessing        : 0.34
% 8.94/3.49  Parsing              : 0.18
% 8.94/3.49  CNF conversion       : 0.02
% 8.94/3.49  Main loop            : 2.32
% 8.94/3.49  Inferencing          : 0.55
% 8.94/3.49  Reduction            : 1.12
% 8.94/3.49  Demodulation         : 0.92
% 8.94/3.49  BG Simplification    : 0.07
% 8.94/3.49  Subsumption          : 0.42
% 8.94/3.49  Abstraction          : 0.11
% 8.94/3.49  MUC search           : 0.00
% 8.94/3.49  Cooper               : 0.00
% 8.94/3.49  Total                : 2.71
% 8.94/3.49  Index Insertion      : 0.00
% 8.94/3.49  Index Deletion       : 0.00
% 8.94/3.49  Index Matching       : 0.00
% 8.94/3.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
