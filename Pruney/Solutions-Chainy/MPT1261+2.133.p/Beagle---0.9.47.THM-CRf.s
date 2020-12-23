%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:30 EST 2020

% Result     : Theorem 9.73s
% Output     : CNFRefutation 9.73s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 224 expanded)
%              Number of leaves         :   41 (  91 expanded)
%              Depth                    :   14
%              Number of atoms          :  179 ( 398 expanded)
%              Number of equality atoms :   88 ( 154 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_135,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_45,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_14284,plain,(
    ! [A_394,B_395,C_396] :
      ( k7_subset_1(A_394,B_395,C_396) = k4_xboole_0(B_395,C_396)
      | ~ m1_subset_1(B_395,k1_zfmisc_1(A_394)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_14290,plain,(
    ! [C_396] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_396) = k4_xboole_0('#skF_2',C_396) ),
    inference(resolution,[status(thm)],[c_50,c_14284])).

tff(c_62,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_130,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_56,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_283,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_3722,plain,(
    ! [A_175,B_176] :
      ( k4_subset_1(u1_struct_0(A_175),B_176,k2_tops_1(A_175,B_176)) = k2_pre_topc(A_175,B_176)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ l1_pre_topc(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3729,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_3722])).

tff(c_3734,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3729])).

tff(c_1892,plain,(
    ! [A_133,B_134,C_135] :
      ( k7_subset_1(A_133,B_134,C_135) = k4_xboole_0(B_134,C_135)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(A_133)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1899,plain,(
    ! [C_136] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_136) = k4_xboole_0('#skF_2',C_136) ),
    inference(resolution,[status(thm)],[c_50,c_1892])).

tff(c_1905,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1899,c_130])).

tff(c_16,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_206,plain,(
    ! [A_66,B_67] : k4_xboole_0(A_66,k4_xboole_0(A_66,B_67)) = k3_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [A_15,B_16] : r1_tarski(k4_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_121,plain,(
    ! [A_58,B_59] :
      ( k2_xboole_0(A_58,B_59) = B_59
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_150,plain,(
    ! [A_61,B_62] : k2_xboole_0(k4_xboole_0(A_61,B_62),A_61) = A_61 ),
    inference(resolution,[status(thm)],[c_20,c_121])).

tff(c_157,plain,(
    ! [B_62] : k4_xboole_0(k1_xboole_0,B_62) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_16])).

tff(c_251,plain,(
    ! [B_69] : k3_xboole_0(k1_xboole_0,B_69) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_157])).

tff(c_273,plain,(
    ! [B_2] : k3_xboole_0(B_2,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_251])).

tff(c_24,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_238,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k3_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_206])).

tff(c_461,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_238])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_197,plain,(
    ! [A_64,B_65] :
      ( k3_xboole_0(A_64,B_65) = A_64
      | ~ r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_205,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_197])).

tff(c_640,plain,(
    ! [A_87,B_88] : k5_xboole_0(A_87,k3_xboole_0(A_87,B_88)) = k4_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_655,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_640])).

tff(c_666,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_655])).

tff(c_803,plain,(
    ! [A_100,B_101] : k3_xboole_0(k4_xboole_0(A_100,B_101),A_100) = k4_xboole_0(A_100,B_101) ),
    inference(resolution,[status(thm)],[c_20,c_197])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_812,plain,(
    ! [A_100,B_101] : k5_xboole_0(k4_xboole_0(A_100,B_101),k4_xboole_0(A_100,B_101)) = k4_xboole_0(k4_xboole_0(A_100,B_101),A_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_803,c_10])).

tff(c_876,plain,(
    ! [A_102,B_103] : k4_xboole_0(k4_xboole_0(A_102,B_103),A_102) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_666,c_812])).

tff(c_22,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_890,plain,(
    ! [A_102,B_103] : k2_xboole_0(A_102,k4_xboole_0(A_102,B_103)) = k2_xboole_0(A_102,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_876,c_22])).

tff(c_929,plain,(
    ! [A_102,B_103] : k2_xboole_0(A_102,k4_xboole_0(A_102,B_103)) = A_102 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_890])).

tff(c_1928,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1905,c_929])).

tff(c_38,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(k2_tops_1(A_34,B_35),k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2685,plain,(
    ! [A_156,B_157,C_158] :
      ( k4_subset_1(A_156,B_157,C_158) = k2_xboole_0(B_157,C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(A_156))
      | ~ m1_subset_1(B_157,k1_zfmisc_1(A_156)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12437,plain,(
    ! [A_312,B_313,B_314] :
      ( k4_subset_1(u1_struct_0(A_312),B_313,k2_tops_1(A_312,B_314)) = k2_xboole_0(B_313,k2_tops_1(A_312,B_314))
      | ~ m1_subset_1(B_313,k1_zfmisc_1(u1_struct_0(A_312)))
      | ~ m1_subset_1(B_314,k1_zfmisc_1(u1_struct_0(A_312)))
      | ~ l1_pre_topc(A_312) ) ),
    inference(resolution,[status(thm)],[c_38,c_2685])).

tff(c_12444,plain,(
    ! [B_314] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_314)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_314))
      | ~ m1_subset_1(B_314,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_50,c_12437])).

tff(c_12760,plain,(
    ! [B_318] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_318)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_318))
      | ~ m1_subset_1(B_318,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_12444])).

tff(c_12771,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_12760])).

tff(c_12777,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3734,c_1928,c_12771])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2313,plain,(
    ! [A_148,B_149] :
      ( v4_pre_topc(k2_pre_topc(A_148,B_149),A_148)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ l1_pre_topc(A_148)
      | ~ v2_pre_topc(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2320,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_2313])).

tff(c_2325,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2320])).

tff(c_12779,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12777,c_2325])).

tff(c_12781,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_283,c_12779])).

tff(c_12782,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_13115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_12782])).

tff(c_13116,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_13235,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13116,c_56])).

tff(c_14429,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14290,c_13235])).

tff(c_16349,plain,(
    ! [A_447,B_448] :
      ( k4_subset_1(u1_struct_0(A_447),B_448,k2_tops_1(A_447,B_448)) = k2_pre_topc(A_447,B_448)
      | ~ m1_subset_1(B_448,k1_zfmisc_1(u1_struct_0(A_447)))
      | ~ l1_pre_topc(A_447) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_16356,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_16349])).

tff(c_16361,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_16356])).

tff(c_13236,plain,(
    ! [A_348,B_349] : k4_xboole_0(A_348,k4_xboole_0(A_348,B_349)) = k3_xboole_0(A_348,B_349) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_13137,plain,(
    ! [A_337,B_338] : k2_xboole_0(k4_xboole_0(A_337,B_338),A_337) = A_337 ),
    inference(resolution,[status(thm)],[c_20,c_121])).

tff(c_13144,plain,(
    ! [B_338] : k4_xboole_0(k1_xboole_0,B_338) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_13137,c_16])).

tff(c_13279,plain,(
    ! [B_350] : k3_xboole_0(k1_xboole_0,B_350) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_13236,c_13144])).

tff(c_13288,plain,(
    ! [B_350] : k3_xboole_0(B_350,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_13279,c_2])).

tff(c_13274,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k3_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_13236])).

tff(c_13562,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13288,c_13274])).

tff(c_13184,plain,(
    ! [A_340,B_341] :
      ( k3_xboole_0(A_340,B_341) = A_340
      | ~ r1_tarski(A_340,B_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_13192,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_13184])).

tff(c_13355,plain,(
    ! [A_352,B_353] : k5_xboole_0(A_352,k3_xboole_0(A_352,B_353)) = k4_xboole_0(A_352,B_353) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_13370,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_13192,c_13355])).

tff(c_13608,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13562,c_13370])).

tff(c_15536,plain,(
    ! [A_432,B_433] :
      ( r1_tarski(k2_tops_1(A_432,B_433),B_433)
      | ~ v4_pre_topc(B_433,A_432)
      | ~ m1_subset_1(B_433,k1_zfmisc_1(u1_struct_0(A_432)))
      | ~ l1_pre_topc(A_432) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_15543,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_15536])).

tff(c_15548,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_13116,c_15543])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_15558,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_15548,c_18])).

tff(c_15627,plain,(
    k5_xboole_0(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_15558,c_10])).

tff(c_15655,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13608,c_15627])).

tff(c_15691,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_15655,c_22])).

tff(c_15711,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_15691])).

tff(c_15909,plain,(
    ! [A_436,B_437,C_438] :
      ( k4_subset_1(A_436,B_437,C_438) = k2_xboole_0(B_437,C_438)
      | ~ m1_subset_1(C_438,k1_zfmisc_1(A_436))
      | ~ m1_subset_1(B_437,k1_zfmisc_1(A_436)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_23844,plain,(
    ! [A_576,B_577,B_578] :
      ( k4_subset_1(u1_struct_0(A_576),B_577,k2_tops_1(A_576,B_578)) = k2_xboole_0(B_577,k2_tops_1(A_576,B_578))
      | ~ m1_subset_1(B_577,k1_zfmisc_1(u1_struct_0(A_576)))
      | ~ m1_subset_1(B_578,k1_zfmisc_1(u1_struct_0(A_576)))
      | ~ l1_pre_topc(A_576) ) ),
    inference(resolution,[status(thm)],[c_38,c_15909])).

tff(c_23851,plain,(
    ! [B_578] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_578)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_578))
      | ~ m1_subset_1(B_578,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_50,c_23844])).

tff(c_24659,plain,(
    ! [B_585] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_585)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_585))
      | ~ m1_subset_1(B_585,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_23851])).

tff(c_24670,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_24659])).

tff(c_24676,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16361,c_15711,c_24670])).

tff(c_42,plain,(
    ! [A_38,B_40] :
      ( k7_subset_1(u1_struct_0(A_38),k2_pre_topc(A_38,B_40),k1_tops_1(A_38,B_40)) = k2_tops_1(A_38,B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_24683,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24676,c_42])).

tff(c_24687,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_14290,c_24683])).

tff(c_24689,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14429,c_24687])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:13:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.73/4.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.73/4.06  
% 9.73/4.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.73/4.06  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 9.73/4.06  
% 9.73/4.06  %Foreground sorts:
% 9.73/4.06  
% 9.73/4.06  
% 9.73/4.06  %Background operators:
% 9.73/4.06  
% 9.73/4.06  
% 9.73/4.06  %Foreground operators:
% 9.73/4.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.73/4.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.73/4.06  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 9.73/4.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.73/4.06  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.73/4.06  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.73/4.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.73/4.06  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 9.73/4.06  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 9.73/4.06  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 9.73/4.06  tff('#skF_2', type, '#skF_2': $i).
% 9.73/4.06  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 9.73/4.06  tff('#skF_1', type, '#skF_1': $i).
% 9.73/4.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.73/4.06  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 9.73/4.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.73/4.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.73/4.06  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.73/4.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.73/4.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.73/4.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.73/4.06  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 9.73/4.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.73/4.06  
% 9.73/4.08  tff(f_135, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 9.73/4.08  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 9.73/4.08  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 9.73/4.08  tff(f_45, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 9.73/4.08  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.73/4.08  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.73/4.08  tff(f_51, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 9.73/4.08  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 9.73/4.08  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 9.73/4.08  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.73/4.08  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.73/4.08  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.73/4.08  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 9.73/4.08  tff(f_85, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 9.73/4.08  tff(f_75, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 9.73/4.08  tff(f_93, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 9.73/4.08  tff(f_123, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 9.73/4.08  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 9.73/4.08  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.73/4.08  tff(c_14284, plain, (![A_394, B_395, C_396]: (k7_subset_1(A_394, B_395, C_396)=k4_xboole_0(B_395, C_396) | ~m1_subset_1(B_395, k1_zfmisc_1(A_394)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.73/4.08  tff(c_14290, plain, (![C_396]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_396)=k4_xboole_0('#skF_2', C_396))), inference(resolution, [status(thm)], [c_50, c_14284])).
% 9.73/4.08  tff(c_62, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.73/4.08  tff(c_130, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_62])).
% 9.73/4.08  tff(c_56, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.73/4.08  tff(c_283, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_56])).
% 9.73/4.08  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.73/4.08  tff(c_3722, plain, (![A_175, B_176]: (k4_subset_1(u1_struct_0(A_175), B_176, k2_tops_1(A_175, B_176))=k2_pre_topc(A_175, B_176) | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0(A_175))) | ~l1_pre_topc(A_175))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.73/4.08  tff(c_3729, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_3722])).
% 9.73/4.08  tff(c_3734, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3729])).
% 9.73/4.08  tff(c_1892, plain, (![A_133, B_134, C_135]: (k7_subset_1(A_133, B_134, C_135)=k4_xboole_0(B_134, C_135) | ~m1_subset_1(B_134, k1_zfmisc_1(A_133)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.73/4.08  tff(c_1899, plain, (![C_136]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_136)=k4_xboole_0('#skF_2', C_136))), inference(resolution, [status(thm)], [c_50, c_1892])).
% 9.73/4.08  tff(c_1905, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1899, c_130])).
% 9.73/4.08  tff(c_16, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.73/4.08  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.73/4.08  tff(c_206, plain, (![A_66, B_67]: (k4_xboole_0(A_66, k4_xboole_0(A_66, B_67))=k3_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.73/4.08  tff(c_20, plain, (![A_15, B_16]: (r1_tarski(k4_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.73/4.08  tff(c_121, plain, (![A_58, B_59]: (k2_xboole_0(A_58, B_59)=B_59 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.73/4.08  tff(c_150, plain, (![A_61, B_62]: (k2_xboole_0(k4_xboole_0(A_61, B_62), A_61)=A_61)), inference(resolution, [status(thm)], [c_20, c_121])).
% 9.73/4.08  tff(c_157, plain, (![B_62]: (k4_xboole_0(k1_xboole_0, B_62)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_150, c_16])).
% 9.73/4.08  tff(c_251, plain, (![B_69]: (k3_xboole_0(k1_xboole_0, B_69)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_206, c_157])).
% 9.73/4.08  tff(c_273, plain, (![B_2]: (k3_xboole_0(B_2, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_251])).
% 9.73/4.08  tff(c_24, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.73/4.08  tff(c_238, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k3_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_206])).
% 9.73/4.08  tff(c_461, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_273, c_238])).
% 9.73/4.08  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.73/4.08  tff(c_197, plain, (![A_64, B_65]: (k3_xboole_0(A_64, B_65)=A_64 | ~r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.73/4.08  tff(c_205, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_197])).
% 9.73/4.08  tff(c_640, plain, (![A_87, B_88]: (k5_xboole_0(A_87, k3_xboole_0(A_87, B_88))=k4_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.73/4.08  tff(c_655, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_205, c_640])).
% 9.73/4.08  tff(c_666, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_461, c_655])).
% 9.73/4.08  tff(c_803, plain, (![A_100, B_101]: (k3_xboole_0(k4_xboole_0(A_100, B_101), A_100)=k4_xboole_0(A_100, B_101))), inference(resolution, [status(thm)], [c_20, c_197])).
% 9.73/4.08  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.73/4.08  tff(c_812, plain, (![A_100, B_101]: (k5_xboole_0(k4_xboole_0(A_100, B_101), k4_xboole_0(A_100, B_101))=k4_xboole_0(k4_xboole_0(A_100, B_101), A_100))), inference(superposition, [status(thm), theory('equality')], [c_803, c_10])).
% 9.73/4.08  tff(c_876, plain, (![A_102, B_103]: (k4_xboole_0(k4_xboole_0(A_102, B_103), A_102)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_666, c_812])).
% 9.73/4.08  tff(c_22, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.73/4.08  tff(c_890, plain, (![A_102, B_103]: (k2_xboole_0(A_102, k4_xboole_0(A_102, B_103))=k2_xboole_0(A_102, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_876, c_22])).
% 9.73/4.08  tff(c_929, plain, (![A_102, B_103]: (k2_xboole_0(A_102, k4_xboole_0(A_102, B_103))=A_102)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_890])).
% 9.73/4.08  tff(c_1928, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1905, c_929])).
% 9.73/4.08  tff(c_38, plain, (![A_34, B_35]: (m1_subset_1(k2_tops_1(A_34, B_35), k1_zfmisc_1(u1_struct_0(A_34))) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.73/4.08  tff(c_2685, plain, (![A_156, B_157, C_158]: (k4_subset_1(A_156, B_157, C_158)=k2_xboole_0(B_157, C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(A_156)) | ~m1_subset_1(B_157, k1_zfmisc_1(A_156)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.73/4.08  tff(c_12437, plain, (![A_312, B_313, B_314]: (k4_subset_1(u1_struct_0(A_312), B_313, k2_tops_1(A_312, B_314))=k2_xboole_0(B_313, k2_tops_1(A_312, B_314)) | ~m1_subset_1(B_313, k1_zfmisc_1(u1_struct_0(A_312))) | ~m1_subset_1(B_314, k1_zfmisc_1(u1_struct_0(A_312))) | ~l1_pre_topc(A_312))), inference(resolution, [status(thm)], [c_38, c_2685])).
% 9.73/4.08  tff(c_12444, plain, (![B_314]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_314))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_314)) | ~m1_subset_1(B_314, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_50, c_12437])).
% 9.73/4.08  tff(c_12760, plain, (![B_318]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_318))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_318)) | ~m1_subset_1(B_318, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_12444])).
% 9.73/4.08  tff(c_12771, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_12760])).
% 9.73/4.08  tff(c_12777, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3734, c_1928, c_12771])).
% 9.73/4.08  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.73/4.08  tff(c_2313, plain, (![A_148, B_149]: (v4_pre_topc(k2_pre_topc(A_148, B_149), A_148) | ~m1_subset_1(B_149, k1_zfmisc_1(u1_struct_0(A_148))) | ~l1_pre_topc(A_148) | ~v2_pre_topc(A_148))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.73/4.08  tff(c_2320, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_2313])).
% 9.73/4.08  tff(c_2325, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_2320])).
% 9.73/4.08  tff(c_12779, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12777, c_2325])).
% 9.73/4.08  tff(c_12781, plain, $false, inference(negUnitSimplification, [status(thm)], [c_283, c_12779])).
% 9.73/4.08  tff(c_12782, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 9.73/4.08  tff(c_13115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_12782])).
% 9.73/4.08  tff(c_13116, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_62])).
% 9.73/4.08  tff(c_13235, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13116, c_56])).
% 9.73/4.08  tff(c_14429, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14290, c_13235])).
% 9.73/4.08  tff(c_16349, plain, (![A_447, B_448]: (k4_subset_1(u1_struct_0(A_447), B_448, k2_tops_1(A_447, B_448))=k2_pre_topc(A_447, B_448) | ~m1_subset_1(B_448, k1_zfmisc_1(u1_struct_0(A_447))) | ~l1_pre_topc(A_447))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.73/4.08  tff(c_16356, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_16349])).
% 9.73/4.08  tff(c_16361, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_16356])).
% 9.73/4.08  tff(c_13236, plain, (![A_348, B_349]: (k4_xboole_0(A_348, k4_xboole_0(A_348, B_349))=k3_xboole_0(A_348, B_349))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.73/4.08  tff(c_13137, plain, (![A_337, B_338]: (k2_xboole_0(k4_xboole_0(A_337, B_338), A_337)=A_337)), inference(resolution, [status(thm)], [c_20, c_121])).
% 9.73/4.08  tff(c_13144, plain, (![B_338]: (k4_xboole_0(k1_xboole_0, B_338)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13137, c_16])).
% 9.73/4.08  tff(c_13279, plain, (![B_350]: (k3_xboole_0(k1_xboole_0, B_350)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13236, c_13144])).
% 9.73/4.08  tff(c_13288, plain, (![B_350]: (k3_xboole_0(B_350, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13279, c_2])).
% 9.73/4.08  tff(c_13274, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k3_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_13236])).
% 9.73/4.08  tff(c_13562, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_13288, c_13274])).
% 9.73/4.08  tff(c_13184, plain, (![A_340, B_341]: (k3_xboole_0(A_340, B_341)=A_340 | ~r1_tarski(A_340, B_341))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.73/4.08  tff(c_13192, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_13184])).
% 9.73/4.08  tff(c_13355, plain, (![A_352, B_353]: (k5_xboole_0(A_352, k3_xboole_0(A_352, B_353))=k4_xboole_0(A_352, B_353))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.73/4.08  tff(c_13370, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_13192, c_13355])).
% 9.73/4.08  tff(c_13608, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_13562, c_13370])).
% 9.73/4.08  tff(c_15536, plain, (![A_432, B_433]: (r1_tarski(k2_tops_1(A_432, B_433), B_433) | ~v4_pre_topc(B_433, A_432) | ~m1_subset_1(B_433, k1_zfmisc_1(u1_struct_0(A_432))) | ~l1_pre_topc(A_432))), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.73/4.08  tff(c_15543, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_15536])).
% 9.73/4.08  tff(c_15548, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_13116, c_15543])).
% 9.73/4.08  tff(c_18, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.73/4.08  tff(c_15558, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_15548, c_18])).
% 9.73/4.08  tff(c_15627, plain, (k5_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_15558, c_10])).
% 9.73/4.08  tff(c_15655, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_13608, c_15627])).
% 9.73/4.08  tff(c_15691, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_15655, c_22])).
% 9.73/4.08  tff(c_15711, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_15691])).
% 9.73/4.08  tff(c_15909, plain, (![A_436, B_437, C_438]: (k4_subset_1(A_436, B_437, C_438)=k2_xboole_0(B_437, C_438) | ~m1_subset_1(C_438, k1_zfmisc_1(A_436)) | ~m1_subset_1(B_437, k1_zfmisc_1(A_436)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.73/4.08  tff(c_23844, plain, (![A_576, B_577, B_578]: (k4_subset_1(u1_struct_0(A_576), B_577, k2_tops_1(A_576, B_578))=k2_xboole_0(B_577, k2_tops_1(A_576, B_578)) | ~m1_subset_1(B_577, k1_zfmisc_1(u1_struct_0(A_576))) | ~m1_subset_1(B_578, k1_zfmisc_1(u1_struct_0(A_576))) | ~l1_pre_topc(A_576))), inference(resolution, [status(thm)], [c_38, c_15909])).
% 9.73/4.08  tff(c_23851, plain, (![B_578]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_578))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_578)) | ~m1_subset_1(B_578, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_50, c_23844])).
% 9.73/4.08  tff(c_24659, plain, (![B_585]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_585))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_585)) | ~m1_subset_1(B_585, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_23851])).
% 9.73/4.08  tff(c_24670, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_24659])).
% 9.73/4.08  tff(c_24676, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_16361, c_15711, c_24670])).
% 9.73/4.08  tff(c_42, plain, (![A_38, B_40]: (k7_subset_1(u1_struct_0(A_38), k2_pre_topc(A_38, B_40), k1_tops_1(A_38, B_40))=k2_tops_1(A_38, B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.73/4.08  tff(c_24683, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24676, c_42])).
% 9.73/4.08  tff(c_24687, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_14290, c_24683])).
% 9.73/4.08  tff(c_24689, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14429, c_24687])).
% 9.73/4.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.73/4.08  
% 9.73/4.08  Inference rules
% 9.73/4.08  ----------------------
% 9.73/4.08  #Ref     : 0
% 9.73/4.08  #Sup     : 6195
% 9.73/4.08  #Fact    : 0
% 9.73/4.08  #Define  : 0
% 9.73/4.08  #Split   : 12
% 9.73/4.08  #Chain   : 0
% 9.73/4.08  #Close   : 0
% 9.73/4.08  
% 9.73/4.08  Ordering : KBO
% 9.73/4.08  
% 9.73/4.08  Simplification rules
% 9.73/4.08  ----------------------
% 9.73/4.08  #Subsume      : 1291
% 9.73/4.08  #Demod        : 4646
% 9.73/4.08  #Tautology    : 3264
% 9.73/4.08  #SimpNegUnit  : 2
% 9.73/4.08  #BackRed      : 11
% 9.73/4.08  
% 9.73/4.08  #Partial instantiations: 0
% 9.73/4.08  #Strategies tried      : 1
% 9.73/4.08  
% 9.73/4.08  Timing (in seconds)
% 9.73/4.08  ----------------------
% 9.73/4.08  Preprocessing        : 0.33
% 9.73/4.08  Parsing              : 0.17
% 9.73/4.08  CNF conversion       : 0.02
% 9.73/4.08  Main loop            : 2.81
% 9.73/4.08  Inferencing          : 0.64
% 9.73/4.08  Reduction            : 1.36
% 9.73/4.08  Demodulation         : 1.14
% 9.73/4.08  BG Simplification    : 0.07
% 9.73/4.08  Subsumption          : 0.58
% 9.73/4.08  Abstraction          : 0.11
% 9.73/4.08  MUC search           : 0.00
% 9.73/4.08  Cooper               : 0.00
% 9.73/4.08  Total                : 3.18
% 9.73/4.08  Index Insertion      : 0.00
% 9.73/4.08  Index Deletion       : 0.00
% 9.73/4.08  Index Matching       : 0.00
% 9.73/4.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
