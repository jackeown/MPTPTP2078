%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:24 EST 2020

% Result     : Theorem 11.80s
% Output     : CNFRefutation 11.80s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 167 expanded)
%              Number of leaves         :   42 (  73 expanded)
%              Depth                    :   14
%              Number of atoms          :  145 ( 300 expanded)
%              Number of equality atoms :   69 ( 114 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_61,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_33814,plain,(
    ! [A_543,B_544,C_545] :
      ( k7_subset_1(A_543,B_544,C_545) = k4_xboole_0(B_544,C_545)
      | ~ m1_subset_1(B_544,k1_zfmisc_1(A_543)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_33822,plain,(
    ! [C_545] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_545) = k4_xboole_0('#skF_2',C_545) ),
    inference(resolution,[status(thm)],[c_50,c_33814])).

tff(c_62,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_160,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_56,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_221,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2733,plain,(
    ! [B_162,A_163] :
      ( v4_pre_topc(B_162,A_163)
      | k2_pre_topc(A_163,B_162) != B_162
      | ~ v2_pre_topc(A_163)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ l1_pre_topc(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2743,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_2733])).

tff(c_2752,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54,c_2743])).

tff(c_2753,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_2752])).

tff(c_12,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_910,plain,(
    ! [A_100,B_101,C_102] :
      ( k7_subset_1(A_100,B_101,C_102) = k4_xboole_0(B_101,C_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1115,plain,(
    ! [C_116] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_116) = k4_xboole_0('#skF_2',C_116) ),
    inference(resolution,[status(thm)],[c_50,c_910])).

tff(c_1121,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1115,c_160])).

tff(c_18,plain,(
    ! [A_12,B_13,C_14] : k4_xboole_0(k4_xboole_0(A_12,B_13),C_14) = k4_xboole_0(A_12,k2_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3787,plain,(
    ! [C_182] : k4_xboole_0('#skF_2',k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_182)) = k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),C_182) ),
    inference(superposition,[status(thm),theory(equality)],[c_1121,c_18])).

tff(c_16,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_280,plain,(
    ! [A_70,B_71] : k4_xboole_0(A_70,k4_xboole_0(A_70,B_71)) = k3_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_30,plain,(
    ! [A_27] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_207,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(A_61,B_62)
      | ~ m1_subset_1(A_61,k1_zfmisc_1(B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_219,plain,(
    ! [A_27] : r1_tarski(k1_xboole_0,A_27) ),
    inference(resolution,[status(thm)],[c_30,c_207])).

tff(c_231,plain,(
    ! [B_66,A_67] :
      ( B_66 = A_67
      | ~ r1_tarski(B_66,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_247,plain,(
    ! [A_68] :
      ( k1_xboole_0 = A_68
      | ~ r1_tarski(A_68,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_219,c_231])).

tff(c_262,plain,(
    ! [B_9] : k4_xboole_0(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_247])).

tff(c_323,plain,(
    ! [B_73] : k3_xboole_0(k1_xboole_0,B_73) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_262])).

tff(c_341,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_323])).

tff(c_76,plain,(
    ! [B_52,A_53] : k2_xboole_0(B_52,A_53) = k2_xboole_0(A_53,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_92,plain,(
    ! [A_53] : k2_xboole_0(k1_xboole_0,A_53) = A_53 ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_12])).

tff(c_386,plain,(
    ! [A_75,B_76] : k2_xboole_0(A_75,k4_xboole_0(B_76,A_75)) = k2_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_393,plain,(
    ! [B_76] : k4_xboole_0(B_76,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_92])).

tff(c_413,plain,(
    ! [B_77] : k4_xboole_0(B_77,k1_xboole_0) = B_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_393])).

tff(c_20,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_422,plain,(
    ! [B_77] : k4_xboole_0(B_77,B_77) = k3_xboole_0(B_77,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_20])).

tff(c_442,plain,(
    ! [B_77] : k4_xboole_0(B_77,B_77) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_422])).

tff(c_579,plain,(
    ! [A_82,B_83,C_84] : k4_xboole_0(k4_xboole_0(A_82,B_83),C_84) = k4_xboole_0(A_82,k2_xboole_0(B_83,C_84)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_622,plain,(
    ! [A_82,B_83] : k4_xboole_0(A_82,k2_xboole_0(B_83,k4_xboole_0(A_82,B_83))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_579])).

tff(c_648,plain,(
    ! [A_82,B_83] : k4_xboole_0(A_82,k2_xboole_0(B_83,A_82)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_622])).

tff(c_3814,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3787,c_648])).

tff(c_3902,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3814,c_16])).

tff(c_3919,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3902])).

tff(c_3296,plain,(
    ! [A_171,B_172] :
      ( k4_subset_1(u1_struct_0(A_171),B_172,k2_tops_1(A_171,B_172)) = k2_pre_topc(A_171,B_172)
      | ~ m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ l1_pre_topc(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3303,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_3296])).

tff(c_3311,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3303])).

tff(c_42,plain,(
    ! [A_36,B_37] :
      ( m1_subset_1(k2_tops_1(A_36,B_37),k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2539,plain,(
    ! [A_152,B_153,C_154] :
      ( k4_subset_1(A_152,B_153,C_154) = k2_xboole_0(B_153,C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(A_152))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(A_152)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_32789,plain,(
    ! [A_475,B_476,B_477] :
      ( k4_subset_1(u1_struct_0(A_475),B_476,k2_tops_1(A_475,B_477)) = k2_xboole_0(B_476,k2_tops_1(A_475,B_477))
      | ~ m1_subset_1(B_476,k1_zfmisc_1(u1_struct_0(A_475)))
      | ~ m1_subset_1(B_477,k1_zfmisc_1(u1_struct_0(A_475)))
      | ~ l1_pre_topc(A_475) ) ),
    inference(resolution,[status(thm)],[c_42,c_2539])).

tff(c_32796,plain,(
    ! [B_477] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_477)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_477))
      | ~ m1_subset_1(B_477,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_50,c_32789])).

tff(c_32810,plain,(
    ! [B_478] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_478)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_478))
      | ~ m1_subset_1(B_478,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_32796])).

tff(c_32821,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_32810])).

tff(c_32831,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3919,c_3311,c_32821])).

tff(c_32833,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2753,c_32831])).

tff(c_32834,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_33377,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_32834])).

tff(c_33378,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_33432,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33378,c_56])).

tff(c_34156,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33822,c_33432])).

tff(c_34282,plain,(
    ! [A_569,B_570] :
      ( k2_pre_topc(A_569,B_570) = B_570
      | ~ v4_pre_topc(B_570,A_569)
      | ~ m1_subset_1(B_570,k1_zfmisc_1(u1_struct_0(A_569)))
      | ~ l1_pre_topc(A_569) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34292,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_34282])).

tff(c_34301,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_33378,c_34292])).

tff(c_35809,plain,(
    ! [A_609,B_610] :
      ( k7_subset_1(u1_struct_0(A_609),k2_pre_topc(A_609,B_610),k1_tops_1(A_609,B_610)) = k2_tops_1(A_609,B_610)
      | ~ m1_subset_1(B_610,k1_zfmisc_1(u1_struct_0(A_609)))
      | ~ l1_pre_topc(A_609) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_35818,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_34301,c_35809])).

tff(c_35822,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_33822,c_35818])).

tff(c_35824,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34156,c_35822])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:18:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.80/5.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.80/5.41  
% 11.80/5.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.80/5.41  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 11.80/5.41  
% 11.80/5.41  %Foreground sorts:
% 11.80/5.41  
% 11.80/5.41  
% 11.80/5.41  %Background operators:
% 11.80/5.41  
% 11.80/5.41  
% 11.80/5.41  %Foreground operators:
% 11.80/5.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.80/5.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.80/5.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.80/5.41  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 11.80/5.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.80/5.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.80/5.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.80/5.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.80/5.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.80/5.41  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 11.80/5.41  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 11.80/5.41  tff('#skF_2', type, '#skF_2': $i).
% 11.80/5.41  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 11.80/5.41  tff('#skF_1', type, '#skF_1': $i).
% 11.80/5.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.80/5.41  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 11.80/5.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.80/5.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.80/5.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.80/5.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.80/5.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.80/5.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.80/5.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.80/5.41  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 11.80/5.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.80/5.41  
% 11.80/5.43  tff(f_126, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 11.80/5.43  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 11.80/5.43  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 11.80/5.43  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 11.80/5.43  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 11.80/5.43  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 11.80/5.43  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.80/5.43  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.80/5.43  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.80/5.43  tff(f_61, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 11.80/5.43  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.80/5.43  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.80/5.43  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 11.80/5.43  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 11.80/5.43  tff(f_92, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 11.80/5.43  tff(f_55, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 11.80/5.43  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 11.80/5.43  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 11.80/5.43  tff(c_33814, plain, (![A_543, B_544, C_545]: (k7_subset_1(A_543, B_544, C_545)=k4_xboole_0(B_544, C_545) | ~m1_subset_1(B_544, k1_zfmisc_1(A_543)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.80/5.43  tff(c_33822, plain, (![C_545]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_545)=k4_xboole_0('#skF_2', C_545))), inference(resolution, [status(thm)], [c_50, c_33814])).
% 11.80/5.43  tff(c_62, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 11.80/5.43  tff(c_160, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_62])).
% 11.80/5.43  tff(c_56, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 11.80/5.43  tff(c_221, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_56])).
% 11.80/5.43  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 11.80/5.43  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 11.80/5.43  tff(c_2733, plain, (![B_162, A_163]: (v4_pre_topc(B_162, A_163) | k2_pre_topc(A_163, B_162)!=B_162 | ~v2_pre_topc(A_163) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0(A_163))) | ~l1_pre_topc(A_163))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.80/5.43  tff(c_2743, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_2733])).
% 11.80/5.43  tff(c_2752, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54, c_2743])).
% 11.80/5.43  tff(c_2753, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_221, c_2752])).
% 11.80/5.43  tff(c_12, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.80/5.43  tff(c_910, plain, (![A_100, B_101, C_102]: (k7_subset_1(A_100, B_101, C_102)=k4_xboole_0(B_101, C_102) | ~m1_subset_1(B_101, k1_zfmisc_1(A_100)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.80/5.43  tff(c_1115, plain, (![C_116]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_116)=k4_xboole_0('#skF_2', C_116))), inference(resolution, [status(thm)], [c_50, c_910])).
% 11.80/5.43  tff(c_1121, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1115, c_160])).
% 11.80/5.43  tff(c_18, plain, (![A_12, B_13, C_14]: (k4_xboole_0(k4_xboole_0(A_12, B_13), C_14)=k4_xboole_0(A_12, k2_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.80/5.43  tff(c_3787, plain, (![C_182]: (k4_xboole_0('#skF_2', k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_182))=k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), C_182))), inference(superposition, [status(thm), theory('equality')], [c_1121, c_18])).
% 11.80/5.43  tff(c_16, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.80/5.43  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.80/5.43  tff(c_280, plain, (![A_70, B_71]: (k4_xboole_0(A_70, k4_xboole_0(A_70, B_71))=k3_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.80/5.43  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.80/5.43  tff(c_30, plain, (![A_27]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.80/5.43  tff(c_207, plain, (![A_61, B_62]: (r1_tarski(A_61, B_62) | ~m1_subset_1(A_61, k1_zfmisc_1(B_62)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.80/5.43  tff(c_219, plain, (![A_27]: (r1_tarski(k1_xboole_0, A_27))), inference(resolution, [status(thm)], [c_30, c_207])).
% 11.80/5.43  tff(c_231, plain, (![B_66, A_67]: (B_66=A_67 | ~r1_tarski(B_66, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.80/5.43  tff(c_247, plain, (![A_68]: (k1_xboole_0=A_68 | ~r1_tarski(A_68, k1_xboole_0))), inference(resolution, [status(thm)], [c_219, c_231])).
% 11.80/5.43  tff(c_262, plain, (![B_9]: (k4_xboole_0(k1_xboole_0, B_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_247])).
% 11.80/5.43  tff(c_323, plain, (![B_73]: (k3_xboole_0(k1_xboole_0, B_73)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_280, c_262])).
% 11.80/5.43  tff(c_341, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_323])).
% 11.80/5.43  tff(c_76, plain, (![B_52, A_53]: (k2_xboole_0(B_52, A_53)=k2_xboole_0(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.80/5.43  tff(c_92, plain, (![A_53]: (k2_xboole_0(k1_xboole_0, A_53)=A_53)), inference(superposition, [status(thm), theory('equality')], [c_76, c_12])).
% 11.80/5.43  tff(c_386, plain, (![A_75, B_76]: (k2_xboole_0(A_75, k4_xboole_0(B_76, A_75))=k2_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.80/5.43  tff(c_393, plain, (![B_76]: (k4_xboole_0(B_76, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_76))), inference(superposition, [status(thm), theory('equality')], [c_386, c_92])).
% 11.80/5.43  tff(c_413, plain, (![B_77]: (k4_xboole_0(B_77, k1_xboole_0)=B_77)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_393])).
% 11.80/5.43  tff(c_20, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.80/5.43  tff(c_422, plain, (![B_77]: (k4_xboole_0(B_77, B_77)=k3_xboole_0(B_77, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_413, c_20])).
% 11.80/5.43  tff(c_442, plain, (![B_77]: (k4_xboole_0(B_77, B_77)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_341, c_422])).
% 11.80/5.43  tff(c_579, plain, (![A_82, B_83, C_84]: (k4_xboole_0(k4_xboole_0(A_82, B_83), C_84)=k4_xboole_0(A_82, k2_xboole_0(B_83, C_84)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.80/5.43  tff(c_622, plain, (![A_82, B_83]: (k4_xboole_0(A_82, k2_xboole_0(B_83, k4_xboole_0(A_82, B_83)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_442, c_579])).
% 11.80/5.43  tff(c_648, plain, (![A_82, B_83]: (k4_xboole_0(A_82, k2_xboole_0(B_83, A_82))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_622])).
% 11.80/5.43  tff(c_3814, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3787, c_648])).
% 11.80/5.43  tff(c_3902, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3814, c_16])).
% 11.80/5.43  tff(c_3919, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_3902])).
% 11.80/5.43  tff(c_3296, plain, (![A_171, B_172]: (k4_subset_1(u1_struct_0(A_171), B_172, k2_tops_1(A_171, B_172))=k2_pre_topc(A_171, B_172) | ~m1_subset_1(B_172, k1_zfmisc_1(u1_struct_0(A_171))) | ~l1_pre_topc(A_171))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.80/5.43  tff(c_3303, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_3296])).
% 11.80/5.43  tff(c_3311, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3303])).
% 11.80/5.43  tff(c_42, plain, (![A_36, B_37]: (m1_subset_1(k2_tops_1(A_36, B_37), k1_zfmisc_1(u1_struct_0(A_36))) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.80/5.43  tff(c_2539, plain, (![A_152, B_153, C_154]: (k4_subset_1(A_152, B_153, C_154)=k2_xboole_0(B_153, C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(A_152)) | ~m1_subset_1(B_153, k1_zfmisc_1(A_152)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.80/5.43  tff(c_32789, plain, (![A_475, B_476, B_477]: (k4_subset_1(u1_struct_0(A_475), B_476, k2_tops_1(A_475, B_477))=k2_xboole_0(B_476, k2_tops_1(A_475, B_477)) | ~m1_subset_1(B_476, k1_zfmisc_1(u1_struct_0(A_475))) | ~m1_subset_1(B_477, k1_zfmisc_1(u1_struct_0(A_475))) | ~l1_pre_topc(A_475))), inference(resolution, [status(thm)], [c_42, c_2539])).
% 11.80/5.43  tff(c_32796, plain, (![B_477]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_477))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_477)) | ~m1_subset_1(B_477, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_50, c_32789])).
% 11.80/5.43  tff(c_32810, plain, (![B_478]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_478))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_478)) | ~m1_subset_1(B_478, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_32796])).
% 11.80/5.43  tff(c_32821, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_32810])).
% 11.80/5.43  tff(c_32831, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3919, c_3311, c_32821])).
% 11.80/5.43  tff(c_32833, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2753, c_32831])).
% 11.80/5.43  tff(c_32834, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 11.80/5.43  tff(c_33377, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_160, c_32834])).
% 11.80/5.43  tff(c_33378, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_62])).
% 11.80/5.43  tff(c_33432, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_33378, c_56])).
% 11.80/5.43  tff(c_34156, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_33822, c_33432])).
% 11.80/5.43  tff(c_34282, plain, (![A_569, B_570]: (k2_pre_topc(A_569, B_570)=B_570 | ~v4_pre_topc(B_570, A_569) | ~m1_subset_1(B_570, k1_zfmisc_1(u1_struct_0(A_569))) | ~l1_pre_topc(A_569))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.80/5.43  tff(c_34292, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_34282])).
% 11.80/5.43  tff(c_34301, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_33378, c_34292])).
% 11.80/5.43  tff(c_35809, plain, (![A_609, B_610]: (k7_subset_1(u1_struct_0(A_609), k2_pre_topc(A_609, B_610), k1_tops_1(A_609, B_610))=k2_tops_1(A_609, B_610) | ~m1_subset_1(B_610, k1_zfmisc_1(u1_struct_0(A_609))) | ~l1_pre_topc(A_609))), inference(cnfTransformation, [status(thm)], [f_107])).
% 11.80/5.43  tff(c_35818, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_34301, c_35809])).
% 11.80/5.43  tff(c_35822, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_33822, c_35818])).
% 11.80/5.43  tff(c_35824, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34156, c_35822])).
% 11.80/5.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.80/5.43  
% 11.80/5.43  Inference rules
% 11.80/5.43  ----------------------
% 11.80/5.43  #Ref     : 0
% 11.80/5.43  #Sup     : 8907
% 11.80/5.43  #Fact    : 0
% 11.80/5.43  #Define  : 0
% 11.80/5.43  #Split   : 6
% 11.80/5.43  #Chain   : 0
% 11.80/5.43  #Close   : 0
% 11.80/5.43  
% 11.80/5.43  Ordering : KBO
% 11.80/5.43  
% 11.80/5.43  Simplification rules
% 11.80/5.43  ----------------------
% 11.80/5.43  #Subsume      : 69
% 11.80/5.43  #Demod        : 9336
% 11.80/5.43  #Tautology    : 6307
% 11.80/5.43  #SimpNegUnit  : 5
% 11.80/5.43  #BackRed      : 4
% 11.80/5.43  
% 11.80/5.43  #Partial instantiations: 0
% 11.80/5.43  #Strategies tried      : 1
% 11.80/5.43  
% 11.80/5.43  Timing (in seconds)
% 11.80/5.43  ----------------------
% 11.80/5.43  Preprocessing        : 0.37
% 11.80/5.43  Parsing              : 0.20
% 11.80/5.43  CNF conversion       : 0.03
% 11.80/5.43  Main loop            : 4.23
% 11.80/5.43  Inferencing          : 0.76
% 11.80/5.43  Reduction            : 2.44
% 11.80/5.43  Demodulation         : 2.16
% 11.80/5.43  BG Simplification    : 0.09
% 11.80/5.43  Subsumption          : 0.72
% 11.80/5.43  Abstraction          : 0.16
% 11.80/5.43  MUC search           : 0.00
% 11.80/5.43  Cooper               : 0.00
% 11.80/5.43  Total                : 4.63
% 11.80/5.43  Index Insertion      : 0.00
% 11.80/5.43  Index Deletion       : 0.00
% 11.80/5.43  Index Matching       : 0.00
% 11.80/5.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
