%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:56 EST 2020

% Result     : Theorem 10.86s
% Output     : CNFRefutation 11.14s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 466 expanded)
%              Number of leaves         :   39 ( 172 expanded)
%              Depth                    :   13
%              Number of atoms          :  260 ( 911 expanded)
%              Number of equality atoms :   99 ( 253 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_133,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_124,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_91,axiom,(
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

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_95,plain,(
    ! [A_59,B_60] :
      ( k3_xboole_0(A_59,B_60) = A_59
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_103,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_95])).

tff(c_113,plain,(
    ! [A_62,B_63] :
      ( k4_xboole_0(A_62,B_63) = k1_xboole_0
      | ~ r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_121,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_113])).

tff(c_18454,plain,(
    ! [A_423,B_424] : k4_xboole_0(A_423,k4_xboole_0(A_423,B_424)) = k3_xboole_0(A_423,B_424) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18469,plain,(
    ! [B_4] : k4_xboole_0(B_4,k1_xboole_0) = k3_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_18454])).

tff(c_18472,plain,(
    ! [B_4] : k4_xboole_0(B_4,k1_xboole_0) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_18469])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_18978,plain,(
    ! [A_459,B_460] :
      ( m1_subset_1(k2_pre_topc(A_459,B_460),k1_zfmisc_1(u1_struct_0(A_459)))
      | ~ m1_subset_1(B_460,k1_zfmisc_1(u1_struct_0(A_459)))
      | ~ l1_pre_topc(A_459) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24,plain,(
    ! [A_19,B_20,C_21] :
      ( k7_subset_1(A_19,B_20,C_21) = k4_xboole_0(B_20,C_21)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_25302,plain,(
    ! [A_616,B_617,C_618] :
      ( k7_subset_1(u1_struct_0(A_616),k2_pre_topc(A_616,B_617),C_618) = k4_xboole_0(k2_pre_topc(A_616,B_617),C_618)
      | ~ m1_subset_1(B_617,k1_zfmisc_1(u1_struct_0(A_616)))
      | ~ l1_pre_topc(A_616) ) ),
    inference(resolution,[status(thm)],[c_18978,c_24])).

tff(c_25312,plain,(
    ! [C_618] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_618) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_618)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_25302])).

tff(c_25324,plain,(
    ! [C_619] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_619) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_619) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_25312])).

tff(c_52,plain,
    ( ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_129,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_660,plain,(
    ! [B_96,A_97] :
      ( v2_tops_1(B_96,A_97)
      | k1_tops_1(A_97,B_96) != k1_xboole_0
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_663,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_660])).

tff(c_666,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_663])).

tff(c_667,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_666])).

tff(c_158,plain,(
    ! [A_70,B_71] : k4_xboole_0(A_70,k4_xboole_0(A_70,B_71)) = k3_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_173,plain,(
    ! [B_4] : k4_xboole_0(B_4,k1_xboole_0) = k3_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_158])).

tff(c_193,plain,(
    ! [B_72] : k4_xboole_0(B_72,k1_xboole_0) = B_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_173])).

tff(c_20,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_199,plain,(
    ! [B_72] : k4_xboole_0(B_72,B_72) = k3_xboole_0(B_72,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_20])).

tff(c_212,plain,(
    ! [B_72] : k3_xboole_0(B_72,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_199])).

tff(c_216,plain,(
    ! [B_73] : k3_xboole_0(B_73,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_199])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_225,plain,(
    ! [B_73] : k3_xboole_0(k1_xboole_0,B_73) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_2])).

tff(c_682,plain,(
    ! [A_99,B_100] : k4_xboole_0(A_99,k3_xboole_0(A_99,B_100)) = k3_xboole_0(A_99,k4_xboole_0(A_99,B_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_20])).

tff(c_819,plain,(
    ! [A_108,B_109] : k4_xboole_0(A_108,k3_xboole_0(B_109,A_108)) = k3_xboole_0(A_108,k4_xboole_0(A_108,B_109)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_682])).

tff(c_6387,plain,(
    ! [A_244,B_245] : k4_xboole_0(A_244,k3_xboole_0(A_244,k4_xboole_0(A_244,B_245))) = k3_xboole_0(A_244,k3_xboole_0(B_245,A_244)) ),
    inference(superposition,[status(thm),theory(equality)],[c_819,c_20])).

tff(c_694,plain,(
    ! [A_99,B_100] : k4_xboole_0(A_99,k3_xboole_0(A_99,k4_xboole_0(A_99,B_100))) = k3_xboole_0(A_99,k3_xboole_0(A_99,B_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_682,c_20])).

tff(c_6408,plain,(
    ! [A_244,B_245] : k3_xboole_0(A_244,k3_xboole_0(B_245,A_244)) = k3_xboole_0(A_244,k3_xboole_0(A_244,B_245)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6387,c_694])).

tff(c_58,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_177,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_58])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_190,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_177,c_14])).

tff(c_1772,plain,(
    ! [A_139,B_140] :
      ( k4_subset_1(u1_struct_0(A_139),B_140,k2_tops_1(A_139,B_140)) = k2_pre_topc(A_139,B_140)
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ l1_pre_topc(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1778,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1772])).

tff(c_1783,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1778])).

tff(c_34,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(k2_tops_1(A_32,B_33),k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1640,plain,(
    ! [A_130,B_131,C_132] :
      ( k4_subset_1(A_130,B_131,C_132) = k2_xboole_0(B_131,C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(A_130))
      | ~ m1_subset_1(B_131,k1_zfmisc_1(A_130)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16150,plain,(
    ! [A_389,B_390,B_391] :
      ( k4_subset_1(u1_struct_0(A_389),B_390,k2_tops_1(A_389,B_391)) = k2_xboole_0(B_390,k2_tops_1(A_389,B_391))
      | ~ m1_subset_1(B_390,k1_zfmisc_1(u1_struct_0(A_389)))
      | ~ m1_subset_1(B_391,k1_zfmisc_1(u1_struct_0(A_389)))
      | ~ l1_pre_topc(A_389) ) ),
    inference(resolution,[status(thm)],[c_34,c_1640])).

tff(c_16160,plain,(
    ! [B_391] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_391)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_391))
      | ~ m1_subset_1(B_391,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_16150])).

tff(c_16607,plain,(
    ! [B_393] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_393)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_393))
      | ~ m1_subset_1(B_393,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_16160])).

tff(c_16624,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_16607])).

tff(c_16634,plain,(
    k2_tops_1('#skF_1','#skF_2') = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_1783,c_16624])).

tff(c_576,plain,(
    ! [A_93,B_94] :
      ( r1_tarski(k1_tops_1(A_93,B_94),B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_578,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_576])).

tff(c_581,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_578])).

tff(c_321,plain,(
    ! [A_77,C_78,B_79] :
      ( r1_tarski(A_77,C_78)
      | ~ r1_tarski(B_79,C_78)
      | ~ r1_tarski(A_77,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_375,plain,(
    ! [A_83] :
      ( r1_tarski(A_83,k2_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_83,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_177,c_321])).

tff(c_16,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(A_9,C_11)
      | ~ r1_tarski(B_10,C_11)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1479,plain,(
    ! [A_127,A_128] :
      ( r1_tarski(A_127,k2_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_127,A_128)
      | ~ r1_tarski(A_128,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_375,c_16])).

tff(c_1483,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_581,c_1479])).

tff(c_1495,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1483])).

tff(c_16702,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16634,c_1495])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_17062,plain,(
    k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16702,c_12])).

tff(c_161,plain,(
    ! [A_70,B_71] : k4_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k3_xboole_0(A_70,k4_xboole_0(A_70,B_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_20])).

tff(c_176,plain,(
    ! [B_4] : k4_xboole_0(B_4,k1_xboole_0) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_173])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_353,plain,(
    ! [A_81,B_82] :
      ( k3_xboole_0(A_81,B_82) = A_81
      | k4_xboole_0(A_81,B_82) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_95])).

tff(c_928,plain,(
    ! [A_114,B_115] :
      ( k3_xboole_0(A_114,k4_xboole_0(A_114,B_115)) = A_114
      | k3_xboole_0(A_114,B_115) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_353])).

tff(c_937,plain,(
    ! [A_114,B_115] :
      ( k3_xboole_0(A_114,k4_xboole_0(A_114,k4_xboole_0(A_114,B_115))) = k4_xboole_0(A_114,A_114)
      | k3_xboole_0(A_114,B_115) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_928,c_161])).

tff(c_1184,plain,(
    ! [A_119,B_120] :
      ( k3_xboole_0(A_119,k3_xboole_0(A_119,B_120)) = k1_xboole_0
      | k3_xboole_0(A_119,B_120) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_121,c_937])).

tff(c_1196,plain,(
    ! [A_119,B_120] :
      ( k3_xboole_0(A_119,k4_xboole_0(A_119,k3_xboole_0(A_119,B_120))) = k4_xboole_0(A_119,k1_xboole_0)
      | k3_xboole_0(A_119,B_120) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1184,c_161])).

tff(c_1255,plain,(
    ! [A_119,B_120] :
      ( k3_xboole_0(A_119,k3_xboole_0(A_119,k4_xboole_0(A_119,B_120))) = A_119
      | k3_xboole_0(A_119,B_120) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_176,c_1196])).

tff(c_17169,plain,
    ( k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_xboole_0)) = k1_tops_1('#skF_1','#skF_2')
    | k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_17062,c_1255])).

tff(c_17226,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_225,c_6408,c_17169])).

tff(c_17227,plain,(
    k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_667,c_17226])).

tff(c_1390,plain,(
    ! [A_123,B_124] :
      ( m1_subset_1(k2_pre_topc(A_123,B_124),k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_10694,plain,(
    ! [A_298,B_299,C_300] :
      ( k7_subset_1(u1_struct_0(A_298),k2_pre_topc(A_298,B_299),C_300) = k4_xboole_0(k2_pre_topc(A_298,B_299),C_300)
      | ~ m1_subset_1(B_299,k1_zfmisc_1(u1_struct_0(A_298)))
      | ~ l1_pre_topc(A_298) ) ),
    inference(resolution,[status(thm)],[c_1390,c_24])).

tff(c_10700,plain,(
    ! [C_300] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_300) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_300)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_10694])).

tff(c_10706,plain,(
    ! [C_301] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_301) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_301) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_10700])).

tff(c_36,plain,(
    ! [A_34,B_36] :
      ( k7_subset_1(u1_struct_0(A_34),k2_pre_topc(A_34,B_36),k1_tops_1(A_34,B_36)) = k2_tops_1(A_34,B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_10713,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10706,c_36])).

tff(c_10723,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_10713])).

tff(c_16663,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16634,c_10723])).

tff(c_18401,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) = k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_16663,c_20])).

tff(c_18425,plain,(
    k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_121,c_18401])).

tff(c_18427,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17227,c_18425])).

tff(c_18429,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_18869,plain,(
    ! [A_456,B_457] :
      ( k1_tops_1(A_456,B_457) = k1_xboole_0
      | ~ v2_tops_1(B_457,A_456)
      | ~ m1_subset_1(B_457,k1_zfmisc_1(u1_struct_0(A_456)))
      | ~ l1_pre_topc(A_456) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_18872,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_18869])).

tff(c_18875,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_18429,c_18872])).

tff(c_21417,plain,(
    ! [A_531,B_532] :
      ( k7_subset_1(u1_struct_0(A_531),k2_pre_topc(A_531,B_532),k1_tops_1(A_531,B_532)) = k2_tops_1(A_531,B_532)
      | ~ m1_subset_1(B_532,k1_zfmisc_1(u1_struct_0(A_531)))
      | ~ l1_pre_topc(A_531) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_21426,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18875,c_21417])).

tff(c_21430,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_21426])).

tff(c_25330,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_25324,c_21430])).

tff(c_25346,plain,(
    k2_tops_1('#skF_1','#skF_2') = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18472,c_25330])).

tff(c_18428,plain,(
    ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_25364,plain,(
    ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25346,c_18428])).

tff(c_32,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k2_pre_topc(A_30,B_31),k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_19383,plain,(
    ! [A_473,B_474,C_475] :
      ( k4_subset_1(A_473,B_474,C_475) = k2_xboole_0(B_474,C_475)
      | ~ m1_subset_1(C_475,k1_zfmisc_1(A_473))
      | ~ m1_subset_1(B_474,k1_zfmisc_1(A_473)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_19408,plain,(
    ! [B_478] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_478,'#skF_2') = k2_xboole_0(B_478,'#skF_2')
      | ~ m1_subset_1(B_478,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_48,c_19383])).

tff(c_19416,plain,(
    ! [B_31] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_31),'#skF_2') = k2_xboole_0(k2_pre_topc('#skF_1',B_31),'#skF_2')
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_19408])).

tff(c_21273,plain,(
    ! [B_522] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_522),'#skF_2') = k2_xboole_0(k2_pre_topc('#skF_1',B_522),'#skF_2')
      | ~ m1_subset_1(B_522,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_19416])).

tff(c_21291,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_21273])).

tff(c_30,plain,(
    ! [A_26,B_27,C_29] :
      ( r1_tarski(k3_subset_1(A_26,k4_subset_1(A_26,B_27,C_29)),k3_subset_1(A_26,B_27))
      | ~ m1_subset_1(C_29,k1_zfmisc_1(A_26))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_21534,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2')),k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_21291,c_30])).

tff(c_21538,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2')),k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_21534])).

tff(c_22185,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_21538])).

tff(c_22188,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_22185])).

tff(c_22192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_22188])).

tff(c_22194,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_21538])).

tff(c_19653,plain,(
    ! [A_482,B_483] :
      ( k4_subset_1(u1_struct_0(A_482),B_483,k2_tops_1(A_482,B_483)) = k2_pre_topc(A_482,B_483)
      | ~ m1_subset_1(B_483,k1_zfmisc_1(u1_struct_0(A_482)))
      | ~ l1_pre_topc(A_482) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_19659,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_19653])).

tff(c_19664,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_19659])).

tff(c_25362,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25346,c_19664])).

tff(c_25435,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_25362,c_30])).

tff(c_25441,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_22194,c_25435])).

tff(c_26,plain,(
    ! [B_23,C_25,A_22] :
      ( r1_tarski(B_23,C_25)
      | ~ r1_tarski(k3_subset_1(A_22,C_25),k3_subset_1(A_22,B_23))
      | ~ m1_subset_1(C_25,k1_zfmisc_1(A_22))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_25468,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_25441,c_26])).

tff(c_25495,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_22194,c_25468])).

tff(c_25497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25364,c_25495])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:31:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.86/4.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.86/4.29  
% 10.86/4.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.86/4.30  %$ v2_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 10.86/4.30  
% 10.86/4.30  %Foreground sorts:
% 10.86/4.30  
% 10.86/4.30  
% 10.86/4.30  %Background operators:
% 10.86/4.30  
% 10.86/4.30  
% 10.86/4.30  %Foreground operators:
% 10.86/4.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.86/4.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.86/4.30  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 10.86/4.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.86/4.30  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 10.86/4.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.86/4.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.86/4.30  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.86/4.30  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 10.86/4.30  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 10.86/4.30  tff('#skF_2', type, '#skF_2': $i).
% 10.86/4.30  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 10.86/4.30  tff('#skF_1', type, '#skF_1': $i).
% 10.86/4.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.86/4.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.86/4.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.86/4.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.86/4.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.86/4.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.86/4.30  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.86/4.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.86/4.30  
% 11.14/4.32  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.14/4.32  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.14/4.32  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 11.14/4.32  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.14/4.32  tff(f_143, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 11.14/4.32  tff(f_85, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 11.14/4.32  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 11.14/4.32  tff(f_133, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 11.14/4.32  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.14/4.32  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.14/4.32  tff(f_124, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 11.14/4.32  tff(f_91, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 11.14/4.32  tff(f_59, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 11.14/4.32  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 11.14/4.32  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 11.14/4.32  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 11.14/4.32  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_subset_1)).
% 11.14/4.32  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 11.14/4.32  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.14/4.32  tff(c_95, plain, (![A_59, B_60]: (k3_xboole_0(A_59, B_60)=A_59 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.14/4.32  tff(c_103, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_95])).
% 11.14/4.32  tff(c_113, plain, (![A_62, B_63]: (k4_xboole_0(A_62, B_63)=k1_xboole_0 | ~r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.14/4.32  tff(c_121, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_113])).
% 11.14/4.32  tff(c_18454, plain, (![A_423, B_424]: (k4_xboole_0(A_423, k4_xboole_0(A_423, B_424))=k3_xboole_0(A_423, B_424))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.14/4.32  tff(c_18469, plain, (![B_4]: (k4_xboole_0(B_4, k1_xboole_0)=k3_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_121, c_18454])).
% 11.14/4.32  tff(c_18472, plain, (![B_4]: (k4_xboole_0(B_4, k1_xboole_0)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_103, c_18469])).
% 11.14/4.32  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 11.14/4.32  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 11.14/4.32  tff(c_18978, plain, (![A_459, B_460]: (m1_subset_1(k2_pre_topc(A_459, B_460), k1_zfmisc_1(u1_struct_0(A_459))) | ~m1_subset_1(B_460, k1_zfmisc_1(u1_struct_0(A_459))) | ~l1_pre_topc(A_459))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.14/4.32  tff(c_24, plain, (![A_19, B_20, C_21]: (k7_subset_1(A_19, B_20, C_21)=k4_xboole_0(B_20, C_21) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.14/4.32  tff(c_25302, plain, (![A_616, B_617, C_618]: (k7_subset_1(u1_struct_0(A_616), k2_pre_topc(A_616, B_617), C_618)=k4_xboole_0(k2_pre_topc(A_616, B_617), C_618) | ~m1_subset_1(B_617, k1_zfmisc_1(u1_struct_0(A_616))) | ~l1_pre_topc(A_616))), inference(resolution, [status(thm)], [c_18978, c_24])).
% 11.14/4.32  tff(c_25312, plain, (![C_618]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_618)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_618) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_25302])).
% 11.14/4.32  tff(c_25324, plain, (![C_619]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_619)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_619))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_25312])).
% 11.14/4.32  tff(c_52, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 11.14/4.32  tff(c_129, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_52])).
% 11.14/4.32  tff(c_660, plain, (![B_96, A_97]: (v2_tops_1(B_96, A_97) | k1_tops_1(A_97, B_96)!=k1_xboole_0 | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_133])).
% 11.14/4.32  tff(c_663, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_660])).
% 11.14/4.32  tff(c_666, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_663])).
% 11.14/4.32  tff(c_667, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_129, c_666])).
% 11.14/4.32  tff(c_158, plain, (![A_70, B_71]: (k4_xboole_0(A_70, k4_xboole_0(A_70, B_71))=k3_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.14/4.32  tff(c_173, plain, (![B_4]: (k4_xboole_0(B_4, k1_xboole_0)=k3_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_121, c_158])).
% 11.14/4.32  tff(c_193, plain, (![B_72]: (k4_xboole_0(B_72, k1_xboole_0)=B_72)), inference(demodulation, [status(thm), theory('equality')], [c_103, c_173])).
% 11.14/4.32  tff(c_20, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.14/4.32  tff(c_199, plain, (![B_72]: (k4_xboole_0(B_72, B_72)=k3_xboole_0(B_72, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_193, c_20])).
% 11.14/4.32  tff(c_212, plain, (![B_72]: (k3_xboole_0(B_72, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_199])).
% 11.14/4.32  tff(c_216, plain, (![B_73]: (k3_xboole_0(B_73, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_199])).
% 11.14/4.32  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.14/4.32  tff(c_225, plain, (![B_73]: (k3_xboole_0(k1_xboole_0, B_73)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_216, c_2])).
% 11.14/4.32  tff(c_682, plain, (![A_99, B_100]: (k4_xboole_0(A_99, k3_xboole_0(A_99, B_100))=k3_xboole_0(A_99, k4_xboole_0(A_99, B_100)))), inference(superposition, [status(thm), theory('equality')], [c_158, c_20])).
% 11.14/4.32  tff(c_819, plain, (![A_108, B_109]: (k4_xboole_0(A_108, k3_xboole_0(B_109, A_108))=k3_xboole_0(A_108, k4_xboole_0(A_108, B_109)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_682])).
% 11.14/4.32  tff(c_6387, plain, (![A_244, B_245]: (k4_xboole_0(A_244, k3_xboole_0(A_244, k4_xboole_0(A_244, B_245)))=k3_xboole_0(A_244, k3_xboole_0(B_245, A_244)))), inference(superposition, [status(thm), theory('equality')], [c_819, c_20])).
% 11.14/4.32  tff(c_694, plain, (![A_99, B_100]: (k4_xboole_0(A_99, k3_xboole_0(A_99, k4_xboole_0(A_99, B_100)))=k3_xboole_0(A_99, k3_xboole_0(A_99, B_100)))), inference(superposition, [status(thm), theory('equality')], [c_682, c_20])).
% 11.14/4.32  tff(c_6408, plain, (![A_244, B_245]: (k3_xboole_0(A_244, k3_xboole_0(B_245, A_244))=k3_xboole_0(A_244, k3_xboole_0(A_244, B_245)))), inference(superposition, [status(thm), theory('equality')], [c_6387, c_694])).
% 11.14/4.32  tff(c_58, plain, (v2_tops_1('#skF_2', '#skF_1') | r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 11.14/4.32  tff(c_177, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_129, c_58])).
% 11.14/4.32  tff(c_14, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.14/4.32  tff(c_190, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_177, c_14])).
% 11.14/4.32  tff(c_1772, plain, (![A_139, B_140]: (k4_subset_1(u1_struct_0(A_139), B_140, k2_tops_1(A_139, B_140))=k2_pre_topc(A_139, B_140) | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0(A_139))) | ~l1_pre_topc(A_139))), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.14/4.32  tff(c_1778, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_1772])).
% 11.14/4.32  tff(c_1783, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1778])).
% 11.14/4.32  tff(c_34, plain, (![A_32, B_33]: (m1_subset_1(k2_tops_1(A_32, B_33), k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.14/4.32  tff(c_1640, plain, (![A_130, B_131, C_132]: (k4_subset_1(A_130, B_131, C_132)=k2_xboole_0(B_131, C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(A_130)) | ~m1_subset_1(B_131, k1_zfmisc_1(A_130)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.14/4.32  tff(c_16150, plain, (![A_389, B_390, B_391]: (k4_subset_1(u1_struct_0(A_389), B_390, k2_tops_1(A_389, B_391))=k2_xboole_0(B_390, k2_tops_1(A_389, B_391)) | ~m1_subset_1(B_390, k1_zfmisc_1(u1_struct_0(A_389))) | ~m1_subset_1(B_391, k1_zfmisc_1(u1_struct_0(A_389))) | ~l1_pre_topc(A_389))), inference(resolution, [status(thm)], [c_34, c_1640])).
% 11.14/4.32  tff(c_16160, plain, (![B_391]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_391))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_391)) | ~m1_subset_1(B_391, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_16150])).
% 11.14/4.32  tff(c_16607, plain, (![B_393]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_393))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_393)) | ~m1_subset_1(B_393, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_16160])).
% 11.14/4.32  tff(c_16624, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_16607])).
% 11.14/4.32  tff(c_16634, plain, (k2_tops_1('#skF_1', '#skF_2')=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_190, c_1783, c_16624])).
% 11.14/4.32  tff(c_576, plain, (![A_93, B_94]: (r1_tarski(k1_tops_1(A_93, B_94), B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_105])).
% 11.14/4.32  tff(c_578, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_576])).
% 11.14/4.32  tff(c_581, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_578])).
% 11.14/4.32  tff(c_321, plain, (![A_77, C_78, B_79]: (r1_tarski(A_77, C_78) | ~r1_tarski(B_79, C_78) | ~r1_tarski(A_77, B_79))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.14/4.32  tff(c_375, plain, (![A_83]: (r1_tarski(A_83, k2_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(A_83, '#skF_2'))), inference(resolution, [status(thm)], [c_177, c_321])).
% 11.14/4.32  tff(c_16, plain, (![A_9, C_11, B_10]: (r1_tarski(A_9, C_11) | ~r1_tarski(B_10, C_11) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.14/4.32  tff(c_1479, plain, (![A_127, A_128]: (r1_tarski(A_127, k2_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(A_127, A_128) | ~r1_tarski(A_128, '#skF_2'))), inference(resolution, [status(thm)], [c_375, c_16])).
% 11.14/4.32  tff(c_1483, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_581, c_1479])).
% 11.14/4.32  tff(c_1495, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1483])).
% 11.14/4.32  tff(c_16702, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16634, c_1495])).
% 11.14/4.32  tff(c_12, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.14/4.32  tff(c_17062, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_16702, c_12])).
% 11.14/4.32  tff(c_161, plain, (![A_70, B_71]: (k4_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k3_xboole_0(A_70, k4_xboole_0(A_70, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_158, c_20])).
% 11.14/4.32  tff(c_176, plain, (![B_4]: (k4_xboole_0(B_4, k1_xboole_0)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_103, c_173])).
% 11.14/4.32  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.14/4.32  tff(c_353, plain, (![A_81, B_82]: (k3_xboole_0(A_81, B_82)=A_81 | k4_xboole_0(A_81, B_82)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_95])).
% 11.14/4.32  tff(c_928, plain, (![A_114, B_115]: (k3_xboole_0(A_114, k4_xboole_0(A_114, B_115))=A_114 | k3_xboole_0(A_114, B_115)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_353])).
% 11.14/4.32  tff(c_937, plain, (![A_114, B_115]: (k3_xboole_0(A_114, k4_xboole_0(A_114, k4_xboole_0(A_114, B_115)))=k4_xboole_0(A_114, A_114) | k3_xboole_0(A_114, B_115)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_928, c_161])).
% 11.14/4.32  tff(c_1184, plain, (![A_119, B_120]: (k3_xboole_0(A_119, k3_xboole_0(A_119, B_120))=k1_xboole_0 | k3_xboole_0(A_119, B_120)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_121, c_937])).
% 11.14/4.32  tff(c_1196, plain, (![A_119, B_120]: (k3_xboole_0(A_119, k4_xboole_0(A_119, k3_xboole_0(A_119, B_120)))=k4_xboole_0(A_119, k1_xboole_0) | k3_xboole_0(A_119, B_120)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1184, c_161])).
% 11.14/4.32  tff(c_1255, plain, (![A_119, B_120]: (k3_xboole_0(A_119, k3_xboole_0(A_119, k4_xboole_0(A_119, B_120)))=A_119 | k3_xboole_0(A_119, B_120)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_161, c_176, c_1196])).
% 11.14/4.32  tff(c_17169, plain, (k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_xboole_0))=k1_tops_1('#skF_1', '#skF_2') | k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_17062, c_1255])).
% 11.14/4.32  tff(c_17226, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_212, c_225, c_6408, c_17169])).
% 11.14/4.32  tff(c_17227, plain, (k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_667, c_17226])).
% 11.14/4.32  tff(c_1390, plain, (![A_123, B_124]: (m1_subset_1(k2_pre_topc(A_123, B_124), k1_zfmisc_1(u1_struct_0(A_123))) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.14/4.32  tff(c_10694, plain, (![A_298, B_299, C_300]: (k7_subset_1(u1_struct_0(A_298), k2_pre_topc(A_298, B_299), C_300)=k4_xboole_0(k2_pre_topc(A_298, B_299), C_300) | ~m1_subset_1(B_299, k1_zfmisc_1(u1_struct_0(A_298))) | ~l1_pre_topc(A_298))), inference(resolution, [status(thm)], [c_1390, c_24])).
% 11.14/4.32  tff(c_10700, plain, (![C_300]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_300)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_300) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_10694])).
% 11.14/4.32  tff(c_10706, plain, (![C_301]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_301)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_301))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_10700])).
% 11.14/4.32  tff(c_36, plain, (![A_34, B_36]: (k7_subset_1(u1_struct_0(A_34), k2_pre_topc(A_34, B_36), k1_tops_1(A_34, B_36))=k2_tops_1(A_34, B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.14/4.32  tff(c_10713, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10706, c_36])).
% 11.14/4.32  tff(c_10723, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_10713])).
% 11.14/4.32  tff(c_16663, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16634, c_10723])).
% 11.14/4.32  tff(c_18401, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))=k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_16663, c_20])).
% 11.14/4.32  tff(c_18425, plain, (k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_121, c_18401])).
% 11.14/4.32  tff(c_18427, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17227, c_18425])).
% 11.14/4.32  tff(c_18429, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 11.14/4.32  tff(c_18869, plain, (![A_456, B_457]: (k1_tops_1(A_456, B_457)=k1_xboole_0 | ~v2_tops_1(B_457, A_456) | ~m1_subset_1(B_457, k1_zfmisc_1(u1_struct_0(A_456))) | ~l1_pre_topc(A_456))), inference(cnfTransformation, [status(thm)], [f_133])).
% 11.14/4.32  tff(c_18872, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_18869])).
% 11.14/4.32  tff(c_18875, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_18429, c_18872])).
% 11.14/4.32  tff(c_21417, plain, (![A_531, B_532]: (k7_subset_1(u1_struct_0(A_531), k2_pre_topc(A_531, B_532), k1_tops_1(A_531, B_532))=k2_tops_1(A_531, B_532) | ~m1_subset_1(B_532, k1_zfmisc_1(u1_struct_0(A_531))) | ~l1_pre_topc(A_531))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.14/4.32  tff(c_21426, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_18875, c_21417])).
% 11.14/4.32  tff(c_21430, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_21426])).
% 11.14/4.32  tff(c_25330, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_25324, c_21430])).
% 11.14/4.32  tff(c_25346, plain, (k2_tops_1('#skF_1', '#skF_2')=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18472, c_25330])).
% 11.14/4.32  tff(c_18428, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_52])).
% 11.14/4.32  tff(c_25364, plain, (~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_25346, c_18428])).
% 11.14/4.32  tff(c_32, plain, (![A_30, B_31]: (m1_subset_1(k2_pre_topc(A_30, B_31), k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.14/4.32  tff(c_19383, plain, (![A_473, B_474, C_475]: (k4_subset_1(A_473, B_474, C_475)=k2_xboole_0(B_474, C_475) | ~m1_subset_1(C_475, k1_zfmisc_1(A_473)) | ~m1_subset_1(B_474, k1_zfmisc_1(A_473)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.14/4.32  tff(c_19408, plain, (![B_478]: (k4_subset_1(u1_struct_0('#skF_1'), B_478, '#skF_2')=k2_xboole_0(B_478, '#skF_2') | ~m1_subset_1(B_478, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_48, c_19383])).
% 11.14/4.32  tff(c_19416, plain, (![B_31]: (k4_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', B_31), '#skF_2')=k2_xboole_0(k2_pre_topc('#skF_1', B_31), '#skF_2') | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_19408])).
% 11.14/4.32  tff(c_21273, plain, (![B_522]: (k4_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', B_522), '#skF_2')=k2_xboole_0(k2_pre_topc('#skF_1', B_522), '#skF_2') | ~m1_subset_1(B_522, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_19416])).
% 11.14/4.32  tff(c_21291, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_48, c_21273])).
% 11.14/4.32  tff(c_30, plain, (![A_26, B_27, C_29]: (r1_tarski(k3_subset_1(A_26, k4_subset_1(A_26, B_27, C_29)), k3_subset_1(A_26, B_27)) | ~m1_subset_1(C_29, k1_zfmisc_1(A_26)) | ~m1_subset_1(B_27, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.14/4.32  tff(c_21534, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_21291, c_30])).
% 11.14/4.32  tff(c_21538, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_21534])).
% 11.14/4.32  tff(c_22185, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_21538])).
% 11.14/4.32  tff(c_22188, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_22185])).
% 11.14/4.32  tff(c_22192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_22188])).
% 11.14/4.32  tff(c_22194, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_21538])).
% 11.14/4.32  tff(c_19653, plain, (![A_482, B_483]: (k4_subset_1(u1_struct_0(A_482), B_483, k2_tops_1(A_482, B_483))=k2_pre_topc(A_482, B_483) | ~m1_subset_1(B_483, k1_zfmisc_1(u1_struct_0(A_482))) | ~l1_pre_topc(A_482))), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.14/4.32  tff(c_19659, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_19653])).
% 11.14/4.32  tff(c_19664, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_19659])).
% 11.14/4.32  tff(c_25362, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_25346, c_19664])).
% 11.14/4.32  tff(c_25435, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_25362, c_30])).
% 11.14/4.32  tff(c_25441, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_22194, c_25435])).
% 11.14/4.32  tff(c_26, plain, (![B_23, C_25, A_22]: (r1_tarski(B_23, C_25) | ~r1_tarski(k3_subset_1(A_22, C_25), k3_subset_1(A_22, B_23)) | ~m1_subset_1(C_25, k1_zfmisc_1(A_22)) | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.14/4.32  tff(c_25468, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_25441, c_26])).
% 11.14/4.32  tff(c_25495, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_22194, c_25468])).
% 11.14/4.32  tff(c_25497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25364, c_25495])).
% 11.14/4.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.14/4.32  
% 11.14/4.32  Inference rules
% 11.14/4.32  ----------------------
% 11.14/4.32  #Ref     : 0
% 11.14/4.32  #Sup     : 5840
% 11.14/4.32  #Fact    : 0
% 11.14/4.32  #Define  : 0
% 11.14/4.32  #Split   : 24
% 11.14/4.32  #Chain   : 0
% 11.14/4.32  #Close   : 0
% 11.14/4.32  
% 11.14/4.32  Ordering : KBO
% 11.14/4.32  
% 11.14/4.32  Simplification rules
% 11.14/4.32  ----------------------
% 11.14/4.32  #Subsume      : 2334
% 11.14/4.32  #Demod        : 5276
% 11.14/4.32  #Tautology    : 1666
% 11.14/4.32  #SimpNegUnit  : 195
% 11.14/4.32  #BackRed      : 106
% 11.14/4.32  
% 11.14/4.32  #Partial instantiations: 0
% 11.14/4.32  #Strategies tried      : 1
% 11.14/4.32  
% 11.14/4.32  Timing (in seconds)
% 11.14/4.32  ----------------------
% 11.14/4.32  Preprocessing        : 0.33
% 11.14/4.32  Parsing              : 0.18
% 11.14/4.32  CNF conversion       : 0.02
% 11.14/4.32  Main loop            : 3.20
% 11.14/4.32  Inferencing          : 0.70
% 11.14/4.32  Reduction            : 1.43
% 11.14/4.32  Demodulation         : 1.13
% 11.14/4.32  BG Simplification    : 0.08
% 11.14/4.33  Subsumption          : 0.81
% 11.14/4.33  Abstraction          : 0.13
% 11.14/4.33  MUC search           : 0.00
% 11.14/4.33  Cooper               : 0.00
% 11.14/4.33  Total                : 3.59
% 11.14/4.33  Index Insertion      : 0.00
% 11.14/4.33  Index Deletion       : 0.00
% 11.14/4.33  Index Matching       : 0.00
% 11.14/4.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
