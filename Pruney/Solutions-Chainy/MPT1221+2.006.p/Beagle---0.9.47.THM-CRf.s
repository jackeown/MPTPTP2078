%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:24 EST 2020

% Result     : Theorem 5.17s
% Output     : CNFRefutation 5.31s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 364 expanded)
%              Number of leaves         :   38 ( 139 expanded)
%              Depth                    :   13
%              Number of atoms          :  154 ( 651 expanded)
%              Number of equality atoms :   53 ( 158 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_60,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(A),k2_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_34,plain,(
    ! [A_30] :
      ( l1_struct_0(A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_92,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_97,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_34,c_92])).

tff(c_101,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_97])).

tff(c_46,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_107,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_46])).

tff(c_108,plain,(
    v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_40,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_158,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_101,c_40])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_102,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_36])).

tff(c_126,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_137,plain,(
    r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_102,c_126])).

tff(c_274,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,B_59) = k3_subset_1(A_58,B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_285,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_102,c_274])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_156,plain,(
    k3_xboole_0('#skF_2',k2_struct_0('#skF_1')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_137,c_4])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_109,plain,(
    ! [A_39,B_40] : k1_setfam_1(k2_tarski(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_163,plain,(
    ! [A_49,B_50] : k1_setfam_1(k2_tarski(A_49,B_50)) = k3_xboole_0(B_50,A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_109])).

tff(c_22,plain,(
    ! [A_22,B_23] : k1_setfam_1(k2_tarski(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_169,plain,(
    ! [B_50,A_49] : k3_xboole_0(B_50,A_49) = k3_xboole_0(A_49,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_22])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_335,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_xboole_0(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_6])).

tff(c_338,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_169,c_335])).

tff(c_412,plain,(
    k3_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_6])).

tff(c_415,plain,(
    k3_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_412])).

tff(c_10,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_12] : m1_subset_1(k2_subset_1(A_12),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_47,plain,(
    ! [A_12] : m1_subset_1(A_12,k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14])).

tff(c_26,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,k1_zfmisc_1(B_25))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_639,plain,(
    ! [A_88,B_89,C_90] :
      ( k9_subset_1(A_88,B_89,k3_subset_1(A_88,C_90)) = k7_subset_1(A_88,B_89,C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(A_88))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1773,plain,(
    ! [B_142,B_143,A_144] :
      ( k9_subset_1(B_142,B_143,k3_subset_1(B_142,A_144)) = k7_subset_1(B_142,B_143,A_144)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(B_142))
      | ~ r1_tarski(A_144,B_142) ) ),
    inference(resolution,[status(thm)],[c_26,c_639])).

tff(c_1936,plain,(
    ! [A_147,A_148] :
      ( k9_subset_1(A_147,A_147,k3_subset_1(A_147,A_148)) = k7_subset_1(A_147,A_147,A_148)
      | ~ r1_tarski(A_148,A_147) ) ),
    inference(resolution,[status(thm)],[c_47,c_1773])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k3_subset_1(A_13,B_14),k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_473,plain,(
    ! [A_75,B_76,C_77] :
      ( k9_subset_1(A_75,B_76,C_77) = k3_xboole_0(B_76,C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1578,plain,(
    ! [A_132,B_133,B_134] :
      ( k9_subset_1(A_132,B_133,k3_subset_1(A_132,B_134)) = k3_xboole_0(B_133,k3_subset_1(A_132,B_134))
      | ~ m1_subset_1(B_134,k1_zfmisc_1(A_132)) ) ),
    inference(resolution,[status(thm)],[c_16,c_473])).

tff(c_1593,plain,(
    ! [B_133] : k9_subset_1(k2_struct_0('#skF_1'),B_133,k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_xboole_0(B_133,k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_102,c_1578])).

tff(c_1947,plain,
    ( k3_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2')
    | ~ r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1936,c_1593])).

tff(c_1982,plain,(
    k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_415,c_1947])).

tff(c_874,plain,(
    ! [B_101,A_102] :
      ( v4_pre_topc(B_101,A_102)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_102),k2_struct_0(A_102),B_101),A_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_877,plain,(
    ! [B_101] :
      ( v4_pre_topc(B_101,'#skF_1')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_101),'#skF_1')
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_874])).

tff(c_879,plain,(
    ! [B_101] :
      ( v4_pre_topc(B_101,'#skF_1')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_101),'#skF_1')
      | ~ m1_subset_1(B_101,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_101,c_877])).

tff(c_2004,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1982,c_879])).

tff(c_2010,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_108,c_2004])).

tff(c_2012,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_2010])).

tff(c_2014,plain,(
    ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_2013,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_2017,plain,(
    ! [A_153,B_154] :
      ( r1_tarski(A_153,B_154)
      | ~ m1_subset_1(A_153,k1_zfmisc_1(B_154)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2028,plain,(
    r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_102,c_2017])).

tff(c_2230,plain,(
    ! [A_174,B_175] :
      ( k4_xboole_0(A_174,B_175) = k3_subset_1(A_174,B_175)
      | ~ m1_subset_1(B_175,k1_zfmisc_1(A_174)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2245,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_102,c_2230])).

tff(c_2049,plain,(
    k3_xboole_0('#skF_2',k2_struct_0('#skF_1')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2028,c_4])).

tff(c_2054,plain,(
    ! [A_157,B_158] : k1_setfam_1(k2_tarski(A_157,B_158)) = k3_xboole_0(A_157,B_158) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2084,plain,(
    ! [B_161,A_162] : k1_setfam_1(k2_tarski(B_161,A_162)) = k3_xboole_0(A_162,B_161) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2054])).

tff(c_2090,plain,(
    ! [B_161,A_162] : k3_xboole_0(B_161,A_162) = k3_xboole_0(A_162,B_161) ),
    inference(superposition,[status(thm),theory(equality)],[c_2084,c_22])).

tff(c_2251,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_xboole_0(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2245,c_6])).

tff(c_2254,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2049,c_2090,c_2251])).

tff(c_2360,plain,(
    k3_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2254,c_6])).

tff(c_2363,plain,(
    k3_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2245,c_2360])).

tff(c_2427,plain,(
    ! [A_194,B_195,C_196] :
      ( k9_subset_1(A_194,B_195,k3_subset_1(A_194,C_196)) = k7_subset_1(A_194,B_195,C_196)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(A_194))
      | ~ m1_subset_1(B_195,k1_zfmisc_1(A_194)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3792,plain,(
    ! [B_254,B_255,A_256] :
      ( k9_subset_1(B_254,B_255,k3_subset_1(B_254,A_256)) = k7_subset_1(B_254,B_255,A_256)
      | ~ m1_subset_1(B_255,k1_zfmisc_1(B_254))
      | ~ r1_tarski(A_256,B_254) ) ),
    inference(resolution,[status(thm)],[c_26,c_2427])).

tff(c_4040,plain,(
    ! [A_260,A_261] :
      ( k9_subset_1(A_260,A_260,k3_subset_1(A_260,A_261)) = k7_subset_1(A_260,A_260,A_261)
      | ~ r1_tarski(A_261,A_260) ) ),
    inference(resolution,[status(thm)],[c_47,c_3792])).

tff(c_2317,plain,(
    ! [A_180,B_181,C_182] :
      ( k9_subset_1(A_180,B_181,C_182) = k3_xboole_0(B_181,C_182)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(A_180)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3587,plain,(
    ! [A_244,B_245,B_246] :
      ( k9_subset_1(A_244,B_245,k3_subset_1(A_244,B_246)) = k3_xboole_0(B_245,k3_subset_1(A_244,B_246))
      | ~ m1_subset_1(B_246,k1_zfmisc_1(A_244)) ) ),
    inference(resolution,[status(thm)],[c_16,c_2317])).

tff(c_3602,plain,(
    ! [B_245] : k9_subset_1(k2_struct_0('#skF_1'),B_245,k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_xboole_0(B_245,k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_102,c_3587])).

tff(c_4051,plain,
    ( k3_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2')
    | ~ r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4040,c_3602])).

tff(c_4086,plain,(
    k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2028,c_2363,c_4051])).

tff(c_2635,plain,(
    ! [A_206,B_207] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(A_206),k2_struct_0(A_206),B_207),A_206)
      | ~ v4_pre_topc(B_207,A_206)
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0(A_206)))
      | ~ l1_pre_topc(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2638,plain,(
    ! [B_207] :
      ( v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_207),'#skF_1')
      | ~ v4_pre_topc(B_207,'#skF_1')
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_2635])).

tff(c_2640,plain,(
    ! [B_207] :
      ( v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_207),'#skF_1')
      | ~ v4_pre_topc(B_207,'#skF_1')
      | ~ m1_subset_1(B_207,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_101,c_2638])).

tff(c_4108,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4086,c_2640])).

tff(c_4114,plain,(
    v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_2013,c_4108])).

tff(c_4116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2014,c_4114])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:10:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.17/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.17/2.00  
% 5.17/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.17/2.00  %$ v4_pre_topc > v3_pre_topc > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 5.17/2.00  
% 5.17/2.00  %Foreground sorts:
% 5.17/2.00  
% 5.17/2.00  
% 5.17/2.00  %Background operators:
% 5.17/2.00  
% 5.17/2.00  
% 5.17/2.00  %Foreground operators:
% 5.17/2.00  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.17/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.17/2.00  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.17/2.00  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.17/2.00  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.17/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.17/2.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.17/2.00  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.17/2.00  tff('#skF_2', type, '#skF_2': $i).
% 5.17/2.00  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.17/2.00  tff('#skF_1', type, '#skF_1': $i).
% 5.17/2.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.17/2.00  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.17/2.00  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.17/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.17/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.17/2.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.17/2.00  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.17/2.00  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.17/2.00  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.17/2.00  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.17/2.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.17/2.00  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.17/2.00  
% 5.31/2.02  tff(f_91, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 5.31/2.02  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.31/2.02  tff(f_68, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.31/2.02  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.31/2.02  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.31/2.02  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.31/2.02  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.31/2.02  tff(f_60, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.31/2.02  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.31/2.02  tff(f_37, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.31/2.02  tff(f_43, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.31/2.02  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 5.31/2.02  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.31/2.02  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 5.31/2.02  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k7_subset_1(u1_struct_0(A), k2_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_pre_topc)).
% 5.31/2.02  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.31/2.02  tff(c_34, plain, (![A_30]: (l1_struct_0(A_30) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.31/2.02  tff(c_92, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.31/2.02  tff(c_97, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_pre_topc(A_38))), inference(resolution, [status(thm)], [c_34, c_92])).
% 5.31/2.02  tff(c_101, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_97])).
% 5.31/2.02  tff(c_46, plain, (v4_pre_topc('#skF_2', '#skF_1') | v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.31/2.02  tff(c_107, plain, (v4_pre_topc('#skF_2', '#skF_1') | v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_46])).
% 5.31/2.02  tff(c_108, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_107])).
% 5.31/2.02  tff(c_40, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.31/2.02  tff(c_158, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_101, c_40])).
% 5.31/2.02  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.31/2.02  tff(c_102, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_36])).
% 5.31/2.02  tff(c_126, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | ~m1_subset_1(A_45, k1_zfmisc_1(B_46)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.31/2.02  tff(c_137, plain, (r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_102, c_126])).
% 5.31/2.02  tff(c_274, plain, (![A_58, B_59]: (k4_xboole_0(A_58, B_59)=k3_subset_1(A_58, B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.31/2.02  tff(c_285, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_102, c_274])).
% 5.31/2.02  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.31/2.02  tff(c_156, plain, (k3_xboole_0('#skF_2', k2_struct_0('#skF_1'))='#skF_2'), inference(resolution, [status(thm)], [c_137, c_4])).
% 5.31/2.02  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.31/2.02  tff(c_109, plain, (![A_39, B_40]: (k1_setfam_1(k2_tarski(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.31/2.02  tff(c_163, plain, (![A_49, B_50]: (k1_setfam_1(k2_tarski(A_49, B_50))=k3_xboole_0(B_50, A_49))), inference(superposition, [status(thm), theory('equality')], [c_8, c_109])).
% 5.31/2.02  tff(c_22, plain, (![A_22, B_23]: (k1_setfam_1(k2_tarski(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.31/2.02  tff(c_169, plain, (![B_50, A_49]: (k3_xboole_0(B_50, A_49)=k3_xboole_0(A_49, B_50))), inference(superposition, [status(thm), theory('equality')], [c_163, c_22])).
% 5.31/2.02  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.31/2.02  tff(c_335, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_xboole_0(k2_struct_0('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_285, c_6])).
% 5.31/2.02  tff(c_338, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_156, c_169, c_335])).
% 5.31/2.02  tff(c_412, plain, (k3_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_338, c_6])).
% 5.31/2.02  tff(c_415, plain, (k3_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_285, c_412])).
% 5.31/2.02  tff(c_10, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.31/2.02  tff(c_14, plain, (![A_12]: (m1_subset_1(k2_subset_1(A_12), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.31/2.02  tff(c_47, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14])).
% 5.31/2.02  tff(c_26, plain, (![A_24, B_25]: (m1_subset_1(A_24, k1_zfmisc_1(B_25)) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.31/2.02  tff(c_639, plain, (![A_88, B_89, C_90]: (k9_subset_1(A_88, B_89, k3_subset_1(A_88, C_90))=k7_subset_1(A_88, B_89, C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(A_88)) | ~m1_subset_1(B_89, k1_zfmisc_1(A_88)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.31/2.02  tff(c_1773, plain, (![B_142, B_143, A_144]: (k9_subset_1(B_142, B_143, k3_subset_1(B_142, A_144))=k7_subset_1(B_142, B_143, A_144) | ~m1_subset_1(B_143, k1_zfmisc_1(B_142)) | ~r1_tarski(A_144, B_142))), inference(resolution, [status(thm)], [c_26, c_639])).
% 5.31/2.02  tff(c_1936, plain, (![A_147, A_148]: (k9_subset_1(A_147, A_147, k3_subset_1(A_147, A_148))=k7_subset_1(A_147, A_147, A_148) | ~r1_tarski(A_148, A_147))), inference(resolution, [status(thm)], [c_47, c_1773])).
% 5.31/2.02  tff(c_16, plain, (![A_13, B_14]: (m1_subset_1(k3_subset_1(A_13, B_14), k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.31/2.02  tff(c_473, plain, (![A_75, B_76, C_77]: (k9_subset_1(A_75, B_76, C_77)=k3_xboole_0(B_76, C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.31/2.02  tff(c_1578, plain, (![A_132, B_133, B_134]: (k9_subset_1(A_132, B_133, k3_subset_1(A_132, B_134))=k3_xboole_0(B_133, k3_subset_1(A_132, B_134)) | ~m1_subset_1(B_134, k1_zfmisc_1(A_132)))), inference(resolution, [status(thm)], [c_16, c_473])).
% 5.31/2.02  tff(c_1593, plain, (![B_133]: (k9_subset_1(k2_struct_0('#skF_1'), B_133, k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_xboole_0(B_133, k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')))), inference(resolution, [status(thm)], [c_102, c_1578])).
% 5.31/2.02  tff(c_1947, plain, (k3_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2') | ~r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1936, c_1593])).
% 5.31/2.02  tff(c_1982, plain, (k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_415, c_1947])).
% 5.31/2.02  tff(c_874, plain, (![B_101, A_102]: (v4_pre_topc(B_101, A_102) | ~v3_pre_topc(k7_subset_1(u1_struct_0(A_102), k2_struct_0(A_102), B_101), A_102) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.31/2.02  tff(c_877, plain, (![B_101]: (v4_pre_topc(B_101, '#skF_1') | ~v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_101), '#skF_1') | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_874])).
% 5.31/2.02  tff(c_879, plain, (![B_101]: (v4_pre_topc(B_101, '#skF_1') | ~v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_101), '#skF_1') | ~m1_subset_1(B_101, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_101, c_877])).
% 5.31/2.02  tff(c_2004, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1982, c_879])).
% 5.31/2.02  tff(c_2010, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_108, c_2004])).
% 5.31/2.02  tff(c_2012, plain, $false, inference(negUnitSimplification, [status(thm)], [c_158, c_2010])).
% 5.31/2.02  tff(c_2014, plain, (~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_107])).
% 5.31/2.02  tff(c_2013, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_107])).
% 5.31/2.02  tff(c_2017, plain, (![A_153, B_154]: (r1_tarski(A_153, B_154) | ~m1_subset_1(A_153, k1_zfmisc_1(B_154)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.31/2.02  tff(c_2028, plain, (r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_102, c_2017])).
% 5.31/2.02  tff(c_2230, plain, (![A_174, B_175]: (k4_xboole_0(A_174, B_175)=k3_subset_1(A_174, B_175) | ~m1_subset_1(B_175, k1_zfmisc_1(A_174)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.31/2.02  tff(c_2245, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_102, c_2230])).
% 5.31/2.02  tff(c_2049, plain, (k3_xboole_0('#skF_2', k2_struct_0('#skF_1'))='#skF_2'), inference(resolution, [status(thm)], [c_2028, c_4])).
% 5.31/2.02  tff(c_2054, plain, (![A_157, B_158]: (k1_setfam_1(k2_tarski(A_157, B_158))=k3_xboole_0(A_157, B_158))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.31/2.02  tff(c_2084, plain, (![B_161, A_162]: (k1_setfam_1(k2_tarski(B_161, A_162))=k3_xboole_0(A_162, B_161))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2054])).
% 5.31/2.02  tff(c_2090, plain, (![B_161, A_162]: (k3_xboole_0(B_161, A_162)=k3_xboole_0(A_162, B_161))), inference(superposition, [status(thm), theory('equality')], [c_2084, c_22])).
% 5.31/2.02  tff(c_2251, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_xboole_0(k2_struct_0('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2245, c_6])).
% 5.31/2.02  tff(c_2254, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2049, c_2090, c_2251])).
% 5.31/2.02  tff(c_2360, plain, (k3_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2254, c_6])).
% 5.31/2.02  tff(c_2363, plain, (k3_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2245, c_2360])).
% 5.31/2.02  tff(c_2427, plain, (![A_194, B_195, C_196]: (k9_subset_1(A_194, B_195, k3_subset_1(A_194, C_196))=k7_subset_1(A_194, B_195, C_196) | ~m1_subset_1(C_196, k1_zfmisc_1(A_194)) | ~m1_subset_1(B_195, k1_zfmisc_1(A_194)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.31/2.02  tff(c_3792, plain, (![B_254, B_255, A_256]: (k9_subset_1(B_254, B_255, k3_subset_1(B_254, A_256))=k7_subset_1(B_254, B_255, A_256) | ~m1_subset_1(B_255, k1_zfmisc_1(B_254)) | ~r1_tarski(A_256, B_254))), inference(resolution, [status(thm)], [c_26, c_2427])).
% 5.31/2.02  tff(c_4040, plain, (![A_260, A_261]: (k9_subset_1(A_260, A_260, k3_subset_1(A_260, A_261))=k7_subset_1(A_260, A_260, A_261) | ~r1_tarski(A_261, A_260))), inference(resolution, [status(thm)], [c_47, c_3792])).
% 5.31/2.02  tff(c_2317, plain, (![A_180, B_181, C_182]: (k9_subset_1(A_180, B_181, C_182)=k3_xboole_0(B_181, C_182) | ~m1_subset_1(C_182, k1_zfmisc_1(A_180)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.31/2.02  tff(c_3587, plain, (![A_244, B_245, B_246]: (k9_subset_1(A_244, B_245, k3_subset_1(A_244, B_246))=k3_xboole_0(B_245, k3_subset_1(A_244, B_246)) | ~m1_subset_1(B_246, k1_zfmisc_1(A_244)))), inference(resolution, [status(thm)], [c_16, c_2317])).
% 5.31/2.02  tff(c_3602, plain, (![B_245]: (k9_subset_1(k2_struct_0('#skF_1'), B_245, k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_xboole_0(B_245, k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')))), inference(resolution, [status(thm)], [c_102, c_3587])).
% 5.31/2.02  tff(c_4051, plain, (k3_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2') | ~r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4040, c_3602])).
% 5.31/2.02  tff(c_4086, plain, (k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2028, c_2363, c_4051])).
% 5.31/2.02  tff(c_2635, plain, (![A_206, B_207]: (v3_pre_topc(k7_subset_1(u1_struct_0(A_206), k2_struct_0(A_206), B_207), A_206) | ~v4_pre_topc(B_207, A_206) | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0(A_206))) | ~l1_pre_topc(A_206))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.31/2.02  tff(c_2638, plain, (![B_207]: (v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_207), '#skF_1') | ~v4_pre_topc(B_207, '#skF_1') | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_2635])).
% 5.31/2.02  tff(c_2640, plain, (![B_207]: (v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_207), '#skF_1') | ~v4_pre_topc(B_207, '#skF_1') | ~m1_subset_1(B_207, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_101, c_2638])).
% 5.31/2.02  tff(c_4108, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4086, c_2640])).
% 5.31/2.02  tff(c_4114, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_2013, c_4108])).
% 5.31/2.02  tff(c_4116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2014, c_4114])).
% 5.31/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.31/2.02  
% 5.31/2.02  Inference rules
% 5.31/2.02  ----------------------
% 5.31/2.02  #Ref     : 0
% 5.31/2.02  #Sup     : 999
% 5.31/2.02  #Fact    : 0
% 5.31/2.02  #Define  : 0
% 5.31/2.02  #Split   : 3
% 5.31/2.02  #Chain   : 0
% 5.31/2.02  #Close   : 0
% 5.31/2.02  
% 5.31/2.02  Ordering : KBO
% 5.31/2.02  
% 5.31/2.02  Simplification rules
% 5.31/2.02  ----------------------
% 5.31/2.03  #Subsume      : 27
% 5.31/2.03  #Demod        : 964
% 5.31/2.03  #Tautology    : 539
% 5.31/2.03  #SimpNegUnit  : 4
% 5.31/2.03  #BackRed      : 14
% 5.31/2.03  
% 5.31/2.03  #Partial instantiations: 0
% 5.31/2.03  #Strategies tried      : 1
% 5.31/2.03  
% 5.31/2.03  Timing (in seconds)
% 5.31/2.03  ----------------------
% 5.31/2.03  Preprocessing        : 0.31
% 5.31/2.03  Parsing              : 0.17
% 5.31/2.03  CNF conversion       : 0.02
% 5.31/2.03  Main loop            : 0.94
% 5.31/2.03  Inferencing          : 0.30
% 5.31/2.03  Reduction            : 0.38
% 5.31/2.03  Demodulation         : 0.31
% 5.31/2.03  BG Simplification    : 0.04
% 5.31/2.03  Subsumption          : 0.15
% 5.31/2.03  Abstraction          : 0.05
% 5.31/2.03  MUC search           : 0.00
% 5.31/2.03  Cooper               : 0.00
% 5.31/2.03  Total                : 1.29
% 5.31/2.03  Index Insertion      : 0.00
% 5.31/2.03  Index Deletion       : 0.00
% 5.31/2.03  Index Matching       : 0.00
% 5.31/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
