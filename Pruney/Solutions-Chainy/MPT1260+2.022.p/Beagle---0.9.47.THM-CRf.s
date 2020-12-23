%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:03 EST 2020

% Result     : Theorem 16.53s
% Output     : CNFRefutation 16.67s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 294 expanded)
%              Number of leaves         :   44 ( 117 expanded)
%              Depth                    :   11
%              Number of atoms          :  167 ( 515 expanded)
%              Number of equality atoms :   63 ( 194 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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

tff(f_161,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_149,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_89,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_128,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_70,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_152,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_18,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_464,plain,(
    ! [A_101,B_102] : k4_xboole_0(A_101,k4_xboole_0(A_101,B_102)) = k3_xboole_0(A_101,B_102) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_499,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_464])).

tff(c_512,plain,(
    ! [A_103] : k4_xboole_0(A_103,A_103) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_499])).

tff(c_16,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_523,plain,(
    ! [A_103] : r1_tarski(k1_xboole_0,A_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_16])).

tff(c_48,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(A_45,k1_zfmisc_1(B_46))
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1921,plain,(
    ! [A_150,B_151] :
      ( k4_xboole_0(A_150,B_151) = k3_subset_1(A_150,B_151)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(A_150)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8253,plain,(
    ! [B_266,A_267] :
      ( k4_xboole_0(B_266,A_267) = k3_subset_1(B_266,A_267)
      | ~ r1_tarski(A_267,B_266) ) ),
    inference(resolution,[status(thm)],[c_48,c_1921])).

tff(c_8313,plain,(
    ! [A_103] : k4_xboole_0(A_103,k1_xboole_0) = k3_subset_1(A_103,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_523,c_8253])).

tff(c_8346,plain,(
    ! [A_103] : k3_subset_1(A_103,k1_xboole_0) = A_103 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_8313])).

tff(c_66,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_64,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_2727,plain,(
    ! [A_169,B_170,C_171] :
      ( k7_subset_1(A_169,B_170,C_171) = k4_xboole_0(B_170,C_171)
      | ~ m1_subset_1(B_170,k1_zfmisc_1(A_169)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2736,plain,(
    ! [C_171] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_171) = k4_xboole_0('#skF_2',C_171) ),
    inference(resolution,[status(thm)],[c_64,c_2727])).

tff(c_5529,plain,(
    ! [A_229,B_230] :
      ( k7_subset_1(u1_struct_0(A_229),B_230,k2_tops_1(A_229,B_230)) = k1_tops_1(A_229,B_230)
      | ~ m1_subset_1(B_230,k1_zfmisc_1(u1_struct_0(A_229)))
      | ~ l1_pre_topc(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_5563,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_5529])).

tff(c_5598,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2736,c_5563])).

tff(c_3657,plain,(
    ! [A_200,B_201] :
      ( m1_subset_1(k2_pre_topc(A_200,B_201),k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ l1_pre_topc(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_42,plain,(
    ! [A_40,B_41,C_42] :
      ( k7_subset_1(A_40,B_41,C_42) = k4_xboole_0(B_41,C_42)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_41454,plain,(
    ! [A_581,B_582,C_583] :
      ( k7_subset_1(u1_struct_0(A_581),k2_pre_topc(A_581,B_582),C_583) = k4_xboole_0(k2_pre_topc(A_581,B_582),C_583)
      | ~ m1_subset_1(B_582,k1_zfmisc_1(u1_struct_0(A_581)))
      | ~ l1_pre_topc(A_581) ) ),
    inference(resolution,[status(thm)],[c_3657,c_42])).

tff(c_41488,plain,(
    ! [C_583] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_583) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_583)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_64,c_41454])).

tff(c_54533,plain,(
    ! [C_680] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_680) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_680) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_41488])).

tff(c_76,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_266,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_76])).

tff(c_54569,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_54533,c_266])).

tff(c_22,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,(
    ! [B_24,A_23] : k2_tarski(B_24,A_23) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_153,plain,(
    ! [A_79,B_80] : k1_setfam_1(k2_tarski(A_79,B_80)) = k3_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_196,plain,(
    ! [B_87,A_88] : k1_setfam_1(k2_tarski(B_87,A_88)) = k3_xboole_0(A_88,B_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_153])).

tff(c_44,plain,(
    ! [A_43,B_44] : k1_setfam_1(k2_tarski(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_202,plain,(
    ! [B_87,A_88] : k3_xboole_0(B_87,A_88) = k3_xboole_0(A_88,B_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_44])).

tff(c_1420,plain,(
    ! [A_138,B_139,C_140] : k4_xboole_0(k3_xboole_0(A_138,B_139),C_140) = k3_xboole_0(A_138,k4_xboole_0(B_139,C_140)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_509,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_499])).

tff(c_4093,plain,(
    ! [A_213,B_214] : k3_xboole_0(A_213,k4_xboole_0(B_214,k3_xboole_0(A_213,B_214))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1420,c_509])).

tff(c_4222,plain,(
    ! [A_88,B_87] : k3_xboole_0(A_88,k4_xboole_0(B_87,k3_xboole_0(B_87,A_88))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_4093])).

tff(c_4266,plain,(
    ! [A_88,B_87] : k3_xboole_0(A_88,k4_xboole_0(B_87,A_88)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_4222])).

tff(c_54857,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_54569,c_4266])).

tff(c_477,plain,(
    ! [A_101,B_102] : r1_tarski(k3_xboole_0(A_101,B_102),A_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_464,c_16])).

tff(c_8310,plain,(
    ! [A_101,B_102] : k4_xboole_0(A_101,k3_xboole_0(A_101,B_102)) = k3_subset_1(A_101,k3_xboole_0(A_101,B_102)) ),
    inference(resolution,[status(thm)],[c_477,c_8253])).

tff(c_8344,plain,(
    ! [A_101,B_102] : k3_subset_1(A_101,k3_xboole_0(A_101,B_102)) = k4_xboole_0(A_101,B_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_8310])).

tff(c_55028,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_54857,c_8344])).

tff(c_55108,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8346,c_5598,c_55028])).

tff(c_68,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_3146,plain,(
    ! [A_185,B_186,C_187] :
      ( m1_subset_1(k7_subset_1(A_185,B_186,C_187),k1_zfmisc_1(A_185))
      | ~ m1_subset_1(B_186,k1_zfmisc_1(A_185)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3159,plain,(
    ! [C_171] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_171),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2736,c_3146])).

tff(c_3168,plain,(
    ! [C_171] : m1_subset_1(k4_xboole_0('#skF_2',C_171),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3159])).

tff(c_3260,plain,(
    ! [A_189,B_190] :
      ( v3_pre_topc(k1_tops_1(A_189,B_190),A_189)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3264,plain,(
    ! [C_171] :
      ( v3_pre_topc(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',C_171)),'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_3168,c_3260])).

tff(c_3281,plain,(
    ! [C_171] : v3_pre_topc(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',C_171)),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_3264])).

tff(c_5616,plain,(
    v3_pre_topc(k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5598,c_3281])).

tff(c_55148,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55108,c_55108,c_5616])).

tff(c_55179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_55148])).

tff(c_55180,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_57734,plain,(
    ! [A_764,B_765,C_766] :
      ( k7_subset_1(A_764,B_765,C_766) = k4_xboole_0(B_765,C_766)
      | ~ m1_subset_1(B_765,k1_zfmisc_1(A_764)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_57743,plain,(
    ! [C_766] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_766) = k4_xboole_0('#skF_2',C_766) ),
    inference(resolution,[status(thm)],[c_64,c_57734])).

tff(c_60636,plain,(
    ! [A_830,B_831] :
      ( k7_subset_1(u1_struct_0(A_830),B_831,k2_tops_1(A_830,B_831)) = k1_tops_1(A_830,B_831)
      | ~ m1_subset_1(B_831,k1_zfmisc_1(u1_struct_0(A_830)))
      | ~ l1_pre_topc(A_830) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_60666,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_60636])).

tff(c_60695,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_57743,c_60666])).

tff(c_60741,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_60695,c_16])).

tff(c_55181,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_61413,plain,(
    ! [B_838,A_839,C_840] :
      ( r1_tarski(B_838,k1_tops_1(A_839,C_840))
      | ~ r1_tarski(B_838,C_840)
      | ~ v3_pre_topc(B_838,A_839)
      | ~ m1_subset_1(C_840,k1_zfmisc_1(u1_struct_0(A_839)))
      | ~ m1_subset_1(B_838,k1_zfmisc_1(u1_struct_0(A_839)))
      | ~ l1_pre_topc(A_839) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_61445,plain,(
    ! [B_838] :
      ( r1_tarski(B_838,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_838,'#skF_2')
      | ~ v3_pre_topc(B_838,'#skF_1')
      | ~ m1_subset_1(B_838,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_64,c_61413])).

tff(c_73264,plain,(
    ! [B_989] :
      ( r1_tarski(B_989,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_989,'#skF_2')
      | ~ v3_pre_topc(B_989,'#skF_1')
      | ~ m1_subset_1(B_989,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_61445])).

tff(c_73309,plain,
    ( r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_73264])).

tff(c_73336,plain,(
    r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55181,c_8,c_73309])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_73343,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_73336,c_4])).

tff(c_73352,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60741,c_73343])).

tff(c_54,plain,(
    ! [A_51,B_53] :
      ( k7_subset_1(u1_struct_0(A_51),k2_pre_topc(A_51,B_53),k1_tops_1(A_51,B_53)) = k2_tops_1(A_51,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_73388,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_73352,c_54])).

tff(c_73394,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_73388])).

tff(c_73396,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55180,c_73394])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:53:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.53/9.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.53/9.94  
% 16.53/9.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.53/9.94  %$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 16.53/9.94  
% 16.53/9.94  %Foreground sorts:
% 16.53/9.94  
% 16.53/9.94  
% 16.53/9.94  %Background operators:
% 16.53/9.94  
% 16.53/9.94  
% 16.53/9.94  %Foreground operators:
% 16.53/9.94  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 16.53/9.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.53/9.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.53/9.94  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 16.53/9.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.53/9.94  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 16.53/9.94  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 16.53/9.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.53/9.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.53/9.94  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 16.53/9.94  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 16.53/9.94  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 16.53/9.94  tff('#skF_2', type, '#skF_2': $i).
% 16.53/9.94  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 16.53/9.94  tff('#skF_1', type, '#skF_1': $i).
% 16.53/9.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.53/9.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.53/9.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.53/9.94  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 16.53/9.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.53/9.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.53/9.94  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 16.53/9.94  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 16.53/9.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.53/9.94  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 16.53/9.94  
% 16.67/9.96  tff(f_161, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 16.67/9.96  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 16.67/9.96  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 16.67/9.96  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 16.67/9.96  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 16.67/9.96  tff(f_93, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 16.67/9.96  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 16.67/9.96  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 16.67/9.96  tff(f_149, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 16.67/9.96  tff(f_99, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 16.67/9.96  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 16.67/9.96  tff(f_55, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 16.67/9.96  tff(f_89, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 16.67/9.96  tff(f_53, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 16.67/9.96  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 16.67/9.96  tff(f_107, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 16.67/9.96  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.67/9.96  tff(f_128, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 16.67/9.96  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 16.67/9.96  tff(c_70, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 16.67/9.96  tff(c_152, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_70])).
% 16.67/9.96  tff(c_18, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 16.67/9.96  tff(c_14, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 16.67/9.96  tff(c_464, plain, (![A_101, B_102]: (k4_xboole_0(A_101, k4_xboole_0(A_101, B_102))=k3_xboole_0(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_51])).
% 16.67/9.96  tff(c_499, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_464])).
% 16.67/9.96  tff(c_512, plain, (![A_103]: (k4_xboole_0(A_103, A_103)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_499])).
% 16.67/9.96  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 16.67/9.96  tff(c_523, plain, (![A_103]: (r1_tarski(k1_xboole_0, A_103))), inference(superposition, [status(thm), theory('equality')], [c_512, c_16])).
% 16.67/9.96  tff(c_48, plain, (![A_45, B_46]: (m1_subset_1(A_45, k1_zfmisc_1(B_46)) | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.67/9.96  tff(c_1921, plain, (![A_150, B_151]: (k4_xboole_0(A_150, B_151)=k3_subset_1(A_150, B_151) | ~m1_subset_1(B_151, k1_zfmisc_1(A_150)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 16.67/9.96  tff(c_8253, plain, (![B_266, A_267]: (k4_xboole_0(B_266, A_267)=k3_subset_1(B_266, A_267) | ~r1_tarski(A_267, B_266))), inference(resolution, [status(thm)], [c_48, c_1921])).
% 16.67/9.96  tff(c_8313, plain, (![A_103]: (k4_xboole_0(A_103, k1_xboole_0)=k3_subset_1(A_103, k1_xboole_0))), inference(resolution, [status(thm)], [c_523, c_8253])).
% 16.67/9.96  tff(c_8346, plain, (![A_103]: (k3_subset_1(A_103, k1_xboole_0)=A_103)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_8313])).
% 16.67/9.96  tff(c_66, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 16.67/9.96  tff(c_64, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 16.67/9.96  tff(c_2727, plain, (![A_169, B_170, C_171]: (k7_subset_1(A_169, B_170, C_171)=k4_xboole_0(B_170, C_171) | ~m1_subset_1(B_170, k1_zfmisc_1(A_169)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 16.67/9.96  tff(c_2736, plain, (![C_171]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_171)=k4_xboole_0('#skF_2', C_171))), inference(resolution, [status(thm)], [c_64, c_2727])).
% 16.67/9.96  tff(c_5529, plain, (![A_229, B_230]: (k7_subset_1(u1_struct_0(A_229), B_230, k2_tops_1(A_229, B_230))=k1_tops_1(A_229, B_230) | ~m1_subset_1(B_230, k1_zfmisc_1(u1_struct_0(A_229))) | ~l1_pre_topc(A_229))), inference(cnfTransformation, [status(thm)], [f_149])).
% 16.67/9.96  tff(c_5563, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_5529])).
% 16.67/9.96  tff(c_5598, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2736, c_5563])).
% 16.67/9.96  tff(c_3657, plain, (![A_200, B_201]: (m1_subset_1(k2_pre_topc(A_200, B_201), k1_zfmisc_1(u1_struct_0(A_200))) | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0(A_200))) | ~l1_pre_topc(A_200))), inference(cnfTransformation, [status(thm)], [f_99])).
% 16.67/9.96  tff(c_42, plain, (![A_40, B_41, C_42]: (k7_subset_1(A_40, B_41, C_42)=k4_xboole_0(B_41, C_42) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 16.67/9.96  tff(c_41454, plain, (![A_581, B_582, C_583]: (k7_subset_1(u1_struct_0(A_581), k2_pre_topc(A_581, B_582), C_583)=k4_xboole_0(k2_pre_topc(A_581, B_582), C_583) | ~m1_subset_1(B_582, k1_zfmisc_1(u1_struct_0(A_581))) | ~l1_pre_topc(A_581))), inference(resolution, [status(thm)], [c_3657, c_42])).
% 16.67/9.96  tff(c_41488, plain, (![C_583]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_583)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_583) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_64, c_41454])).
% 16.67/9.96  tff(c_54533, plain, (![C_680]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_680)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_680))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_41488])).
% 16.67/9.96  tff(c_76, plain, (v3_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 16.67/9.96  tff(c_266, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_152, c_76])).
% 16.67/9.96  tff(c_54569, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_54533, c_266])).
% 16.67/9.96  tff(c_22, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 16.67/9.96  tff(c_28, plain, (![B_24, A_23]: (k2_tarski(B_24, A_23)=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_55])).
% 16.67/9.96  tff(c_153, plain, (![A_79, B_80]: (k1_setfam_1(k2_tarski(A_79, B_80))=k3_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_89])).
% 16.67/9.96  tff(c_196, plain, (![B_87, A_88]: (k1_setfam_1(k2_tarski(B_87, A_88))=k3_xboole_0(A_88, B_87))), inference(superposition, [status(thm), theory('equality')], [c_28, c_153])).
% 16.67/9.96  tff(c_44, plain, (![A_43, B_44]: (k1_setfam_1(k2_tarski(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_89])).
% 16.67/9.96  tff(c_202, plain, (![B_87, A_88]: (k3_xboole_0(B_87, A_88)=k3_xboole_0(A_88, B_87))), inference(superposition, [status(thm), theory('equality')], [c_196, c_44])).
% 16.67/9.96  tff(c_1420, plain, (![A_138, B_139, C_140]: (k4_xboole_0(k3_xboole_0(A_138, B_139), C_140)=k3_xboole_0(A_138, k4_xboole_0(B_139, C_140)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 16.67/9.96  tff(c_509, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_499])).
% 16.67/9.96  tff(c_4093, plain, (![A_213, B_214]: (k3_xboole_0(A_213, k4_xboole_0(B_214, k3_xboole_0(A_213, B_214)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1420, c_509])).
% 16.67/9.96  tff(c_4222, plain, (![A_88, B_87]: (k3_xboole_0(A_88, k4_xboole_0(B_87, k3_xboole_0(B_87, A_88)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_202, c_4093])).
% 16.67/9.96  tff(c_4266, plain, (![A_88, B_87]: (k3_xboole_0(A_88, k4_xboole_0(B_87, A_88))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_4222])).
% 16.67/9.96  tff(c_54857, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_54569, c_4266])).
% 16.67/9.96  tff(c_477, plain, (![A_101, B_102]: (r1_tarski(k3_xboole_0(A_101, B_102), A_101))), inference(superposition, [status(thm), theory('equality')], [c_464, c_16])).
% 16.67/9.96  tff(c_8310, plain, (![A_101, B_102]: (k4_xboole_0(A_101, k3_xboole_0(A_101, B_102))=k3_subset_1(A_101, k3_xboole_0(A_101, B_102)))), inference(resolution, [status(thm)], [c_477, c_8253])).
% 16.67/9.96  tff(c_8344, plain, (![A_101, B_102]: (k3_subset_1(A_101, k3_xboole_0(A_101, B_102))=k4_xboole_0(A_101, B_102))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_8310])).
% 16.67/9.96  tff(c_55028, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_54857, c_8344])).
% 16.67/9.96  tff(c_55108, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8346, c_5598, c_55028])).
% 16.67/9.96  tff(c_68, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 16.67/9.96  tff(c_3146, plain, (![A_185, B_186, C_187]: (m1_subset_1(k7_subset_1(A_185, B_186, C_187), k1_zfmisc_1(A_185)) | ~m1_subset_1(B_186, k1_zfmisc_1(A_185)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.67/9.96  tff(c_3159, plain, (![C_171]: (m1_subset_1(k4_xboole_0('#skF_2', C_171), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_2736, c_3146])).
% 16.67/9.96  tff(c_3168, plain, (![C_171]: (m1_subset_1(k4_xboole_0('#skF_2', C_171), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3159])).
% 16.67/9.96  tff(c_3260, plain, (![A_189, B_190]: (v3_pre_topc(k1_tops_1(A_189, B_190), A_189) | ~m1_subset_1(B_190, k1_zfmisc_1(u1_struct_0(A_189))) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189))), inference(cnfTransformation, [status(thm)], [f_107])).
% 16.67/9.96  tff(c_3264, plain, (![C_171]: (v3_pre_topc(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', C_171)), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_3168, c_3260])).
% 16.67/9.96  tff(c_3281, plain, (![C_171]: (v3_pre_topc(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', C_171)), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_3264])).
% 16.67/9.96  tff(c_5616, plain, (v3_pre_topc(k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5598, c_3281])).
% 16.67/9.96  tff(c_55148, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_55108, c_55108, c_5616])).
% 16.67/9.96  tff(c_55179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_152, c_55148])).
% 16.67/9.96  tff(c_55180, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_70])).
% 16.67/9.96  tff(c_57734, plain, (![A_764, B_765, C_766]: (k7_subset_1(A_764, B_765, C_766)=k4_xboole_0(B_765, C_766) | ~m1_subset_1(B_765, k1_zfmisc_1(A_764)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 16.67/9.96  tff(c_57743, plain, (![C_766]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_766)=k4_xboole_0('#skF_2', C_766))), inference(resolution, [status(thm)], [c_64, c_57734])).
% 16.67/9.96  tff(c_60636, plain, (![A_830, B_831]: (k7_subset_1(u1_struct_0(A_830), B_831, k2_tops_1(A_830, B_831))=k1_tops_1(A_830, B_831) | ~m1_subset_1(B_831, k1_zfmisc_1(u1_struct_0(A_830))) | ~l1_pre_topc(A_830))), inference(cnfTransformation, [status(thm)], [f_149])).
% 16.67/9.96  tff(c_60666, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_60636])).
% 16.67/9.96  tff(c_60695, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_57743, c_60666])).
% 16.67/9.96  tff(c_60741, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_60695, c_16])).
% 16.67/9.96  tff(c_55181, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_70])).
% 16.67/9.96  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 16.67/9.96  tff(c_61413, plain, (![B_838, A_839, C_840]: (r1_tarski(B_838, k1_tops_1(A_839, C_840)) | ~r1_tarski(B_838, C_840) | ~v3_pre_topc(B_838, A_839) | ~m1_subset_1(C_840, k1_zfmisc_1(u1_struct_0(A_839))) | ~m1_subset_1(B_838, k1_zfmisc_1(u1_struct_0(A_839))) | ~l1_pre_topc(A_839))), inference(cnfTransformation, [status(thm)], [f_128])).
% 16.67/9.96  tff(c_61445, plain, (![B_838]: (r1_tarski(B_838, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_838, '#skF_2') | ~v3_pre_topc(B_838, '#skF_1') | ~m1_subset_1(B_838, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_64, c_61413])).
% 16.67/9.96  tff(c_73264, plain, (![B_989]: (r1_tarski(B_989, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_989, '#skF_2') | ~v3_pre_topc(B_989, '#skF_1') | ~m1_subset_1(B_989, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_61445])).
% 16.67/9.96  tff(c_73309, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_73264])).
% 16.67/9.96  tff(c_73336, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_55181, c_8, c_73309])).
% 16.67/9.96  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 16.67/9.96  tff(c_73343, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_73336, c_4])).
% 16.67/9.96  tff(c_73352, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60741, c_73343])).
% 16.67/9.96  tff(c_54, plain, (![A_51, B_53]: (k7_subset_1(u1_struct_0(A_51), k2_pre_topc(A_51, B_53), k1_tops_1(A_51, B_53))=k2_tops_1(A_51, B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_114])).
% 16.67/9.96  tff(c_73388, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_73352, c_54])).
% 16.67/9.96  tff(c_73394, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_73388])).
% 16.67/9.96  tff(c_73396, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55180, c_73394])).
% 16.67/9.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.67/9.96  
% 16.67/9.96  Inference rules
% 16.67/9.96  ----------------------
% 16.67/9.96  #Ref     : 0
% 16.67/9.96  #Sup     : 18042
% 16.67/9.96  #Fact    : 0
% 16.67/9.96  #Define  : 0
% 16.67/9.96  #Split   : 4
% 16.67/9.96  #Chain   : 0
% 16.67/9.96  #Close   : 0
% 16.67/9.96  
% 16.67/9.96  Ordering : KBO
% 16.67/9.96  
% 16.67/9.96  Simplification rules
% 16.67/9.96  ----------------------
% 16.67/9.96  #Subsume      : 150
% 16.67/9.96  #Demod        : 21509
% 16.67/9.96  #Tautology    : 12460
% 16.67/9.96  #SimpNegUnit  : 3
% 16.67/9.96  #BackRed      : 112
% 16.67/9.96  
% 16.67/9.96  #Partial instantiations: 0
% 16.67/9.96  #Strategies tried      : 1
% 16.67/9.96  
% 16.67/9.96  Timing (in seconds)
% 16.67/9.96  ----------------------
% 16.67/9.97  Preprocessing        : 0.35
% 16.67/9.97  Parsing              : 0.19
% 16.67/9.97  CNF conversion       : 0.02
% 16.67/9.97  Main loop            : 8.78
% 16.67/9.97  Inferencing          : 1.26
% 16.67/9.97  Reduction            : 5.36
% 16.67/9.97  Demodulation         : 4.79
% 16.67/9.97  BG Simplification    : 0.14
% 16.67/9.97  Subsumption          : 1.60
% 16.67/9.97  Abstraction          : 0.26
% 16.67/9.97  MUC search           : 0.00
% 16.67/9.97  Cooper               : 0.00
% 16.67/9.97  Total                : 9.17
% 16.67/9.97  Index Insertion      : 0.00
% 16.67/9.97  Index Deletion       : 0.00
% 16.67/9.97  Index Matching       : 0.00
% 16.67/9.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
