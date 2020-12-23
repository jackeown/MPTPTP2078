%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:05 EST 2020

% Result     : Theorem 10.60s
% Output     : CNFRefutation 10.60s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 748 expanded)
%              Number of leaves         :   44 ( 270 expanded)
%              Depth                    :   15
%              Number of atoms          :  249 (1570 expanded)
%              Number of equality atoms :   87 ( 448 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_158,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_67,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_51,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_132,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_139,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_146,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_62,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_124,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_60,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_56,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_247,plain,(
    ! [A_102,B_103] :
      ( k4_xboole_0(A_102,B_103) = k3_subset_1(A_102,B_103)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_259,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_247])).

tff(c_28,plain,(
    ! [A_26,B_27] : k6_subset_1(A_26,B_27) = k4_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    ! [A_16,B_17] : m1_subset_1(k6_subset_1(A_16,B_17),k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_69,plain,(
    ! [A_16,B_17] : m1_subset_1(k4_xboole_0(A_16,B_17),k1_zfmisc_1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_20])).

tff(c_272,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_69])).

tff(c_48,plain,(
    ! [C_60,A_48,D_62,B_56] :
      ( v3_pre_topc(C_60,A_48)
      | k1_tops_1(A_48,C_60) != C_60
      | ~ m1_subset_1(D_62,k1_zfmisc_1(u1_struct_0(B_56)))
      | ~ m1_subset_1(C_60,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(B_56)
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2363,plain,(
    ! [D_218,B_219] :
      ( ~ m1_subset_1(D_218,k1_zfmisc_1(u1_struct_0(B_219)))
      | ~ l1_pre_topc(B_219) ) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_2379,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_272,c_2363])).

tff(c_2397,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2379])).

tff(c_2675,plain,(
    ! [C_224,A_225] :
      ( v3_pre_topc(C_224,A_225)
      | k1_tops_1(A_225,C_224) != C_224
      | ~ m1_subset_1(C_224,k1_zfmisc_1(u1_struct_0(A_225)))
      | ~ l1_pre_topc(A_225)
      | ~ v2_pre_topc(A_225) ) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2711,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_2675])).

tff(c_2725,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_2711])).

tff(c_2726,plain,(
    k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_2725])).

tff(c_865,plain,(
    ! [A_147,B_148] :
      ( m1_subset_1(k2_pre_topc(A_147,B_148),k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ l1_pre_topc(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_30,plain,(
    ! [A_28,B_29,C_30] :
      ( k7_subset_1(A_28,B_29,C_30) = k4_xboole_0(B_29,C_30)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10877,plain,(
    ! [A_436,B_437,C_438] :
      ( k7_subset_1(u1_struct_0(A_436),k2_pre_topc(A_436,B_437),C_438) = k4_xboole_0(k2_pre_topc(A_436,B_437),C_438)
      | ~ m1_subset_1(B_437,k1_zfmisc_1(u1_struct_0(A_436)))
      | ~ l1_pre_topc(A_436) ) ),
    inference(resolution,[status(thm)],[c_865,c_30])).

tff(c_10907,plain,(
    ! [C_438] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_438) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_438)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_56,c_10877])).

tff(c_11028,plain,(
    ! [C_441] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_441) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_441) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_10907])).

tff(c_68,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_172,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_68])).

tff(c_11042,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_11028,c_172])).

tff(c_12,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_11196,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11042,c_12])).

tff(c_1422,plain,(
    ! [A_181,B_182] :
      ( k4_subset_1(u1_struct_0(A_181),B_182,k2_tops_1(A_181,B_182)) = k2_pre_topc(A_181,B_182)
      | ~ m1_subset_1(B_182,k1_zfmisc_1(u1_struct_0(A_181)))
      | ~ l1_pre_topc(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1442,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_1422])).

tff(c_1454,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1442])).

tff(c_996,plain,(
    ! [A_156,B_157] :
      ( m1_subset_1(k2_tops_1(A_156,B_157),k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_24,plain,(
    ! [A_21,B_22] :
      ( k3_subset_1(A_21,k3_subset_1(A_21,B_22)) = B_22
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1009,plain,(
    ! [A_156,B_157] :
      ( k3_subset_1(u1_struct_0(A_156),k3_subset_1(u1_struct_0(A_156),k2_tops_1(A_156,B_157))) = k2_tops_1(A_156,B_157)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156) ) ),
    inference(resolution,[status(thm)],[c_996,c_24])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = k3_subset_1(A_12,B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8810,plain,(
    ! [A_399,B_400] :
      ( k4_xboole_0(u1_struct_0(A_399),k2_tops_1(A_399,B_400)) = k3_subset_1(u1_struct_0(A_399),k2_tops_1(A_399,B_400))
      | ~ m1_subset_1(B_400,k1_zfmisc_1(u1_struct_0(A_399)))
      | ~ l1_pre_topc(A_399) ) ),
    inference(resolution,[status(thm)],[c_996,c_16])).

tff(c_8836,plain,
    ( k4_xboole_0(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_8810])).

tff(c_8850,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_8836])).

tff(c_1977,plain,(
    ! [A_208,B_209] : k4_xboole_0(A_208,k4_xboole_0(A_208,B_209)) = k3_subset_1(A_208,k4_xboole_0(A_208,B_209)) ),
    inference(resolution,[status(thm)],[c_69,c_247])).

tff(c_115,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(A_77,B_78)
      | ~ m1_subset_1(A_77,k1_zfmisc_1(B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_122,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(resolution,[status(thm)],[c_69,c_115])).

tff(c_2042,plain,(
    ! [A_208,B_209] : r1_tarski(k3_subset_1(A_208,k4_xboole_0(A_208,B_209)),A_208) ),
    inference(superposition,[status(thm),theory(equality)],[c_1977,c_122])).

tff(c_8986,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8850,c_2042])).

tff(c_14277,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1009,c_8986])).

tff(c_14297,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_14277])).

tff(c_38,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(A_37,k1_zfmisc_1(B_38))
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1224,plain,(
    ! [A_170,B_171,C_172] :
      ( k4_subset_1(A_170,B_171,C_172) = k2_xboole_0(B_171,C_172)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(A_170))
      | ~ m1_subset_1(B_171,k1_zfmisc_1(A_170)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5300,plain,(
    ! [B_301,B_302,A_303] :
      ( k4_subset_1(B_301,B_302,A_303) = k2_xboole_0(B_302,A_303)
      | ~ m1_subset_1(B_302,k1_zfmisc_1(B_301))
      | ~ r1_tarski(A_303,B_301) ) ),
    inference(resolution,[status(thm)],[c_38,c_1224])).

tff(c_5369,plain,(
    ! [A_303] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_303) = k2_xboole_0('#skF_2',A_303)
      | ~ r1_tarski(A_303,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_56,c_5300])).

tff(c_14305,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_14297,c_5369])).

tff(c_14327,plain,(
    k2_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11196,c_1454,c_14305])).

tff(c_663,plain,(
    ! [A_130,B_131,C_132] :
      ( k7_subset_1(A_130,B_131,C_132) = k4_xboole_0(B_131,C_132)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(A_130)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_681,plain,(
    ! [C_132] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_132) = k4_xboole_0('#skF_2',C_132) ),
    inference(resolution,[status(thm)],[c_56,c_663])).

tff(c_1540,plain,(
    ! [A_187,B_188] :
      ( k7_subset_1(u1_struct_0(A_187),B_188,k2_tops_1(A_187,B_188)) = k1_tops_1(A_187,B_188)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0(A_187)))
      | ~ l1_pre_topc(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1560,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_1540])).

tff(c_1572,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_681,c_1560])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_355,plain,(
    ! [A_107,B_108,C_109] :
      ( r1_tarski(A_107,k2_xboole_0(B_108,C_109))
      | ~ r1_tarski(k4_xboole_0(A_107,B_108),C_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_371,plain,(
    ! [A_107,B_108] : r1_tarski(A_107,k2_xboole_0(B_108,k4_xboole_0(A_107,B_108))) ),
    inference(resolution,[status(thm)],[c_8,c_355])).

tff(c_375,plain,(
    ! [A_110,B_111] : r1_tarski(A_110,k2_xboole_0(B_111,A_110)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_371])).

tff(c_456,plain,(
    ! [B_116,A_117] : r1_tarski(k4_xboole_0(B_116,A_117),k2_xboole_0(A_117,B_116)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_375])).

tff(c_543,plain,(
    ! [A_123,B_124] : r1_tarski(k4_xboole_0(A_123,B_124),k2_xboole_0(A_123,B_124)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_456])).

tff(c_566,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,k4_xboole_0(B_8,A_7)),k2_xboole_0(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_543])).

tff(c_11166,plain,(
    r1_tarski(k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')),k2_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_11042,c_566])).

tff(c_11226,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1572,c_11166])).

tff(c_14346,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14327,c_11226])).

tff(c_390,plain,(
    ! [B_2,A_1] : r1_tarski(B_2,k2_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_375])).

tff(c_14651,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14327,c_390])).

tff(c_257,plain,(
    ! [B_38,A_37] :
      ( k4_xboole_0(B_38,A_37) = k3_subset_1(B_38,A_37)
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_38,c_247])).

tff(c_2577,plain,(
    ! [B_222,A_223] : k4_xboole_0(k2_xboole_0(B_222,A_223),A_223) = k3_subset_1(k2_xboole_0(B_222,A_223),A_223) ),
    inference(resolution,[status(thm)],[c_375,c_257])).

tff(c_2661,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),A_1) = k3_subset_1(k2_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2577])).

tff(c_14561,plain,(
    k3_subset_1(k2_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2'),'#skF_2') = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14327,c_2661])).

tff(c_14717,plain,(
    k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14327,c_11042,c_2,c_14561])).

tff(c_200,plain,(
    ! [A_98,B_99] :
      ( k3_subset_1(A_98,k3_subset_1(A_98,B_99)) = B_99
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_207,plain,(
    ! [B_38,A_37] :
      ( k3_subset_1(B_38,k3_subset_1(B_38,A_37)) = A_37
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_38,c_200])).

tff(c_15281,plain,
    ( k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14717,c_207])).

tff(c_15293,plain,(
    k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14651,c_15281])).

tff(c_46,plain,(
    ! [A_45,B_47] :
      ( k7_subset_1(u1_struct_0(A_45),k2_pre_topc(A_45,B_47),k1_tops_1(A_45,B_47)) = k2_tops_1(A_45,B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_11053,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_11028])).

tff(c_11066,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_11053])).

tff(c_14834,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_14346,c_257])).

tff(c_14842,plain,(
    k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11066,c_14834])).

tff(c_16159,plain,
    ( k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14842,c_207])).

tff(c_16171,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14346,c_15293,c_16159])).

tff(c_16173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2726,c_16171])).

tff(c_16174,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_16175,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_16363,plain,(
    ! [A_556,B_557] :
      ( k4_xboole_0(A_556,B_557) = k3_subset_1(A_556,B_557)
      | ~ m1_subset_1(B_557,k1_zfmisc_1(A_556)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16375,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_16363])).

tff(c_16385,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_16375,c_69])).

tff(c_50,plain,(
    ! [B_56,D_62,C_60,A_48] :
      ( k1_tops_1(B_56,D_62) = D_62
      | ~ v3_pre_topc(D_62,B_56)
      | ~ m1_subset_1(D_62,k1_zfmisc_1(u1_struct_0(B_56)))
      | ~ m1_subset_1(C_60,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(B_56)
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_18316,plain,(
    ! [C_669,A_670] :
      ( ~ m1_subset_1(C_669,k1_zfmisc_1(u1_struct_0(A_670)))
      | ~ l1_pre_topc(A_670)
      | ~ v2_pre_topc(A_670) ) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_18338,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16385,c_18316])).

tff(c_18358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_18338])).

tff(c_18489,plain,(
    ! [B_674,D_675] :
      ( k1_tops_1(B_674,D_675) = D_675
      | ~ v3_pre_topc(D_675,B_674)
      | ~ m1_subset_1(D_675,k1_zfmisc_1(u1_struct_0(B_674)))
      | ~ l1_pre_topc(B_674) ) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_18525,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_18489])).

tff(c_18539,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_16175,c_18525])).

tff(c_16584,plain,(
    ! [A_578,B_579,C_580] :
      ( k7_subset_1(A_578,B_579,C_580) = k4_xboole_0(B_579,C_580)
      | ~ m1_subset_1(B_579,k1_zfmisc_1(A_578)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_16602,plain,(
    ! [C_580] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_580) = k4_xboole_0('#skF_2',C_580) ),
    inference(resolution,[status(thm)],[c_56,c_16584])).

tff(c_17383,plain,(
    ! [A_635,B_636] :
      ( k7_subset_1(u1_struct_0(A_635),B_636,k2_tops_1(A_635,B_636)) = k1_tops_1(A_635,B_636)
      | ~ m1_subset_1(B_636,k1_zfmisc_1(u1_struct_0(A_635)))
      | ~ l1_pre_topc(A_635) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_17403,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_17383])).

tff(c_17415,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_16602,c_17403])).

tff(c_17455,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_17415,c_122])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_17475,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_17455,c_4])).

tff(c_17512,plain,(
    ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_17475])).

tff(c_18542,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18539,c_17512])).

tff(c_18552,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18542])).

tff(c_18553,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_17475])).

tff(c_19000,plain,(
    ! [A_693,B_694] :
      ( k7_subset_1(u1_struct_0(A_693),k2_pre_topc(A_693,B_694),k1_tops_1(A_693,B_694)) = k2_tops_1(A_693,B_694)
      | ~ m1_subset_1(B_694,k1_zfmisc_1(u1_struct_0(A_693)))
      | ~ l1_pre_topc(A_693) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_19009,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18553,c_19000])).

tff(c_19013,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_19009])).

tff(c_19015,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16174,c_19013])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:15:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.60/4.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.60/4.78  
% 10.60/4.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.60/4.78  %$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 10.60/4.78  
% 10.60/4.78  %Foreground sorts:
% 10.60/4.78  
% 10.60/4.78  
% 10.60/4.78  %Background operators:
% 10.60/4.78  
% 10.60/4.78  
% 10.60/4.78  %Foreground operators:
% 10.60/4.78  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 10.60/4.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.60/4.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.60/4.78  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 10.60/4.78  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.60/4.78  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.60/4.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.60/4.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.60/4.78  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.60/4.78  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 10.60/4.78  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 10.60/4.78  tff('#skF_2', type, '#skF_2': $i).
% 10.60/4.78  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 10.60/4.78  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 10.60/4.78  tff('#skF_1', type, '#skF_1': $i).
% 10.60/4.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.60/4.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.60/4.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.60/4.78  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.60/4.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.60/4.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.60/4.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.60/4.78  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.60/4.78  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 10.60/4.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.60/4.78  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.60/4.78  
% 10.60/4.80  tff(f_158, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 10.60/4.80  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 10.60/4.80  tff(f_67, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 10.60/4.80  tff(f_51, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 10.60/4.80  tff(f_132, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 10.60/4.80  tff(f_90, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 10.60/4.80  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 10.60/4.80  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 10.60/4.80  tff(f_139, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 10.60/4.80  tff(f_96, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 10.60/4.80  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 10.60/4.80  tff(f_84, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.60/4.80  tff(f_65, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 10.60/4.80  tff(f_146, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 10.60/4.80  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 10.60/4.80  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.60/4.80  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 10.60/4.80  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 10.60/4.80  tff(c_62, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 10.60/4.80  tff(c_124, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_62])).
% 10.60/4.80  tff(c_60, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 10.60/4.80  tff(c_58, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 10.60/4.80  tff(c_56, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 10.60/4.80  tff(c_247, plain, (![A_102, B_103]: (k4_xboole_0(A_102, B_103)=k3_subset_1(A_102, B_103) | ~m1_subset_1(B_103, k1_zfmisc_1(A_102)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.60/4.80  tff(c_259, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_56, c_247])).
% 10.60/4.80  tff(c_28, plain, (![A_26, B_27]: (k6_subset_1(A_26, B_27)=k4_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.60/4.80  tff(c_20, plain, (![A_16, B_17]: (m1_subset_1(k6_subset_1(A_16, B_17), k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.60/4.80  tff(c_69, plain, (![A_16, B_17]: (m1_subset_1(k4_xboole_0(A_16, B_17), k1_zfmisc_1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_20])).
% 10.60/4.80  tff(c_272, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_259, c_69])).
% 10.60/4.80  tff(c_48, plain, (![C_60, A_48, D_62, B_56]: (v3_pre_topc(C_60, A_48) | k1_tops_1(A_48, C_60)!=C_60 | ~m1_subset_1(D_62, k1_zfmisc_1(u1_struct_0(B_56))) | ~m1_subset_1(C_60, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(B_56) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.60/4.80  tff(c_2363, plain, (![D_218, B_219]: (~m1_subset_1(D_218, k1_zfmisc_1(u1_struct_0(B_219))) | ~l1_pre_topc(B_219))), inference(splitLeft, [status(thm)], [c_48])).
% 10.60/4.80  tff(c_2379, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_272, c_2363])).
% 10.60/4.80  tff(c_2397, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_2379])).
% 10.60/4.80  tff(c_2675, plain, (![C_224, A_225]: (v3_pre_topc(C_224, A_225) | k1_tops_1(A_225, C_224)!=C_224 | ~m1_subset_1(C_224, k1_zfmisc_1(u1_struct_0(A_225))) | ~l1_pre_topc(A_225) | ~v2_pre_topc(A_225))), inference(splitRight, [status(thm)], [c_48])).
% 10.60/4.80  tff(c_2711, plain, (v3_pre_topc('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_2675])).
% 10.60/4.80  tff(c_2725, plain, (v3_pre_topc('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_2711])).
% 10.60/4.80  tff(c_2726, plain, (k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_124, c_2725])).
% 10.60/4.80  tff(c_865, plain, (![A_147, B_148]: (m1_subset_1(k2_pre_topc(A_147, B_148), k1_zfmisc_1(u1_struct_0(A_147))) | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0(A_147))) | ~l1_pre_topc(A_147))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.60/4.80  tff(c_30, plain, (![A_28, B_29, C_30]: (k7_subset_1(A_28, B_29, C_30)=k4_xboole_0(B_29, C_30) | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.60/4.80  tff(c_10877, plain, (![A_436, B_437, C_438]: (k7_subset_1(u1_struct_0(A_436), k2_pre_topc(A_436, B_437), C_438)=k4_xboole_0(k2_pre_topc(A_436, B_437), C_438) | ~m1_subset_1(B_437, k1_zfmisc_1(u1_struct_0(A_436))) | ~l1_pre_topc(A_436))), inference(resolution, [status(thm)], [c_865, c_30])).
% 10.60/4.80  tff(c_10907, plain, (![C_438]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_438)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_438) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_56, c_10877])).
% 10.60/4.80  tff(c_11028, plain, (![C_441]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_441)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_441))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_10907])).
% 10.60/4.80  tff(c_68, plain, (v3_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 10.60/4.80  tff(c_172, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_124, c_68])).
% 10.60/4.80  tff(c_11042, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11028, c_172])).
% 10.60/4.80  tff(c_12, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.60/4.80  tff(c_11196, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_11042, c_12])).
% 10.60/4.80  tff(c_1422, plain, (![A_181, B_182]: (k4_subset_1(u1_struct_0(A_181), B_182, k2_tops_1(A_181, B_182))=k2_pre_topc(A_181, B_182) | ~m1_subset_1(B_182, k1_zfmisc_1(u1_struct_0(A_181))) | ~l1_pre_topc(A_181))), inference(cnfTransformation, [status(thm)], [f_139])).
% 10.60/4.80  tff(c_1442, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_1422])).
% 10.60/4.80  tff(c_1454, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1442])).
% 10.60/4.80  tff(c_996, plain, (![A_156, B_157]: (m1_subset_1(k2_tops_1(A_156, B_157), k1_zfmisc_1(u1_struct_0(A_156))) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156))), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.60/4.80  tff(c_24, plain, (![A_21, B_22]: (k3_subset_1(A_21, k3_subset_1(A_21, B_22))=B_22 | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.60/4.80  tff(c_1009, plain, (![A_156, B_157]: (k3_subset_1(u1_struct_0(A_156), k3_subset_1(u1_struct_0(A_156), k2_tops_1(A_156, B_157)))=k2_tops_1(A_156, B_157) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156))), inference(resolution, [status(thm)], [c_996, c_24])).
% 10.60/4.80  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=k3_subset_1(A_12, B_13) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.60/4.80  tff(c_8810, plain, (![A_399, B_400]: (k4_xboole_0(u1_struct_0(A_399), k2_tops_1(A_399, B_400))=k3_subset_1(u1_struct_0(A_399), k2_tops_1(A_399, B_400)) | ~m1_subset_1(B_400, k1_zfmisc_1(u1_struct_0(A_399))) | ~l1_pre_topc(A_399))), inference(resolution, [status(thm)], [c_996, c_16])).
% 10.60/4.80  tff(c_8836, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_8810])).
% 10.60/4.80  tff(c_8850, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_8836])).
% 10.60/4.80  tff(c_1977, plain, (![A_208, B_209]: (k4_xboole_0(A_208, k4_xboole_0(A_208, B_209))=k3_subset_1(A_208, k4_xboole_0(A_208, B_209)))), inference(resolution, [status(thm)], [c_69, c_247])).
% 10.60/4.80  tff(c_115, plain, (![A_77, B_78]: (r1_tarski(A_77, B_78) | ~m1_subset_1(A_77, k1_zfmisc_1(B_78)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.60/4.80  tff(c_122, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(resolution, [status(thm)], [c_69, c_115])).
% 10.60/4.80  tff(c_2042, plain, (![A_208, B_209]: (r1_tarski(k3_subset_1(A_208, k4_xboole_0(A_208, B_209)), A_208))), inference(superposition, [status(thm), theory('equality')], [c_1977, c_122])).
% 10.60/4.80  tff(c_8986, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_8850, c_2042])).
% 10.60/4.80  tff(c_14277, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1009, c_8986])).
% 10.60/4.80  tff(c_14297, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_14277])).
% 10.60/4.80  tff(c_38, plain, (![A_37, B_38]: (m1_subset_1(A_37, k1_zfmisc_1(B_38)) | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.60/4.80  tff(c_1224, plain, (![A_170, B_171, C_172]: (k4_subset_1(A_170, B_171, C_172)=k2_xboole_0(B_171, C_172) | ~m1_subset_1(C_172, k1_zfmisc_1(A_170)) | ~m1_subset_1(B_171, k1_zfmisc_1(A_170)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.60/4.80  tff(c_5300, plain, (![B_301, B_302, A_303]: (k4_subset_1(B_301, B_302, A_303)=k2_xboole_0(B_302, A_303) | ~m1_subset_1(B_302, k1_zfmisc_1(B_301)) | ~r1_tarski(A_303, B_301))), inference(resolution, [status(thm)], [c_38, c_1224])).
% 10.60/4.80  tff(c_5369, plain, (![A_303]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_303)=k2_xboole_0('#skF_2', A_303) | ~r1_tarski(A_303, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_56, c_5300])).
% 10.60/4.80  tff(c_14305, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_14297, c_5369])).
% 10.60/4.80  tff(c_14327, plain, (k2_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11196, c_1454, c_14305])).
% 10.60/4.80  tff(c_663, plain, (![A_130, B_131, C_132]: (k7_subset_1(A_130, B_131, C_132)=k4_xboole_0(B_131, C_132) | ~m1_subset_1(B_131, k1_zfmisc_1(A_130)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.60/4.80  tff(c_681, plain, (![C_132]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_132)=k4_xboole_0('#skF_2', C_132))), inference(resolution, [status(thm)], [c_56, c_663])).
% 10.60/4.80  tff(c_1540, plain, (![A_187, B_188]: (k7_subset_1(u1_struct_0(A_187), B_188, k2_tops_1(A_187, B_188))=k1_tops_1(A_187, B_188) | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0(A_187))) | ~l1_pre_topc(A_187))), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.60/4.80  tff(c_1560, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_1540])).
% 10.60/4.80  tff(c_1572, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_681, c_1560])).
% 10.60/4.80  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.60/4.80  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.60/4.80  tff(c_355, plain, (![A_107, B_108, C_109]: (r1_tarski(A_107, k2_xboole_0(B_108, C_109)) | ~r1_tarski(k4_xboole_0(A_107, B_108), C_109))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.60/4.80  tff(c_371, plain, (![A_107, B_108]: (r1_tarski(A_107, k2_xboole_0(B_108, k4_xboole_0(A_107, B_108))))), inference(resolution, [status(thm)], [c_8, c_355])).
% 10.60/4.80  tff(c_375, plain, (![A_110, B_111]: (r1_tarski(A_110, k2_xboole_0(B_111, A_110)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_371])).
% 10.60/4.80  tff(c_456, plain, (![B_116, A_117]: (r1_tarski(k4_xboole_0(B_116, A_117), k2_xboole_0(A_117, B_116)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_375])).
% 10.60/4.80  tff(c_543, plain, (![A_123, B_124]: (r1_tarski(k4_xboole_0(A_123, B_124), k2_xboole_0(A_123, B_124)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_456])).
% 10.60/4.80  tff(c_566, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, k4_xboole_0(B_8, A_7)), k2_xboole_0(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_543])).
% 10.60/4.80  tff(c_11166, plain, (r1_tarski(k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')), k2_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_11042, c_566])).
% 10.60/4.80  tff(c_11226, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1572, c_11166])).
% 10.60/4.80  tff(c_14346, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14327, c_11226])).
% 10.60/4.80  tff(c_390, plain, (![B_2, A_1]: (r1_tarski(B_2, k2_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_375])).
% 10.60/4.80  tff(c_14651, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_14327, c_390])).
% 10.60/4.80  tff(c_257, plain, (![B_38, A_37]: (k4_xboole_0(B_38, A_37)=k3_subset_1(B_38, A_37) | ~r1_tarski(A_37, B_38))), inference(resolution, [status(thm)], [c_38, c_247])).
% 10.60/4.80  tff(c_2577, plain, (![B_222, A_223]: (k4_xboole_0(k2_xboole_0(B_222, A_223), A_223)=k3_subset_1(k2_xboole_0(B_222, A_223), A_223))), inference(resolution, [status(thm)], [c_375, c_257])).
% 10.60/4.80  tff(c_2661, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), A_1)=k3_subset_1(k2_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2577])).
% 10.60/4.80  tff(c_14561, plain, (k3_subset_1(k2_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2'), '#skF_2')=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14327, c_2661])).
% 10.60/4.80  tff(c_14717, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14327, c_11042, c_2, c_14561])).
% 10.60/4.80  tff(c_200, plain, (![A_98, B_99]: (k3_subset_1(A_98, k3_subset_1(A_98, B_99))=B_99 | ~m1_subset_1(B_99, k1_zfmisc_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.60/4.80  tff(c_207, plain, (![B_38, A_37]: (k3_subset_1(B_38, k3_subset_1(B_38, A_37))=A_37 | ~r1_tarski(A_37, B_38))), inference(resolution, [status(thm)], [c_38, c_200])).
% 10.60/4.80  tff(c_15281, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_14717, c_207])).
% 10.60/4.80  tff(c_15293, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14651, c_15281])).
% 10.60/4.80  tff(c_46, plain, (![A_45, B_47]: (k7_subset_1(u1_struct_0(A_45), k2_pre_topc(A_45, B_47), k1_tops_1(A_45, B_47))=k2_tops_1(A_45, B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.60/4.80  tff(c_11053, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_46, c_11028])).
% 10.60/4.80  tff(c_11066, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_11053])).
% 10.60/4.80  tff(c_14834, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_14346, c_257])).
% 10.60/4.80  tff(c_14842, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11066, c_14834])).
% 10.60/4.80  tff(c_16159, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_14842, c_207])).
% 10.60/4.80  tff(c_16171, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14346, c_15293, c_16159])).
% 10.60/4.80  tff(c_16173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2726, c_16171])).
% 10.60/4.80  tff(c_16174, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_62])).
% 10.60/4.80  tff(c_16175, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_62])).
% 10.60/4.80  tff(c_16363, plain, (![A_556, B_557]: (k4_xboole_0(A_556, B_557)=k3_subset_1(A_556, B_557) | ~m1_subset_1(B_557, k1_zfmisc_1(A_556)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.60/4.80  tff(c_16375, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_56, c_16363])).
% 10.60/4.80  tff(c_16385, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_16375, c_69])).
% 10.60/4.80  tff(c_50, plain, (![B_56, D_62, C_60, A_48]: (k1_tops_1(B_56, D_62)=D_62 | ~v3_pre_topc(D_62, B_56) | ~m1_subset_1(D_62, k1_zfmisc_1(u1_struct_0(B_56))) | ~m1_subset_1(C_60, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(B_56) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.60/4.80  tff(c_18316, plain, (![C_669, A_670]: (~m1_subset_1(C_669, k1_zfmisc_1(u1_struct_0(A_670))) | ~l1_pre_topc(A_670) | ~v2_pre_topc(A_670))), inference(splitLeft, [status(thm)], [c_50])).
% 10.60/4.80  tff(c_18338, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16385, c_18316])).
% 10.60/4.80  tff(c_18358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_18338])).
% 10.60/4.80  tff(c_18489, plain, (![B_674, D_675]: (k1_tops_1(B_674, D_675)=D_675 | ~v3_pre_topc(D_675, B_674) | ~m1_subset_1(D_675, k1_zfmisc_1(u1_struct_0(B_674))) | ~l1_pre_topc(B_674))), inference(splitRight, [status(thm)], [c_50])).
% 10.60/4.80  tff(c_18525, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_18489])).
% 10.60/4.80  tff(c_18539, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_16175, c_18525])).
% 10.60/4.80  tff(c_16584, plain, (![A_578, B_579, C_580]: (k7_subset_1(A_578, B_579, C_580)=k4_xboole_0(B_579, C_580) | ~m1_subset_1(B_579, k1_zfmisc_1(A_578)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.60/4.80  tff(c_16602, plain, (![C_580]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_580)=k4_xboole_0('#skF_2', C_580))), inference(resolution, [status(thm)], [c_56, c_16584])).
% 10.60/4.80  tff(c_17383, plain, (![A_635, B_636]: (k7_subset_1(u1_struct_0(A_635), B_636, k2_tops_1(A_635, B_636))=k1_tops_1(A_635, B_636) | ~m1_subset_1(B_636, k1_zfmisc_1(u1_struct_0(A_635))) | ~l1_pre_topc(A_635))), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.60/4.80  tff(c_17403, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_17383])).
% 10.60/4.80  tff(c_17415, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_16602, c_17403])).
% 10.60/4.80  tff(c_17455, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_17415, c_122])).
% 10.60/4.80  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.60/4.80  tff(c_17475, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_17455, c_4])).
% 10.60/4.80  tff(c_17512, plain, (~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_17475])).
% 10.60/4.80  tff(c_18542, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18539, c_17512])).
% 10.60/4.80  tff(c_18552, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_18542])).
% 10.60/4.80  tff(c_18553, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_17475])).
% 10.60/4.80  tff(c_19000, plain, (![A_693, B_694]: (k7_subset_1(u1_struct_0(A_693), k2_pre_topc(A_693, B_694), k1_tops_1(A_693, B_694))=k2_tops_1(A_693, B_694) | ~m1_subset_1(B_694, k1_zfmisc_1(u1_struct_0(A_693))) | ~l1_pre_topc(A_693))), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.60/4.80  tff(c_19009, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_18553, c_19000])).
% 10.60/4.80  tff(c_19013, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_19009])).
% 10.60/4.80  tff(c_19015, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16174, c_19013])).
% 10.60/4.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.60/4.80  
% 10.60/4.80  Inference rules
% 10.60/4.80  ----------------------
% 10.60/4.80  #Ref     : 0
% 10.60/4.80  #Sup     : 4792
% 10.60/4.80  #Fact    : 0
% 10.60/4.80  #Define  : 0
% 10.60/4.80  #Split   : 13
% 10.60/4.80  #Chain   : 0
% 10.60/4.80  #Close   : 0
% 10.60/4.80  
% 10.60/4.80  Ordering : KBO
% 10.60/4.80  
% 10.60/4.80  Simplification rules
% 10.60/4.80  ----------------------
% 10.60/4.80  #Subsume      : 126
% 10.60/4.80  #Demod        : 3609
% 10.60/4.80  #Tautology    : 1602
% 10.60/4.80  #SimpNegUnit  : 15
% 10.60/4.80  #BackRed      : 41
% 10.60/4.80  
% 10.60/4.80  #Partial instantiations: 0
% 10.60/4.80  #Strategies tried      : 1
% 10.60/4.80  
% 10.60/4.80  Timing (in seconds)
% 10.60/4.80  ----------------------
% 10.60/4.81  Preprocessing        : 0.36
% 10.60/4.81  Parsing              : 0.19
% 10.60/4.81  CNF conversion       : 0.03
% 10.60/4.81  Main loop            : 3.67
% 10.60/4.81  Inferencing          : 0.76
% 10.60/4.81  Reduction            : 1.80
% 10.60/4.81  Demodulation         : 1.53
% 10.60/4.81  BG Simplification    : 0.10
% 10.60/4.81  Subsumption          : 0.73
% 10.60/4.81  Abstraction          : 0.16
% 10.60/4.81  MUC search           : 0.00
% 10.60/4.81  Cooper               : 0.00
% 10.60/4.81  Total                : 4.08
% 10.60/4.81  Index Insertion      : 0.00
% 10.60/4.81  Index Deletion       : 0.00
% 10.60/4.81  Index Matching       : 0.00
% 10.60/4.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
