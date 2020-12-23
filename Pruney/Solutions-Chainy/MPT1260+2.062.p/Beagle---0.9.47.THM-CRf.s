%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:08 EST 2020

% Result     : Theorem 8.29s
% Output     : CNFRefutation 8.29s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 166 expanded)
%              Number of leaves         :   34 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :  144 ( 333 expanded)
%              Number of equality atoms :   66 ( 119 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_79,axiom,(
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

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_36,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_169,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_24,plain,(
    ! [C_36,A_24,D_38,B_32] :
      ( v3_pre_topc(C_36,A_24)
      | k1_tops_1(A_24,C_36) != C_36
      | ~ m1_subset_1(D_38,k1_zfmisc_1(u1_struct_0(B_32)))
      | ~ m1_subset_1(C_36,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(B_32)
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1916,plain,(
    ! [D_104,B_105] :
      ( ~ m1_subset_1(D_104,k1_zfmisc_1(u1_struct_0(B_105)))
      | ~ l1_pre_topc(B_105) ) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_1919,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1916])).

tff(c_1923,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1919])).

tff(c_2533,plain,(
    ! [C_114,A_115] :
      ( v3_pre_topc(C_114,A_115)
      | k1_tops_1(A_115,C_114) != C_114
      | ~ m1_subset_1(C_114,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115) ) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_2539,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_2533])).

tff(c_2543,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_2539])).

tff(c_2544,plain,(
    k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_2543])).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_465,plain,(
    ! [A_66,B_67,C_68] :
      ( k7_subset_1(A_66,B_67,C_68) = k4_xboole_0(B_67,C_68)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_468,plain,(
    ! [C_68] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_68) = k4_xboole_0('#skF_2',C_68) ),
    inference(resolution,[status(thm)],[c_30,c_465])).

tff(c_1090,plain,(
    ! [A_88,B_89] :
      ( k7_subset_1(u1_struct_0(A_88),B_89,k2_tops_1(A_88,B_89)) = k1_tops_1(A_88,B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1094,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1090])).

tff(c_1098,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_468,c_1094])).

tff(c_909,plain,(
    ! [A_82,B_83] :
      ( m1_subset_1(k2_pre_topc(A_82,B_83),k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16] :
      ( k7_subset_1(A_14,B_15,C_16) = k4_xboole_0(B_15,C_16)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14204,plain,(
    ! [A_218,B_219,C_220] :
      ( k7_subset_1(u1_struct_0(A_218),k2_pre_topc(A_218,B_219),C_220) = k4_xboole_0(k2_pre_topc(A_218,B_219),C_220)
      | ~ m1_subset_1(B_219,k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ l1_pre_topc(A_218) ) ),
    inference(resolution,[status(thm)],[c_909,c_16])).

tff(c_14208,plain,(
    ! [C_220] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_220) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_220)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_14204])).

tff(c_14663,plain,(
    ! [C_224] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_224) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_224) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_14208])).

tff(c_42,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_273,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_42])).

tff(c_14673,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14663,c_273])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_181,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k4_xboole_0(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_196,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_181])).

tff(c_199,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_196])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_200,plain,(
    ! [A_53,B_54] : k5_xboole_0(A_53,k3_xboole_0(A_53,B_54)) = k4_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_218,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_200])).

tff(c_255,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_218])).

tff(c_358,plain,(
    ! [A_61,B_62,C_63] : k4_xboole_0(k3_xboole_0(A_61,B_62),C_63) = k3_xboole_0(A_61,k4_xboole_0(B_62,C_63)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_415,plain,(
    ! [A_64,C_65] : k3_xboole_0(A_64,k4_xboole_0(A_64,C_65)) = k4_xboole_0(A_64,C_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_358])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_215,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_200])).

tff(c_424,plain,(
    ! [A_64,C_65] : k5_xboole_0(k4_xboole_0(A_64,C_65),k4_xboole_0(A_64,C_65)) = k4_xboole_0(k4_xboole_0(A_64,C_65),A_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_215])).

tff(c_469,plain,(
    ! [A_69,C_70] : k4_xboole_0(k4_xboole_0(A_69,C_70),A_69) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_424])).

tff(c_520,plain,(
    ! [A_71,B_72] : k4_xboole_0(k3_xboole_0(A_71,B_72),A_71) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_469])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] : k4_xboole_0(k3_xboole_0(A_11,B_12),C_13) = k3_xboole_0(A_11,k4_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_531,plain,(
    ! [A_71,B_72] : k3_xboole_0(A_71,k4_xboole_0(B_72,A_71)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_14])).

tff(c_14772,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14673,c_531])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_446,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,k3_xboole_0(A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_415])).

tff(c_913,plain,(
    ! [A_84,B_85] : k3_xboole_0(A_84,k3_xboole_0(A_84,B_85)) = k3_xboole_0(A_84,B_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_446])).

tff(c_934,plain,(
    ! [A_84,B_85] : k5_xboole_0(A_84,k3_xboole_0(A_84,B_85)) = k4_xboole_0(A_84,k3_xboole_0(A_84,B_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_913,c_6])).

tff(c_979,plain,(
    ! [A_84,B_85] : k4_xboole_0(A_84,k3_xboole_0(A_84,B_85)) = k4_xboole_0(A_84,B_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_934])).

tff(c_14863,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14772,c_979])).

tff(c_14907,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1098,c_14863])).

tff(c_14909,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2544,c_14907])).

tff(c_14910,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_14911,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_26,plain,(
    ! [B_32,D_38,C_36,A_24] :
      ( k1_tops_1(B_32,D_38) = D_38
      | ~ v3_pre_topc(D_38,B_32)
      | ~ m1_subset_1(D_38,k1_zfmisc_1(u1_struct_0(B_32)))
      | ~ m1_subset_1(C_36,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(B_32)
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_17332,plain,(
    ! [C_289,A_290] :
      ( ~ m1_subset_1(C_289,k1_zfmisc_1(u1_struct_0(A_290)))
      | ~ l1_pre_topc(A_290)
      | ~ v2_pre_topc(A_290) ) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_17338,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_17332])).

tff(c_17343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_17338])).

tff(c_17828,plain,(
    ! [B_297,D_298] :
      ( k1_tops_1(B_297,D_298) = D_298
      | ~ v3_pre_topc(D_298,B_297)
      | ~ m1_subset_1(D_298,k1_zfmisc_1(u1_struct_0(B_297)))
      | ~ l1_pre_topc(B_297) ) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_17834,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_17828])).

tff(c_17838,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_14911,c_17834])).

tff(c_22,plain,(
    ! [A_21,B_23] :
      ( k7_subset_1(u1_struct_0(A_21),k2_pre_topc(A_21,B_23),k1_tops_1(A_21,B_23)) = k2_tops_1(A_21,B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_17851,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_17838,c_22])).

tff(c_17855,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_17851])).

tff(c_17857,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14910,c_17855])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:12:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.29/3.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.29/3.02  
% 8.29/3.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.29/3.02  %$ v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.29/3.02  
% 8.29/3.02  %Foreground sorts:
% 8.29/3.02  
% 8.29/3.02  
% 8.29/3.02  %Background operators:
% 8.29/3.02  
% 8.29/3.02  
% 8.29/3.02  %Foreground operators:
% 8.29/3.02  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 8.29/3.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.29/3.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.29/3.02  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 8.29/3.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.29/3.02  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.29/3.02  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.29/3.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.29/3.02  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.29/3.02  tff('#skF_2', type, '#skF_2': $i).
% 8.29/3.02  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 8.29/3.02  tff('#skF_1', type, '#skF_1': $i).
% 8.29/3.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.29/3.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.29/3.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.29/3.02  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.29/3.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.29/3.02  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.29/3.02  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.29/3.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.29/3.02  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.29/3.02  
% 8.29/3.04  tff(f_98, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 8.29/3.04  tff(f_79, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 8.29/3.04  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 8.29/3.04  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 8.29/3.04  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 8.29/3.04  tff(f_51, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 8.29/3.04  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.29/3.04  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 8.29/3.04  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.29/3.04  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.29/3.04  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 8.29/3.04  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.29/3.04  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 8.29/3.04  tff(c_36, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.29/3.04  tff(c_169, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 8.29/3.04  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.29/3.04  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.29/3.04  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.29/3.04  tff(c_24, plain, (![C_36, A_24, D_38, B_32]: (v3_pre_topc(C_36, A_24) | k1_tops_1(A_24, C_36)!=C_36 | ~m1_subset_1(D_38, k1_zfmisc_1(u1_struct_0(B_32))) | ~m1_subset_1(C_36, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(B_32) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.29/3.04  tff(c_1916, plain, (![D_104, B_105]: (~m1_subset_1(D_104, k1_zfmisc_1(u1_struct_0(B_105))) | ~l1_pre_topc(B_105))), inference(splitLeft, [status(thm)], [c_24])).
% 8.29/3.04  tff(c_1919, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1916])).
% 8.29/3.04  tff(c_1923, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_1919])).
% 8.29/3.04  tff(c_2533, plain, (![C_114, A_115]: (v3_pre_topc(C_114, A_115) | k1_tops_1(A_115, C_114)!=C_114 | ~m1_subset_1(C_114, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115) | ~v2_pre_topc(A_115))), inference(splitRight, [status(thm)], [c_24])).
% 8.29/3.04  tff(c_2539, plain, (v3_pre_topc('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_2533])).
% 8.29/3.04  tff(c_2543, plain, (v3_pre_topc('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_2539])).
% 8.29/3.04  tff(c_2544, plain, (k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_169, c_2543])).
% 8.29/3.04  tff(c_10, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.29/3.04  tff(c_465, plain, (![A_66, B_67, C_68]: (k7_subset_1(A_66, B_67, C_68)=k4_xboole_0(B_67, C_68) | ~m1_subset_1(B_67, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.29/3.04  tff(c_468, plain, (![C_68]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_68)=k4_xboole_0('#skF_2', C_68))), inference(resolution, [status(thm)], [c_30, c_465])).
% 8.29/3.04  tff(c_1090, plain, (![A_88, B_89]: (k7_subset_1(u1_struct_0(A_88), B_89, k2_tops_1(A_88, B_89))=k1_tops_1(A_88, B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.29/3.04  tff(c_1094, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1090])).
% 8.29/3.04  tff(c_1098, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_468, c_1094])).
% 8.29/3.04  tff(c_909, plain, (![A_82, B_83]: (m1_subset_1(k2_pre_topc(A_82, B_83), k1_zfmisc_1(u1_struct_0(A_82))) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.29/3.04  tff(c_16, plain, (![A_14, B_15, C_16]: (k7_subset_1(A_14, B_15, C_16)=k4_xboole_0(B_15, C_16) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.29/3.04  tff(c_14204, plain, (![A_218, B_219, C_220]: (k7_subset_1(u1_struct_0(A_218), k2_pre_topc(A_218, B_219), C_220)=k4_xboole_0(k2_pre_topc(A_218, B_219), C_220) | ~m1_subset_1(B_219, k1_zfmisc_1(u1_struct_0(A_218))) | ~l1_pre_topc(A_218))), inference(resolution, [status(thm)], [c_909, c_16])).
% 8.29/3.04  tff(c_14208, plain, (![C_220]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_220)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_220) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_14204])).
% 8.29/3.04  tff(c_14663, plain, (![C_224]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_224)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_224))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_14208])).
% 8.29/3.04  tff(c_42, plain, (v3_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.29/3.04  tff(c_273, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_169, c_42])).
% 8.29/3.04  tff(c_14673, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14663, c_273])).
% 8.29/3.04  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.29/3.04  tff(c_8, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.29/3.04  tff(c_181, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k4_xboole_0(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.29/3.04  tff(c_196, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_181])).
% 8.29/3.04  tff(c_199, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_196])).
% 8.29/3.04  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.29/3.04  tff(c_200, plain, (![A_53, B_54]: (k5_xboole_0(A_53, k3_xboole_0(A_53, B_54))=k4_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.29/3.04  tff(c_218, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_200])).
% 8.29/3.04  tff(c_255, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_199, c_218])).
% 8.29/3.04  tff(c_358, plain, (![A_61, B_62, C_63]: (k4_xboole_0(k3_xboole_0(A_61, B_62), C_63)=k3_xboole_0(A_61, k4_xboole_0(B_62, C_63)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.29/3.04  tff(c_415, plain, (![A_64, C_65]: (k3_xboole_0(A_64, k4_xboole_0(A_64, C_65))=k4_xboole_0(A_64, C_65))), inference(superposition, [status(thm), theory('equality')], [c_4, c_358])).
% 8.29/3.04  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.29/3.04  tff(c_215, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_200])).
% 8.29/3.04  tff(c_424, plain, (![A_64, C_65]: (k5_xboole_0(k4_xboole_0(A_64, C_65), k4_xboole_0(A_64, C_65))=k4_xboole_0(k4_xboole_0(A_64, C_65), A_64))), inference(superposition, [status(thm), theory('equality')], [c_415, c_215])).
% 8.29/3.04  tff(c_469, plain, (![A_69, C_70]: (k4_xboole_0(k4_xboole_0(A_69, C_70), A_69)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_255, c_424])).
% 8.29/3.04  tff(c_520, plain, (![A_71, B_72]: (k4_xboole_0(k3_xboole_0(A_71, B_72), A_71)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_469])).
% 8.29/3.04  tff(c_14, plain, (![A_11, B_12, C_13]: (k4_xboole_0(k3_xboole_0(A_11, B_12), C_13)=k3_xboole_0(A_11, k4_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.29/3.04  tff(c_531, plain, (![A_71, B_72]: (k3_xboole_0(A_71, k4_xboole_0(B_72, A_71))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_520, c_14])).
% 8.29/3.04  tff(c_14772, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_14673, c_531])).
% 8.29/3.04  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.29/3.04  tff(c_446, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, k3_xboole_0(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_415])).
% 8.29/3.04  tff(c_913, plain, (![A_84, B_85]: (k3_xboole_0(A_84, k3_xboole_0(A_84, B_85))=k3_xboole_0(A_84, B_85))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_446])).
% 8.29/3.04  tff(c_934, plain, (![A_84, B_85]: (k5_xboole_0(A_84, k3_xboole_0(A_84, B_85))=k4_xboole_0(A_84, k3_xboole_0(A_84, B_85)))), inference(superposition, [status(thm), theory('equality')], [c_913, c_6])).
% 8.29/3.04  tff(c_979, plain, (![A_84, B_85]: (k4_xboole_0(A_84, k3_xboole_0(A_84, B_85))=k4_xboole_0(A_84, B_85))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_934])).
% 8.29/3.04  tff(c_14863, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14772, c_979])).
% 8.29/3.04  tff(c_14907, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1098, c_14863])).
% 8.29/3.04  tff(c_14909, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2544, c_14907])).
% 8.29/3.04  tff(c_14910, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 8.29/3.04  tff(c_14911, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 8.29/3.04  tff(c_26, plain, (![B_32, D_38, C_36, A_24]: (k1_tops_1(B_32, D_38)=D_38 | ~v3_pre_topc(D_38, B_32) | ~m1_subset_1(D_38, k1_zfmisc_1(u1_struct_0(B_32))) | ~m1_subset_1(C_36, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(B_32) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.29/3.04  tff(c_17332, plain, (![C_289, A_290]: (~m1_subset_1(C_289, k1_zfmisc_1(u1_struct_0(A_290))) | ~l1_pre_topc(A_290) | ~v2_pre_topc(A_290))), inference(splitLeft, [status(thm)], [c_26])).
% 8.29/3.04  tff(c_17338, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_17332])).
% 8.29/3.04  tff(c_17343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_17338])).
% 8.29/3.04  tff(c_17828, plain, (![B_297, D_298]: (k1_tops_1(B_297, D_298)=D_298 | ~v3_pre_topc(D_298, B_297) | ~m1_subset_1(D_298, k1_zfmisc_1(u1_struct_0(B_297))) | ~l1_pre_topc(B_297))), inference(splitRight, [status(thm)], [c_26])).
% 8.29/3.04  tff(c_17834, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_17828])).
% 8.29/3.04  tff(c_17838, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_14911, c_17834])).
% 8.29/3.04  tff(c_22, plain, (![A_21, B_23]: (k7_subset_1(u1_struct_0(A_21), k2_pre_topc(A_21, B_23), k1_tops_1(A_21, B_23))=k2_tops_1(A_21, B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.29/3.04  tff(c_17851, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_17838, c_22])).
% 8.29/3.04  tff(c_17855, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_17851])).
% 8.29/3.04  tff(c_17857, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14910, c_17855])).
% 8.29/3.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.29/3.04  
% 8.29/3.04  Inference rules
% 8.29/3.04  ----------------------
% 8.29/3.04  #Ref     : 0
% 8.29/3.04  #Sup     : 4455
% 8.29/3.04  #Fact    : 0
% 8.29/3.04  #Define  : 0
% 8.29/3.04  #Split   : 4
% 8.29/3.04  #Chain   : 0
% 8.29/3.04  #Close   : 0
% 8.29/3.04  
% 8.29/3.04  Ordering : KBO
% 8.29/3.04  
% 8.29/3.04  Simplification rules
% 8.29/3.04  ----------------------
% 8.29/3.04  #Subsume      : 28
% 8.29/3.04  #Demod        : 5785
% 8.29/3.04  #Tautology    : 3420
% 8.29/3.04  #SimpNegUnit  : 5
% 8.29/3.04  #BackRed      : 17
% 8.29/3.04  
% 8.29/3.04  #Partial instantiations: 0
% 8.29/3.04  #Strategies tried      : 1
% 8.29/3.04  
% 8.29/3.04  Timing (in seconds)
% 8.29/3.04  ----------------------
% 8.29/3.04  Preprocessing        : 0.31
% 8.29/3.04  Parsing              : 0.17
% 8.29/3.04  CNF conversion       : 0.02
% 8.29/3.04  Main loop            : 1.95
% 8.29/3.04  Inferencing          : 0.44
% 8.29/3.04  Reduction            : 1.12
% 8.29/3.04  Demodulation         : 0.99
% 8.29/3.04  BG Simplification    : 0.05
% 8.29/3.04  Subsumption          : 0.24
% 8.29/3.04  Abstraction          : 0.09
% 8.29/3.04  MUC search           : 0.00
% 8.29/3.04  Cooper               : 0.00
% 8.29/3.04  Total                : 2.29
% 8.29/3.04  Index Insertion      : 0.00
% 8.29/3.04  Index Deletion       : 0.00
% 8.29/3.04  Index Matching       : 0.00
% 8.29/3.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
