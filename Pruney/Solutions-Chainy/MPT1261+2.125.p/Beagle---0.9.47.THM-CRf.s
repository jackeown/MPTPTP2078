%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:29 EST 2020

% Result     : Theorem 8.66s
% Output     : CNFRefutation 8.66s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 130 expanded)
%              Number of leaves         :   35 (  60 expanded)
%              Depth                    :    8
%              Number of atoms          :  114 ( 249 expanded)
%              Number of equality atoms :   52 (  87 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_64,axiom,(
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

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_10378,plain,(
    ! [A_196,B_197,C_198] :
      ( k7_subset_1(A_196,B_197,C_198) = k4_xboole_0(B_197,C_198)
      | ~ m1_subset_1(B_197,k1_zfmisc_1(A_196)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10381,plain,(
    ! [C_198] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_198) = k4_xboole_0('#skF_2',C_198) ),
    inference(resolution,[status(thm)],[c_30,c_10378])).

tff(c_36,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_139,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1740,plain,(
    ! [B_92,A_93] :
      ( v4_pre_topc(B_92,A_93)
      | k2_pre_topc(A_93,B_92) != B_92
      | ~ v2_pre_topc(A_93)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1746,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1740])).

tff(c_1750,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_1746])).

tff(c_1751,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_1750])).

tff(c_2248,plain,(
    ! [A_100,B_101] :
      ( k4_subset_1(u1_struct_0(A_100),B_101,k2_tops_1(A_100,B_101)) = k2_pre_topc(A_100,B_101)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2252,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_2248])).

tff(c_2256,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2252])).

tff(c_238,plain,(
    ! [A_50,B_51,C_52] :
      ( k7_subset_1(A_50,B_51,C_52) = k4_xboole_0(B_51,C_52)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_241,plain,(
    ! [C_52] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_52) = k4_xboole_0('#skF_2',C_52) ),
    inference(resolution,[status(thm)],[c_30,c_238])).

tff(c_42,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_273,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_42])).

tff(c_274,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_273])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_205,plain,(
    ! [A_48,B_49] : k2_xboole_0(k5_xboole_0(A_48,B_49),k3_xboole_0(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_226,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k3_xboole_0(A_3,k3_xboole_0(A_3,B_4))) = k2_xboole_0(A_3,k3_xboole_0(A_3,B_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_205])).

tff(c_237,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k3_xboole_0(A_3,k3_xboole_0(A_3,B_4))) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_226])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_280,plain,(
    ! [A_56,B_57] : k2_xboole_0(k4_xboole_0(A_56,B_57),k3_xboole_0(A_56,k3_xboole_0(A_56,B_57))) = A_56 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_226])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_289,plain,(
    ! [A_56,B_57] : k2_xboole_0(k4_xboole_0(A_56,B_57),k3_xboole_0(A_56,k3_xboole_0(A_56,B_57))) = k2_xboole_0(k4_xboole_0(A_56,B_57),A_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_8])).

tff(c_300,plain,(
    ! [A_58,B_59] : k2_xboole_0(A_58,k4_xboole_0(A_58,B_59)) = A_58 ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_2,c_289])).

tff(c_315,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_300])).

tff(c_24,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(k2_tops_1(A_24,B_25),k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1201,plain,(
    ! [A_83,B_84,C_85] :
      ( k4_subset_1(A_83,B_84,C_85) = k2_xboole_0(B_84,C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(A_83))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_9321,plain,(
    ! [A_175,B_176,B_177] :
      ( k4_subset_1(u1_struct_0(A_175),B_176,k2_tops_1(A_175,B_177)) = k2_xboole_0(B_176,k2_tops_1(A_175,B_177))
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ l1_pre_topc(A_175) ) ),
    inference(resolution,[status(thm)],[c_24,c_1201])).

tff(c_9325,plain,(
    ! [B_177] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_177)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_177))
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_9321])).

tff(c_10103,plain,(
    ! [B_180] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_180)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_180))
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_9325])).

tff(c_10110,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_10103])).

tff(c_10115,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2256,c_315,c_10110])).

tff(c_10117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1751,c_10115])).

tff(c_10118,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_10382,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10381,c_10118])).

tff(c_10119,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_10740,plain,(
    ! [A_210,B_211] :
      ( k2_pre_topc(A_210,B_211) = B_211
      | ~ v4_pre_topc(B_211,A_210)
      | ~ m1_subset_1(B_211,k1_zfmisc_1(u1_struct_0(A_210)))
      | ~ l1_pre_topc(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10746,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_10740])).

tff(c_10750,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_10119,c_10746])).

tff(c_12020,plain,(
    ! [A_243,B_244] :
      ( k7_subset_1(u1_struct_0(A_243),k2_pre_topc(A_243,B_244),k1_tops_1(A_243,B_244)) = k2_tops_1(A_243,B_244)
      | ~ m1_subset_1(B_244,k1_zfmisc_1(u1_struct_0(A_243)))
      | ~ l1_pre_topc(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12029,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10750,c_12020])).

tff(c_12033,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_10381,c_12029])).

tff(c_12035,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10382,c_12033])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:24:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.66/3.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.66/3.38  
% 8.66/3.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.66/3.38  %$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 8.66/3.38  
% 8.66/3.38  %Foreground sorts:
% 8.66/3.38  
% 8.66/3.38  
% 8.66/3.38  %Background operators:
% 8.66/3.38  
% 8.66/3.38  
% 8.66/3.38  %Foreground operators:
% 8.66/3.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.66/3.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.66/3.38  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 8.66/3.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.66/3.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.66/3.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.66/3.38  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.66/3.38  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.66/3.38  tff('#skF_2', type, '#skF_2': $i).
% 8.66/3.38  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 8.66/3.38  tff('#skF_1', type, '#skF_1': $i).
% 8.66/3.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.66/3.38  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.66/3.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.66/3.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.66/3.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.66/3.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.66/3.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.66/3.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.66/3.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.66/3.38  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.66/3.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.66/3.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.66/3.38  
% 8.66/3.40  tff(f_96, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 8.66/3.40  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 8.66/3.40  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 8.66/3.40  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 8.66/3.40  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 8.66/3.40  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.66/3.40  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_xboole_1)).
% 8.66/3.40  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.66/3.40  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 8.66/3.40  tff(f_70, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 8.66/3.40  tff(f_43, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 8.66/3.40  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 8.66/3.40  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.66/3.40  tff(c_10378, plain, (![A_196, B_197, C_198]: (k7_subset_1(A_196, B_197, C_198)=k4_xboole_0(B_197, C_198) | ~m1_subset_1(B_197, k1_zfmisc_1(A_196)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.66/3.40  tff(c_10381, plain, (![C_198]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_198)=k4_xboole_0('#skF_2', C_198))), inference(resolution, [status(thm)], [c_30, c_10378])).
% 8.66/3.40  tff(c_36, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.66/3.40  tff(c_139, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 8.66/3.40  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.66/3.40  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.66/3.40  tff(c_1740, plain, (![B_92, A_93]: (v4_pre_topc(B_92, A_93) | k2_pre_topc(A_93, B_92)!=B_92 | ~v2_pre_topc(A_93) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.66/3.40  tff(c_1746, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1740])).
% 8.66/3.40  tff(c_1750, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_1746])).
% 8.66/3.40  tff(c_1751, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_139, c_1750])).
% 8.66/3.40  tff(c_2248, plain, (![A_100, B_101]: (k4_subset_1(u1_struct_0(A_100), B_101, k2_tops_1(A_100, B_101))=k2_pre_topc(A_100, B_101) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.66/3.40  tff(c_2252, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_2248])).
% 8.66/3.40  tff(c_2256, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2252])).
% 8.66/3.40  tff(c_238, plain, (![A_50, B_51, C_52]: (k7_subset_1(A_50, B_51, C_52)=k4_xboole_0(B_51, C_52) | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.66/3.40  tff(c_241, plain, (![C_52]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_52)=k4_xboole_0('#skF_2', C_52))), inference(resolution, [status(thm)], [c_30, c_238])).
% 8.66/3.40  tff(c_42, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.66/3.40  tff(c_273, plain, (v4_pre_topc('#skF_2', '#skF_1') | k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_241, c_42])).
% 8.66/3.40  tff(c_274, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_139, c_273])).
% 8.66/3.40  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k3_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.66/3.40  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.66/3.40  tff(c_205, plain, (![A_48, B_49]: (k2_xboole_0(k5_xboole_0(A_48, B_49), k3_xboole_0(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.66/3.40  tff(c_226, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k3_xboole_0(A_3, k3_xboole_0(A_3, B_4)))=k2_xboole_0(A_3, k3_xboole_0(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_205])).
% 8.66/3.40  tff(c_237, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k3_xboole_0(A_3, k3_xboole_0(A_3, B_4)))=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_226])).
% 8.66/3.40  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.66/3.40  tff(c_280, plain, (![A_56, B_57]: (k2_xboole_0(k4_xboole_0(A_56, B_57), k3_xboole_0(A_56, k3_xboole_0(A_56, B_57)))=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_226])).
% 8.66/3.40  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.66/3.40  tff(c_289, plain, (![A_56, B_57]: (k2_xboole_0(k4_xboole_0(A_56, B_57), k3_xboole_0(A_56, k3_xboole_0(A_56, B_57)))=k2_xboole_0(k4_xboole_0(A_56, B_57), A_56))), inference(superposition, [status(thm), theory('equality')], [c_280, c_8])).
% 8.66/3.40  tff(c_300, plain, (![A_58, B_59]: (k2_xboole_0(A_58, k4_xboole_0(A_58, B_59))=A_58)), inference(demodulation, [status(thm), theory('equality')], [c_237, c_2, c_289])).
% 8.66/3.40  tff(c_315, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_274, c_300])).
% 8.66/3.40  tff(c_24, plain, (![A_24, B_25]: (m1_subset_1(k2_tops_1(A_24, B_25), k1_zfmisc_1(u1_struct_0(A_24))) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.66/3.40  tff(c_1201, plain, (![A_83, B_84, C_85]: (k4_subset_1(A_83, B_84, C_85)=k2_xboole_0(B_84, C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(A_83)) | ~m1_subset_1(B_84, k1_zfmisc_1(A_83)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.66/3.40  tff(c_9321, plain, (![A_175, B_176, B_177]: (k4_subset_1(u1_struct_0(A_175), B_176, k2_tops_1(A_175, B_177))=k2_xboole_0(B_176, k2_tops_1(A_175, B_177)) | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0(A_175))) | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0(A_175))) | ~l1_pre_topc(A_175))), inference(resolution, [status(thm)], [c_24, c_1201])).
% 8.66/3.40  tff(c_9325, plain, (![B_177]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_177))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_177)) | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_9321])).
% 8.66/3.40  tff(c_10103, plain, (![B_180]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_180))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_180)) | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_9325])).
% 8.66/3.40  tff(c_10110, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_10103])).
% 8.66/3.40  tff(c_10115, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2256, c_315, c_10110])).
% 8.66/3.40  tff(c_10117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1751, c_10115])).
% 8.66/3.40  tff(c_10118, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 8.66/3.40  tff(c_10382, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10381, c_10118])).
% 8.66/3.40  tff(c_10119, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 8.66/3.40  tff(c_10740, plain, (![A_210, B_211]: (k2_pre_topc(A_210, B_211)=B_211 | ~v4_pre_topc(B_211, A_210) | ~m1_subset_1(B_211, k1_zfmisc_1(u1_struct_0(A_210))) | ~l1_pre_topc(A_210))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.66/3.40  tff(c_10746, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_10740])).
% 8.66/3.40  tff(c_10750, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_10119, c_10746])).
% 8.66/3.40  tff(c_12020, plain, (![A_243, B_244]: (k7_subset_1(u1_struct_0(A_243), k2_pre_topc(A_243, B_244), k1_tops_1(A_243, B_244))=k2_tops_1(A_243, B_244) | ~m1_subset_1(B_244, k1_zfmisc_1(u1_struct_0(A_243))) | ~l1_pre_topc(A_243))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.66/3.40  tff(c_12029, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10750, c_12020])).
% 8.66/3.40  tff(c_12033, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_10381, c_12029])).
% 8.66/3.40  tff(c_12035, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10382, c_12033])).
% 8.66/3.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.66/3.40  
% 8.66/3.40  Inference rules
% 8.66/3.40  ----------------------
% 8.66/3.40  #Ref     : 0
% 8.66/3.40  #Sup     : 2983
% 8.66/3.40  #Fact    : 0
% 8.66/3.40  #Define  : 0
% 8.66/3.40  #Split   : 2
% 8.66/3.40  #Chain   : 0
% 8.66/3.40  #Close   : 0
% 8.66/3.40  
% 8.66/3.40  Ordering : KBO
% 8.66/3.40  
% 8.66/3.40  Simplification rules
% 8.66/3.40  ----------------------
% 8.66/3.40  #Subsume      : 45
% 8.66/3.40  #Demod        : 7718
% 8.66/3.40  #Tautology    : 2356
% 8.66/3.40  #SimpNegUnit  : 5
% 8.66/3.40  #BackRed      : 1
% 8.66/3.40  
% 8.66/3.40  #Partial instantiations: 0
% 8.66/3.40  #Strategies tried      : 1
% 8.66/3.40  
% 8.66/3.40  Timing (in seconds)
% 8.66/3.40  ----------------------
% 8.66/3.40  Preprocessing        : 0.35
% 8.66/3.40  Parsing              : 0.19
% 8.66/3.40  CNF conversion       : 0.02
% 8.66/3.40  Main loop            : 2.22
% 8.66/3.40  Inferencing          : 0.48
% 8.66/3.40  Reduction            : 1.45
% 8.66/3.40  Demodulation         : 1.34
% 8.66/3.40  BG Simplification    : 0.04
% 8.66/3.40  Subsumption          : 0.18
% 8.66/3.40  Abstraction          : 0.13
% 8.66/3.40  MUC search           : 0.00
% 8.66/3.40  Cooper               : 0.00
% 8.66/3.40  Total                : 2.61
% 8.66/3.40  Index Insertion      : 0.00
% 8.66/3.40  Index Deletion       : 0.00
% 8.66/3.40  Index Matching       : 0.00
% 8.66/3.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
