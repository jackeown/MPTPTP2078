%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:36 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 183 expanded)
%              Number of leaves         :   32 (  78 expanded)
%              Depth                    :   10
%              Number of atoms          :  125 ( 381 expanded)
%              Number of equality atoms :   56 ( 131 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_58,axiom,(
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

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_845,plain,(
    ! [A_99,B_100,C_101] :
      ( k7_subset_1(A_99,B_100,C_101) = k4_xboole_0(B_100,C_101)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_848,plain,(
    ! [C_101] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_101) = k4_xboole_0('#skF_2',C_101) ),
    inference(resolution,[status(thm)],[c_28,c_845])).

tff(c_1065,plain,(
    ! [A_126,B_127] :
      ( k7_subset_1(u1_struct_0(A_126),B_127,k2_tops_1(A_126,B_127)) = k1_tops_1(A_126,B_127)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1069,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1065])).

tff(c_1073,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_848,c_1069])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1083,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1073,c_4])).

tff(c_40,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_96,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_34,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_129,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_34])).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_301,plain,(
    ! [B_61,A_62] :
      ( v4_pre_topc(B_61,A_62)
      | k2_pre_topc(A_62,B_61) != B_61
      | ~ v2_pre_topc(A_62)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_307,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_301])).

tff(c_311,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_307])).

tff(c_312,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_311])).

tff(c_381,plain,(
    ! [A_67,B_68] :
      ( k4_subset_1(u1_struct_0(A_67),B_68,k2_tops_1(A_67,B_68)) = k2_pre_topc(A_67,B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_385,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_381])).

tff(c_389,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_385])).

tff(c_101,plain,(
    ! [A_42,B_43,C_44] :
      ( k7_subset_1(A_42,B_43,C_44) = k4_xboole_0(B_43,C_44)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_105,plain,(
    ! [C_45] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_45) = k4_xboole_0('#skF_2',C_45) ),
    inference(resolution,[status(thm)],[c_28,c_101])).

tff(c_111,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_96])).

tff(c_123,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_4])).

tff(c_104,plain,(
    ! [C_44] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_44) = k4_xboole_0('#skF_2',C_44) ),
    inference(resolution,[status(thm)],[c_28,c_101])).

tff(c_314,plain,(
    ! [A_65,B_66] :
      ( k7_subset_1(u1_struct_0(A_65),B_66,k2_tops_1(A_65,B_66)) = k1_tops_1(A_65,B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_318,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_314])).

tff(c_322,plain,(
    k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_123,c_104,c_318])).

tff(c_68,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k4_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_71,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k3_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,k4_xboole_0(A_38,B_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_4])).

tff(c_333,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2'))) = k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_71])).

tff(c_340,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_111,c_333])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_367,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_2])).

tff(c_18,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k2_tops_1(A_18,B_19),k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_260,plain,(
    ! [A_56,B_57,C_58] :
      ( k4_subset_1(A_56,B_57,C_58) = k2_xboole_0(B_57,C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(A_56))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_819,plain,(
    ! [A_95,B_96,B_97] :
      ( k4_subset_1(u1_struct_0(A_95),B_96,k2_tops_1(A_95,B_97)) = k2_xboole_0(B_96,k2_tops_1(A_95,B_97))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(resolution,[status(thm)],[c_18,c_260])).

tff(c_823,plain,(
    ! [B_97] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_97)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_97))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_819])).

tff(c_828,plain,(
    ! [B_98] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_98)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_98))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_823])).

tff(c_835,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_828])).

tff(c_840,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_367,c_835])).

tff(c_842,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_312,c_840])).

tff(c_844,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_849,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_848,c_844])).

tff(c_1087,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1083,c_849])).

tff(c_843,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_907,plain,(
    ! [A_109,B_110] :
      ( k2_pre_topc(A_109,B_110) = B_110
      | ~ v4_pre_topc(B_110,A_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_913,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_907])).

tff(c_917,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_843,c_913])).

tff(c_1144,plain,(
    ! [A_128,B_129] :
      ( k7_subset_1(u1_struct_0(A_128),k2_pre_topc(A_128,B_129),k1_tops_1(A_128,B_129)) = k2_tops_1(A_128,B_129)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1153,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_917,c_1144])).

tff(c_1157,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1083,c_848,c_1153])).

tff(c_1159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1087,c_1157])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:33:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.51  
% 3.21/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.51  %$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 3.21/1.51  
% 3.21/1.51  %Foreground sorts:
% 3.21/1.51  
% 3.21/1.51  
% 3.21/1.51  %Background operators:
% 3.21/1.51  
% 3.21/1.51  
% 3.21/1.51  %Foreground operators:
% 3.21/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.21/1.51  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.21/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.21/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.21/1.51  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.21/1.51  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.21/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.21/1.51  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.21/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.21/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.21/1.51  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.21/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.21/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.21/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.21/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.21/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.21/1.51  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.21/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.51  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.21/1.51  
% 3.46/1.53  tff(f_105, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 3.46/1.53  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.46/1.53  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 3.46/1.53  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.46/1.53  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.46/1.53  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 3.46/1.53  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.46/1.53  tff(f_64, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 3.46/1.53  tff(f_37, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.46/1.53  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 3.46/1.53  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.46/1.53  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.46/1.53  tff(c_845, plain, (![A_99, B_100, C_101]: (k7_subset_1(A_99, B_100, C_101)=k4_xboole_0(B_100, C_101) | ~m1_subset_1(B_100, k1_zfmisc_1(A_99)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.46/1.53  tff(c_848, plain, (![C_101]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_101)=k4_xboole_0('#skF_2', C_101))), inference(resolution, [status(thm)], [c_28, c_845])).
% 3.46/1.53  tff(c_1065, plain, (![A_126, B_127]: (k7_subset_1(u1_struct_0(A_126), B_127, k2_tops_1(A_126, B_127))=k1_tops_1(A_126, B_127) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.46/1.53  tff(c_1069, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_1065])).
% 3.46/1.53  tff(c_1073, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_848, c_1069])).
% 3.46/1.53  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.46/1.53  tff(c_1083, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1073, c_4])).
% 3.46/1.53  tff(c_40, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.46/1.53  tff(c_96, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_40])).
% 3.46/1.53  tff(c_34, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.46/1.53  tff(c_129, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_34])).
% 3.46/1.53  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.46/1.53  tff(c_301, plain, (![B_61, A_62]: (v4_pre_topc(B_61, A_62) | k2_pre_topc(A_62, B_61)!=B_61 | ~v2_pre_topc(A_62) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.46/1.53  tff(c_307, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_301])).
% 3.46/1.53  tff(c_311, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_307])).
% 3.46/1.53  tff(c_312, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_129, c_311])).
% 3.46/1.53  tff(c_381, plain, (![A_67, B_68]: (k4_subset_1(u1_struct_0(A_67), B_68, k2_tops_1(A_67, B_68))=k2_pre_topc(A_67, B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.46/1.53  tff(c_385, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_381])).
% 3.46/1.53  tff(c_389, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_385])).
% 3.46/1.53  tff(c_101, plain, (![A_42, B_43, C_44]: (k7_subset_1(A_42, B_43, C_44)=k4_xboole_0(B_43, C_44) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.46/1.53  tff(c_105, plain, (![C_45]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_45)=k4_xboole_0('#skF_2', C_45))), inference(resolution, [status(thm)], [c_28, c_101])).
% 3.46/1.53  tff(c_111, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_105, c_96])).
% 3.46/1.53  tff(c_123, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_111, c_4])).
% 3.46/1.53  tff(c_104, plain, (![C_44]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_44)=k4_xboole_0('#skF_2', C_44))), inference(resolution, [status(thm)], [c_28, c_101])).
% 3.46/1.53  tff(c_314, plain, (![A_65, B_66]: (k7_subset_1(u1_struct_0(A_65), B_66, k2_tops_1(A_65, B_66))=k1_tops_1(A_65, B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.46/1.53  tff(c_318, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_314])).
% 3.46/1.53  tff(c_322, plain, (k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_123, c_104, c_318])).
% 3.46/1.53  tff(c_68, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k4_xboole_0(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.46/1.53  tff(c_71, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k3_xboole_0(A_38, B_39))=k3_xboole_0(A_38, k4_xboole_0(A_38, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_4])).
% 3.46/1.53  tff(c_333, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2')))=k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_322, c_71])).
% 3.46/1.53  tff(c_340, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_111, c_333])).
% 3.46/1.53  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k3_xboole_0(A_1, B_2))=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.46/1.53  tff(c_367, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_340, c_2])).
% 3.46/1.53  tff(c_18, plain, (![A_18, B_19]: (m1_subset_1(k2_tops_1(A_18, B_19), k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.46/1.53  tff(c_260, plain, (![A_56, B_57, C_58]: (k4_subset_1(A_56, B_57, C_58)=k2_xboole_0(B_57, C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(A_56)) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.46/1.53  tff(c_819, plain, (![A_95, B_96, B_97]: (k4_subset_1(u1_struct_0(A_95), B_96, k2_tops_1(A_95, B_97))=k2_xboole_0(B_96, k2_tops_1(A_95, B_97)) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(resolution, [status(thm)], [c_18, c_260])).
% 3.46/1.53  tff(c_823, plain, (![B_97]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_97))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_97)) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_819])).
% 3.46/1.53  tff(c_828, plain, (![B_98]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_98))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_98)) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_823])).
% 3.46/1.53  tff(c_835, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_828])).
% 3.46/1.53  tff(c_840, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_389, c_367, c_835])).
% 3.46/1.53  tff(c_842, plain, $false, inference(negUnitSimplification, [status(thm)], [c_312, c_840])).
% 3.46/1.53  tff(c_844, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 3.46/1.53  tff(c_849, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_848, c_844])).
% 3.46/1.53  tff(c_1087, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1083, c_849])).
% 3.46/1.53  tff(c_843, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_40])).
% 3.46/1.53  tff(c_907, plain, (![A_109, B_110]: (k2_pre_topc(A_109, B_110)=B_110 | ~v4_pre_topc(B_110, A_109) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.46/1.53  tff(c_913, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_907])).
% 3.46/1.53  tff(c_917, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_843, c_913])).
% 3.46/1.53  tff(c_1144, plain, (![A_128, B_129]: (k7_subset_1(u1_struct_0(A_128), k2_pre_topc(A_128, B_129), k1_tops_1(A_128, B_129))=k2_tops_1(A_128, B_129) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.46/1.53  tff(c_1153, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_917, c_1144])).
% 3.46/1.53  tff(c_1157, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1083, c_848, c_1153])).
% 3.46/1.53  tff(c_1159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1087, c_1157])).
% 3.46/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.53  
% 3.46/1.53  Inference rules
% 3.46/1.53  ----------------------
% 3.46/1.53  #Ref     : 0
% 3.46/1.53  #Sup     : 294
% 3.46/1.53  #Fact    : 0
% 3.46/1.53  #Define  : 0
% 3.46/1.53  #Split   : 2
% 3.46/1.53  #Chain   : 0
% 3.46/1.53  #Close   : 0
% 3.46/1.53  
% 3.46/1.53  Ordering : KBO
% 3.46/1.53  
% 3.46/1.53  Simplification rules
% 3.46/1.53  ----------------------
% 3.46/1.53  #Subsume      : 2
% 3.46/1.53  #Demod        : 235
% 3.46/1.53  #Tautology    : 180
% 3.46/1.53  #SimpNegUnit  : 3
% 3.46/1.53  #BackRed      : 6
% 3.46/1.53  
% 3.46/1.53  #Partial instantiations: 0
% 3.46/1.53  #Strategies tried      : 1
% 3.46/1.53  
% 3.46/1.53  Timing (in seconds)
% 3.46/1.53  ----------------------
% 3.46/1.53  Preprocessing        : 0.32
% 3.46/1.53  Parsing              : 0.17
% 3.46/1.53  CNF conversion       : 0.02
% 3.46/1.53  Main loop            : 0.44
% 3.46/1.53  Inferencing          : 0.16
% 3.46/1.53  Reduction            : 0.16
% 3.46/1.53  Demodulation         : 0.13
% 3.46/1.53  BG Simplification    : 0.02
% 3.46/1.53  Subsumption          : 0.06
% 3.46/1.53  Abstraction          : 0.03
% 3.46/1.53  MUC search           : 0.00
% 3.46/1.53  Cooper               : 0.00
% 3.46/1.53  Total                : 0.79
% 3.46/1.53  Index Insertion      : 0.00
% 3.46/1.53  Index Deletion       : 0.00
% 3.46/1.53  Index Matching       : 0.00
% 3.46/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
