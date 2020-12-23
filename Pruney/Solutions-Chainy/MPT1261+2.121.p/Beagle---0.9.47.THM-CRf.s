%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:28 EST 2020

% Result     : Theorem 5.74s
% Output     : CNFRefutation 5.74s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 473 expanded)
%              Number of leaves         :   40 ( 176 expanded)
%              Depth                    :   16
%              Number of atoms          :  177 ( 991 expanded)
%              Number of equality atoms :   66 ( 307 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_76,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_37,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3763,plain,(
    ! [A_227,B_228,C_229] :
      ( k7_subset_1(A_227,B_228,C_229) = k4_xboole_0(B_228,C_229)
      | ~ m1_subset_1(B_228,k1_zfmisc_1(A_227)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3772,plain,(
    ! [C_229] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_229) = k4_xboole_0('#skF_2',C_229) ),
    inference(resolution,[status(thm)],[c_40,c_3763])).

tff(c_52,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_111,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_211,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_46])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_858,plain,(
    ! [B_102,A_103] :
      ( v4_pre_topc(B_102,A_103)
      | k2_pre_topc(A_103,B_102) != B_102
      | ~ v2_pre_topc(A_103)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_872,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_858])).

tff(c_878,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_872])).

tff(c_879,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_878])).

tff(c_633,plain,(
    ! [A_71,B_72,C_73] :
      ( k7_subset_1(A_71,B_72,C_73) = k4_xboole_0(B_72,C_73)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_643,plain,(
    ! [C_74] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_74) = k4_xboole_0('#skF_2',C_74) ),
    inference(resolution,[status(thm)],[c_40,c_633])).

tff(c_649,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_643,c_111])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_661,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_649,c_6])).

tff(c_994,plain,(
    ! [A_114,B_115] :
      ( k4_subset_1(u1_struct_0(A_114),B_115,k2_tops_1(A_114,B_115)) = k2_pre_topc(A_114,B_115)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1004,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_994])).

tff(c_1010,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1004])).

tff(c_734,plain,(
    ! [A_83,B_84] :
      ( m1_subset_1(k2_tops_1(A_83,B_84),k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_24,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ m1_subset_1(A_24,k1_zfmisc_1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_744,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(k2_tops_1(A_83,B_84),u1_struct_0(A_83))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(resolution,[status(thm)],[c_734,c_24])).

tff(c_26,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,k1_zfmisc_1(B_25))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_822,plain,(
    ! [A_98,B_99,C_100] :
      ( k4_subset_1(A_98,B_99,C_100) = k2_xboole_0(B_99,C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(A_98))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_933,plain,(
    ! [B_106,B_107,A_108] :
      ( k4_subset_1(B_106,B_107,A_108) = k2_xboole_0(B_107,A_108)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(B_106))
      | ~ r1_tarski(A_108,B_106) ) ),
    inference(resolution,[status(thm)],[c_26,c_822])).

tff(c_946,plain,(
    ! [A_109] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_109) = k2_xboole_0('#skF_2',A_109)
      | ~ r1_tarski(A_109,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_40,c_933])).

tff(c_950,plain,(
    ! [B_84] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_84)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_84))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_744,c_946])).

tff(c_1406,plain,(
    ! [B_132] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_132)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_132))
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_950])).

tff(c_1421,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_1406])).

tff(c_1428,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1010,c_1421])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k3_subset_1(A_12,B_13),k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1792,plain,(
    ! [A_145,B_146,B_147] :
      ( k4_subset_1(A_145,B_146,k3_subset_1(A_145,B_147)) = k2_xboole_0(B_146,k3_subset_1(A_145,B_147))
      | ~ m1_subset_1(B_146,k1_zfmisc_1(A_145))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(A_145)) ) ),
    inference(resolution,[status(thm)],[c_14,c_822])).

tff(c_1887,plain,(
    ! [B_154,A_155,B_156] :
      ( k4_subset_1(B_154,A_155,k3_subset_1(B_154,B_156)) = k2_xboole_0(A_155,k3_subset_1(B_154,B_156))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(B_154))
      | ~ r1_tarski(A_155,B_154) ) ),
    inference(resolution,[status(thm)],[c_26,c_1792])).

tff(c_1980,plain,(
    ! [B_158,A_159,A_160] :
      ( k4_subset_1(B_158,A_159,k3_subset_1(B_158,A_160)) = k2_xboole_0(A_159,k3_subset_1(B_158,A_160))
      | ~ r1_tarski(A_159,B_158)
      | ~ r1_tarski(A_160,B_158) ) ),
    inference(resolution,[status(thm)],[c_26,c_1887])).

tff(c_12,plain,(
    ! [A_11] : k2_subset_1(A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( k4_subset_1(A_20,B_21,k3_subset_1(A_20,B_21)) = k2_subset_1(A_20)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_684,plain,(
    ! [A_78,B_79] :
      ( k4_subset_1(A_78,B_79,k3_subset_1(A_78,B_79)) = A_78
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_20])).

tff(c_692,plain,(
    ! [B_25,A_24] :
      ( k4_subset_1(B_25,A_24,k3_subset_1(B_25,A_24)) = B_25
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_26,c_684])).

tff(c_2046,plain,(
    ! [A_161,B_162] :
      ( k2_xboole_0(A_161,k3_subset_1(B_162,A_161)) = B_162
      | ~ r1_tarski(A_161,B_162)
      | ~ r1_tarski(A_161,B_162)
      | ~ r1_tarski(A_161,B_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1980,c_692])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2105,plain,(
    ! [A_163,B_164] :
      ( k2_xboole_0(A_163,k3_subset_1(B_164,A_163)) = k2_xboole_0(A_163,B_164)
      | ~ r1_tarski(A_163,B_164)
      | ~ r1_tarski(A_163,B_164)
      | ~ r1_tarski(A_163,B_164) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2046,c_8])).

tff(c_126,plain,(
    ! [A_53,B_54] : k2_xboole_0(A_53,k2_xboole_0(A_53,B_54)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_141,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k2_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_126])).

tff(c_2141,plain,(
    ! [B_164,A_163] :
      ( k2_xboole_0(k3_subset_1(B_164,A_163),k2_xboole_0(A_163,B_164)) = k2_xboole_0(k3_subset_1(B_164,A_163),A_163)
      | ~ r1_tarski(A_163,B_164)
      | ~ r1_tarski(A_163,B_164)
      | ~ r1_tarski(A_163,B_164) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2105,c_141])).

tff(c_3109,plain,(
    ! [A_203,B_204] :
      ( k2_xboole_0(k2_xboole_0(A_203,B_204),k3_subset_1(B_204,A_203)) = k2_xboole_0(A_203,k3_subset_1(B_204,A_203))
      | ~ r1_tarski(A_203,B_204)
      | ~ r1_tarski(A_203,B_204)
      | ~ r1_tarski(A_203,B_204) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_2141])).

tff(c_3253,plain,(
    ! [B_205,A_206] :
      ( k2_xboole_0(k2_xboole_0(B_205,A_206),k3_subset_1(B_205,A_206)) = k2_xboole_0(A_206,k3_subset_1(B_205,A_206))
      | ~ r1_tarski(A_206,B_205)
      | ~ r1_tarski(A_206,B_205)
      | ~ r1_tarski(A_206,B_205) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3109])).

tff(c_3351,plain,
    ( k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k2_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1428,c_3253])).

tff(c_3407,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k2_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_661,c_661,c_3351])).

tff(c_2006,plain,(
    ! [A_160,B_158] :
      ( k2_xboole_0(A_160,k3_subset_1(B_158,A_160)) = B_158
      | ~ r1_tarski(A_160,B_158)
      | ~ r1_tarski(A_160,B_158)
      | ~ r1_tarski(A_160,B_158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1980,c_692])).

tff(c_3435,plain,
    ( k2_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = '#skF_2'
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3407,c_2006])).

tff(c_3486,plain,(
    k2_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_661,c_661,c_3435])).

tff(c_1460,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1428,c_8])).

tff(c_1472,plain,(
    k2_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1428,c_1460])).

tff(c_3541,plain,(
    k2_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k2_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3486,c_8])).

tff(c_3553,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3486,c_1472,c_2,c_3541])).

tff(c_3555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_879,c_3553])).

tff(c_3556,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_3646,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3556,c_46])).

tff(c_3773,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3772,c_3646])).

tff(c_4154,plain,(
    ! [A_242,B_243] :
      ( k2_pre_topc(A_242,B_243) = B_243
      | ~ v4_pre_topc(B_243,A_242)
      | ~ m1_subset_1(B_243,k1_zfmisc_1(u1_struct_0(A_242)))
      | ~ l1_pre_topc(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4168,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_4154])).

tff(c_4174,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3556,c_4168])).

tff(c_4486,plain,(
    ! [A_284,B_285] :
      ( k7_subset_1(u1_struct_0(A_284),k2_pre_topc(A_284,B_285),k1_tops_1(A_284,B_285)) = k2_tops_1(A_284,B_285)
      | ~ m1_subset_1(B_285,k1_zfmisc_1(u1_struct_0(A_284)))
      | ~ l1_pre_topc(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4495,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4174,c_4486])).

tff(c_4499,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_3772,c_4495])).

tff(c_4501,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3773,c_4499])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:28:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.74/2.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.74/2.08  
% 5.74/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.74/2.08  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 5.74/2.08  
% 5.74/2.08  %Foreground sorts:
% 5.74/2.08  
% 5.74/2.08  
% 5.74/2.08  %Background operators:
% 5.74/2.08  
% 5.74/2.08  
% 5.74/2.08  %Foreground operators:
% 5.74/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.74/2.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.74/2.08  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.74/2.08  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.74/2.08  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.74/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.74/2.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.74/2.08  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.74/2.08  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.74/2.08  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.74/2.08  tff('#skF_2', type, '#skF_2': $i).
% 5.74/2.08  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.74/2.08  tff('#skF_1', type, '#skF_1': $i).
% 5.74/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.74/2.08  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.74/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.74/2.08  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.74/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.74/2.08  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.74/2.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.74/2.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.74/2.08  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.74/2.08  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.74/2.08  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.74/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.74/2.08  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.74/2.08  
% 5.74/2.10  tff(f_116, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 5.74/2.10  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.74/2.10  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.74/2.10  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.74/2.10  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 5.74/2.10  tff(f_82, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.74/2.10  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.74/2.10  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.74/2.10  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.74/2.10  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.74/2.10  tff(f_37, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.74/2.10  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 5.74/2.10  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 5.74/2.10  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 5.74/2.10  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.74/2.10  tff(c_3763, plain, (![A_227, B_228, C_229]: (k7_subset_1(A_227, B_228, C_229)=k4_xboole_0(B_228, C_229) | ~m1_subset_1(B_228, k1_zfmisc_1(A_227)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.74/2.10  tff(c_3772, plain, (![C_229]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_229)=k4_xboole_0('#skF_2', C_229))), inference(resolution, [status(thm)], [c_40, c_3763])).
% 5.74/2.10  tff(c_52, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.74/2.10  tff(c_111, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_52])).
% 5.74/2.10  tff(c_46, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.74/2.10  tff(c_211, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_46])).
% 5.74/2.10  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.74/2.10  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.74/2.10  tff(c_858, plain, (![B_102, A_103]: (v4_pre_topc(B_102, A_103) | k2_pre_topc(A_103, B_102)!=B_102 | ~v2_pre_topc(A_103) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.74/2.10  tff(c_872, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_858])).
% 5.74/2.10  tff(c_878, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_872])).
% 5.74/2.10  tff(c_879, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_211, c_878])).
% 5.74/2.10  tff(c_633, plain, (![A_71, B_72, C_73]: (k7_subset_1(A_71, B_72, C_73)=k4_xboole_0(B_72, C_73) | ~m1_subset_1(B_72, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.74/2.10  tff(c_643, plain, (![C_74]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_74)=k4_xboole_0('#skF_2', C_74))), inference(resolution, [status(thm)], [c_40, c_633])).
% 5.74/2.10  tff(c_649, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_643, c_111])).
% 5.74/2.10  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.74/2.10  tff(c_661, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_649, c_6])).
% 5.74/2.10  tff(c_994, plain, (![A_114, B_115]: (k4_subset_1(u1_struct_0(A_114), B_115, k2_tops_1(A_114, B_115))=k2_pre_topc(A_114, B_115) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.74/2.10  tff(c_1004, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_994])).
% 5.74/2.10  tff(c_1010, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1004])).
% 5.74/2.10  tff(c_734, plain, (![A_83, B_84]: (m1_subset_1(k2_tops_1(A_83, B_84), k1_zfmisc_1(u1_struct_0(A_83))) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.74/2.10  tff(c_24, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~m1_subset_1(A_24, k1_zfmisc_1(B_25)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.74/2.10  tff(c_744, plain, (![A_83, B_84]: (r1_tarski(k2_tops_1(A_83, B_84), u1_struct_0(A_83)) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(resolution, [status(thm)], [c_734, c_24])).
% 5.74/2.10  tff(c_26, plain, (![A_24, B_25]: (m1_subset_1(A_24, k1_zfmisc_1(B_25)) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.74/2.10  tff(c_822, plain, (![A_98, B_99, C_100]: (k4_subset_1(A_98, B_99, C_100)=k2_xboole_0(B_99, C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(A_98)) | ~m1_subset_1(B_99, k1_zfmisc_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.74/2.10  tff(c_933, plain, (![B_106, B_107, A_108]: (k4_subset_1(B_106, B_107, A_108)=k2_xboole_0(B_107, A_108) | ~m1_subset_1(B_107, k1_zfmisc_1(B_106)) | ~r1_tarski(A_108, B_106))), inference(resolution, [status(thm)], [c_26, c_822])).
% 5.74/2.10  tff(c_946, plain, (![A_109]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_109)=k2_xboole_0('#skF_2', A_109) | ~r1_tarski(A_109, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_40, c_933])).
% 5.74/2.10  tff(c_950, plain, (![B_84]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_84))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_84)) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_744, c_946])).
% 5.74/2.10  tff(c_1406, plain, (![B_132]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_132))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_132)) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_950])).
% 5.74/2.10  tff(c_1421, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_1406])).
% 5.74/2.10  tff(c_1428, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1010, c_1421])).
% 5.74/2.10  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.74/2.10  tff(c_14, plain, (![A_12, B_13]: (m1_subset_1(k3_subset_1(A_12, B_13), k1_zfmisc_1(A_12)) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.74/2.10  tff(c_1792, plain, (![A_145, B_146, B_147]: (k4_subset_1(A_145, B_146, k3_subset_1(A_145, B_147))=k2_xboole_0(B_146, k3_subset_1(A_145, B_147)) | ~m1_subset_1(B_146, k1_zfmisc_1(A_145)) | ~m1_subset_1(B_147, k1_zfmisc_1(A_145)))), inference(resolution, [status(thm)], [c_14, c_822])).
% 5.74/2.10  tff(c_1887, plain, (![B_154, A_155, B_156]: (k4_subset_1(B_154, A_155, k3_subset_1(B_154, B_156))=k2_xboole_0(A_155, k3_subset_1(B_154, B_156)) | ~m1_subset_1(B_156, k1_zfmisc_1(B_154)) | ~r1_tarski(A_155, B_154))), inference(resolution, [status(thm)], [c_26, c_1792])).
% 5.74/2.10  tff(c_1980, plain, (![B_158, A_159, A_160]: (k4_subset_1(B_158, A_159, k3_subset_1(B_158, A_160))=k2_xboole_0(A_159, k3_subset_1(B_158, A_160)) | ~r1_tarski(A_159, B_158) | ~r1_tarski(A_160, B_158))), inference(resolution, [status(thm)], [c_26, c_1887])).
% 5.74/2.10  tff(c_12, plain, (![A_11]: (k2_subset_1(A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.74/2.10  tff(c_20, plain, (![A_20, B_21]: (k4_subset_1(A_20, B_21, k3_subset_1(A_20, B_21))=k2_subset_1(A_20) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.74/2.10  tff(c_684, plain, (![A_78, B_79]: (k4_subset_1(A_78, B_79, k3_subset_1(A_78, B_79))=A_78 | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_20])).
% 5.74/2.10  tff(c_692, plain, (![B_25, A_24]: (k4_subset_1(B_25, A_24, k3_subset_1(B_25, A_24))=B_25 | ~r1_tarski(A_24, B_25))), inference(resolution, [status(thm)], [c_26, c_684])).
% 5.74/2.10  tff(c_2046, plain, (![A_161, B_162]: (k2_xboole_0(A_161, k3_subset_1(B_162, A_161))=B_162 | ~r1_tarski(A_161, B_162) | ~r1_tarski(A_161, B_162) | ~r1_tarski(A_161, B_162))), inference(superposition, [status(thm), theory('equality')], [c_1980, c_692])).
% 5.74/2.10  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.74/2.10  tff(c_2105, plain, (![A_163, B_164]: (k2_xboole_0(A_163, k3_subset_1(B_164, A_163))=k2_xboole_0(A_163, B_164) | ~r1_tarski(A_163, B_164) | ~r1_tarski(A_163, B_164) | ~r1_tarski(A_163, B_164))), inference(superposition, [status(thm), theory('equality')], [c_2046, c_8])).
% 5.74/2.10  tff(c_126, plain, (![A_53, B_54]: (k2_xboole_0(A_53, k2_xboole_0(A_53, B_54))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.74/2.10  tff(c_141, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k2_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_126])).
% 5.74/2.10  tff(c_2141, plain, (![B_164, A_163]: (k2_xboole_0(k3_subset_1(B_164, A_163), k2_xboole_0(A_163, B_164))=k2_xboole_0(k3_subset_1(B_164, A_163), A_163) | ~r1_tarski(A_163, B_164) | ~r1_tarski(A_163, B_164) | ~r1_tarski(A_163, B_164))), inference(superposition, [status(thm), theory('equality')], [c_2105, c_141])).
% 5.74/2.10  tff(c_3109, plain, (![A_203, B_204]: (k2_xboole_0(k2_xboole_0(A_203, B_204), k3_subset_1(B_204, A_203))=k2_xboole_0(A_203, k3_subset_1(B_204, A_203)) | ~r1_tarski(A_203, B_204) | ~r1_tarski(A_203, B_204) | ~r1_tarski(A_203, B_204))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_2141])).
% 5.74/2.10  tff(c_3253, plain, (![B_205, A_206]: (k2_xboole_0(k2_xboole_0(B_205, A_206), k3_subset_1(B_205, A_206))=k2_xboole_0(A_206, k3_subset_1(B_205, A_206)) | ~r1_tarski(A_206, B_205) | ~r1_tarski(A_206, B_205) | ~r1_tarski(A_206, B_205))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3109])).
% 5.74/2.10  tff(c_3351, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k2_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1428, c_3253])).
% 5.74/2.10  tff(c_3407, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k2_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_661, c_661, c_661, c_3351])).
% 5.74/2.10  tff(c_2006, plain, (![A_160, B_158]: (k2_xboole_0(A_160, k3_subset_1(B_158, A_160))=B_158 | ~r1_tarski(A_160, B_158) | ~r1_tarski(A_160, B_158) | ~r1_tarski(A_160, B_158))), inference(superposition, [status(thm), theory('equality')], [c_1980, c_692])).
% 5.74/2.10  tff(c_3435, plain, (k2_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))='#skF_2' | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3407, c_2006])).
% 5.74/2.10  tff(c_3486, plain, (k2_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_661, c_661, c_661, c_3435])).
% 5.74/2.10  tff(c_1460, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1428, c_8])).
% 5.74/2.10  tff(c_1472, plain, (k2_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1428, c_1460])).
% 5.74/2.10  tff(c_3541, plain, (k2_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k2_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3486, c_8])).
% 5.74/2.10  tff(c_3553, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3486, c_1472, c_2, c_3541])).
% 5.74/2.10  tff(c_3555, plain, $false, inference(negUnitSimplification, [status(thm)], [c_879, c_3553])).
% 5.74/2.10  tff(c_3556, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 5.74/2.10  tff(c_3646, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3556, c_46])).
% 5.74/2.10  tff(c_3773, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3772, c_3646])).
% 5.74/2.10  tff(c_4154, plain, (![A_242, B_243]: (k2_pre_topc(A_242, B_243)=B_243 | ~v4_pre_topc(B_243, A_242) | ~m1_subset_1(B_243, k1_zfmisc_1(u1_struct_0(A_242))) | ~l1_pre_topc(A_242))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.74/2.10  tff(c_4168, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_4154])).
% 5.74/2.10  tff(c_4174, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3556, c_4168])).
% 5.74/2.10  tff(c_4486, plain, (![A_284, B_285]: (k7_subset_1(u1_struct_0(A_284), k2_pre_topc(A_284, B_285), k1_tops_1(A_284, B_285))=k2_tops_1(A_284, B_285) | ~m1_subset_1(B_285, k1_zfmisc_1(u1_struct_0(A_284))) | ~l1_pre_topc(A_284))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.74/2.10  tff(c_4495, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4174, c_4486])).
% 5.74/2.10  tff(c_4499, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_3772, c_4495])).
% 5.74/2.10  tff(c_4501, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3773, c_4499])).
% 5.74/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.74/2.10  
% 5.74/2.10  Inference rules
% 5.74/2.10  ----------------------
% 5.74/2.10  #Ref     : 0
% 5.74/2.10  #Sup     : 1067
% 5.74/2.10  #Fact    : 0
% 5.74/2.10  #Define  : 0
% 5.74/2.10  #Split   : 6
% 5.74/2.10  #Chain   : 0
% 5.74/2.10  #Close   : 0
% 5.74/2.10  
% 5.74/2.10  Ordering : KBO
% 5.74/2.10  
% 5.74/2.10  Simplification rules
% 5.74/2.10  ----------------------
% 5.74/2.10  #Subsume      : 126
% 5.74/2.10  #Demod        : 1299
% 5.74/2.10  #Tautology    : 621
% 5.74/2.10  #SimpNegUnit  : 5
% 5.74/2.10  #BackRed      : 3
% 5.74/2.10  
% 5.74/2.10  #Partial instantiations: 0
% 5.74/2.10  #Strategies tried      : 1
% 5.74/2.10  
% 5.74/2.10  Timing (in seconds)
% 5.74/2.10  ----------------------
% 5.74/2.11  Preprocessing        : 0.32
% 5.74/2.11  Parsing              : 0.17
% 5.74/2.11  CNF conversion       : 0.02
% 5.74/2.11  Main loop            : 1.00
% 5.74/2.11  Inferencing          : 0.30
% 5.74/2.11  Reduction            : 0.45
% 5.74/2.11  Demodulation         : 0.37
% 5.74/2.11  BG Simplification    : 0.04
% 5.74/2.11  Subsumption          : 0.16
% 5.74/2.11  Abstraction          : 0.06
% 5.74/2.11  MUC search           : 0.00
% 5.74/2.11  Cooper               : 0.00
% 5.74/2.11  Total                : 1.36
% 5.74/2.11  Index Insertion      : 0.00
% 5.74/2.11  Index Deletion       : 0.00
% 5.74/2.11  Index Matching       : 0.00
% 5.74/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
