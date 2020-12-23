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
% DateTime   : Thu Dec  3 10:21:25 EST 2020

% Result     : Theorem 5.18s
% Output     : CNFRefutation 5.38s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 123 expanded)
%              Number of leaves         :   34 (  55 expanded)
%              Depth                    :    8
%              Number of atoms          :  117 ( 238 expanded)
%              Number of equality atoms :   44 (  70 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_100,negated_conjecture,(
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

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4636,plain,(
    ! [A_158,B_159,C_160] :
      ( k7_subset_1(A_158,B_159,C_160) = k4_xboole_0(B_159,C_160)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(A_158)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4639,plain,(
    ! [C_160] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_160) = k4_xboole_0('#skF_2',C_160) ),
    inference(resolution,[status(thm)],[c_28,c_4636])).

tff(c_34,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_141,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1316,plain,(
    ! [A_97,B_98] :
      ( k4_subset_1(u1_struct_0(A_97),B_98,k2_tops_1(A_97,B_98)) = k2_pre_topc(A_97,B_98)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1320,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1316])).

tff(c_1324,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1320])).

tff(c_40,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_211,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_40])).

tff(c_263,plain,(
    ! [A_57,B_58,C_59] :
      ( k7_subset_1(A_57,B_58,C_59) = k4_xboole_0(B_58,C_59)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_310,plain,(
    ! [C_62] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_62) = k4_xboole_0('#skF_2',C_62) ),
    inference(resolution,[status(thm)],[c_28,c_263])).

tff(c_322,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_310])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_113,plain,(
    ! [A_41,B_42] :
      ( k2_xboole_0(A_41,B_42) = B_42
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_118,plain,(
    ! [A_43,B_44] : k2_xboole_0(k4_xboole_0(A_43,B_44),A_43) = A_43 ),
    inference(resolution,[status(thm)],[c_10,c_113])).

tff(c_138,plain,(
    ! [A_1,B_44] : k2_xboole_0(A_1,k4_xboole_0(A_1,B_44)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_118])).

tff(c_369,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_138])).

tff(c_18,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k2_tops_1(A_19,B_20),k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_571,plain,(
    ! [A_77,B_78,C_79] :
      ( k4_subset_1(A_77,B_78,C_79) = k2_xboole_0(B_78,C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(A_77))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4446,plain,(
    ! [A_140,B_141,B_142] :
      ( k4_subset_1(u1_struct_0(A_140),B_141,k2_tops_1(A_140,B_142)) = k2_xboole_0(B_141,k2_tops_1(A_140,B_142))
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140) ) ),
    inference(resolution,[status(thm)],[c_18,c_571])).

tff(c_4450,plain,(
    ! [B_142] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_142)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_142))
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_4446])).

tff(c_4458,plain,(
    ! [B_143] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_143)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_143))
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4450])).

tff(c_4465,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_4458])).

tff(c_4470,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1324,c_369,c_4465])).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_464,plain,(
    ! [A_69,B_70] :
      ( v4_pre_topc(k2_pre_topc(A_69,B_70),A_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_468,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_464])).

tff(c_472,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_468])).

tff(c_4472,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4470,c_472])).

tff(c_4474,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_4472])).

tff(c_4475,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_4679,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4639,c_4475])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4476,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_4949,plain,(
    ! [A_180,B_181] :
      ( r1_tarski(k2_tops_1(A_180,B_181),B_181)
      | ~ v4_pre_topc(B_181,A_180)
      | ~ m1_subset_1(B_181,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ l1_pre_topc(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4953,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_4949])).

tff(c_4957,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4476,c_4953])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4965,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_4957,c_8])).

tff(c_5032,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_4965])).

tff(c_5453,plain,(
    ! [A_192,B_193] :
      ( k7_subset_1(u1_struct_0(A_192),B_193,k2_tops_1(A_192,B_193)) = k1_tops_1(A_192,B_193)
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ l1_pre_topc(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_5457,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_5453])).

tff(c_5461,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4639,c_5457])).

tff(c_12,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5477,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5461,c_12])).

tff(c_5493,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5032,c_5477])).

tff(c_5495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4679,c_5493])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:54:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.18/2.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.18/2.10  
% 5.18/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.18/2.10  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 5.18/2.10  
% 5.18/2.10  %Foreground sorts:
% 5.18/2.10  
% 5.18/2.10  
% 5.18/2.10  %Background operators:
% 5.18/2.10  
% 5.18/2.10  
% 5.18/2.10  %Foreground operators:
% 5.18/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.18/2.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.18/2.10  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.18/2.10  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.18/2.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.18/2.10  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.18/2.10  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.18/2.10  tff('#skF_2', type, '#skF_2': $i).
% 5.18/2.10  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.18/2.10  tff('#skF_1', type, '#skF_1': $i).
% 5.18/2.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.18/2.10  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.18/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.18/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.18/2.10  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.18/2.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.18/2.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.18/2.10  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.18/2.10  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.18/2.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.18/2.10  
% 5.38/2.12  tff(f_100, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 5.38/2.12  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.38/2.12  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 5.38/2.12  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.38/2.12  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.38/2.12  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.38/2.12  tff(f_57, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.38/2.12  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.38/2.12  tff(f_65, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 5.38/2.12  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.38/2.12  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 5.38/2.12  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.38/2.12  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 5.38/2.12  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.38/2.12  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.38/2.12  tff(c_4636, plain, (![A_158, B_159, C_160]: (k7_subset_1(A_158, B_159, C_160)=k4_xboole_0(B_159, C_160) | ~m1_subset_1(B_159, k1_zfmisc_1(A_158)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.38/2.12  tff(c_4639, plain, (![C_160]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_160)=k4_xboole_0('#skF_2', C_160))), inference(resolution, [status(thm)], [c_28, c_4636])).
% 5.38/2.12  tff(c_34, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.38/2.12  tff(c_141, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_34])).
% 5.38/2.12  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.38/2.12  tff(c_1316, plain, (![A_97, B_98]: (k4_subset_1(u1_struct_0(A_97), B_98, k2_tops_1(A_97, B_98))=k2_pre_topc(A_97, B_98) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.38/2.12  tff(c_1320, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_1316])).
% 5.38/2.12  tff(c_1324, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1320])).
% 5.38/2.12  tff(c_40, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.38/2.12  tff(c_211, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_141, c_40])).
% 5.38/2.12  tff(c_263, plain, (![A_57, B_58, C_59]: (k7_subset_1(A_57, B_58, C_59)=k4_xboole_0(B_58, C_59) | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.38/2.12  tff(c_310, plain, (![C_62]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_62)=k4_xboole_0('#skF_2', C_62))), inference(resolution, [status(thm)], [c_28, c_263])).
% 5.38/2.12  tff(c_322, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_211, c_310])).
% 5.38/2.12  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.38/2.12  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.38/2.12  tff(c_113, plain, (![A_41, B_42]: (k2_xboole_0(A_41, B_42)=B_42 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.38/2.12  tff(c_118, plain, (![A_43, B_44]: (k2_xboole_0(k4_xboole_0(A_43, B_44), A_43)=A_43)), inference(resolution, [status(thm)], [c_10, c_113])).
% 5.38/2.12  tff(c_138, plain, (![A_1, B_44]: (k2_xboole_0(A_1, k4_xboole_0(A_1, B_44))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_118])).
% 5.38/2.12  tff(c_369, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_322, c_138])).
% 5.38/2.12  tff(c_18, plain, (![A_19, B_20]: (m1_subset_1(k2_tops_1(A_19, B_20), k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.38/2.12  tff(c_571, plain, (![A_77, B_78, C_79]: (k4_subset_1(A_77, B_78, C_79)=k2_xboole_0(B_78, C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(A_77)) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.38/2.12  tff(c_4446, plain, (![A_140, B_141, B_142]: (k4_subset_1(u1_struct_0(A_140), B_141, k2_tops_1(A_140, B_142))=k2_xboole_0(B_141, k2_tops_1(A_140, B_142)) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_140))) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140))), inference(resolution, [status(thm)], [c_18, c_571])).
% 5.38/2.12  tff(c_4450, plain, (![B_142]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_142))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_142)) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_4446])).
% 5.38/2.12  tff(c_4458, plain, (![B_143]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_143))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_143)) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_4450])).
% 5.38/2.12  tff(c_4465, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_4458])).
% 5.38/2.12  tff(c_4470, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1324, c_369, c_4465])).
% 5.38/2.12  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.38/2.12  tff(c_464, plain, (![A_69, B_70]: (v4_pre_topc(k2_pre_topc(A_69, B_70), A_69) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.38/2.12  tff(c_468, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_464])).
% 5.38/2.12  tff(c_472, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_468])).
% 5.38/2.12  tff(c_4472, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4470, c_472])).
% 5.38/2.12  tff(c_4474, plain, $false, inference(negUnitSimplification, [status(thm)], [c_141, c_4472])).
% 5.38/2.12  tff(c_4475, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_34])).
% 5.38/2.12  tff(c_4679, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4639, c_4475])).
% 5.38/2.12  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.38/2.12  tff(c_4476, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 5.38/2.12  tff(c_4949, plain, (![A_180, B_181]: (r1_tarski(k2_tops_1(A_180, B_181), B_181) | ~v4_pre_topc(B_181, A_180) | ~m1_subset_1(B_181, k1_zfmisc_1(u1_struct_0(A_180))) | ~l1_pre_topc(A_180))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.38/2.12  tff(c_4953, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_4949])).
% 5.38/2.12  tff(c_4957, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_4476, c_4953])).
% 5.38/2.12  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.38/2.12  tff(c_4965, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_4957, c_8])).
% 5.38/2.12  tff(c_5032, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4, c_4965])).
% 5.38/2.12  tff(c_5453, plain, (![A_192, B_193]: (k7_subset_1(u1_struct_0(A_192), B_193, k2_tops_1(A_192, B_193))=k1_tops_1(A_192, B_193) | ~m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0(A_192))) | ~l1_pre_topc(A_192))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.38/2.12  tff(c_5457, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_5453])).
% 5.38/2.12  tff(c_5461, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_4639, c_5457])).
% 5.38/2.12  tff(c_12, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.38/2.12  tff(c_5477, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5461, c_12])).
% 5.38/2.12  tff(c_5493, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5032, c_5477])).
% 5.38/2.12  tff(c_5495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4679, c_5493])).
% 5.38/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.38/2.12  
% 5.38/2.12  Inference rules
% 5.38/2.12  ----------------------
% 5.38/2.12  #Ref     : 0
% 5.38/2.12  #Sup     : 1382
% 5.38/2.12  #Fact    : 0
% 5.38/2.12  #Define  : 0
% 5.38/2.12  #Split   : 1
% 5.38/2.12  #Chain   : 0
% 5.38/2.12  #Close   : 0
% 5.38/2.12  
% 5.38/2.12  Ordering : KBO
% 5.38/2.12  
% 5.38/2.12  Simplification rules
% 5.38/2.12  ----------------------
% 5.38/2.12  #Subsume      : 113
% 5.38/2.12  #Demod        : 1944
% 5.38/2.12  #Tautology    : 961
% 5.38/2.12  #SimpNegUnit  : 3
% 5.38/2.12  #BackRed      : 4
% 5.38/2.12  
% 5.38/2.12  #Partial instantiations: 0
% 5.38/2.12  #Strategies tried      : 1
% 5.38/2.12  
% 5.38/2.12  Timing (in seconds)
% 5.38/2.12  ----------------------
% 5.38/2.12  Preprocessing        : 0.33
% 5.38/2.12  Parsing              : 0.17
% 5.38/2.12  CNF conversion       : 0.02
% 5.38/2.12  Main loop            : 1.02
% 5.38/2.12  Inferencing          : 0.28
% 5.38/2.12  Reduction            : 0.52
% 5.38/2.12  Demodulation         : 0.46
% 5.38/2.12  BG Simplification    : 0.03
% 5.38/2.12  Subsumption          : 0.12
% 5.38/2.12  Abstraction          : 0.06
% 5.38/2.12  MUC search           : 0.00
% 5.38/2.12  Cooper               : 0.00
% 5.38/2.12  Total                : 1.39
% 5.38/2.12  Index Insertion      : 0.00
% 5.38/2.12  Index Deletion       : 0.00
% 5.38/2.12  Index Matching       : 0.00
% 5.38/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
