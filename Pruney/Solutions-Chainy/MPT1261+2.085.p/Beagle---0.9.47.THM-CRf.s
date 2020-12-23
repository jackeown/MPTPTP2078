%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:23 EST 2020

% Result     : Theorem 4.51s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 134 expanded)
%              Number of leaves         :   36 (  62 expanded)
%              Depth                    :    7
%              Number of atoms          :  110 ( 264 expanded)
%              Number of equality atoms :   48 (  87 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_80,axiom,(
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

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_49,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3200,plain,(
    ! [A_220,B_221,C_222] :
      ( k7_subset_1(A_220,B_221,C_222) = k4_xboole_0(B_221,C_222)
      | ~ m1_subset_1(B_221,k1_zfmisc_1(A_220)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3206,plain,(
    ! [C_222] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_222) = k4_xboole_0('#skF_2',C_222) ),
    inference(resolution,[status(thm)],[c_34,c_3200])).

tff(c_46,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_125,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_40,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_294,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1189,plain,(
    ! [B_119,A_120] :
      ( v4_pre_topc(B_119,A_120)
      | k2_pre_topc(A_120,B_119) != B_119
      | ~ v2_pre_topc(A_120)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1202,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_1189])).

tff(c_1212,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_1202])).

tff(c_1213,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_294,c_1212])).

tff(c_1328,plain,(
    ! [A_125,B_126] :
      ( k4_subset_1(u1_struct_0(A_125),B_126,k2_tops_1(A_125,B_126)) = k2_pre_topc(A_125,B_126)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1337,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_1328])).

tff(c_1347,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1337])).

tff(c_559,plain,(
    ! [A_84,B_85,C_86] :
      ( k7_subset_1(A_84,B_85,C_86) = k4_xboole_0(B_85,C_86)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_614,plain,(
    ! [C_90] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_90) = k4_xboole_0('#skF_2',C_90) ),
    inference(resolution,[status(thm)],[c_34,c_559])).

tff(c_629,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_614])).

tff(c_14,plain,(
    ! [B_15,A_14] : k2_tarski(B_15,A_14) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_90,plain,(
    ! [A_44,B_45] : k3_tarski(k2_tarski(A_44,B_45)) = k2_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_163,plain,(
    ! [A_53,B_54] : k3_tarski(k2_tarski(A_53,B_54)) = k2_xboole_0(B_54,A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_90])).

tff(c_16,plain,(
    ! [A_16,B_17] : k3_tarski(k2_tarski(A_16,B_17)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_195,plain,(
    ! [B_57,A_58] : k2_xboole_0(B_57,A_58) = k2_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_16])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_120,plain,(
    ! [A_48,B_49] :
      ( k2_xboole_0(A_48,B_49) = B_49
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_124,plain,(
    ! [A_9,B_10] : k2_xboole_0(k4_xboole_0(A_9,B_10),A_9) = A_9 ),
    inference(resolution,[status(thm)],[c_10,c_120])).

tff(c_211,plain,(
    ! [B_57,B_10] : k2_xboole_0(B_57,k4_xboole_0(B_57,B_10)) = B_57 ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_124])).

tff(c_947,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_629,c_211])).

tff(c_18,plain,(
    ! [A_18,B_19,C_20] :
      ( m1_subset_1(k7_subset_1(A_18,B_19,C_20),k1_zfmisc_1(A_18))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1024,plain,(
    ! [A_110,B_111,C_112] :
      ( k4_subset_1(A_110,B_111,C_112) = k2_xboole_0(B_111,C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(A_110))
      | ~ m1_subset_1(B_111,k1_zfmisc_1(A_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2210,plain,(
    ! [A_160,B_161,B_162,C_163] :
      ( k4_subset_1(A_160,B_161,k7_subset_1(A_160,B_162,C_163)) = k2_xboole_0(B_161,k7_subset_1(A_160,B_162,C_163))
      | ~ m1_subset_1(B_161,k1_zfmisc_1(A_160))
      | ~ m1_subset_1(B_162,k1_zfmisc_1(A_160)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1024])).

tff(c_2571,plain,(
    ! [B_168,C_169] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k7_subset_1(u1_struct_0('#skF_1'),B_168,C_169)) = k2_xboole_0('#skF_2',k7_subset_1(u1_struct_0('#skF_1'),B_168,C_169))
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_34,c_2210])).

tff(c_2590,plain,
    ( k2_xboole_0('#skF_2',k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2'))) = k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_2571])).

tff(c_2600,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1347,c_947,c_125,c_2590])).

tff(c_2602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1213,c_2600])).

tff(c_2603,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_2772,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_2603])).

tff(c_2773,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2943,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2773,c_40])).

tff(c_3293,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3206,c_2943])).

tff(c_3484,plain,(
    ! [A_241,B_242] :
      ( k2_pre_topc(A_241,B_242) = B_242
      | ~ v4_pre_topc(B_242,A_241)
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(A_241)))
      | ~ l1_pre_topc(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3494,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_3484])).

tff(c_3501,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2773,c_3494])).

tff(c_4790,plain,(
    ! [A_290,B_291] :
      ( k7_subset_1(u1_struct_0(A_290),k2_pre_topc(A_290,B_291),k1_tops_1(A_290,B_291)) = k2_tops_1(A_290,B_291)
      | ~ m1_subset_1(B_291,k1_zfmisc_1(u1_struct_0(A_290)))
      | ~ l1_pre_topc(A_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4806,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3501,c_4790])).

tff(c_4812,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_3206,c_4806])).

tff(c_4814,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3293,c_4812])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:17:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.51/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.85  
% 4.51/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.85  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.51/1.85  
% 4.51/1.85  %Foreground sorts:
% 4.51/1.85  
% 4.51/1.85  
% 4.51/1.85  %Background operators:
% 4.51/1.85  
% 4.51/1.85  
% 4.51/1.85  %Foreground operators:
% 4.51/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.51/1.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.51/1.85  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.51/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.51/1.85  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.51/1.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.51/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.51/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.51/1.85  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.51/1.85  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.51/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.51/1.85  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.51/1.85  tff('#skF_1', type, '#skF_1': $i).
% 4.51/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.51/1.85  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.51/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.51/1.85  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.51/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.51/1.85  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.51/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.51/1.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.51/1.85  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.51/1.85  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.51/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.51/1.85  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.51/1.85  
% 4.51/1.86  tff(f_106, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 4.51/1.86  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.51/1.86  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.51/1.86  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 4.51/1.86  tff(f_47, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.51/1.86  tff(f_49, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.51/1.86  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.51/1.86  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.51/1.86  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 4.51/1.86  tff(f_59, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.51/1.86  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 4.51/1.86  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.51/1.86  tff(c_3200, plain, (![A_220, B_221, C_222]: (k7_subset_1(A_220, B_221, C_222)=k4_xboole_0(B_221, C_222) | ~m1_subset_1(B_221, k1_zfmisc_1(A_220)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.51/1.86  tff(c_3206, plain, (![C_222]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_222)=k4_xboole_0('#skF_2', C_222))), inference(resolution, [status(thm)], [c_34, c_3200])).
% 4.51/1.86  tff(c_46, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.51/1.86  tff(c_125, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_46])).
% 4.51/1.86  tff(c_40, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.51/1.86  tff(c_294, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_40])).
% 4.51/1.86  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.51/1.86  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.51/1.86  tff(c_1189, plain, (![B_119, A_120]: (v4_pre_topc(B_119, A_120) | k2_pre_topc(A_120, B_119)!=B_119 | ~v2_pre_topc(A_120) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.51/1.86  tff(c_1202, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_1189])).
% 4.51/1.86  tff(c_1212, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_1202])).
% 4.51/1.86  tff(c_1213, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_294, c_1212])).
% 4.51/1.86  tff(c_1328, plain, (![A_125, B_126]: (k4_subset_1(u1_struct_0(A_125), B_126, k2_tops_1(A_125, B_126))=k2_pre_topc(A_125, B_126) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.51/1.86  tff(c_1337, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_1328])).
% 4.51/1.86  tff(c_1347, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1337])).
% 4.51/1.86  tff(c_559, plain, (![A_84, B_85, C_86]: (k7_subset_1(A_84, B_85, C_86)=k4_xboole_0(B_85, C_86) | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.51/1.86  tff(c_614, plain, (![C_90]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_90)=k4_xboole_0('#skF_2', C_90))), inference(resolution, [status(thm)], [c_34, c_559])).
% 4.51/1.86  tff(c_629, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_125, c_614])).
% 4.51/1.86  tff(c_14, plain, (![B_15, A_14]: (k2_tarski(B_15, A_14)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.51/1.86  tff(c_90, plain, (![A_44, B_45]: (k3_tarski(k2_tarski(A_44, B_45))=k2_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.51/1.86  tff(c_163, plain, (![A_53, B_54]: (k3_tarski(k2_tarski(A_53, B_54))=k2_xboole_0(B_54, A_53))), inference(superposition, [status(thm), theory('equality')], [c_14, c_90])).
% 4.51/1.86  tff(c_16, plain, (![A_16, B_17]: (k3_tarski(k2_tarski(A_16, B_17))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.51/1.86  tff(c_195, plain, (![B_57, A_58]: (k2_xboole_0(B_57, A_58)=k2_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_163, c_16])).
% 4.51/1.86  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.51/1.86  tff(c_120, plain, (![A_48, B_49]: (k2_xboole_0(A_48, B_49)=B_49 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.51/1.86  tff(c_124, plain, (![A_9, B_10]: (k2_xboole_0(k4_xboole_0(A_9, B_10), A_9)=A_9)), inference(resolution, [status(thm)], [c_10, c_120])).
% 4.51/1.86  tff(c_211, plain, (![B_57, B_10]: (k2_xboole_0(B_57, k4_xboole_0(B_57, B_10))=B_57)), inference(superposition, [status(thm), theory('equality')], [c_195, c_124])).
% 4.51/1.86  tff(c_947, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_629, c_211])).
% 4.51/1.86  tff(c_18, plain, (![A_18, B_19, C_20]: (m1_subset_1(k7_subset_1(A_18, B_19, C_20), k1_zfmisc_1(A_18)) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.51/1.86  tff(c_1024, plain, (![A_110, B_111, C_112]: (k4_subset_1(A_110, B_111, C_112)=k2_xboole_0(B_111, C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(A_110)) | ~m1_subset_1(B_111, k1_zfmisc_1(A_110)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.51/1.86  tff(c_2210, plain, (![A_160, B_161, B_162, C_163]: (k4_subset_1(A_160, B_161, k7_subset_1(A_160, B_162, C_163))=k2_xboole_0(B_161, k7_subset_1(A_160, B_162, C_163)) | ~m1_subset_1(B_161, k1_zfmisc_1(A_160)) | ~m1_subset_1(B_162, k1_zfmisc_1(A_160)))), inference(resolution, [status(thm)], [c_18, c_1024])).
% 4.51/1.86  tff(c_2571, plain, (![B_168, C_169]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k7_subset_1(u1_struct_0('#skF_1'), B_168, C_169))=k2_xboole_0('#skF_2', k7_subset_1(u1_struct_0('#skF_1'), B_168, C_169)) | ~m1_subset_1(B_168, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_34, c_2210])).
% 4.51/1.86  tff(c_2590, plain, (k2_xboole_0('#skF_2', k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2')))=k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_125, c_2571])).
% 4.51/1.86  tff(c_2600, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1347, c_947, c_125, c_2590])).
% 4.51/1.86  tff(c_2602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1213, c_2600])).
% 4.51/1.86  tff(c_2603, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 4.51/1.86  tff(c_2772, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_2603])).
% 4.51/1.86  tff(c_2773, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 4.51/1.86  tff(c_2943, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2773, c_40])).
% 4.51/1.86  tff(c_3293, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3206, c_2943])).
% 4.51/1.86  tff(c_3484, plain, (![A_241, B_242]: (k2_pre_topc(A_241, B_242)=B_242 | ~v4_pre_topc(B_242, A_241) | ~m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0(A_241))) | ~l1_pre_topc(A_241))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.51/1.86  tff(c_3494, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_3484])).
% 4.51/1.86  tff(c_3501, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2773, c_3494])).
% 4.51/1.86  tff(c_4790, plain, (![A_290, B_291]: (k7_subset_1(u1_struct_0(A_290), k2_pre_topc(A_290, B_291), k1_tops_1(A_290, B_291))=k2_tops_1(A_290, B_291) | ~m1_subset_1(B_291, k1_zfmisc_1(u1_struct_0(A_290))) | ~l1_pre_topc(A_290))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.51/1.86  tff(c_4806, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3501, c_4790])).
% 4.51/1.86  tff(c_4812, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_3206, c_4806])).
% 4.51/1.86  tff(c_4814, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3293, c_4812])).
% 4.51/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.86  
% 4.51/1.86  Inference rules
% 4.51/1.86  ----------------------
% 4.51/1.86  #Ref     : 0
% 4.51/1.86  #Sup     : 1150
% 4.51/1.86  #Fact    : 0
% 4.51/1.86  #Define  : 0
% 4.51/1.86  #Split   : 2
% 4.51/1.86  #Chain   : 0
% 4.51/1.86  #Close   : 0
% 4.51/1.86  
% 4.51/1.86  Ordering : KBO
% 4.51/1.86  
% 4.51/1.86  Simplification rules
% 4.51/1.86  ----------------------
% 4.51/1.86  #Subsume      : 39
% 4.51/1.86  #Demod        : 899
% 4.51/1.86  #Tautology    : 839
% 4.51/1.86  #SimpNegUnit  : 3
% 4.51/1.86  #BackRed      : 3
% 4.51/1.86  
% 4.51/1.86  #Partial instantiations: 0
% 4.51/1.86  #Strategies tried      : 1
% 4.51/1.86  
% 4.51/1.86  Timing (in seconds)
% 4.51/1.86  ----------------------
% 4.51/1.87  Preprocessing        : 0.33
% 4.51/1.87  Parsing              : 0.18
% 4.51/1.87  CNF conversion       : 0.02
% 4.51/1.87  Main loop            : 0.78
% 4.51/1.87  Inferencing          : 0.26
% 4.51/1.87  Reduction            : 0.33
% 4.51/1.87  Demodulation         : 0.27
% 4.51/1.87  BG Simplification    : 0.03
% 4.51/1.87  Subsumption          : 0.11
% 4.51/1.87  Abstraction          : 0.04
% 4.51/1.87  MUC search           : 0.00
% 4.51/1.87  Cooper               : 0.00
% 4.51/1.87  Total                : 1.14
% 4.51/1.87  Index Insertion      : 0.00
% 4.51/1.87  Index Deletion       : 0.00
% 4.51/1.87  Index Matching       : 0.00
% 4.51/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
