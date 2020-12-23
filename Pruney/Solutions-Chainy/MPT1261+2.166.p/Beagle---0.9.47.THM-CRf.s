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
% DateTime   : Thu Dec  3 10:21:35 EST 2020

% Result     : Theorem 4.87s
% Output     : CNFRefutation 4.87s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 233 expanded)
%              Number of leaves         :   41 (  96 expanded)
%              Depth                    :   12
%              Number of atoms          :  151 ( 436 expanded)
%              Number of equality atoms :   62 ( 129 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_39,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_67,axiom,(
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

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2487,plain,(
    ! [A_194,B_195,C_196] :
      ( k7_subset_1(A_194,B_195,C_196) = k4_xboole_0(B_195,C_196)
      | ~ m1_subset_1(B_195,k1_zfmisc_1(A_194)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2502,plain,(
    ! [C_196] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_196) = k4_xboole_0('#skF_2',C_196) ),
    inference(resolution,[status(thm)],[c_38,c_2487])).

tff(c_44,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_81,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1082,plain,(
    ! [A_112,B_113] :
      ( k4_subset_1(u1_struct_0(A_112),B_113,k2_tops_1(A_112,B_113)) = k2_pre_topc(A_112,B_113)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1097,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1082])).

tff(c_1107,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1097])).

tff(c_357,plain,(
    ! [A_79,B_80,C_81] :
      ( k7_subset_1(A_79,B_80,C_81) = k4_xboole_0(B_80,C_81)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_373,plain,(
    ! [C_82] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_82) = k4_xboole_0('#skF_2',C_82) ),
    inference(resolution,[status(thm)],[c_38,c_357])).

tff(c_50,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_160,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_50])).

tff(c_379,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_160])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_18,B_19] : k6_subset_1(A_18,B_19) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_11,B_12] : m1_subset_1(k6_subset_1(A_11,B_12),k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_51,plain,(
    ! [A_11,B_12] : m1_subset_1(k4_xboole_0(A_11,B_12),k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_12])).

tff(c_142,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(A_65,B_66) = k3_subset_1(A_65,B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_151,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_subset_1(A_11,k4_xboole_0(A_11,B_12)) ),
    inference(resolution,[status(thm)],[c_51,c_142])).

tff(c_158,plain,(
    ! [A_11,B_12] : k3_subset_1(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_151])).

tff(c_221,plain,(
    ! [A_71,B_72] :
      ( k3_subset_1(A_71,k3_subset_1(A_71,B_72)) = B_72
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_229,plain,(
    ! [A_11,B_12] : k3_subset_1(A_11,k3_subset_1(A_11,k4_xboole_0(A_11,B_12))) = k4_xboole_0(A_11,B_12) ),
    inference(resolution,[status(thm)],[c_51,c_221])).

tff(c_236,plain,(
    ! [A_11,B_12] : k3_subset_1(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_229])).

tff(c_114,plain,(
    ! [A_59,B_60] : k4_xboole_0(A_59,k4_xboole_0(A_59,B_60)) = k3_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_126,plain,(
    ! [A_59,B_60] : m1_subset_1(k3_xboole_0(A_59,B_60),k1_zfmisc_1(A_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_51])).

tff(c_155,plain,(
    ! [A_59,B_60] : k4_xboole_0(A_59,k3_xboole_0(A_59,B_60)) = k3_subset_1(A_59,k3_xboole_0(A_59,B_60)) ),
    inference(resolution,[status(thm)],[c_126,c_142])).

tff(c_441,plain,(
    ! [A_59,B_60] : k4_xboole_0(A_59,k3_xboole_0(A_59,B_60)) = k4_xboole_0(A_59,B_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_155])).

tff(c_129,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,k4_xboole_0(A_5,B_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_114])).

tff(c_472,plain,(
    ! [A_88,B_89] : k3_xboole_0(A_88,k4_xboole_0(A_88,B_89)) = k4_xboole_0(A_88,B_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_129])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_520,plain,(
    ! [A_90,B_91] : k2_xboole_0(A_90,k4_xboole_0(A_90,B_91)) = A_90 ),
    inference(superposition,[status(thm),theory(equality)],[c_472,c_4])).

tff(c_532,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_520])).

tff(c_543,plain,(
    ! [A_92,B_93] :
      ( m1_subset_1(k2_tops_1(A_92,B_93),k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,B_26)
      | ~ m1_subset_1(A_25,k1_zfmisc_1(B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_557,plain,(
    ! [A_92,B_93] :
      ( r1_tarski(k2_tops_1(A_92,B_93),u1_struct_0(A_92))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_543,c_24])).

tff(c_26,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(A_25,k1_zfmisc_1(B_26))
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_944,plain,(
    ! [A_102,B_103,C_104] :
      ( k4_subset_1(A_102,B_103,C_104) = k2_xboole_0(B_103,C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(A_102))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1464,plain,(
    ! [B_130,B_131,A_132] :
      ( k4_subset_1(B_130,B_131,A_132) = k2_xboole_0(B_131,A_132)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(B_130))
      | ~ r1_tarski(A_132,B_130) ) ),
    inference(resolution,[status(thm)],[c_26,c_944])).

tff(c_1489,plain,(
    ! [A_133] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_133) = k2_xboole_0('#skF_2',A_133)
      | ~ r1_tarski(A_133,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_38,c_1464])).

tff(c_1493,plain,(
    ! [B_93] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_93)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_93))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_557,c_1489])).

tff(c_2184,plain,(
    ! [B_167] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_167)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_167))
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1493])).

tff(c_2206,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_2184])).

tff(c_2215,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1107,c_532,c_2206])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_676,plain,(
    ! [A_98,B_99] :
      ( v4_pre_topc(k2_pre_topc(A_98,B_99),A_98)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98)
      | ~ v2_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_691,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_676])).

tff(c_701,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_691])).

tff(c_2217,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2215,c_701])).

tff(c_2219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_2217])).

tff(c_2220,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2503,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2502,c_2220])).

tff(c_2221,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2854,plain,(
    ! [A_222,B_223] :
      ( r1_tarski(k2_tops_1(A_222,B_223),B_223)
      | ~ v4_pre_topc(B_223,A_222)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ l1_pre_topc(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2869,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_2854])).

tff(c_2879,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2221,c_2869])).

tff(c_2283,plain,(
    ! [A_182,B_183] :
      ( k4_xboole_0(A_182,B_183) = k3_subset_1(A_182,B_183)
      | ~ m1_subset_1(B_183,k1_zfmisc_1(A_182)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2297,plain,(
    ! [B_26,A_25] :
      ( k4_xboole_0(B_26,A_25) = k3_subset_1(B_26,A_25)
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(resolution,[status(thm)],[c_26,c_2283])).

tff(c_2886,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2879,c_2297])).

tff(c_3316,plain,(
    ! [A_236,B_237] :
      ( k7_subset_1(u1_struct_0(A_236),B_237,k2_tops_1(A_236,B_237)) = k1_tops_1(A_236,B_237)
      | ~ m1_subset_1(B_237,k1_zfmisc_1(u1_struct_0(A_236)))
      | ~ l1_pre_topc(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3331,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_3316])).

tff(c_3343,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2886,c_2502,c_3331])).

tff(c_2292,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_subset_1(A_11,k4_xboole_0(A_11,B_12)) ),
    inference(resolution,[status(thm)],[c_51,c_2283])).

tff(c_2299,plain,(
    ! [A_11,B_12] : k3_subset_1(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2292])).

tff(c_2902,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2886,c_2299])).

tff(c_2329,plain,(
    ! [A_186,B_187] :
      ( k3_subset_1(A_186,k3_subset_1(A_186,B_187)) = B_187
      | ~ m1_subset_1(B_187,k1_zfmisc_1(A_186)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2339,plain,(
    ! [B_26,A_25] :
      ( k3_subset_1(B_26,k3_subset_1(B_26,A_25)) = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(resolution,[status(thm)],[c_26,c_2329])).

tff(c_3055,plain,
    ( k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2902,c_2339])).

tff(c_3064,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2879,c_3055])).

tff(c_2905,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2886,c_6])).

tff(c_3104,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3064,c_2905])).

tff(c_3347,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3343,c_3104])).

tff(c_3354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2503,c_3347])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:24 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.87/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/2.00  
% 4.87/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/2.01  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 4.87/2.01  
% 4.87/2.01  %Foreground sorts:
% 4.87/2.01  
% 4.87/2.01  
% 4.87/2.01  %Background operators:
% 4.87/2.01  
% 4.87/2.01  
% 4.87/2.01  %Foreground operators:
% 4.87/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.87/2.01  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.87/2.01  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.87/2.01  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.87/2.01  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.87/2.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.87/2.01  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.87/2.01  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.87/2.01  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.87/2.01  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.87/2.01  tff('#skF_2', type, '#skF_2': $i).
% 4.87/2.01  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.87/2.01  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 4.87/2.01  tff('#skF_1', type, '#skF_1': $i).
% 4.87/2.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.87/2.01  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.87/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.87/2.01  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.87/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.87/2.01  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.87/2.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.87/2.01  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.87/2.01  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.87/2.01  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.87/2.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.87/2.01  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.87/2.01  
% 4.87/2.03  tff(f_110, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 4.87/2.03  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.87/2.03  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 4.87/2.03  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.87/2.03  tff(f_51, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 4.87/2.03  tff(f_39, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 4.87/2.03  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.87/2.03  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.87/2.03  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 4.87/2.03  tff(f_67, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 4.87/2.03  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.87/2.03  tff(f_49, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.87/2.03  tff(f_75, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 4.87/2.03  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 4.87/2.03  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 4.87/2.03  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.87/2.03  tff(c_2487, plain, (![A_194, B_195, C_196]: (k7_subset_1(A_194, B_195, C_196)=k4_xboole_0(B_195, C_196) | ~m1_subset_1(B_195, k1_zfmisc_1(A_194)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.87/2.03  tff(c_2502, plain, (![C_196]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_196)=k4_xboole_0('#skF_2', C_196))), inference(resolution, [status(thm)], [c_38, c_2487])).
% 4.87/2.03  tff(c_44, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.87/2.03  tff(c_81, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 4.87/2.03  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.87/2.03  tff(c_1082, plain, (![A_112, B_113]: (k4_subset_1(u1_struct_0(A_112), B_113, k2_tops_1(A_112, B_113))=k2_pre_topc(A_112, B_113) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.87/2.03  tff(c_1097, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1082])).
% 4.87/2.03  tff(c_1107, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1097])).
% 4.87/2.03  tff(c_357, plain, (![A_79, B_80, C_81]: (k7_subset_1(A_79, B_80, C_81)=k4_xboole_0(B_80, C_81) | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.87/2.03  tff(c_373, plain, (![C_82]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_82)=k4_xboole_0('#skF_2', C_82))), inference(resolution, [status(thm)], [c_38, c_357])).
% 4.87/2.03  tff(c_50, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.87/2.03  tff(c_160, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_81, c_50])).
% 4.87/2.03  tff(c_379, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_373, c_160])).
% 4.87/2.03  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.87/2.03  tff(c_18, plain, (![A_18, B_19]: (k6_subset_1(A_18, B_19)=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.87/2.03  tff(c_12, plain, (![A_11, B_12]: (m1_subset_1(k6_subset_1(A_11, B_12), k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.87/2.03  tff(c_51, plain, (![A_11, B_12]: (m1_subset_1(k4_xboole_0(A_11, B_12), k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_12])).
% 4.87/2.03  tff(c_142, plain, (![A_65, B_66]: (k4_xboole_0(A_65, B_66)=k3_subset_1(A_65, B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.87/2.03  tff(c_151, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_subset_1(A_11, k4_xboole_0(A_11, B_12)))), inference(resolution, [status(thm)], [c_51, c_142])).
% 4.87/2.03  tff(c_158, plain, (![A_11, B_12]: (k3_subset_1(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_151])).
% 4.87/2.03  tff(c_221, plain, (![A_71, B_72]: (k3_subset_1(A_71, k3_subset_1(A_71, B_72))=B_72 | ~m1_subset_1(B_72, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.87/2.03  tff(c_229, plain, (![A_11, B_12]: (k3_subset_1(A_11, k3_subset_1(A_11, k4_xboole_0(A_11, B_12)))=k4_xboole_0(A_11, B_12))), inference(resolution, [status(thm)], [c_51, c_221])).
% 4.87/2.03  tff(c_236, plain, (![A_11, B_12]: (k3_subset_1(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_229])).
% 4.87/2.03  tff(c_114, plain, (![A_59, B_60]: (k4_xboole_0(A_59, k4_xboole_0(A_59, B_60))=k3_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.87/2.03  tff(c_126, plain, (![A_59, B_60]: (m1_subset_1(k3_xboole_0(A_59, B_60), k1_zfmisc_1(A_59)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_51])).
% 4.87/2.03  tff(c_155, plain, (![A_59, B_60]: (k4_xboole_0(A_59, k3_xboole_0(A_59, B_60))=k3_subset_1(A_59, k3_xboole_0(A_59, B_60)))), inference(resolution, [status(thm)], [c_126, c_142])).
% 4.87/2.03  tff(c_441, plain, (![A_59, B_60]: (k4_xboole_0(A_59, k3_xboole_0(A_59, B_60))=k4_xboole_0(A_59, B_60))), inference(demodulation, [status(thm), theory('equality')], [c_236, c_155])).
% 4.87/2.03  tff(c_129, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k3_xboole_0(A_5, k4_xboole_0(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_114])).
% 4.87/2.03  tff(c_472, plain, (![A_88, B_89]: (k3_xboole_0(A_88, k4_xboole_0(A_88, B_89))=k4_xboole_0(A_88, B_89))), inference(demodulation, [status(thm), theory('equality')], [c_441, c_129])).
% 4.87/2.03  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.87/2.03  tff(c_520, plain, (![A_90, B_91]: (k2_xboole_0(A_90, k4_xboole_0(A_90, B_91))=A_90)), inference(superposition, [status(thm), theory('equality')], [c_472, c_4])).
% 4.87/2.03  tff(c_532, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_379, c_520])).
% 4.87/2.03  tff(c_543, plain, (![A_92, B_93]: (m1_subset_1(k2_tops_1(A_92, B_93), k1_zfmisc_1(u1_struct_0(A_92))) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.87/2.03  tff(c_24, plain, (![A_25, B_26]: (r1_tarski(A_25, B_26) | ~m1_subset_1(A_25, k1_zfmisc_1(B_26)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.87/2.03  tff(c_557, plain, (![A_92, B_93]: (r1_tarski(k2_tops_1(A_92, B_93), u1_struct_0(A_92)) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(resolution, [status(thm)], [c_543, c_24])).
% 4.87/2.03  tff(c_26, plain, (![A_25, B_26]: (m1_subset_1(A_25, k1_zfmisc_1(B_26)) | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.87/2.03  tff(c_944, plain, (![A_102, B_103, C_104]: (k4_subset_1(A_102, B_103, C_104)=k2_xboole_0(B_103, C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(A_102)) | ~m1_subset_1(B_103, k1_zfmisc_1(A_102)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.87/2.03  tff(c_1464, plain, (![B_130, B_131, A_132]: (k4_subset_1(B_130, B_131, A_132)=k2_xboole_0(B_131, A_132) | ~m1_subset_1(B_131, k1_zfmisc_1(B_130)) | ~r1_tarski(A_132, B_130))), inference(resolution, [status(thm)], [c_26, c_944])).
% 4.87/2.03  tff(c_1489, plain, (![A_133]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_133)=k2_xboole_0('#skF_2', A_133) | ~r1_tarski(A_133, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_38, c_1464])).
% 4.87/2.03  tff(c_1493, plain, (![B_93]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_93))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_93)) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_557, c_1489])).
% 4.87/2.03  tff(c_2184, plain, (![B_167]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_167))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_167)) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1493])).
% 4.87/2.03  tff(c_2206, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_2184])).
% 4.87/2.03  tff(c_2215, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1107, c_532, c_2206])).
% 4.87/2.03  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.87/2.03  tff(c_676, plain, (![A_98, B_99]: (v4_pre_topc(k2_pre_topc(A_98, B_99), A_98) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98) | ~v2_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.87/2.03  tff(c_691, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_676])).
% 4.87/2.03  tff(c_701, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_691])).
% 4.87/2.03  tff(c_2217, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2215, c_701])).
% 4.87/2.03  tff(c_2219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_2217])).
% 4.87/2.03  tff(c_2220, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 4.87/2.03  tff(c_2503, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2502, c_2220])).
% 4.87/2.03  tff(c_2221, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 4.87/2.03  tff(c_2854, plain, (![A_222, B_223]: (r1_tarski(k2_tops_1(A_222, B_223), B_223) | ~v4_pre_topc(B_223, A_222) | ~m1_subset_1(B_223, k1_zfmisc_1(u1_struct_0(A_222))) | ~l1_pre_topc(A_222))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.87/2.03  tff(c_2869, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_2854])).
% 4.87/2.03  tff(c_2879, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2221, c_2869])).
% 4.87/2.03  tff(c_2283, plain, (![A_182, B_183]: (k4_xboole_0(A_182, B_183)=k3_subset_1(A_182, B_183) | ~m1_subset_1(B_183, k1_zfmisc_1(A_182)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.87/2.03  tff(c_2297, plain, (![B_26, A_25]: (k4_xboole_0(B_26, A_25)=k3_subset_1(B_26, A_25) | ~r1_tarski(A_25, B_26))), inference(resolution, [status(thm)], [c_26, c_2283])).
% 4.87/2.03  tff(c_2886, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_2879, c_2297])).
% 4.87/2.03  tff(c_3316, plain, (![A_236, B_237]: (k7_subset_1(u1_struct_0(A_236), B_237, k2_tops_1(A_236, B_237))=k1_tops_1(A_236, B_237) | ~m1_subset_1(B_237, k1_zfmisc_1(u1_struct_0(A_236))) | ~l1_pre_topc(A_236))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.87/2.03  tff(c_3331, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_3316])).
% 4.87/2.03  tff(c_3343, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2886, c_2502, c_3331])).
% 4.87/2.03  tff(c_2292, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_subset_1(A_11, k4_xboole_0(A_11, B_12)))), inference(resolution, [status(thm)], [c_51, c_2283])).
% 4.87/2.03  tff(c_2299, plain, (![A_11, B_12]: (k3_subset_1(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2292])).
% 4.87/2.03  tff(c_2902, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2886, c_2299])).
% 4.87/2.03  tff(c_2329, plain, (![A_186, B_187]: (k3_subset_1(A_186, k3_subset_1(A_186, B_187))=B_187 | ~m1_subset_1(B_187, k1_zfmisc_1(A_186)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.87/2.03  tff(c_2339, plain, (![B_26, A_25]: (k3_subset_1(B_26, k3_subset_1(B_26, A_25))=A_25 | ~r1_tarski(A_25, B_26))), inference(resolution, [status(thm)], [c_26, c_2329])).
% 4.87/2.03  tff(c_3055, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2902, c_2339])).
% 4.87/2.03  tff(c_3064, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2879, c_3055])).
% 4.87/2.03  tff(c_2905, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2886, c_6])).
% 4.87/2.03  tff(c_3104, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3064, c_2905])).
% 4.87/2.03  tff(c_3347, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3343, c_3104])).
% 4.87/2.03  tff(c_3354, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2503, c_3347])).
% 4.87/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/2.03  
% 4.87/2.03  Inference rules
% 4.87/2.03  ----------------------
% 4.87/2.03  #Ref     : 0
% 4.87/2.03  #Sup     : 799
% 4.87/2.03  #Fact    : 0
% 4.87/2.03  #Define  : 0
% 4.87/2.03  #Split   : 1
% 4.87/2.03  #Chain   : 0
% 4.87/2.03  #Close   : 0
% 4.87/2.03  
% 4.87/2.03  Ordering : KBO
% 4.87/2.03  
% 4.87/2.03  Simplification rules
% 4.87/2.03  ----------------------
% 4.87/2.03  #Subsume      : 27
% 4.87/2.03  #Demod        : 638
% 4.87/2.03  #Tautology    : 520
% 4.87/2.03  #SimpNegUnit  : 3
% 4.87/2.03  #BackRed      : 24
% 4.87/2.03  
% 4.87/2.03  #Partial instantiations: 0
% 4.87/2.03  #Strategies tried      : 1
% 4.87/2.03  
% 4.87/2.03  Timing (in seconds)
% 4.87/2.03  ----------------------
% 4.87/2.03  Preprocessing        : 0.31
% 4.87/2.03  Parsing              : 0.17
% 4.87/2.03  CNF conversion       : 0.02
% 4.87/2.03  Main loop            : 0.88
% 4.87/2.03  Inferencing          : 0.32
% 4.87/2.03  Reduction            : 0.33
% 4.87/2.03  Demodulation         : 0.25
% 4.87/2.03  BG Simplification    : 0.04
% 4.87/2.03  Subsumption          : 0.12
% 4.87/2.03  Abstraction          : 0.07
% 4.87/2.03  MUC search           : 0.00
% 4.87/2.03  Cooper               : 0.00
% 4.87/2.03  Total                : 1.24
% 4.87/2.03  Index Insertion      : 0.00
% 4.87/2.03  Index Deletion       : 0.00
% 4.87/2.03  Index Matching       : 0.00
% 4.87/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
