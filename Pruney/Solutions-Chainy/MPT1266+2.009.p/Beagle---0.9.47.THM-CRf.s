%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:44 EST 2020

% Result     : Theorem 9.04s
% Output     : CNFRefutation 9.04s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 822 expanded)
%              Number of leaves         :   44 ( 294 expanded)
%              Depth                    :   14
%              Number of atoms          :  245 (1718 expanded)
%              Number of equality atoms :   68 ( 462 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_57,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(c_58,plain,
    ( k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_94,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_42,plain,(
    ! [A_47] :
      ( l1_struct_0(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_79,plain,(
    ! [A_62] :
      ( u1_struct_0(A_62) = k2_struct_0(A_62)
      | ~ l1_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_84,plain,(
    ! [A_63] :
      ( u1_struct_0(A_63) = k2_struct_0(A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_42,c_79])).

tff(c_88,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_84])).

tff(c_54,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_89,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_54])).

tff(c_32,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(k3_subset_1(A_38,B_39),k1_zfmisc_1(A_38))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_424,plain,(
    ! [A_111,B_112] :
      ( k2_pre_topc(A_111,B_112) = k2_struct_0(A_111)
      | ~ v1_tops_1(B_112,A_111)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_438,plain,(
    ! [B_112] :
      ( k2_pre_topc('#skF_1',B_112) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_112,'#skF_1')
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_424])).

tff(c_487,plain,(
    ! [B_118] :
      ( k2_pre_topc('#skF_1',B_118) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_118,'#skF_1')
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_438])).

tff(c_509,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_89,c_487])).

tff(c_518,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_509])).

tff(c_230,plain,(
    ! [A_89,B_90] :
      ( k3_subset_1(A_89,k3_subset_1(A_89,B_90)) = B_90
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_241,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_89,c_230])).

tff(c_600,plain,(
    ! [A_130,B_131] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_130),B_131),A_130)
      | ~ v2_tops_1(B_131,A_130)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_618,plain,(
    ! [B_131] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_131),'#skF_1')
      | ~ v2_tops_1(B_131,'#skF_1')
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_600])).

tff(c_749,plain,(
    ! [B_146] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_146),'#skF_1')
      | ~ v2_tops_1(B_146,'#skF_1')
      | ~ m1_subset_1(B_146,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_88,c_618])).

tff(c_763,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_749])).

tff(c_772,plain,
    ( ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_518,c_763])).

tff(c_776,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_772])).

tff(c_779,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_32,c_776])).

tff(c_783,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_779])).

tff(c_785,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_772])).

tff(c_450,plain,(
    ! [B_114,A_115] :
      ( v1_tops_1(B_114,A_115)
      | k2_pre_topc(A_115,B_114) != k2_struct_0(A_115)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_464,plain,(
    ! [B_114] :
      ( v1_tops_1(B_114,'#skF_1')
      | k2_pre_topc('#skF_1',B_114) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_114,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_450])).

tff(c_473,plain,(
    ! [B_114] :
      ( v1_tops_1(B_114,'#skF_1')
      | k2_pre_topc('#skF_1',B_114) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_114,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_464])).

tff(c_800,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_785,c_473])).

tff(c_808,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_800])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_114,plain,(
    ! [A_70,B_71] :
      ( k4_xboole_0(A_70,B_71) = k1_xboole_0
      | ~ r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_122,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_114])).

tff(c_26,plain,(
    ! [A_34] : k2_subset_1(A_34) = A_34 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    ! [A_37] : m1_subset_1(k2_subset_1(A_37),k1_zfmisc_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_65,plain,(
    ! [A_37] : m1_subset_1(A_37,k1_zfmisc_1(A_37)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30])).

tff(c_175,plain,(
    ! [A_82,B_83] :
      ( k4_xboole_0(A_82,B_83) = k3_subset_1(A_82,B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_181,plain,(
    ! [A_37] : k4_xboole_0(A_37,A_37) = k3_subset_1(A_37,A_37) ),
    inference(resolution,[status(thm)],[c_65,c_175])).

tff(c_184,plain,(
    ! [A_37] : k3_subset_1(A_37,A_37) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_181])).

tff(c_238,plain,(
    ! [A_37] : k3_subset_1(A_37,k3_subset_1(A_37,A_37)) = A_37 ),
    inference(resolution,[status(thm)],[c_65,c_230])).

tff(c_243,plain,(
    ! [A_37] : k3_subset_1(A_37,k1_xboole_0) = A_37 ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_238])).

tff(c_64,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_130,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_64])).

tff(c_44,plain,(
    ! [A_48,B_50] :
      ( k3_subset_1(u1_struct_0(A_48),k2_pre_topc(A_48,k3_subset_1(u1_struct_0(A_48),B_50))) = k1_tops_1(A_48,B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_327,plain,(
    ! [A_104,B_105] :
      ( m1_subset_1(k2_pre_topc(A_104,B_105),k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_34,plain,(
    ! [A_40,B_41] :
      ( k3_subset_1(A_40,k3_subset_1(A_40,B_41)) = B_41
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1275,plain,(
    ! [A_157,B_158] :
      ( k3_subset_1(u1_struct_0(A_157),k3_subset_1(u1_struct_0(A_157),k2_pre_topc(A_157,B_158))) = k2_pre_topc(A_157,B_158)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ l1_pre_topc(A_157) ) ),
    inference(resolution,[status(thm)],[c_327,c_34])).

tff(c_7655,plain,(
    ! [A_316,B_317] :
      ( k3_subset_1(u1_struct_0(A_316),k1_tops_1(A_316,B_317)) = k2_pre_topc(A_316,k3_subset_1(u1_struct_0(A_316),B_317))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_316),B_317),k1_zfmisc_1(u1_struct_0(A_316)))
      | ~ l1_pre_topc(A_316)
      | ~ m1_subset_1(B_317,k1_zfmisc_1(u1_struct_0(A_316)))
      | ~ l1_pre_topc(A_316) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1275])).

tff(c_7744,plain,(
    ! [A_318,B_319] :
      ( k3_subset_1(u1_struct_0(A_318),k1_tops_1(A_318,B_319)) = k2_pre_topc(A_318,k3_subset_1(u1_struct_0(A_318),B_319))
      | ~ l1_pre_topc(A_318)
      | ~ m1_subset_1(B_319,k1_zfmisc_1(u1_struct_0(A_318))) ) ),
    inference(resolution,[status(thm)],[c_32,c_7655])).

tff(c_7766,plain,(
    ! [B_319] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1',B_319)) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_319))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_319,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_7744])).

tff(c_7784,plain,(
    ! [B_320] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k1_tops_1('#skF_1',B_320)) = k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_320))
      | ~ m1_subset_1(B_320,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_88,c_88,c_7766])).

tff(c_7825,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_89,c_7784])).

tff(c_7852,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_130,c_7825])).

tff(c_7854,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_808,c_7852])).

tff(c_7855,plain,(
    v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_800])).

tff(c_568,plain,(
    ! [B_127,A_128] :
      ( v2_tops_1(B_127,A_128)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_128),B_127),A_128)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_583,plain,(
    ! [B_127] :
      ( v2_tops_1(B_127,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_127),'#skF_1')
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_568])).

tff(c_589,plain,(
    ! [B_127] :
      ( v2_tops_1(B_127,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_127),'#skF_1')
      | ~ m1_subset_1(B_127,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_88,c_583])).

tff(c_7859,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_7855,c_589])).

tff(c_7862,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_7859])).

tff(c_7864,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_7862])).

tff(c_7865,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_7890,plain,(
    ! [A_325,B_326] :
      ( k4_xboole_0(A_325,B_326) = k1_xboole_0
      | ~ r1_tarski(A_325,B_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7894,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_7890])).

tff(c_7979,plain,(
    ! [A_344,B_345] :
      ( k4_xboole_0(A_344,B_345) = k3_subset_1(A_344,B_345)
      | ~ m1_subset_1(B_345,k1_zfmisc_1(A_344)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_7988,plain,(
    ! [A_37] : k4_xboole_0(A_37,A_37) = k3_subset_1(A_37,A_37) ),
    inference(resolution,[status(thm)],[c_65,c_7979])).

tff(c_7992,plain,(
    ! [A_37] : k3_subset_1(A_37,A_37) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7894,c_7988])).

tff(c_7866,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_8397,plain,(
    ! [A_390,B_391] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_390),B_391),A_390)
      | ~ v2_tops_1(B_391,A_390)
      | ~ m1_subset_1(B_391,k1_zfmisc_1(u1_struct_0(A_390)))
      | ~ l1_pre_topc(A_390) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_8415,plain,(
    ! [B_391] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_391),'#skF_1')
      | ~ v2_tops_1(B_391,'#skF_1')
      | ~ m1_subset_1(B_391,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_8397])).

tff(c_8422,plain,(
    ! [B_391] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_391),'#skF_1')
      | ~ v2_tops_1(B_391,'#skF_1')
      | ~ m1_subset_1(B_391,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_88,c_8415])).

tff(c_8135,plain,(
    ! [A_366,B_367] :
      ( k2_pre_topc(A_366,B_367) = k2_struct_0(A_366)
      | ~ v1_tops_1(B_367,A_366)
      | ~ m1_subset_1(B_367,k1_zfmisc_1(u1_struct_0(A_366)))
      | ~ l1_pre_topc(A_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_8149,plain,(
    ! [B_367] :
      ( k2_pre_topc('#skF_1',B_367) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_367,'#skF_1')
      | ~ m1_subset_1(B_367,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_8135])).

tff(c_8174,plain,(
    ! [B_370] :
      ( k2_pre_topc('#skF_1',B_370) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_370,'#skF_1')
      | ~ m1_subset_1(B_370,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_8149])).

tff(c_8196,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_89,c_8174])).

tff(c_8199,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_8196])).

tff(c_7948,plain,(
    ! [A_341,B_342] :
      ( k3_subset_1(A_341,k3_subset_1(A_341,B_342)) = B_342
      | ~ m1_subset_1(B_342,k1_zfmisc_1(A_341)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_7956,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_89,c_7948])).

tff(c_8512,plain,(
    ! [B_403] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_403),'#skF_1')
      | ~ v2_tops_1(B_403,'#skF_1')
      | ~ m1_subset_1(B_403,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_88,c_8415])).

tff(c_8530,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_7956,c_8512])).

tff(c_8538,plain,
    ( ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_8199,c_8530])).

tff(c_8539,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_8538])).

tff(c_8542,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_32,c_8539])).

tff(c_8546,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_8542])).

tff(c_8548,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_8538])).

tff(c_8200,plain,(
    ! [B_371,A_372] :
      ( v1_tops_1(B_371,A_372)
      | k2_pre_topc(A_372,B_371) != k2_struct_0(A_372)
      | ~ m1_subset_1(B_371,k1_zfmisc_1(u1_struct_0(A_372)))
      | ~ l1_pre_topc(A_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_8214,plain,(
    ! [B_371] :
      ( v1_tops_1(B_371,'#skF_1')
      | k2_pre_topc('#skF_1',B_371) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_371,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_8200])).

tff(c_8223,plain,(
    ! [B_371] :
      ( v1_tops_1(B_371,'#skF_1')
      | k2_pre_topc('#skF_1',B_371) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_371,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_8214])).

tff(c_8562,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8548,c_8223])).

tff(c_8570,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_8562])).

tff(c_8158,plain,(
    ! [B_367] :
      ( k2_pre_topc('#skF_1',B_367) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_367,'#skF_1')
      | ~ m1_subset_1(B_367,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_8149])).

tff(c_8563,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_8548,c_8158])).

tff(c_8799,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_8570,c_8563])).

tff(c_8802,plain,
    ( ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8422,c_8799])).

tff(c_8806,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_7866,c_8802])).

tff(c_8808,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_8562])).

tff(c_8815,plain,(
    ! [A_409,B_410] :
      ( k3_subset_1(u1_struct_0(A_409),k2_pre_topc(A_409,k3_subset_1(u1_struct_0(A_409),B_410))) = k1_tops_1(A_409,B_410)
      | ~ m1_subset_1(B_410,k1_zfmisc_1(u1_struct_0(A_409)))
      | ~ l1_pre_topc(A_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_8857,plain,(
    ! [B_410] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_410))) = k1_tops_1('#skF_1',B_410)
      | ~ m1_subset_1(B_410,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_8815])).

tff(c_9064,plain,(
    ! [B_415] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_415))) = k1_tops_1('#skF_1',B_415)
      | ~ m1_subset_1(B_415,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_88,c_88,c_8857])).

tff(c_9097,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8808,c_9064])).

tff(c_9118,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_7992,c_9097])).

tff(c_9120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7865,c_9118])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.04/3.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.04/3.33  
% 9.04/3.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.04/3.33  %$ v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 9.04/3.33  
% 9.04/3.33  %Foreground sorts:
% 9.04/3.33  
% 9.04/3.33  
% 9.04/3.33  %Background operators:
% 9.04/3.33  
% 9.04/3.33  
% 9.04/3.33  %Foreground operators:
% 9.04/3.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.04/3.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.04/3.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.04/3.33  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 9.04/3.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.04/3.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.04/3.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.04/3.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.04/3.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.04/3.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.04/3.33  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 9.04/3.33  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 9.04/3.33  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 9.04/3.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.04/3.33  tff('#skF_2', type, '#skF_2': $i).
% 9.04/3.33  tff('#skF_1', type, '#skF_1': $i).
% 9.04/3.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.04/3.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.04/3.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 9.04/3.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.04/3.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.04/3.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.04/3.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.04/3.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.04/3.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.04/3.33  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 9.04/3.33  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 9.04/3.33  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 9.04/3.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.04/3.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.04/3.33  
% 9.04/3.35  tff(f_116, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 9.04/3.35  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 9.04/3.35  tff(f_71, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 9.04/3.35  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 9.04/3.35  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 9.04/3.35  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 9.04/3.35  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 9.04/3.35  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.04/3.35  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 9.04/3.35  tff(f_51, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 9.04/3.35  tff(f_57, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 9.04/3.35  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 9.04/3.35  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 9.04/3.35  tff(f_77, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 9.04/3.35  tff(c_58, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.04/3.35  tff(c_94, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_58])).
% 9.04/3.35  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.04/3.35  tff(c_42, plain, (![A_47]: (l1_struct_0(A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.04/3.35  tff(c_79, plain, (![A_62]: (u1_struct_0(A_62)=k2_struct_0(A_62) | ~l1_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.04/3.35  tff(c_84, plain, (![A_63]: (u1_struct_0(A_63)=k2_struct_0(A_63) | ~l1_pre_topc(A_63))), inference(resolution, [status(thm)], [c_42, c_79])).
% 9.04/3.35  tff(c_88, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_84])).
% 9.04/3.35  tff(c_54, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.04/3.35  tff(c_89, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_54])).
% 9.04/3.35  tff(c_32, plain, (![A_38, B_39]: (m1_subset_1(k3_subset_1(A_38, B_39), k1_zfmisc_1(A_38)) | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.04/3.35  tff(c_424, plain, (![A_111, B_112]: (k2_pre_topc(A_111, B_112)=k2_struct_0(A_111) | ~v1_tops_1(B_112, A_111) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.04/3.35  tff(c_438, plain, (![B_112]: (k2_pre_topc('#skF_1', B_112)=k2_struct_0('#skF_1') | ~v1_tops_1(B_112, '#skF_1') | ~m1_subset_1(B_112, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_424])).
% 9.04/3.35  tff(c_487, plain, (![B_118]: (k2_pre_topc('#skF_1', B_118)=k2_struct_0('#skF_1') | ~v1_tops_1(B_118, '#skF_1') | ~m1_subset_1(B_118, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_438])).
% 9.04/3.35  tff(c_509, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_89, c_487])).
% 9.04/3.35  tff(c_518, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_509])).
% 9.04/3.35  tff(c_230, plain, (![A_89, B_90]: (k3_subset_1(A_89, k3_subset_1(A_89, B_90))=B_90 | ~m1_subset_1(B_90, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.04/3.35  tff(c_241, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_89, c_230])).
% 9.04/3.35  tff(c_600, plain, (![A_130, B_131]: (v1_tops_1(k3_subset_1(u1_struct_0(A_130), B_131), A_130) | ~v2_tops_1(B_131, A_130) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.04/3.35  tff(c_618, plain, (![B_131]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_131), '#skF_1') | ~v2_tops_1(B_131, '#skF_1') | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_600])).
% 9.04/3.35  tff(c_749, plain, (![B_146]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_146), '#skF_1') | ~v2_tops_1(B_146, '#skF_1') | ~m1_subset_1(B_146, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_88, c_618])).
% 9.04/3.35  tff(c_763, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_241, c_749])).
% 9.04/3.35  tff(c_772, plain, (~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_518, c_763])).
% 9.04/3.35  tff(c_776, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_772])).
% 9.04/3.35  tff(c_779, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_32, c_776])).
% 9.04/3.35  tff(c_783, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_779])).
% 9.04/3.35  tff(c_785, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_772])).
% 9.04/3.35  tff(c_450, plain, (![B_114, A_115]: (v1_tops_1(B_114, A_115) | k2_pre_topc(A_115, B_114)!=k2_struct_0(A_115) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.04/3.35  tff(c_464, plain, (![B_114]: (v1_tops_1(B_114, '#skF_1') | k2_pre_topc('#skF_1', B_114)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_114, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_450])).
% 9.04/3.35  tff(c_473, plain, (![B_114]: (v1_tops_1(B_114, '#skF_1') | k2_pre_topc('#skF_1', B_114)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_114, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_464])).
% 9.04/3.35  tff(c_800, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_785, c_473])).
% 9.04/3.35  tff(c_808, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_800])).
% 9.04/3.35  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.04/3.35  tff(c_114, plain, (![A_70, B_71]: (k4_xboole_0(A_70, B_71)=k1_xboole_0 | ~r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.04/3.35  tff(c_122, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_114])).
% 9.04/3.35  tff(c_26, plain, (![A_34]: (k2_subset_1(A_34)=A_34)), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.04/3.35  tff(c_30, plain, (![A_37]: (m1_subset_1(k2_subset_1(A_37), k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.04/3.35  tff(c_65, plain, (![A_37]: (m1_subset_1(A_37, k1_zfmisc_1(A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_30])).
% 9.04/3.35  tff(c_175, plain, (![A_82, B_83]: (k4_xboole_0(A_82, B_83)=k3_subset_1(A_82, B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(A_82)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.04/3.35  tff(c_181, plain, (![A_37]: (k4_xboole_0(A_37, A_37)=k3_subset_1(A_37, A_37))), inference(resolution, [status(thm)], [c_65, c_175])).
% 9.04/3.35  tff(c_184, plain, (![A_37]: (k3_subset_1(A_37, A_37)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_181])).
% 9.04/3.35  tff(c_238, plain, (![A_37]: (k3_subset_1(A_37, k3_subset_1(A_37, A_37))=A_37)), inference(resolution, [status(thm)], [c_65, c_230])).
% 9.04/3.35  tff(c_243, plain, (![A_37]: (k3_subset_1(A_37, k1_xboole_0)=A_37)), inference(demodulation, [status(thm), theory('equality')], [c_184, c_238])).
% 9.04/3.35  tff(c_64, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.04/3.35  tff(c_130, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_94, c_64])).
% 9.04/3.35  tff(c_44, plain, (![A_48, B_50]: (k3_subset_1(u1_struct_0(A_48), k2_pre_topc(A_48, k3_subset_1(u1_struct_0(A_48), B_50)))=k1_tops_1(A_48, B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.04/3.35  tff(c_327, plain, (![A_104, B_105]: (m1_subset_1(k2_pre_topc(A_104, B_105), k1_zfmisc_1(u1_struct_0(A_104))) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.04/3.35  tff(c_34, plain, (![A_40, B_41]: (k3_subset_1(A_40, k3_subset_1(A_40, B_41))=B_41 | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.04/3.35  tff(c_1275, plain, (![A_157, B_158]: (k3_subset_1(u1_struct_0(A_157), k3_subset_1(u1_struct_0(A_157), k2_pre_topc(A_157, B_158)))=k2_pre_topc(A_157, B_158) | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0(A_157))) | ~l1_pre_topc(A_157))), inference(resolution, [status(thm)], [c_327, c_34])).
% 9.04/3.35  tff(c_7655, plain, (![A_316, B_317]: (k3_subset_1(u1_struct_0(A_316), k1_tops_1(A_316, B_317))=k2_pre_topc(A_316, k3_subset_1(u1_struct_0(A_316), B_317)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_316), B_317), k1_zfmisc_1(u1_struct_0(A_316))) | ~l1_pre_topc(A_316) | ~m1_subset_1(B_317, k1_zfmisc_1(u1_struct_0(A_316))) | ~l1_pre_topc(A_316))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1275])).
% 9.04/3.35  tff(c_7744, plain, (![A_318, B_319]: (k3_subset_1(u1_struct_0(A_318), k1_tops_1(A_318, B_319))=k2_pre_topc(A_318, k3_subset_1(u1_struct_0(A_318), B_319)) | ~l1_pre_topc(A_318) | ~m1_subset_1(B_319, k1_zfmisc_1(u1_struct_0(A_318))))), inference(resolution, [status(thm)], [c_32, c_7655])).
% 9.04/3.35  tff(c_7766, plain, (![B_319]: (k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', B_319))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_319)) | ~l1_pre_topc('#skF_1') | ~m1_subset_1(B_319, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_88, c_7744])).
% 9.04/3.35  tff(c_7784, plain, (![B_320]: (k3_subset_1(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', B_320))=k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_320)) | ~m1_subset_1(B_320, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_88, c_88, c_7766])).
% 9.04/3.35  tff(c_7825, plain, (k3_subset_1(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_89, c_7784])).
% 9.04/3.35  tff(c_7852, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_130, c_7825])).
% 9.04/3.35  tff(c_7854, plain, $false, inference(negUnitSimplification, [status(thm)], [c_808, c_7852])).
% 9.04/3.35  tff(c_7855, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_800])).
% 9.04/3.35  tff(c_568, plain, (![B_127, A_128]: (v2_tops_1(B_127, A_128) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_128), B_127), A_128) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.04/3.35  tff(c_583, plain, (![B_127]: (v2_tops_1(B_127, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_127), '#skF_1') | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_568])).
% 9.04/3.35  tff(c_589, plain, (![B_127]: (v2_tops_1(B_127, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_127), '#skF_1') | ~m1_subset_1(B_127, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_88, c_583])).
% 9.04/3.35  tff(c_7859, plain, (v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_7855, c_589])).
% 9.04/3.35  tff(c_7862, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_7859])).
% 9.04/3.35  tff(c_7864, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_7862])).
% 9.04/3.35  tff(c_7865, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 9.04/3.35  tff(c_7890, plain, (![A_325, B_326]: (k4_xboole_0(A_325, B_326)=k1_xboole_0 | ~r1_tarski(A_325, B_326))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.04/3.35  tff(c_7894, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_7890])).
% 9.04/3.35  tff(c_7979, plain, (![A_344, B_345]: (k4_xboole_0(A_344, B_345)=k3_subset_1(A_344, B_345) | ~m1_subset_1(B_345, k1_zfmisc_1(A_344)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.04/3.35  tff(c_7988, plain, (![A_37]: (k4_xboole_0(A_37, A_37)=k3_subset_1(A_37, A_37))), inference(resolution, [status(thm)], [c_65, c_7979])).
% 9.04/3.35  tff(c_7992, plain, (![A_37]: (k3_subset_1(A_37, A_37)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7894, c_7988])).
% 9.04/3.35  tff(c_7866, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 9.04/3.35  tff(c_8397, plain, (![A_390, B_391]: (v1_tops_1(k3_subset_1(u1_struct_0(A_390), B_391), A_390) | ~v2_tops_1(B_391, A_390) | ~m1_subset_1(B_391, k1_zfmisc_1(u1_struct_0(A_390))) | ~l1_pre_topc(A_390))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.04/3.35  tff(c_8415, plain, (![B_391]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_391), '#skF_1') | ~v2_tops_1(B_391, '#skF_1') | ~m1_subset_1(B_391, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_8397])).
% 9.04/3.35  tff(c_8422, plain, (![B_391]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_391), '#skF_1') | ~v2_tops_1(B_391, '#skF_1') | ~m1_subset_1(B_391, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_88, c_8415])).
% 9.04/3.35  tff(c_8135, plain, (![A_366, B_367]: (k2_pre_topc(A_366, B_367)=k2_struct_0(A_366) | ~v1_tops_1(B_367, A_366) | ~m1_subset_1(B_367, k1_zfmisc_1(u1_struct_0(A_366))) | ~l1_pre_topc(A_366))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.04/3.35  tff(c_8149, plain, (![B_367]: (k2_pre_topc('#skF_1', B_367)=k2_struct_0('#skF_1') | ~v1_tops_1(B_367, '#skF_1') | ~m1_subset_1(B_367, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_8135])).
% 9.04/3.35  tff(c_8174, plain, (![B_370]: (k2_pre_topc('#skF_1', B_370)=k2_struct_0('#skF_1') | ~v1_tops_1(B_370, '#skF_1') | ~m1_subset_1(B_370, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_8149])).
% 9.04/3.35  tff(c_8196, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_89, c_8174])).
% 9.04/3.35  tff(c_8199, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_8196])).
% 9.04/3.35  tff(c_7948, plain, (![A_341, B_342]: (k3_subset_1(A_341, k3_subset_1(A_341, B_342))=B_342 | ~m1_subset_1(B_342, k1_zfmisc_1(A_341)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.04/3.35  tff(c_7956, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_89, c_7948])).
% 9.04/3.35  tff(c_8512, plain, (![B_403]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_403), '#skF_1') | ~v2_tops_1(B_403, '#skF_1') | ~m1_subset_1(B_403, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_88, c_8415])).
% 9.04/3.35  tff(c_8530, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_7956, c_8512])).
% 9.04/3.35  tff(c_8538, plain, (~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_8199, c_8530])).
% 9.04/3.35  tff(c_8539, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_8538])).
% 9.04/3.35  tff(c_8542, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_32, c_8539])).
% 9.04/3.35  tff(c_8546, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_8542])).
% 9.04/3.35  tff(c_8548, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_8538])).
% 9.04/3.35  tff(c_8200, plain, (![B_371, A_372]: (v1_tops_1(B_371, A_372) | k2_pre_topc(A_372, B_371)!=k2_struct_0(A_372) | ~m1_subset_1(B_371, k1_zfmisc_1(u1_struct_0(A_372))) | ~l1_pre_topc(A_372))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.04/3.35  tff(c_8214, plain, (![B_371]: (v1_tops_1(B_371, '#skF_1') | k2_pre_topc('#skF_1', B_371)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_371, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_8200])).
% 9.04/3.35  tff(c_8223, plain, (![B_371]: (v1_tops_1(B_371, '#skF_1') | k2_pre_topc('#skF_1', B_371)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_371, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_8214])).
% 9.04/3.35  tff(c_8562, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_8548, c_8223])).
% 9.04/3.35  tff(c_8570, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_8562])).
% 9.04/3.35  tff(c_8158, plain, (![B_367]: (k2_pre_topc('#skF_1', B_367)=k2_struct_0('#skF_1') | ~v1_tops_1(B_367, '#skF_1') | ~m1_subset_1(B_367, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_8149])).
% 9.04/3.35  tff(c_8563, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_8548, c_8158])).
% 9.04/3.35  tff(c_8799, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_8570, c_8563])).
% 9.04/3.35  tff(c_8802, plain, (~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8422, c_8799])).
% 9.04/3.35  tff(c_8806, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_7866, c_8802])).
% 9.04/3.35  tff(c_8808, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_8562])).
% 9.04/3.35  tff(c_8815, plain, (![A_409, B_410]: (k3_subset_1(u1_struct_0(A_409), k2_pre_topc(A_409, k3_subset_1(u1_struct_0(A_409), B_410)))=k1_tops_1(A_409, B_410) | ~m1_subset_1(B_410, k1_zfmisc_1(u1_struct_0(A_409))) | ~l1_pre_topc(A_409))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.04/3.35  tff(c_8857, plain, (![B_410]: (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_410)))=k1_tops_1('#skF_1', B_410) | ~m1_subset_1(B_410, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_8815])).
% 9.04/3.35  tff(c_9064, plain, (![B_415]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_415)))=k1_tops_1('#skF_1', B_415) | ~m1_subset_1(B_415, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_88, c_88, c_8857])).
% 9.04/3.35  tff(c_9097, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_8808, c_9064])).
% 9.04/3.35  tff(c_9118, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_89, c_7992, c_9097])).
% 9.04/3.35  tff(c_9120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7865, c_9118])).
% 9.04/3.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.04/3.35  
% 9.04/3.35  Inference rules
% 9.04/3.35  ----------------------
% 9.04/3.35  #Ref     : 0
% 9.04/3.35  #Sup     : 2209
% 9.04/3.35  #Fact    : 0
% 9.04/3.35  #Define  : 0
% 9.04/3.35  #Split   : 50
% 9.04/3.35  #Chain   : 0
% 9.04/3.35  #Close   : 0
% 9.04/3.35  
% 9.04/3.35  Ordering : KBO
% 9.04/3.35  
% 9.04/3.35  Simplification rules
% 9.04/3.35  ----------------------
% 9.04/3.35  #Subsume      : 339
% 9.04/3.35  #Demod        : 1694
% 9.04/3.35  #Tautology    : 560
% 9.04/3.35  #SimpNegUnit  : 213
% 9.04/3.35  #BackRed      : 4
% 9.04/3.35  
% 9.04/3.35  #Partial instantiations: 0
% 9.04/3.35  #Strategies tried      : 1
% 9.04/3.35  
% 9.04/3.35  Timing (in seconds)
% 9.04/3.35  ----------------------
% 9.04/3.35  Preprocessing        : 0.35
% 9.04/3.35  Parsing              : 0.19
% 9.04/3.35  CNF conversion       : 0.02
% 9.04/3.35  Main loop            : 2.18
% 9.04/3.35  Inferencing          : 0.65
% 9.04/3.35  Reduction            : 0.82
% 9.04/3.35  Demodulation         : 0.57
% 9.04/3.35  BG Simplification    : 0.08
% 9.04/3.36  Subsumption          : 0.49
% 9.04/3.36  Abstraction          : 0.09
% 9.04/3.36  MUC search           : 0.00
% 9.04/3.36  Cooper               : 0.00
% 9.04/3.36  Total                : 2.57
% 9.04/3.36  Index Insertion      : 0.00
% 9.04/3.36  Index Deletion       : 0.00
% 9.04/3.36  Index Matching       : 0.00
% 9.04/3.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
