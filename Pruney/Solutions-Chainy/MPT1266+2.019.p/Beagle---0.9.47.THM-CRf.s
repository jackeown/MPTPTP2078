%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:45 EST 2020

% Result     : Theorem 8.70s
% Output     : CNFRefutation 9.04s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 817 expanded)
%              Number of leaves         :   43 ( 292 expanded)
%              Depth                    :   15
%              Number of atoms          :  241 (1705 expanded)
%              Number of equality atoms :   71 ( 470 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > v1_tops_1 > r2_hidden > m1_subset_1 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_57,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(c_58,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_92,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_52,plain,
    ( k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_98,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_52])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_36,plain,(
    ! [A_47] :
      ( l1_struct_0(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_77,plain,(
    ! [A_62] :
      ( u1_struct_0(A_62) = k2_struct_0(A_62)
      | ~ l1_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_82,plain,(
    ! [A_63] :
      ( u1_struct_0(A_63) = k2_struct_0(A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_36,c_77])).

tff(c_86,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_82])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_87,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_48])).

tff(c_22,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(k3_subset_1(A_34,B_35),k1_zfmisc_1(A_34))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_412,plain,(
    ! [A_114,B_115] :
      ( k2_pre_topc(A_114,B_115) = k2_struct_0(A_114)
      | ~ v1_tops_1(B_115,A_114)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_426,plain,(
    ! [B_115] :
      ( k2_pre_topc('#skF_1',B_115) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_115,'#skF_1')
      | ~ m1_subset_1(B_115,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_412])).

tff(c_454,plain,(
    ! [B_124] :
      ( k2_pre_topc('#skF_1',B_124) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_124,'#skF_1')
      | ~ m1_subset_1(B_124,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_426])).

tff(c_476,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_87,c_454])).

tff(c_478,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_476])).

tff(c_148,plain,(
    ! [A_74,B_75] :
      ( k3_subset_1(A_74,k3_subset_1(A_74,B_75)) = B_75
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_153,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_87,c_148])).

tff(c_516,plain,(
    ! [A_128,B_129] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_128),B_129),A_128)
      | ~ v2_tops_1(B_129,A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_531,plain,(
    ! [B_129] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_129),'#skF_1')
      | ~ v2_tops_1(B_129,'#skF_1')
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_516])).

tff(c_706,plain,(
    ! [B_140] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_140),'#skF_1')
      | ~ v2_tops_1(B_140,'#skF_1')
      | ~ m1_subset_1(B_140,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_86,c_531])).

tff(c_721,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_706])).

tff(c_728,plain,
    ( ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_478,c_721])).

tff(c_767,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_728])).

tff(c_770,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_22,c_767])).

tff(c_774,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_770])).

tff(c_776,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_728])).

tff(c_480,plain,(
    ! [B_125,A_126] :
      ( v1_tops_1(B_125,A_126)
      | k2_pre_topc(A_126,B_125) != k2_struct_0(A_126)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_494,plain,(
    ! [B_125] :
      ( v1_tops_1(B_125,'#skF_1')
      | k2_pre_topc('#skF_1',B_125) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_125,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_480])).

tff(c_503,plain,(
    ! [B_125] :
      ( v1_tops_1(B_125,'#skF_1')
      | k2_pre_topc('#skF_1',B_125) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_125,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_494])).

tff(c_801,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_776,c_503])).

tff(c_811,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_801])).

tff(c_6,plain,(
    ! [A_4] : k5_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_117,plain,(
    ! [A_68,B_69] : k5_xboole_0(A_68,k3_xboole_0(A_68,B_69)) = k4_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_126,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = k4_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_117])).

tff(c_129,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_126])).

tff(c_26,plain,(
    ! [A_38] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_190,plain,(
    ! [A_85,B_86] :
      ( k4_xboole_0(A_85,B_86) = k3_subset_1(A_85,B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_199,plain,(
    ! [A_38] : k4_xboole_0(A_38,k1_xboole_0) = k3_subset_1(A_38,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_190])).

tff(c_203,plain,(
    ! [A_38] : k3_subset_1(A_38,k1_xboole_0) = A_38 ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_199])).

tff(c_38,plain,(
    ! [A_48,B_50] :
      ( k3_subset_1(u1_struct_0(A_48),k2_pre_topc(A_48,k3_subset_1(u1_struct_0(A_48),B_50))) = k1_tops_1(A_48,B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_307,plain,(
    ! [A_105,B_106] :
      ( m1_subset_1(k2_pre_topc(A_105,B_106),k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    ! [A_36,B_37] :
      ( k3_subset_1(A_36,k3_subset_1(A_36,B_37)) = B_37
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1528,plain,(
    ! [A_177,B_178] :
      ( k3_subset_1(u1_struct_0(A_177),k3_subset_1(u1_struct_0(A_177),k2_pre_topc(A_177,B_178))) = k2_pre_topc(A_177,B_178)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ l1_pre_topc(A_177) ) ),
    inference(resolution,[status(thm)],[c_307,c_24])).

tff(c_8094,plain,(
    ! [A_348,B_349] :
      ( k3_subset_1(u1_struct_0(A_348),k1_tops_1(A_348,B_349)) = k2_pre_topc(A_348,k3_subset_1(u1_struct_0(A_348),B_349))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_348),B_349),k1_zfmisc_1(u1_struct_0(A_348)))
      | ~ l1_pre_topc(A_348)
      | ~ m1_subset_1(B_349,k1_zfmisc_1(u1_struct_0(A_348)))
      | ~ l1_pre_topc(A_348) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1528])).

tff(c_8178,plain,(
    ! [A_351,B_352] :
      ( k3_subset_1(u1_struct_0(A_351),k1_tops_1(A_351,B_352)) = k2_pre_topc(A_351,k3_subset_1(u1_struct_0(A_351),B_352))
      | ~ l1_pre_topc(A_351)
      | ~ m1_subset_1(B_352,k1_zfmisc_1(u1_struct_0(A_351))) ) ),
    inference(resolution,[status(thm)],[c_22,c_8094])).

tff(c_8200,plain,(
    ! [B_352] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1',B_352)) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_352))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_352,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_8178])).

tff(c_8218,plain,(
    ! [B_353] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k1_tops_1('#skF_1',B_353)) = k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_353))
      | ~ m1_subset_1(B_353,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_86,c_86,c_8200])).

tff(c_8274,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_87,c_8218])).

tff(c_8310,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_92,c_8274])).

tff(c_8312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_811,c_8310])).

tff(c_8313,plain,(
    v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_801])).

tff(c_643,plain,(
    ! [B_135,A_136] :
      ( v2_tops_1(B_135,A_136)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_136),B_135),A_136)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_661,plain,(
    ! [B_135] :
      ( v2_tops_1(B_135,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_135),'#skF_1')
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_643])).

tff(c_668,plain,(
    ! [B_135] :
      ( v2_tops_1(B_135,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_135),'#skF_1')
      | ~ m1_subset_1(B_135,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_86,c_661])).

tff(c_8318,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8313,c_668])).

tff(c_8321,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_8318])).

tff(c_8323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_8321])).

tff(c_8325,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_8346,plain,(
    ! [A_358,B_359] : k5_xboole_0(A_358,k3_xboole_0(A_358,B_359)) = k4_xboole_0(A_358,B_359) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8355,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = k4_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_8346])).

tff(c_8358,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8355])).

tff(c_8400,plain,(
    ! [A_373,B_374] :
      ( k4_xboole_0(A_373,B_374) = k3_subset_1(A_373,B_374)
      | ~ m1_subset_1(B_374,k1_zfmisc_1(A_373)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8406,plain,(
    ! [A_38] : k4_xboole_0(A_38,k1_xboole_0) = k3_subset_1(A_38,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_8400])).

tff(c_8409,plain,(
    ! [A_38] : k3_subset_1(A_38,k1_xboole_0) = A_38 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8358,c_8406])).

tff(c_8386,plain,(
    ! [A_370,B_371] :
      ( k3_subset_1(A_370,k3_subset_1(A_370,B_371)) = B_371
      | ~ m1_subset_1(B_371,k1_zfmisc_1(A_370)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8392,plain,(
    ! [A_38] : k3_subset_1(A_38,k3_subset_1(A_38,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_8386])).

tff(c_8410,plain,(
    ! [A_38] : k3_subset_1(A_38,A_38) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8409,c_8392])).

tff(c_8324,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_8826,plain,(
    ! [A_425,B_426] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_425),B_426),A_425)
      | ~ v2_tops_1(B_426,A_425)
      | ~ m1_subset_1(B_426,k1_zfmisc_1(u1_struct_0(A_425)))
      | ~ l1_pre_topc(A_425) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_8844,plain,(
    ! [B_426] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_426),'#skF_1')
      | ~ v2_tops_1(B_426,'#skF_1')
      | ~ m1_subset_1(B_426,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_8826])).

tff(c_8851,plain,(
    ! [B_426] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_426),'#skF_1')
      | ~ v2_tops_1(B_426,'#skF_1')
      | ~ m1_subset_1(B_426,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_86,c_8844])).

tff(c_8646,plain,(
    ! [B_410,A_411] :
      ( v1_tops_1(B_410,A_411)
      | k2_pre_topc(A_411,B_410) != k2_struct_0(A_411)
      | ~ m1_subset_1(B_410,k1_zfmisc_1(u1_struct_0(A_411)))
      | ~ l1_pre_topc(A_411) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_8660,plain,(
    ! [B_410] :
      ( v1_tops_1(B_410,'#skF_1')
      | k2_pre_topc('#skF_1',B_410) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_410,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_8646])).

tff(c_8720,plain,(
    ! [B_418] :
      ( v1_tops_1(B_418,'#skF_1')
      | k2_pre_topc('#skF_1',B_418) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_418,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_8660])).

tff(c_8743,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_87,c_8720])).

tff(c_8745,plain,(
    k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_8743])).

tff(c_8671,plain,(
    ! [A_412,B_413] :
      ( k2_pre_topc(A_412,B_413) = k2_struct_0(A_412)
      | ~ v1_tops_1(B_413,A_412)
      | ~ m1_subset_1(B_413,k1_zfmisc_1(u1_struct_0(A_412)))
      | ~ l1_pre_topc(A_412) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_8685,plain,(
    ! [B_413] :
      ( k2_pre_topc('#skF_1',B_413) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_413,'#skF_1')
      | ~ m1_subset_1(B_413,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_8671])).

tff(c_8769,plain,(
    ! [B_421] :
      ( k2_pre_topc('#skF_1',B_421) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_421,'#skF_1')
      | ~ m1_subset_1(B_421,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_8685])).

tff(c_8783,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_87,c_8769])).

tff(c_8794,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_8745,c_8783])).

tff(c_8391,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_87,c_8386])).

tff(c_8962,plain,(
    ! [B_434] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_434),'#skF_1')
      | ~ v2_tops_1(B_434,'#skF_1')
      | ~ m1_subset_1(B_434,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_86,c_8844])).

tff(c_8972,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8391,c_8962])).

tff(c_8982,plain,
    ( ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_8794,c_8972])).

tff(c_8998,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_8982])).

tff(c_9001,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_22,c_8998])).

tff(c_9005,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_9001])).

tff(c_9007,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_8982])).

tff(c_8694,plain,(
    ! [B_413] :
      ( k2_pre_topc('#skF_1',B_413) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_413,'#skF_1')
      | ~ m1_subset_1(B_413,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_8685])).

tff(c_9051,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_9007,c_8694])).

tff(c_9311,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_9051])).

tff(c_9314,plain,
    ( ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8851,c_9311])).

tff(c_9318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_8324,c_9314])).

tff(c_9319,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_9051])).

tff(c_9063,plain,(
    ! [A_444,B_445] :
      ( k3_subset_1(u1_struct_0(A_444),k2_pre_topc(A_444,k3_subset_1(u1_struct_0(A_444),B_445))) = k1_tops_1(A_444,B_445)
      | ~ m1_subset_1(B_445,k1_zfmisc_1(u1_struct_0(A_444)))
      | ~ l1_pre_topc(A_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_9105,plain,(
    ! [B_445] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_445))) = k1_tops_1('#skF_1',B_445)
      | ~ m1_subset_1(B_445,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_9063])).

tff(c_9116,plain,(
    ! [B_445] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_445))) = k1_tops_1('#skF_1',B_445)
      | ~ m1_subset_1(B_445,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_86,c_86,c_9105])).

tff(c_9337,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_9319,c_9116])).

tff(c_9351,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_8410,c_9337])).

tff(c_9353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8325,c_9351])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.70/3.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.70/3.18  
% 8.70/3.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.70/3.18  %$ v2_tops_1 > v1_tops_1 > r2_hidden > m1_subset_1 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.70/3.18  
% 8.70/3.18  %Foreground sorts:
% 8.70/3.18  
% 8.70/3.18  
% 8.70/3.18  %Background operators:
% 8.70/3.18  
% 8.70/3.18  
% 8.70/3.18  %Foreground operators:
% 8.70/3.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.70/3.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.70/3.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.70/3.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.70/3.18  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 8.70/3.18  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.70/3.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.70/3.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.70/3.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.70/3.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.70/3.18  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.70/3.18  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 8.70/3.18  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.70/3.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.70/3.18  tff('#skF_2', type, '#skF_2': $i).
% 8.70/3.18  tff('#skF_1', type, '#skF_1': $i).
% 8.70/3.18  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.70/3.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.70/3.18  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.70/3.18  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.70/3.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.70/3.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.70/3.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.70/3.18  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.70/3.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.70/3.18  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 8.70/3.18  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.70/3.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.70/3.18  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.70/3.18  
% 9.04/3.20  tff(f_114, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 9.04/3.20  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 9.04/3.20  tff(f_69, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 9.04/3.20  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 9.04/3.20  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 9.04/3.20  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 9.04/3.20  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_1)).
% 9.04/3.20  tff(f_31, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 9.04/3.20  tff(f_29, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 9.04/3.20  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.04/3.20  tff(f_57, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 9.04/3.20  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 9.04/3.20  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 9.04/3.20  tff(f_75, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 9.04/3.20  tff(c_58, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.04/3.20  tff(c_92, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_58])).
% 9.04/3.20  tff(c_52, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.04/3.20  tff(c_98, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_52])).
% 9.04/3.20  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.04/3.20  tff(c_36, plain, (![A_47]: (l1_struct_0(A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.04/3.20  tff(c_77, plain, (![A_62]: (u1_struct_0(A_62)=k2_struct_0(A_62) | ~l1_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.04/3.20  tff(c_82, plain, (![A_63]: (u1_struct_0(A_63)=k2_struct_0(A_63) | ~l1_pre_topc(A_63))), inference(resolution, [status(thm)], [c_36, c_77])).
% 9.04/3.20  tff(c_86, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_82])).
% 9.04/3.20  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.04/3.20  tff(c_87, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_48])).
% 9.04/3.20  tff(c_22, plain, (![A_34, B_35]: (m1_subset_1(k3_subset_1(A_34, B_35), k1_zfmisc_1(A_34)) | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.04/3.20  tff(c_412, plain, (![A_114, B_115]: (k2_pre_topc(A_114, B_115)=k2_struct_0(A_114) | ~v1_tops_1(B_115, A_114) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.04/3.20  tff(c_426, plain, (![B_115]: (k2_pre_topc('#skF_1', B_115)=k2_struct_0('#skF_1') | ~v1_tops_1(B_115, '#skF_1') | ~m1_subset_1(B_115, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_412])).
% 9.04/3.20  tff(c_454, plain, (![B_124]: (k2_pre_topc('#skF_1', B_124)=k2_struct_0('#skF_1') | ~v1_tops_1(B_124, '#skF_1') | ~m1_subset_1(B_124, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_426])).
% 9.04/3.20  tff(c_476, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_87, c_454])).
% 9.04/3.20  tff(c_478, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_476])).
% 9.04/3.20  tff(c_148, plain, (![A_74, B_75]: (k3_subset_1(A_74, k3_subset_1(A_74, B_75))=B_75 | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.04/3.20  tff(c_153, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_87, c_148])).
% 9.04/3.20  tff(c_516, plain, (![A_128, B_129]: (v1_tops_1(k3_subset_1(u1_struct_0(A_128), B_129), A_128) | ~v2_tops_1(B_129, A_128) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.04/3.20  tff(c_531, plain, (![B_129]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_129), '#skF_1') | ~v2_tops_1(B_129, '#skF_1') | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_516])).
% 9.04/3.20  tff(c_706, plain, (![B_140]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_140), '#skF_1') | ~v2_tops_1(B_140, '#skF_1') | ~m1_subset_1(B_140, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_86, c_531])).
% 9.04/3.20  tff(c_721, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_153, c_706])).
% 9.04/3.20  tff(c_728, plain, (~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_478, c_721])).
% 9.04/3.20  tff(c_767, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_728])).
% 9.04/3.20  tff(c_770, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_22, c_767])).
% 9.04/3.20  tff(c_774, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_770])).
% 9.04/3.20  tff(c_776, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_728])).
% 9.04/3.20  tff(c_480, plain, (![B_125, A_126]: (v1_tops_1(B_125, A_126) | k2_pre_topc(A_126, B_125)!=k2_struct_0(A_126) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.04/3.20  tff(c_494, plain, (![B_125]: (v1_tops_1(B_125, '#skF_1') | k2_pre_topc('#skF_1', B_125)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_125, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_480])).
% 9.04/3.20  tff(c_503, plain, (![B_125]: (v1_tops_1(B_125, '#skF_1') | k2_pre_topc('#skF_1', B_125)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_125, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_494])).
% 9.04/3.20  tff(c_801, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_776, c_503])).
% 9.04/3.20  tff(c_811, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_801])).
% 9.04/3.20  tff(c_6, plain, (![A_4]: (k5_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.04/3.20  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.04/3.20  tff(c_117, plain, (![A_68, B_69]: (k5_xboole_0(A_68, k3_xboole_0(A_68, B_69))=k4_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.04/3.20  tff(c_126, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=k4_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_117])).
% 9.04/3.20  tff(c_129, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_126])).
% 9.04/3.20  tff(c_26, plain, (![A_38]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.04/3.20  tff(c_190, plain, (![A_85, B_86]: (k4_xboole_0(A_85, B_86)=k3_subset_1(A_85, B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.04/3.20  tff(c_199, plain, (![A_38]: (k4_xboole_0(A_38, k1_xboole_0)=k3_subset_1(A_38, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_190])).
% 9.04/3.20  tff(c_203, plain, (![A_38]: (k3_subset_1(A_38, k1_xboole_0)=A_38)), inference(demodulation, [status(thm), theory('equality')], [c_129, c_199])).
% 9.04/3.20  tff(c_38, plain, (![A_48, B_50]: (k3_subset_1(u1_struct_0(A_48), k2_pre_topc(A_48, k3_subset_1(u1_struct_0(A_48), B_50)))=k1_tops_1(A_48, B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.04/3.20  tff(c_307, plain, (![A_105, B_106]: (m1_subset_1(k2_pre_topc(A_105, B_106), k1_zfmisc_1(u1_struct_0(A_105))) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.04/3.20  tff(c_24, plain, (![A_36, B_37]: (k3_subset_1(A_36, k3_subset_1(A_36, B_37))=B_37 | ~m1_subset_1(B_37, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.04/3.20  tff(c_1528, plain, (![A_177, B_178]: (k3_subset_1(u1_struct_0(A_177), k3_subset_1(u1_struct_0(A_177), k2_pre_topc(A_177, B_178)))=k2_pre_topc(A_177, B_178) | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0(A_177))) | ~l1_pre_topc(A_177))), inference(resolution, [status(thm)], [c_307, c_24])).
% 9.04/3.20  tff(c_8094, plain, (![A_348, B_349]: (k3_subset_1(u1_struct_0(A_348), k1_tops_1(A_348, B_349))=k2_pre_topc(A_348, k3_subset_1(u1_struct_0(A_348), B_349)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_348), B_349), k1_zfmisc_1(u1_struct_0(A_348))) | ~l1_pre_topc(A_348) | ~m1_subset_1(B_349, k1_zfmisc_1(u1_struct_0(A_348))) | ~l1_pre_topc(A_348))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1528])).
% 9.04/3.20  tff(c_8178, plain, (![A_351, B_352]: (k3_subset_1(u1_struct_0(A_351), k1_tops_1(A_351, B_352))=k2_pre_topc(A_351, k3_subset_1(u1_struct_0(A_351), B_352)) | ~l1_pre_topc(A_351) | ~m1_subset_1(B_352, k1_zfmisc_1(u1_struct_0(A_351))))), inference(resolution, [status(thm)], [c_22, c_8094])).
% 9.04/3.20  tff(c_8200, plain, (![B_352]: (k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', B_352))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_352)) | ~l1_pre_topc('#skF_1') | ~m1_subset_1(B_352, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_86, c_8178])).
% 9.04/3.20  tff(c_8218, plain, (![B_353]: (k3_subset_1(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', B_353))=k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_353)) | ~m1_subset_1(B_353, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_86, c_86, c_8200])).
% 9.04/3.20  tff(c_8274, plain, (k3_subset_1(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_87, c_8218])).
% 9.04/3.20  tff(c_8310, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_92, c_8274])).
% 9.04/3.20  tff(c_8312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_811, c_8310])).
% 9.04/3.20  tff(c_8313, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_801])).
% 9.04/3.20  tff(c_643, plain, (![B_135, A_136]: (v2_tops_1(B_135, A_136) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_136), B_135), A_136) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.04/3.20  tff(c_661, plain, (![B_135]: (v2_tops_1(B_135, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_135), '#skF_1') | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_643])).
% 9.04/3.20  tff(c_668, plain, (![B_135]: (v2_tops_1(B_135, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_135), '#skF_1') | ~m1_subset_1(B_135, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_86, c_661])).
% 9.04/3.20  tff(c_8318, plain, (v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8313, c_668])).
% 9.04/3.20  tff(c_8321, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_8318])).
% 9.04/3.20  tff(c_8323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_8321])).
% 9.04/3.20  tff(c_8325, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 9.04/3.20  tff(c_8346, plain, (![A_358, B_359]: (k5_xboole_0(A_358, k3_xboole_0(A_358, B_359))=k4_xboole_0(A_358, B_359))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.04/3.20  tff(c_8355, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=k4_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_8346])).
% 9.04/3.20  tff(c_8358, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8355])).
% 9.04/3.20  tff(c_8400, plain, (![A_373, B_374]: (k4_xboole_0(A_373, B_374)=k3_subset_1(A_373, B_374) | ~m1_subset_1(B_374, k1_zfmisc_1(A_373)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.04/3.20  tff(c_8406, plain, (![A_38]: (k4_xboole_0(A_38, k1_xboole_0)=k3_subset_1(A_38, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_8400])).
% 9.04/3.20  tff(c_8409, plain, (![A_38]: (k3_subset_1(A_38, k1_xboole_0)=A_38)), inference(demodulation, [status(thm), theory('equality')], [c_8358, c_8406])).
% 9.04/3.20  tff(c_8386, plain, (![A_370, B_371]: (k3_subset_1(A_370, k3_subset_1(A_370, B_371))=B_371 | ~m1_subset_1(B_371, k1_zfmisc_1(A_370)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.04/3.20  tff(c_8392, plain, (![A_38]: (k3_subset_1(A_38, k3_subset_1(A_38, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_8386])).
% 9.04/3.20  tff(c_8410, plain, (![A_38]: (k3_subset_1(A_38, A_38)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8409, c_8392])).
% 9.04/3.20  tff(c_8324, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 9.04/3.20  tff(c_8826, plain, (![A_425, B_426]: (v1_tops_1(k3_subset_1(u1_struct_0(A_425), B_426), A_425) | ~v2_tops_1(B_426, A_425) | ~m1_subset_1(B_426, k1_zfmisc_1(u1_struct_0(A_425))) | ~l1_pre_topc(A_425))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.04/3.20  tff(c_8844, plain, (![B_426]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_426), '#skF_1') | ~v2_tops_1(B_426, '#skF_1') | ~m1_subset_1(B_426, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_8826])).
% 9.04/3.20  tff(c_8851, plain, (![B_426]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_426), '#skF_1') | ~v2_tops_1(B_426, '#skF_1') | ~m1_subset_1(B_426, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_86, c_8844])).
% 9.04/3.20  tff(c_8646, plain, (![B_410, A_411]: (v1_tops_1(B_410, A_411) | k2_pre_topc(A_411, B_410)!=k2_struct_0(A_411) | ~m1_subset_1(B_410, k1_zfmisc_1(u1_struct_0(A_411))) | ~l1_pre_topc(A_411))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.04/3.20  tff(c_8660, plain, (![B_410]: (v1_tops_1(B_410, '#skF_1') | k2_pre_topc('#skF_1', B_410)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_410, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_8646])).
% 9.04/3.20  tff(c_8720, plain, (![B_418]: (v1_tops_1(B_418, '#skF_1') | k2_pre_topc('#skF_1', B_418)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_418, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_8660])).
% 9.04/3.20  tff(c_8743, plain, (v1_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_87, c_8720])).
% 9.04/3.20  tff(c_8745, plain, (k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_8743])).
% 9.04/3.20  tff(c_8671, plain, (![A_412, B_413]: (k2_pre_topc(A_412, B_413)=k2_struct_0(A_412) | ~v1_tops_1(B_413, A_412) | ~m1_subset_1(B_413, k1_zfmisc_1(u1_struct_0(A_412))) | ~l1_pre_topc(A_412))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.04/3.20  tff(c_8685, plain, (![B_413]: (k2_pre_topc('#skF_1', B_413)=k2_struct_0('#skF_1') | ~v1_tops_1(B_413, '#skF_1') | ~m1_subset_1(B_413, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_8671])).
% 9.04/3.20  tff(c_8769, plain, (![B_421]: (k2_pre_topc('#skF_1', B_421)=k2_struct_0('#skF_1') | ~v1_tops_1(B_421, '#skF_1') | ~m1_subset_1(B_421, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_8685])).
% 9.04/3.20  tff(c_8783, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_87, c_8769])).
% 9.04/3.20  tff(c_8794, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_8745, c_8783])).
% 9.04/3.20  tff(c_8391, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_87, c_8386])).
% 9.04/3.20  tff(c_8962, plain, (![B_434]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_434), '#skF_1') | ~v2_tops_1(B_434, '#skF_1') | ~m1_subset_1(B_434, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_86, c_8844])).
% 9.04/3.20  tff(c_8972, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_8391, c_8962])).
% 9.04/3.20  tff(c_8982, plain, (~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_8794, c_8972])).
% 9.04/3.20  tff(c_8998, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_8982])).
% 9.04/3.20  tff(c_9001, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_22, c_8998])).
% 9.04/3.20  tff(c_9005, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_9001])).
% 9.04/3.20  tff(c_9007, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_8982])).
% 9.04/3.20  tff(c_8694, plain, (![B_413]: (k2_pre_topc('#skF_1', B_413)=k2_struct_0('#skF_1') | ~v1_tops_1(B_413, '#skF_1') | ~m1_subset_1(B_413, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_8685])).
% 9.04/3.20  tff(c_9051, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_9007, c_8694])).
% 9.04/3.20  tff(c_9311, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_9051])).
% 9.04/3.20  tff(c_9314, plain, (~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8851, c_9311])).
% 9.04/3.20  tff(c_9318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_8324, c_9314])).
% 9.04/3.20  tff(c_9319, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_9051])).
% 9.04/3.20  tff(c_9063, plain, (![A_444, B_445]: (k3_subset_1(u1_struct_0(A_444), k2_pre_topc(A_444, k3_subset_1(u1_struct_0(A_444), B_445)))=k1_tops_1(A_444, B_445) | ~m1_subset_1(B_445, k1_zfmisc_1(u1_struct_0(A_444))) | ~l1_pre_topc(A_444))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.04/3.20  tff(c_9105, plain, (![B_445]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_445)))=k1_tops_1('#skF_1', B_445) | ~m1_subset_1(B_445, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_9063])).
% 9.04/3.20  tff(c_9116, plain, (![B_445]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_445)))=k1_tops_1('#skF_1', B_445) | ~m1_subset_1(B_445, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_86, c_86, c_9105])).
% 9.04/3.20  tff(c_9337, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_9319, c_9116])).
% 9.04/3.20  tff(c_9351, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_87, c_8410, c_9337])).
% 9.04/3.20  tff(c_9353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8325, c_9351])).
% 9.04/3.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.04/3.20  
% 9.04/3.20  Inference rules
% 9.04/3.20  ----------------------
% 9.04/3.20  #Ref     : 0
% 9.04/3.20  #Sup     : 2250
% 9.04/3.20  #Fact    : 0
% 9.04/3.20  #Define  : 0
% 9.04/3.20  #Split   : 36
% 9.04/3.20  #Chain   : 0
% 9.04/3.20  #Close   : 0
% 9.04/3.20  
% 9.04/3.20  Ordering : KBO
% 9.04/3.20  
% 9.04/3.20  Simplification rules
% 9.04/3.20  ----------------------
% 9.04/3.20  #Subsume      : 390
% 9.04/3.20  #Demod        : 1820
% 9.04/3.20  #Tautology    : 539
% 9.04/3.20  #SimpNegUnit  : 200
% 9.04/3.20  #BackRed      : 4
% 9.04/3.20  
% 9.04/3.20  #Partial instantiations: 0
% 9.04/3.20  #Strategies tried      : 1
% 9.04/3.20  
% 9.04/3.20  Timing (in seconds)
% 9.04/3.20  ----------------------
% 9.04/3.21  Preprocessing        : 0.35
% 9.04/3.21  Parsing              : 0.19
% 9.04/3.21  CNF conversion       : 0.02
% 9.04/3.21  Main loop            : 2.07
% 9.04/3.21  Inferencing          : 0.61
% 9.04/3.21  Reduction            : 0.80
% 9.04/3.21  Demodulation         : 0.58
% 9.04/3.21  BG Simplification    : 0.07
% 9.04/3.21  Subsumption          : 0.45
% 9.04/3.21  Abstraction          : 0.09
% 9.04/3.21  MUC search           : 0.00
% 9.04/3.21  Cooper               : 0.00
% 9.04/3.21  Total                : 2.46
% 9.04/3.21  Index Insertion      : 0.00
% 9.04/3.21  Index Deletion       : 0.00
% 9.04/3.21  Index Matching       : 0.00
% 9.04/3.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
