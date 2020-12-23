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
% DateTime   : Thu Dec  3 10:21:44 EST 2020

% Result     : Theorem 8.52s
% Output     : CNFRefutation 8.52s
% Verified   : 
% Statistics : Number of formulae       :  151 (1103 expanded)
%              Number of leaves         :   37 ( 381 expanded)
%              Depth                    :   15
%              Number of atoms          :  266 (2383 expanded)
%              Number of equality atoms :   77 ( 651 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

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

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

tff(f_37,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_39,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_55,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

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

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(c_52,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_90,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,
    ( k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_111,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_46])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_30,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_85,plain,(
    ! [A_35] :
      ( u1_struct_0(A_35) = k2_struct_0(A_35)
      | ~ l1_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_95,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = k2_struct_0(A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(resolution,[status(thm)],[c_30,c_85])).

tff(c_99,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_95])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_100,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_42])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k3_subset_1(A_10,B_11),k1_zfmisc_1(A_10))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_300,plain,(
    ! [B_62,A_63] :
      ( v1_tops_1(B_62,A_63)
      | k2_pre_topc(A_63,B_62) != k2_struct_0(A_63)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_314,plain,(
    ! [B_62] :
      ( v1_tops_1(B_62,'#skF_1')
      | k2_pre_topc('#skF_1',B_62) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_300])).

tff(c_333,plain,(
    ! [B_66] :
      ( v1_tops_1(B_66,'#skF_1')
      | k2_pre_topc('#skF_1',B_66) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_314])).

tff(c_355,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_100,c_333])).

tff(c_358,plain,(
    k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_355])).

tff(c_359,plain,(
    ! [A_67,B_68] :
      ( k2_pre_topc(A_67,B_68) = k2_struct_0(A_67)
      | ~ v1_tops_1(B_68,A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_373,plain,(
    ! [B_68] :
      ( k2_pre_topc('#skF_1',B_68) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_68,'#skF_1')
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_359])).

tff(c_400,plain,(
    ! [B_71] :
      ( k2_pre_topc('#skF_1',B_71) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_71,'#skF_1')
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_373])).

tff(c_414,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_100,c_400])).

tff(c_426,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_358,c_414])).

tff(c_197,plain,(
    ! [A_52,B_53] :
      ( k3_subset_1(A_52,k3_subset_1(A_52,B_53)) = B_53
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_209,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_100,c_197])).

tff(c_548,plain,(
    ! [A_80,B_81] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_80),B_81),A_80)
      | ~ v2_tops_1(B_81,A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_562,plain,(
    ! [B_81] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_81),'#skF_1')
      | ~ v2_tops_1(B_81,'#skF_1')
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_548])).

tff(c_802,plain,(
    ! [B_90] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_90),'#skF_1')
      | ~ v2_tops_1(B_90,'#skF_1')
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_99,c_562])).

tff(c_818,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_802])).

tff(c_828,plain,
    ( ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_426,c_818])).

tff(c_835,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_828])).

tff(c_895,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_20,c_835])).

tff(c_899,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_895])).

tff(c_901,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_828])).

tff(c_382,plain,(
    ! [B_68] :
      ( k2_pre_topc('#skF_1',B_68) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_68,'#skF_1')
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_373])).

tff(c_915,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_901,c_382])).

tff(c_997,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_915])).

tff(c_323,plain,(
    ! [B_62] :
      ( v1_tops_1(B_62,'#skF_1')
      | k2_pre_topc('#skF_1',B_62) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_314])).

tff(c_916,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_901,c_323])).

tff(c_1004,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_997,c_916])).

tff(c_12,plain,(
    ! [A_5] : k1_subset_1(A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [A_14] : k3_subset_1(A_14,k1_subset_1(A_14)) = k2_subset_1(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_54,plain,(
    ! [A_14] : k3_subset_1(A_14,k1_subset_1(A_14)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_24])).

tff(c_55,plain,(
    ! [A_14] : k3_subset_1(A_14,k1_xboole_0) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_54])).

tff(c_32,plain,(
    ! [A_19,B_21] :
      ( k3_subset_1(u1_struct_0(A_19),k2_pre_topc(A_19,k3_subset_1(u1_struct_0(A_19),B_21))) = k1_tops_1(A_19,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_251,plain,(
    ! [A_57,B_58] :
      ( m1_subset_1(k2_pre_topc(A_57,B_58),k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( k3_subset_1(A_12,k3_subset_1(A_12,B_13)) = B_13
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1166,plain,(
    ! [A_98,B_99] :
      ( k3_subset_1(u1_struct_0(A_98),k3_subset_1(u1_struct_0(A_98),k2_pre_topc(A_98,B_99))) = k2_pre_topc(A_98,B_99)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(resolution,[status(thm)],[c_251,c_22])).

tff(c_7027,plain,(
    ! [A_231,B_232] :
      ( k3_subset_1(u1_struct_0(A_231),k1_tops_1(A_231,B_232)) = k2_pre_topc(A_231,k3_subset_1(u1_struct_0(A_231),B_232))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_231),B_232),k1_zfmisc_1(u1_struct_0(A_231)))
      | ~ l1_pre_topc(A_231)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(u1_struct_0(A_231)))
      | ~ l1_pre_topc(A_231) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1166])).

tff(c_7107,plain,(
    ! [A_233,B_234] :
      ( k3_subset_1(u1_struct_0(A_233),k1_tops_1(A_233,B_234)) = k2_pre_topc(A_233,k3_subset_1(u1_struct_0(A_233),B_234))
      | ~ l1_pre_topc(A_233)
      | ~ m1_subset_1(B_234,k1_zfmisc_1(u1_struct_0(A_233))) ) ),
    inference(resolution,[status(thm)],[c_20,c_7027])).

tff(c_7129,plain,(
    ! [B_234] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1',B_234)) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_234))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_234,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_7107])).

tff(c_7147,plain,(
    ! [B_235] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k1_tops_1('#skF_1',B_235)) = k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_235))
      | ~ m1_subset_1(B_235,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_99,c_99,c_7129])).

tff(c_7203,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_100,c_7147])).

tff(c_7238,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_90,c_7203])).

tff(c_7240,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1004,c_7238])).

tff(c_7242,plain,(
    v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_915])).

tff(c_484,plain,(
    ! [B_74,A_75] :
      ( v2_tops_1(B_74,A_75)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_75),B_74),A_75)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_495,plain,(
    ! [B_74] :
      ( v2_tops_1(B_74,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_74),'#skF_1')
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_484])).

tff(c_503,plain,(
    ! [B_74] :
      ( v2_tops_1(B_74,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_74),'#skF_1')
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_99,c_495])).

tff(c_7245,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_7242,c_503])).

tff(c_7248,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_7245])).

tff(c_7250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_7248])).

tff(c_7251,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_7253,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_7255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7251,c_7253])).

tff(c_7256,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_7259,plain,(
    ! [A_236] :
      ( u1_struct_0(A_236) = k2_struct_0(A_236)
      | ~ l1_pre_topc(A_236) ) ),
    inference(resolution,[status(thm)],[c_30,c_85])).

tff(c_7263,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_7259])).

tff(c_7264,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7263,c_42])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_7269,plain,(
    ! [A_237,B_238] :
      ( k4_xboole_0(A_237,B_238) = k1_xboole_0
      | ~ r1_tarski(A_237,B_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7273,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_7269])).

tff(c_18,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_53,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18])).

tff(c_7308,plain,(
    ! [A_246,B_247] :
      ( k4_xboole_0(A_246,B_247) = k3_subset_1(A_246,B_247)
      | ~ m1_subset_1(B_247,k1_zfmisc_1(A_246)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7314,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_subset_1(A_9,A_9) ),
    inference(resolution,[status(thm)],[c_53,c_7308])).

tff(c_7317,plain,(
    ! [A_9] : k3_subset_1(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7273,c_7314])).

tff(c_7612,plain,(
    ! [A_273,B_274] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_273),B_274),A_273)
      | ~ v2_tops_1(B_274,A_273)
      | ~ m1_subset_1(B_274,k1_zfmisc_1(u1_struct_0(A_273)))
      | ~ l1_pre_topc(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_7623,plain,(
    ! [B_274] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_274),'#skF_1')
      | ~ v2_tops_1(B_274,'#skF_1')
      | ~ m1_subset_1(B_274,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7263,c_7612])).

tff(c_7631,plain,(
    ! [B_274] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_274),'#skF_1')
      | ~ v2_tops_1(B_274,'#skF_1')
      | ~ m1_subset_1(B_274,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_7263,c_7623])).

tff(c_7543,plain,(
    ! [B_268,A_269] :
      ( v1_tops_1(B_268,A_269)
      | k2_pre_topc(A_269,B_268) != k2_struct_0(A_269)
      | ~ m1_subset_1(B_268,k1_zfmisc_1(u1_struct_0(A_269)))
      | ~ l1_pre_topc(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_7557,plain,(
    ! [B_268] :
      ( v1_tops_1(B_268,'#skF_1')
      | k2_pre_topc('#skF_1',B_268) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_268,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7263,c_7543])).

tff(c_7584,plain,(
    ! [B_272] :
      ( v1_tops_1(B_272,'#skF_1')
      | k2_pre_topc('#skF_1',B_272) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_272,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_7557])).

tff(c_7606,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_7264,c_7584])).

tff(c_7611,plain,(
    k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_7606])).

tff(c_7510,plain,(
    ! [A_264,B_265] :
      ( k2_pre_topc(A_264,B_265) = k2_struct_0(A_264)
      | ~ v1_tops_1(B_265,A_264)
      | ~ m1_subset_1(B_265,k1_zfmisc_1(u1_struct_0(A_264)))
      | ~ l1_pre_topc(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_7524,plain,(
    ! [B_265] :
      ( k2_pre_topc('#skF_1',B_265) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_265,'#skF_1')
      | ~ m1_subset_1(B_265,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7263,c_7510])).

tff(c_7641,plain,(
    ! [B_276] :
      ( k2_pre_topc('#skF_1',B_276) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_276,'#skF_1')
      | ~ m1_subset_1(B_276,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_7524])).

tff(c_7655,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_7264,c_7641])).

tff(c_7667,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_7611,c_7655])).

tff(c_7318,plain,(
    ! [A_248,B_249] :
      ( k3_subset_1(A_248,k3_subset_1(A_248,B_249)) = B_249
      | ~ m1_subset_1(B_249,k1_zfmisc_1(A_248)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_7323,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_7264,c_7318])).

tff(c_7765,plain,(
    ! [B_283] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_283),'#skF_1')
      | ~ v2_tops_1(B_283,'#skF_1')
      | ~ m1_subset_1(B_283,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_7263,c_7623])).

tff(c_7772,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_7323,c_7765])).

tff(c_7781,plain,
    ( ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_7667,c_7772])).

tff(c_7849,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_7781])).

tff(c_7852,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_20,c_7849])).

tff(c_7856,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7264,c_7852])).

tff(c_7858,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_7781])).

tff(c_7566,plain,(
    ! [B_268] :
      ( v1_tops_1(B_268,'#skF_1')
      | k2_pre_topc('#skF_1',B_268) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_268,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_7557])).

tff(c_7926,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_7858,c_7566])).

tff(c_8034,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_7926])).

tff(c_7533,plain,(
    ! [B_265] :
      ( k2_pre_topc('#skF_1',B_265) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_265,'#skF_1')
      | ~ m1_subset_1(B_265,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_7524])).

tff(c_7925,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_7858,c_7533])).

tff(c_8190,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_8034,c_7925])).

tff(c_8193,plain,
    ( ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_7631,c_8190])).

tff(c_8197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7264,c_7251,c_8193])).

tff(c_8199,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_7926])).

tff(c_7859,plain,(
    ! [A_287,B_288] :
      ( k3_subset_1(u1_struct_0(A_287),k2_pre_topc(A_287,k3_subset_1(u1_struct_0(A_287),B_288))) = k1_tops_1(A_287,B_288)
      | ~ m1_subset_1(B_288,k1_zfmisc_1(u1_struct_0(A_287)))
      | ~ l1_pre_topc(A_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_7894,plain,(
    ! [B_288] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_288))) = k1_tops_1('#skF_1',B_288)
      | ~ m1_subset_1(B_288,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7263,c_7859])).

tff(c_8598,plain,(
    ! [B_308] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_308))) = k1_tops_1('#skF_1',B_308)
      | ~ m1_subset_1(B_308,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_7263,c_7263,c_7894])).

tff(c_8637,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8199,c_8598])).

tff(c_8664,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7264,c_7317,c_8637])).

tff(c_8666,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7256,c_8664])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:49:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.52/2.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.52/2.91  
% 8.52/2.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.52/2.91  %$ v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.52/2.91  
% 8.52/2.91  %Foreground sorts:
% 8.52/2.91  
% 8.52/2.91  
% 8.52/2.91  %Background operators:
% 8.52/2.91  
% 8.52/2.91  
% 8.52/2.91  %Foreground operators:
% 8.52/2.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.52/2.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.52/2.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.52/2.91  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 8.52/2.91  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.52/2.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.52/2.91  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.52/2.91  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 8.52/2.91  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.52/2.91  tff('#skF_2', type, '#skF_2': $i).
% 8.52/2.91  tff('#skF_1', type, '#skF_1': $i).
% 8.52/2.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.52/2.91  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.52/2.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.52/2.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.52/2.91  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 8.52/2.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.52/2.91  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 8.52/2.91  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 8.52/2.91  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.52/2.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.52/2.91  
% 8.52/2.93  tff(f_104, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 8.52/2.93  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 8.52/2.93  tff(f_59, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 8.52/2.93  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 8.52/2.93  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 8.52/2.93  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 8.52/2.93  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 8.52/2.93  tff(f_37, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 8.52/2.93  tff(f_39, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 8.52/2.93  tff(f_55, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 8.52/2.93  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 8.52/2.93  tff(f_65, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 8.52/2.93  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.52/2.93  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 8.52/2.93  tff(f_45, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 8.52/2.93  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 8.52/2.93  tff(c_52, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.52/2.93  tff(c_90, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 8.52/2.93  tff(c_46, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.52/2.93  tff(c_111, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_46])).
% 8.52/2.93  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.52/2.93  tff(c_30, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.52/2.93  tff(c_85, plain, (![A_35]: (u1_struct_0(A_35)=k2_struct_0(A_35) | ~l1_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.52/2.93  tff(c_95, plain, (![A_36]: (u1_struct_0(A_36)=k2_struct_0(A_36) | ~l1_pre_topc(A_36))), inference(resolution, [status(thm)], [c_30, c_85])).
% 8.52/2.93  tff(c_99, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_95])).
% 8.52/2.93  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.52/2.93  tff(c_100, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_42])).
% 8.52/2.93  tff(c_20, plain, (![A_10, B_11]: (m1_subset_1(k3_subset_1(A_10, B_11), k1_zfmisc_1(A_10)) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.52/2.93  tff(c_300, plain, (![B_62, A_63]: (v1_tops_1(B_62, A_63) | k2_pre_topc(A_63, B_62)!=k2_struct_0(A_63) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.52/2.93  tff(c_314, plain, (![B_62]: (v1_tops_1(B_62, '#skF_1') | k2_pre_topc('#skF_1', B_62)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_62, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_300])).
% 8.52/2.93  tff(c_333, plain, (![B_66]: (v1_tops_1(B_66, '#skF_1') | k2_pre_topc('#skF_1', B_66)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_66, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_314])).
% 8.52/2.93  tff(c_355, plain, (v1_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_100, c_333])).
% 8.52/2.93  tff(c_358, plain, (k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_355])).
% 8.52/2.93  tff(c_359, plain, (![A_67, B_68]: (k2_pre_topc(A_67, B_68)=k2_struct_0(A_67) | ~v1_tops_1(B_68, A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.52/2.93  tff(c_373, plain, (![B_68]: (k2_pre_topc('#skF_1', B_68)=k2_struct_0('#skF_1') | ~v1_tops_1(B_68, '#skF_1') | ~m1_subset_1(B_68, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_359])).
% 8.52/2.93  tff(c_400, plain, (![B_71]: (k2_pre_topc('#skF_1', B_71)=k2_struct_0('#skF_1') | ~v1_tops_1(B_71, '#skF_1') | ~m1_subset_1(B_71, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_373])).
% 8.52/2.93  tff(c_414, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_100, c_400])).
% 8.52/2.93  tff(c_426, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_358, c_414])).
% 8.52/2.93  tff(c_197, plain, (![A_52, B_53]: (k3_subset_1(A_52, k3_subset_1(A_52, B_53))=B_53 | ~m1_subset_1(B_53, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.52/2.93  tff(c_209, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_100, c_197])).
% 8.52/2.93  tff(c_548, plain, (![A_80, B_81]: (v1_tops_1(k3_subset_1(u1_struct_0(A_80), B_81), A_80) | ~v2_tops_1(B_81, A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.52/2.93  tff(c_562, plain, (![B_81]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_81), '#skF_1') | ~v2_tops_1(B_81, '#skF_1') | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_548])).
% 8.52/2.93  tff(c_802, plain, (![B_90]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_90), '#skF_1') | ~v2_tops_1(B_90, '#skF_1') | ~m1_subset_1(B_90, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_99, c_562])).
% 8.52/2.93  tff(c_818, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_209, c_802])).
% 8.52/2.93  tff(c_828, plain, (~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_426, c_818])).
% 8.52/2.93  tff(c_835, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_828])).
% 8.52/2.93  tff(c_895, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_20, c_835])).
% 8.52/2.93  tff(c_899, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_895])).
% 8.52/2.93  tff(c_901, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_828])).
% 8.52/2.93  tff(c_382, plain, (![B_68]: (k2_pre_topc('#skF_1', B_68)=k2_struct_0('#skF_1') | ~v1_tops_1(B_68, '#skF_1') | ~m1_subset_1(B_68, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_373])).
% 8.52/2.93  tff(c_915, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_901, c_382])).
% 8.52/2.93  tff(c_997, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_915])).
% 8.52/2.93  tff(c_323, plain, (![B_62]: (v1_tops_1(B_62, '#skF_1') | k2_pre_topc('#skF_1', B_62)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_62, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_314])).
% 8.52/2.93  tff(c_916, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_901, c_323])).
% 8.52/2.93  tff(c_1004, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_997, c_916])).
% 8.52/2.93  tff(c_12, plain, (![A_5]: (k1_subset_1(A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.52/2.93  tff(c_14, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.52/2.93  tff(c_24, plain, (![A_14]: (k3_subset_1(A_14, k1_subset_1(A_14))=k2_subset_1(A_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.52/2.93  tff(c_54, plain, (![A_14]: (k3_subset_1(A_14, k1_subset_1(A_14))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_24])).
% 8.52/2.93  tff(c_55, plain, (![A_14]: (k3_subset_1(A_14, k1_xboole_0)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_54])).
% 8.52/2.93  tff(c_32, plain, (![A_19, B_21]: (k3_subset_1(u1_struct_0(A_19), k2_pre_topc(A_19, k3_subset_1(u1_struct_0(A_19), B_21)))=k1_tops_1(A_19, B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.52/2.93  tff(c_251, plain, (![A_57, B_58]: (m1_subset_1(k2_pre_topc(A_57, B_58), k1_zfmisc_1(u1_struct_0(A_57))) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.52/2.93  tff(c_22, plain, (![A_12, B_13]: (k3_subset_1(A_12, k3_subset_1(A_12, B_13))=B_13 | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.52/2.93  tff(c_1166, plain, (![A_98, B_99]: (k3_subset_1(u1_struct_0(A_98), k3_subset_1(u1_struct_0(A_98), k2_pre_topc(A_98, B_99)))=k2_pre_topc(A_98, B_99) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(resolution, [status(thm)], [c_251, c_22])).
% 8.52/2.93  tff(c_7027, plain, (![A_231, B_232]: (k3_subset_1(u1_struct_0(A_231), k1_tops_1(A_231, B_232))=k2_pre_topc(A_231, k3_subset_1(u1_struct_0(A_231), B_232)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_231), B_232), k1_zfmisc_1(u1_struct_0(A_231))) | ~l1_pre_topc(A_231) | ~m1_subset_1(B_232, k1_zfmisc_1(u1_struct_0(A_231))) | ~l1_pre_topc(A_231))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1166])).
% 8.52/2.93  tff(c_7107, plain, (![A_233, B_234]: (k3_subset_1(u1_struct_0(A_233), k1_tops_1(A_233, B_234))=k2_pre_topc(A_233, k3_subset_1(u1_struct_0(A_233), B_234)) | ~l1_pre_topc(A_233) | ~m1_subset_1(B_234, k1_zfmisc_1(u1_struct_0(A_233))))), inference(resolution, [status(thm)], [c_20, c_7027])).
% 8.52/2.93  tff(c_7129, plain, (![B_234]: (k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', B_234))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_234)) | ~l1_pre_topc('#skF_1') | ~m1_subset_1(B_234, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_99, c_7107])).
% 8.52/2.93  tff(c_7147, plain, (![B_235]: (k3_subset_1(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', B_235))=k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_235)) | ~m1_subset_1(B_235, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_99, c_99, c_7129])).
% 8.52/2.93  tff(c_7203, plain, (k3_subset_1(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_100, c_7147])).
% 8.52/2.93  tff(c_7238, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_90, c_7203])).
% 8.52/2.93  tff(c_7240, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1004, c_7238])).
% 8.52/2.93  tff(c_7242, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_915])).
% 8.52/2.93  tff(c_484, plain, (![B_74, A_75]: (v2_tops_1(B_74, A_75) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_75), B_74), A_75) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.52/2.93  tff(c_495, plain, (![B_74]: (v2_tops_1(B_74, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_74), '#skF_1') | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_484])).
% 8.52/2.93  tff(c_503, plain, (![B_74]: (v2_tops_1(B_74, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_74), '#skF_1') | ~m1_subset_1(B_74, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_99, c_495])).
% 8.52/2.93  tff(c_7245, plain, (v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_7242, c_503])).
% 8.52/2.93  tff(c_7248, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_7245])).
% 8.52/2.93  tff(c_7250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_7248])).
% 8.52/2.93  tff(c_7251, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 8.52/2.93  tff(c_7253, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 8.52/2.93  tff(c_7255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7251, c_7253])).
% 8.52/2.93  tff(c_7256, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_46])).
% 8.52/2.93  tff(c_7259, plain, (![A_236]: (u1_struct_0(A_236)=k2_struct_0(A_236) | ~l1_pre_topc(A_236))), inference(resolution, [status(thm)], [c_30, c_85])).
% 8.52/2.93  tff(c_7263, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_7259])).
% 8.52/2.93  tff(c_7264, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_7263, c_42])).
% 8.52/2.93  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.52/2.93  tff(c_7269, plain, (![A_237, B_238]: (k4_xboole_0(A_237, B_238)=k1_xboole_0 | ~r1_tarski(A_237, B_238))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.52/2.93  tff(c_7273, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_7269])).
% 8.52/2.93  tff(c_18, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.52/2.93  tff(c_53, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_18])).
% 8.52/2.93  tff(c_7308, plain, (![A_246, B_247]: (k4_xboole_0(A_246, B_247)=k3_subset_1(A_246, B_247) | ~m1_subset_1(B_247, k1_zfmisc_1(A_246)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.52/2.93  tff(c_7314, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_subset_1(A_9, A_9))), inference(resolution, [status(thm)], [c_53, c_7308])).
% 8.52/2.93  tff(c_7317, plain, (![A_9]: (k3_subset_1(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7273, c_7314])).
% 8.52/2.93  tff(c_7612, plain, (![A_273, B_274]: (v1_tops_1(k3_subset_1(u1_struct_0(A_273), B_274), A_273) | ~v2_tops_1(B_274, A_273) | ~m1_subset_1(B_274, k1_zfmisc_1(u1_struct_0(A_273))) | ~l1_pre_topc(A_273))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.52/2.93  tff(c_7623, plain, (![B_274]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_274), '#skF_1') | ~v2_tops_1(B_274, '#skF_1') | ~m1_subset_1(B_274, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_7263, c_7612])).
% 8.52/2.93  tff(c_7631, plain, (![B_274]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_274), '#skF_1') | ~v2_tops_1(B_274, '#skF_1') | ~m1_subset_1(B_274, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_7263, c_7623])).
% 8.52/2.93  tff(c_7543, plain, (![B_268, A_269]: (v1_tops_1(B_268, A_269) | k2_pre_topc(A_269, B_268)!=k2_struct_0(A_269) | ~m1_subset_1(B_268, k1_zfmisc_1(u1_struct_0(A_269))) | ~l1_pre_topc(A_269))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.52/2.93  tff(c_7557, plain, (![B_268]: (v1_tops_1(B_268, '#skF_1') | k2_pre_topc('#skF_1', B_268)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_268, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_7263, c_7543])).
% 8.52/2.93  tff(c_7584, plain, (![B_272]: (v1_tops_1(B_272, '#skF_1') | k2_pre_topc('#skF_1', B_272)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_272, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_7557])).
% 8.52/2.93  tff(c_7606, plain, (v1_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_7264, c_7584])).
% 8.52/2.93  tff(c_7611, plain, (k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_7606])).
% 8.52/2.93  tff(c_7510, plain, (![A_264, B_265]: (k2_pre_topc(A_264, B_265)=k2_struct_0(A_264) | ~v1_tops_1(B_265, A_264) | ~m1_subset_1(B_265, k1_zfmisc_1(u1_struct_0(A_264))) | ~l1_pre_topc(A_264))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.52/2.93  tff(c_7524, plain, (![B_265]: (k2_pre_topc('#skF_1', B_265)=k2_struct_0('#skF_1') | ~v1_tops_1(B_265, '#skF_1') | ~m1_subset_1(B_265, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_7263, c_7510])).
% 8.52/2.93  tff(c_7641, plain, (![B_276]: (k2_pre_topc('#skF_1', B_276)=k2_struct_0('#skF_1') | ~v1_tops_1(B_276, '#skF_1') | ~m1_subset_1(B_276, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_7524])).
% 8.52/2.93  tff(c_7655, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_7264, c_7641])).
% 8.52/2.93  tff(c_7667, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_7611, c_7655])).
% 8.52/2.93  tff(c_7318, plain, (![A_248, B_249]: (k3_subset_1(A_248, k3_subset_1(A_248, B_249))=B_249 | ~m1_subset_1(B_249, k1_zfmisc_1(A_248)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.52/2.93  tff(c_7323, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_7264, c_7318])).
% 8.52/2.93  tff(c_7765, plain, (![B_283]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_283), '#skF_1') | ~v2_tops_1(B_283, '#skF_1') | ~m1_subset_1(B_283, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_7263, c_7623])).
% 8.52/2.93  tff(c_7772, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_7323, c_7765])).
% 8.52/2.93  tff(c_7781, plain, (~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_7667, c_7772])).
% 8.52/2.93  tff(c_7849, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_7781])).
% 8.52/2.93  tff(c_7852, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_20, c_7849])).
% 8.52/2.93  tff(c_7856, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7264, c_7852])).
% 8.52/2.93  tff(c_7858, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_7781])).
% 8.52/2.93  tff(c_7566, plain, (![B_268]: (v1_tops_1(B_268, '#skF_1') | k2_pre_topc('#skF_1', B_268)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_268, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_7557])).
% 8.52/2.93  tff(c_7926, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_7858, c_7566])).
% 8.52/2.93  tff(c_8034, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_7926])).
% 8.52/2.93  tff(c_7533, plain, (![B_265]: (k2_pre_topc('#skF_1', B_265)=k2_struct_0('#skF_1') | ~v1_tops_1(B_265, '#skF_1') | ~m1_subset_1(B_265, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_7524])).
% 8.52/2.93  tff(c_7925, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_7858, c_7533])).
% 8.52/2.93  tff(c_8190, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_8034, c_7925])).
% 8.52/2.93  tff(c_8193, plain, (~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_7631, c_8190])).
% 8.52/2.93  tff(c_8197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7264, c_7251, c_8193])).
% 8.52/2.93  tff(c_8199, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_7926])).
% 8.52/2.93  tff(c_7859, plain, (![A_287, B_288]: (k3_subset_1(u1_struct_0(A_287), k2_pre_topc(A_287, k3_subset_1(u1_struct_0(A_287), B_288)))=k1_tops_1(A_287, B_288) | ~m1_subset_1(B_288, k1_zfmisc_1(u1_struct_0(A_287))) | ~l1_pre_topc(A_287))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.52/2.93  tff(c_7894, plain, (![B_288]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_288)))=k1_tops_1('#skF_1', B_288) | ~m1_subset_1(B_288, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_7263, c_7859])).
% 8.52/2.93  tff(c_8598, plain, (![B_308]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_308)))=k1_tops_1('#skF_1', B_308) | ~m1_subset_1(B_308, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_7263, c_7263, c_7894])).
% 8.52/2.93  tff(c_8637, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_8199, c_8598])).
% 8.52/2.93  tff(c_8664, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7264, c_7317, c_8637])).
% 8.52/2.93  tff(c_8666, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7256, c_8664])).
% 8.52/2.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.52/2.93  
% 8.52/2.93  Inference rules
% 8.52/2.93  ----------------------
% 8.52/2.93  #Ref     : 0
% 8.52/2.93  #Sup     : 2097
% 8.52/2.93  #Fact    : 0
% 8.52/2.93  #Define  : 0
% 8.52/2.93  #Split   : 54
% 8.52/2.93  #Chain   : 0
% 8.52/2.93  #Close   : 0
% 8.52/2.93  
% 8.52/2.93  Ordering : KBO
% 8.52/2.93  
% 8.52/2.93  Simplification rules
% 8.52/2.93  ----------------------
% 8.52/2.93  #Subsume      : 289
% 8.52/2.93  #Demod        : 1634
% 8.52/2.93  #Tautology    : 546
% 8.52/2.93  #SimpNegUnit  : 191
% 8.52/2.93  #BackRed      : 3
% 8.52/2.93  
% 8.52/2.93  #Partial instantiations: 0
% 8.52/2.93  #Strategies tried      : 1
% 8.52/2.93  
% 8.52/2.93  Timing (in seconds)
% 8.52/2.93  ----------------------
% 8.72/2.93  Preprocessing        : 0.33
% 8.72/2.93  Parsing              : 0.18
% 8.72/2.93  CNF conversion       : 0.02
% 8.72/2.93  Main loop            : 1.81
% 8.72/2.93  Inferencing          : 0.54
% 8.72/2.93  Reduction            : 0.69
% 8.72/2.93  Demodulation         : 0.49
% 8.72/2.93  BG Simplification    : 0.07
% 8.72/2.93  Subsumption          : 0.38
% 8.72/2.93  Abstraction          : 0.08
% 8.72/2.93  MUC search           : 0.00
% 8.72/2.93  Cooper               : 0.00
% 8.72/2.93  Total                : 2.19
% 8.72/2.93  Index Insertion      : 0.00
% 8.72/2.94  Index Deletion       : 0.00
% 8.72/2.94  Index Matching       : 0.00
% 8.72/2.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
