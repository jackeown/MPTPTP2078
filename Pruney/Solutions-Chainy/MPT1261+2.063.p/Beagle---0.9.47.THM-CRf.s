%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:20 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 158 expanded)
%              Number of leaves         :   36 (  70 expanded)
%              Depth                    :    9
%              Number of atoms          :  137 ( 309 expanded)
%              Number of equality atoms :   53 (  94 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_716,plain,(
    ! [A_110,B_111,C_112] :
      ( k7_subset_1(A_110,B_111,C_112) = k4_xboole_0(B_111,C_112)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(A_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_719,plain,(
    ! [C_112] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_112) = k4_xboole_0('#skF_2',C_112) ),
    inference(resolution,[status(thm)],[c_28,c_716])).

tff(c_34,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_119,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_414,plain,(
    ! [A_75,B_76] :
      ( k4_subset_1(u1_struct_0(A_75),B_76,k2_tops_1(A_75,B_76)) = k2_pre_topc(A_75,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_418,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_414])).

tff(c_422,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_418])).

tff(c_280,plain,(
    ! [A_57,B_58,C_59] :
      ( k7_subset_1(A_57,B_58,C_59) = k4_xboole_0(B_58,C_59)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_284,plain,(
    ! [C_60] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_60) = k4_xboole_0('#skF_2',C_60) ),
    inference(resolution,[status(thm)],[c_28,c_280])).

tff(c_40,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_262,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_40])).

tff(c_290,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_262])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_75,plain,(
    ! [A_37,B_38] :
      ( k2_xboole_0(A_37,B_38) = B_38
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_79,plain,(
    ! [A_5,B_6] : k2_xboole_0(k4_xboole_0(A_5,B_6),A_5) = A_5 ),
    inference(resolution,[status(thm)],[c_6,c_75])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_89,plain,(
    ! [A_41,B_42] : k3_tarski(k2_tarski(A_41,B_42)) = k2_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_192,plain,(
    ! [A_51,B_52] : k3_tarski(k2_tarski(A_51,B_52)) = k2_xboole_0(B_52,A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_89])).

tff(c_10,plain,(
    ! [A_9,B_10] : k3_tarski(k2_tarski(A_9,B_10)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_215,plain,(
    ! [B_53,A_54] : k2_xboole_0(B_53,A_54) = k2_xboole_0(A_54,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_10])).

tff(c_253,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = A_5 ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_215])).

tff(c_302,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_253])).

tff(c_18,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k2_tops_1(A_19,B_20),k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_383,plain,(
    ! [A_67,B_68,C_69] :
      ( k4_subset_1(A_67,B_68,C_69) = k2_xboole_0(B_68,C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(A_67))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_504,plain,(
    ! [A_92,B_93,B_94] :
      ( k4_subset_1(u1_struct_0(A_92),B_93,k2_tops_1(A_92,B_94)) = k2_xboole_0(B_93,k2_tops_1(A_92,B_94))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_18,c_383])).

tff(c_508,plain,(
    ! [B_94] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_94)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_94))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_504])).

tff(c_513,plain,(
    ! [B_95] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_95)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_95))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_508])).

tff(c_520,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_513])).

tff(c_525,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_302,c_520])).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_373,plain,(
    ! [A_65,B_66] :
      ( v4_pre_topc(k2_pre_topc(A_65,B_66),A_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_377,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_373])).

tff(c_381,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_377])).

tff(c_527,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_381])).

tff(c_529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_527])).

tff(c_530,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_720,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_530])).

tff(c_800,plain,(
    ! [A_124,B_125] :
      ( k4_subset_1(u1_struct_0(A_124),B_125,k2_tops_1(A_124,B_125)) = k2_pre_topc(A_124,B_125)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_804,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_800])).

tff(c_808,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_804])).

tff(c_531,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_743,plain,(
    ! [A_118,B_119] :
      ( r1_tarski(k2_tops_1(A_118,B_119),B_119)
      | ~ v4_pre_topc(B_119,A_118)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_747,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_743])).

tff(c_751,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_531,c_747])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_755,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_751,c_4])).

tff(c_604,plain,(
    ! [B_102,A_103] : k3_tarski(k2_tarski(B_102,A_103)) = k2_xboole_0(A_103,B_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_89])).

tff(c_610,plain,(
    ! [B_102,A_103] : k2_xboole_0(B_102,A_103) = k2_xboole_0(A_103,B_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_604,c_10])).

tff(c_759,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_755,c_610])).

tff(c_779,plain,(
    ! [A_120,B_121,C_122] :
      ( k4_subset_1(A_120,B_121,C_122) = k2_xboole_0(B_121,C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(A_120))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(A_120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_891,plain,(
    ! [A_143,B_144,B_145] :
      ( k4_subset_1(u1_struct_0(A_143),B_144,k2_tops_1(A_143,B_145)) = k2_xboole_0(B_144,k2_tops_1(A_143,B_145))
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143) ) ),
    inference(resolution,[status(thm)],[c_18,c_779])).

tff(c_895,plain,(
    ! [B_145] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_145)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_145))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_891])).

tff(c_900,plain,(
    ! [B_146] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_146)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_146))
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_895])).

tff(c_907,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_900])).

tff(c_912,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_759,c_907])).

tff(c_22,plain,(
    ! [A_23,B_25] :
      ( k7_subset_1(u1_struct_0(A_23),k2_pre_topc(A_23,B_25),k1_tops_1(A_23,B_25)) = k2_tops_1(A_23,B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_919,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_912,c_22])).

tff(c_923,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_719,c_919])).

tff(c_925,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_720,c_923])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:00:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.51  
% 3.14/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.51  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 3.14/1.51  
% 3.14/1.51  %Foreground sorts:
% 3.14/1.51  
% 3.14/1.51  
% 3.14/1.51  %Background operators:
% 3.14/1.51  
% 3.14/1.51  
% 3.14/1.51  %Foreground operators:
% 3.14/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.14/1.51  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.14/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.14/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.14/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.14/1.51  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.14/1.51  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.14/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.14/1.51  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.14/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.14/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.51  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.14/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.14/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.14/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.14/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.14/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.14/1.51  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.14/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.51  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.14/1.51  
% 3.23/1.53  tff(f_98, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 3.23/1.53  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.23/1.53  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 3.23/1.53  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.23/1.53  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.23/1.53  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.23/1.53  tff(f_37, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.23/1.53  tff(f_55, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 3.23/1.53  tff(f_43, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.23/1.53  tff(f_63, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 3.23/1.53  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 3.23/1.53  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 3.23/1.53  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.23/1.53  tff(c_716, plain, (![A_110, B_111, C_112]: (k7_subset_1(A_110, B_111, C_112)=k4_xboole_0(B_111, C_112) | ~m1_subset_1(B_111, k1_zfmisc_1(A_110)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.23/1.53  tff(c_719, plain, (![C_112]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_112)=k4_xboole_0('#skF_2', C_112))), inference(resolution, [status(thm)], [c_28, c_716])).
% 3.23/1.53  tff(c_34, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.23/1.53  tff(c_119, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_34])).
% 3.23/1.53  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.23/1.53  tff(c_414, plain, (![A_75, B_76]: (k4_subset_1(u1_struct_0(A_75), B_76, k2_tops_1(A_75, B_76))=k2_pre_topc(A_75, B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.23/1.53  tff(c_418, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_414])).
% 3.23/1.53  tff(c_422, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_418])).
% 3.23/1.53  tff(c_280, plain, (![A_57, B_58, C_59]: (k7_subset_1(A_57, B_58, C_59)=k4_xboole_0(B_58, C_59) | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.23/1.53  tff(c_284, plain, (![C_60]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_60)=k4_xboole_0('#skF_2', C_60))), inference(resolution, [status(thm)], [c_28, c_280])).
% 3.23/1.53  tff(c_40, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.23/1.53  tff(c_262, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_119, c_40])).
% 3.23/1.53  tff(c_290, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_284, c_262])).
% 3.23/1.53  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.23/1.53  tff(c_75, plain, (![A_37, B_38]: (k2_xboole_0(A_37, B_38)=B_38 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.53  tff(c_79, plain, (![A_5, B_6]: (k2_xboole_0(k4_xboole_0(A_5, B_6), A_5)=A_5)), inference(resolution, [status(thm)], [c_6, c_75])).
% 3.23/1.53  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.23/1.53  tff(c_89, plain, (![A_41, B_42]: (k3_tarski(k2_tarski(A_41, B_42))=k2_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.23/1.53  tff(c_192, plain, (![A_51, B_52]: (k3_tarski(k2_tarski(A_51, B_52))=k2_xboole_0(B_52, A_51))), inference(superposition, [status(thm), theory('equality')], [c_8, c_89])).
% 3.23/1.53  tff(c_10, plain, (![A_9, B_10]: (k3_tarski(k2_tarski(A_9, B_10))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.23/1.53  tff(c_215, plain, (![B_53, A_54]: (k2_xboole_0(B_53, A_54)=k2_xboole_0(A_54, B_53))), inference(superposition, [status(thm), theory('equality')], [c_192, c_10])).
% 3.23/1.53  tff(c_253, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(A_5, B_6))=A_5)), inference(superposition, [status(thm), theory('equality')], [c_79, c_215])).
% 3.23/1.53  tff(c_302, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_290, c_253])).
% 3.23/1.53  tff(c_18, plain, (![A_19, B_20]: (m1_subset_1(k2_tops_1(A_19, B_20), k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.23/1.53  tff(c_383, plain, (![A_67, B_68, C_69]: (k4_subset_1(A_67, B_68, C_69)=k2_xboole_0(B_68, C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(A_67)) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.23/1.53  tff(c_504, plain, (![A_92, B_93, B_94]: (k4_subset_1(u1_struct_0(A_92), B_93, k2_tops_1(A_92, B_94))=k2_xboole_0(B_93, k2_tops_1(A_92, B_94)) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(resolution, [status(thm)], [c_18, c_383])).
% 3.23/1.53  tff(c_508, plain, (![B_94]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_94))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_94)) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_504])).
% 3.23/1.53  tff(c_513, plain, (![B_95]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_95))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_95)) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_508])).
% 3.23/1.53  tff(c_520, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_513])).
% 3.23/1.53  tff(c_525, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_422, c_302, c_520])).
% 3.23/1.53  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.23/1.53  tff(c_373, plain, (![A_65, B_66]: (v4_pre_topc(k2_pre_topc(A_65, B_66), A_65) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.23/1.53  tff(c_377, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_373])).
% 3.23/1.53  tff(c_381, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_377])).
% 3.23/1.53  tff(c_527, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_525, c_381])).
% 3.23/1.53  tff(c_529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_527])).
% 3.23/1.53  tff(c_530, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_34])).
% 3.23/1.53  tff(c_720, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_719, c_530])).
% 3.23/1.53  tff(c_800, plain, (![A_124, B_125]: (k4_subset_1(u1_struct_0(A_124), B_125, k2_tops_1(A_124, B_125))=k2_pre_topc(A_124, B_125) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.23/1.53  tff(c_804, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_800])).
% 3.23/1.53  tff(c_808, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_804])).
% 3.23/1.53  tff(c_531, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 3.23/1.53  tff(c_743, plain, (![A_118, B_119]: (r1_tarski(k2_tops_1(A_118, B_119), B_119) | ~v4_pre_topc(B_119, A_118) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.23/1.53  tff(c_747, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_743])).
% 3.23/1.53  tff(c_751, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_531, c_747])).
% 3.23/1.53  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.53  tff(c_755, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_751, c_4])).
% 3.23/1.53  tff(c_604, plain, (![B_102, A_103]: (k3_tarski(k2_tarski(B_102, A_103))=k2_xboole_0(A_103, B_102))), inference(superposition, [status(thm), theory('equality')], [c_8, c_89])).
% 3.23/1.53  tff(c_610, plain, (![B_102, A_103]: (k2_xboole_0(B_102, A_103)=k2_xboole_0(A_103, B_102))), inference(superposition, [status(thm), theory('equality')], [c_604, c_10])).
% 3.23/1.53  tff(c_759, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_755, c_610])).
% 3.23/1.53  tff(c_779, plain, (![A_120, B_121, C_122]: (k4_subset_1(A_120, B_121, C_122)=k2_xboole_0(B_121, C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(A_120)) | ~m1_subset_1(B_121, k1_zfmisc_1(A_120)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.23/1.53  tff(c_891, plain, (![A_143, B_144, B_145]: (k4_subset_1(u1_struct_0(A_143), B_144, k2_tops_1(A_143, B_145))=k2_xboole_0(B_144, k2_tops_1(A_143, B_145)) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_143))) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143))), inference(resolution, [status(thm)], [c_18, c_779])).
% 3.23/1.53  tff(c_895, plain, (![B_145]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_145))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_145)) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_891])).
% 3.23/1.53  tff(c_900, plain, (![B_146]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_146))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_146)) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_895])).
% 3.23/1.53  tff(c_907, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_900])).
% 3.23/1.53  tff(c_912, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_808, c_759, c_907])).
% 3.23/1.53  tff(c_22, plain, (![A_23, B_25]: (k7_subset_1(u1_struct_0(A_23), k2_pre_topc(A_23, B_25), k1_tops_1(A_23, B_25))=k2_tops_1(A_23, B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.23/1.53  tff(c_919, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_912, c_22])).
% 3.23/1.53  tff(c_923, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_719, c_919])).
% 3.23/1.53  tff(c_925, plain, $false, inference(negUnitSimplification, [status(thm)], [c_720, c_923])).
% 3.23/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.53  
% 3.23/1.53  Inference rules
% 3.23/1.53  ----------------------
% 3.23/1.53  #Ref     : 0
% 3.23/1.53  #Sup     : 215
% 3.23/1.53  #Fact    : 0
% 3.23/1.53  #Define  : 0
% 3.23/1.53  #Split   : 1
% 3.23/1.53  #Chain   : 0
% 3.23/1.53  #Close   : 0
% 3.23/1.53  
% 3.23/1.53  Ordering : KBO
% 3.23/1.53  
% 3.23/1.53  Simplification rules
% 3.23/1.53  ----------------------
% 3.23/1.53  #Subsume      : 9
% 3.23/1.53  #Demod        : 73
% 3.23/1.53  #Tautology    : 152
% 3.23/1.53  #SimpNegUnit  : 3
% 3.23/1.53  #BackRed      : 5
% 3.23/1.53  
% 3.23/1.53  #Partial instantiations: 0
% 3.23/1.53  #Strategies tried      : 1
% 3.23/1.53  
% 3.23/1.53  Timing (in seconds)
% 3.23/1.53  ----------------------
% 3.23/1.53  Preprocessing        : 0.35
% 3.23/1.53  Parsing              : 0.18
% 3.23/1.53  CNF conversion       : 0.02
% 3.23/1.53  Main loop            : 0.38
% 3.23/1.53  Inferencing          : 0.15
% 3.23/1.53  Reduction            : 0.12
% 3.23/1.53  Demodulation         : 0.09
% 3.23/1.53  BG Simplification    : 0.02
% 3.23/1.53  Subsumption          : 0.06
% 3.23/1.53  Abstraction          : 0.02
% 3.23/1.53  MUC search           : 0.00
% 3.23/1.53  Cooper               : 0.00
% 3.23/1.53  Total                : 0.76
% 3.23/1.53  Index Insertion      : 0.00
% 3.23/1.53  Index Deletion       : 0.00
% 3.23/1.53  Index Matching       : 0.00
% 3.23/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
