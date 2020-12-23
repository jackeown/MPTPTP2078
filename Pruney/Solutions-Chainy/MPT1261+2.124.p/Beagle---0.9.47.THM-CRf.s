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

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 141 expanded)
%              Number of leaves         :   30 (  61 expanded)
%              Depth                    :    9
%              Number of atoms          :  130 ( 297 expanded)
%              Number of equality atoms :   46 (  83 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_342,plain,(
    ! [A_74,B_75,C_76] :
      ( k7_subset_1(A_74,B_75,C_76) = k4_xboole_0(B_75,C_76)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_345,plain,(
    ! [C_76] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_76) = k4_xboole_0('#skF_2',C_76) ),
    inference(resolution,[status(thm)],[c_22,c_342])).

tff(c_34,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_107,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_28,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_134,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_28])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_239,plain,(
    ! [A_54,B_55] :
      ( k4_subset_1(u1_struct_0(A_54),B_55,k2_tops_1(A_54,B_55)) = k2_pre_topc(A_54,B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_243,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_239])).

tff(c_247,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_243])).

tff(c_114,plain,(
    ! [A_37,B_38,C_39] :
      ( k7_subset_1(A_37,B_38,C_39) = k4_xboole_0(B_38,C_39)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_118,plain,(
    ! [C_40] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_40) = k4_xboole_0('#skF_2',C_40) ),
    inference(resolution,[status(thm)],[c_22,c_114])).

tff(c_124,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_107])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_69,plain,(
    ! [A_31,B_32] :
      ( k2_xboole_0(A_31,B_32) = B_32
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [A_33,B_34] : k2_xboole_0(k4_xboole_0(A_33,B_34),A_33) = A_33 ),
    inference(resolution,[status(thm)],[c_6,c_69])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_80,plain,(
    ! [A_33,B_34] : k2_xboole_0(A_33,k4_xboole_0(A_33,B_34)) = A_33 ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_2])).

tff(c_138,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_80])).

tff(c_12,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k2_tops_1(A_13,B_14),k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_191,plain,(
    ! [A_45,B_46,C_47] :
      ( k4_subset_1(A_45,B_46,C_47) = k2_xboole_0(B_46,C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(A_45))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_312,plain,(
    ! [A_70,B_71,B_72] :
      ( k4_subset_1(u1_struct_0(A_70),B_71,k2_tops_1(A_70,B_72)) = k2_xboole_0(B_71,k2_tops_1(A_70,B_72))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_12,c_191])).

tff(c_316,plain,(
    ! [B_72] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_72)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_72))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_312])).

tff(c_321,plain,(
    ! [B_73] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_73)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_73))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_316])).

tff(c_328,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_321])).

tff(c_333,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_138,c_328])).

tff(c_26,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_182,plain,(
    ! [A_43,B_44] :
      ( v4_pre_topc(k2_pre_topc(A_43,B_44),A_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_186,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_182])).

tff(c_190,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_186])).

tff(c_335,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_190])).

tff(c_337,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_335])).

tff(c_339,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_348,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_339])).

tff(c_428,plain,(
    ! [A_88,B_89] :
      ( k4_subset_1(u1_struct_0(A_88),B_89,k2_tops_1(A_88,B_89)) = k2_pre_topc(A_88,B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_432,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_428])).

tff(c_436,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_432])).

tff(c_338,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_392,plain,(
    ! [A_86,B_87] :
      ( r1_tarski(k2_tops_1(A_86,B_87),B_87)
      | ~ v4_pre_topc(B_87,A_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_396,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_392])).

tff(c_400,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_338,c_396])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_404,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_400,c_4])).

tff(c_408,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_2])).

tff(c_371,plain,(
    ! [A_82,B_83,C_84] :
      ( k4_subset_1(A_82,B_83,C_84) = k2_xboole_0(B_83,C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(A_82))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_519,plain,(
    ! [A_107,B_108,B_109] :
      ( k4_subset_1(u1_struct_0(A_107),B_108,k2_tops_1(A_107,B_109)) = k2_xboole_0(B_108,k2_tops_1(A_107,B_109))
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_12,c_371])).

tff(c_523,plain,(
    ! [B_109] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_109)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_109))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_519])).

tff(c_528,plain,(
    ! [B_110] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_110)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_110))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_523])).

tff(c_535,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_528])).

tff(c_540,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_408,c_535])).

tff(c_16,plain,(
    ! [A_17,B_19] :
      ( k7_subset_1(u1_struct_0(A_17),k2_pre_topc(A_17,B_19),k1_tops_1(A_17,B_19)) = k2_tops_1(A_17,B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_547,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_16])).

tff(c_551,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_345,c_547])).

tff(c_553,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_348,c_551])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:17:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.47  
% 2.66/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.47  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.66/1.47  
% 2.66/1.47  %Foreground sorts:
% 2.66/1.47  
% 2.66/1.47  
% 2.66/1.47  %Background operators:
% 2.66/1.47  
% 2.66/1.47  
% 2.66/1.47  %Foreground operators:
% 2.66/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.66/1.47  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.66/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.66/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.47  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.66/1.47  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.66/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.66/1.47  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.66/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.66/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.66/1.47  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.66/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.66/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.66/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.66/1.47  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.66/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.47  
% 2.81/1.49  tff(f_92, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 2.81/1.49  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.81/1.49  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 2.81/1.49  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.81/1.49  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.81/1.49  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.81/1.49  tff(f_49, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 2.81/1.49  tff(f_39, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.81/1.49  tff(f_57, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 2.81/1.49  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 2.81/1.49  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 2.81/1.49  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.81/1.49  tff(c_342, plain, (![A_74, B_75, C_76]: (k7_subset_1(A_74, B_75, C_76)=k4_xboole_0(B_75, C_76) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.81/1.49  tff(c_345, plain, (![C_76]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_76)=k4_xboole_0('#skF_2', C_76))), inference(resolution, [status(thm)], [c_22, c_342])).
% 2.81/1.49  tff(c_34, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.81/1.49  tff(c_107, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_34])).
% 2.81/1.49  tff(c_28, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.81/1.49  tff(c_134, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_28])).
% 2.81/1.49  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.81/1.49  tff(c_239, plain, (![A_54, B_55]: (k4_subset_1(u1_struct_0(A_54), B_55, k2_tops_1(A_54, B_55))=k2_pre_topc(A_54, B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.81/1.49  tff(c_243, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_239])).
% 2.81/1.49  tff(c_247, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_243])).
% 2.81/1.49  tff(c_114, plain, (![A_37, B_38, C_39]: (k7_subset_1(A_37, B_38, C_39)=k4_xboole_0(B_38, C_39) | ~m1_subset_1(B_38, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.81/1.49  tff(c_118, plain, (![C_40]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_40)=k4_xboole_0('#skF_2', C_40))), inference(resolution, [status(thm)], [c_22, c_114])).
% 2.81/1.49  tff(c_124, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_118, c_107])).
% 2.81/1.49  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.81/1.49  tff(c_69, plain, (![A_31, B_32]: (k2_xboole_0(A_31, B_32)=B_32 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.81/1.49  tff(c_74, plain, (![A_33, B_34]: (k2_xboole_0(k4_xboole_0(A_33, B_34), A_33)=A_33)), inference(resolution, [status(thm)], [c_6, c_69])).
% 2.81/1.49  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.81/1.49  tff(c_80, plain, (![A_33, B_34]: (k2_xboole_0(A_33, k4_xboole_0(A_33, B_34))=A_33)), inference(superposition, [status(thm), theory('equality')], [c_74, c_2])).
% 2.81/1.49  tff(c_138, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_124, c_80])).
% 2.81/1.49  tff(c_12, plain, (![A_13, B_14]: (m1_subset_1(k2_tops_1(A_13, B_14), k1_zfmisc_1(u1_struct_0(A_13))) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.81/1.49  tff(c_191, plain, (![A_45, B_46, C_47]: (k4_subset_1(A_45, B_46, C_47)=k2_xboole_0(B_46, C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(A_45)) | ~m1_subset_1(B_46, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.81/1.49  tff(c_312, plain, (![A_70, B_71, B_72]: (k4_subset_1(u1_struct_0(A_70), B_71, k2_tops_1(A_70, B_72))=k2_xboole_0(B_71, k2_tops_1(A_70, B_72)) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(resolution, [status(thm)], [c_12, c_191])).
% 2.81/1.49  tff(c_316, plain, (![B_72]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_72))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_72)) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_312])).
% 2.81/1.49  tff(c_321, plain, (![B_73]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_73))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_73)) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_316])).
% 2.81/1.49  tff(c_328, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_321])).
% 2.81/1.49  tff(c_333, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_247, c_138, c_328])).
% 2.81/1.49  tff(c_26, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.81/1.49  tff(c_182, plain, (![A_43, B_44]: (v4_pre_topc(k2_pre_topc(A_43, B_44), A_43) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43) | ~v2_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.81/1.49  tff(c_186, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_182])).
% 2.81/1.49  tff(c_190, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_186])).
% 2.81/1.49  tff(c_335, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_333, c_190])).
% 2.81/1.49  tff(c_337, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_335])).
% 2.81/1.49  tff(c_339, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_34])).
% 2.81/1.49  tff(c_348, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_345, c_339])).
% 2.81/1.49  tff(c_428, plain, (![A_88, B_89]: (k4_subset_1(u1_struct_0(A_88), B_89, k2_tops_1(A_88, B_89))=k2_pre_topc(A_88, B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.81/1.49  tff(c_432, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_428])).
% 2.81/1.49  tff(c_436, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_432])).
% 2.81/1.49  tff(c_338, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 2.81/1.49  tff(c_392, plain, (![A_86, B_87]: (r1_tarski(k2_tops_1(A_86, B_87), B_87) | ~v4_pre_topc(B_87, A_86) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.81/1.49  tff(c_396, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_392])).
% 2.81/1.49  tff(c_400, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_338, c_396])).
% 2.81/1.49  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.81/1.49  tff(c_404, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_400, c_4])).
% 2.81/1.49  tff(c_408, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_404, c_2])).
% 2.81/1.49  tff(c_371, plain, (![A_82, B_83, C_84]: (k4_subset_1(A_82, B_83, C_84)=k2_xboole_0(B_83, C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(A_82)) | ~m1_subset_1(B_83, k1_zfmisc_1(A_82)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.81/1.49  tff(c_519, plain, (![A_107, B_108, B_109]: (k4_subset_1(u1_struct_0(A_107), B_108, k2_tops_1(A_107, B_109))=k2_xboole_0(B_108, k2_tops_1(A_107, B_109)) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(resolution, [status(thm)], [c_12, c_371])).
% 2.81/1.49  tff(c_523, plain, (![B_109]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_109))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_109)) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_519])).
% 2.81/1.49  tff(c_528, plain, (![B_110]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_110))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_110)) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_523])).
% 2.81/1.49  tff(c_535, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_528])).
% 2.81/1.49  tff(c_540, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_436, c_408, c_535])).
% 2.81/1.49  tff(c_16, plain, (![A_17, B_19]: (k7_subset_1(u1_struct_0(A_17), k2_pre_topc(A_17, B_19), k1_tops_1(A_17, B_19))=k2_tops_1(A_17, B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.81/1.49  tff(c_547, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_540, c_16])).
% 2.81/1.49  tff(c_551, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_345, c_547])).
% 2.81/1.49  tff(c_553, plain, $false, inference(negUnitSimplification, [status(thm)], [c_348, c_551])).
% 2.81/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.49  
% 2.81/1.49  Inference rules
% 2.81/1.49  ----------------------
% 2.81/1.49  #Ref     : 0
% 2.81/1.49  #Sup     : 125
% 2.81/1.49  #Fact    : 0
% 2.81/1.49  #Define  : 0
% 2.81/1.49  #Split   : 1
% 2.81/1.49  #Chain   : 0
% 2.81/1.49  #Close   : 0
% 2.81/1.49  
% 2.81/1.49  Ordering : KBO
% 2.81/1.49  
% 2.81/1.49  Simplification rules
% 2.81/1.49  ----------------------
% 2.81/1.49  #Subsume      : 6
% 2.81/1.49  #Demod        : 55
% 2.81/1.49  #Tautology    : 74
% 2.81/1.49  #SimpNegUnit  : 2
% 2.81/1.49  #BackRed      : 5
% 2.81/1.49  
% 2.81/1.49  #Partial instantiations: 0
% 2.81/1.49  #Strategies tried      : 1
% 2.81/1.49  
% 2.81/1.49  Timing (in seconds)
% 2.81/1.49  ----------------------
% 2.81/1.49  Preprocessing        : 0.33
% 2.81/1.49  Parsing              : 0.18
% 2.81/1.49  CNF conversion       : 0.02
% 2.81/1.49  Main loop            : 0.30
% 2.81/1.49  Inferencing          : 0.12
% 2.81/1.49  Reduction            : 0.10
% 2.81/1.49  Demodulation         : 0.07
% 2.81/1.49  BG Simplification    : 0.02
% 2.81/1.49  Subsumption          : 0.05
% 2.81/1.49  Abstraction          : 0.02
% 2.81/1.49  MUC search           : 0.00
% 2.81/1.49  Cooper               : 0.00
% 2.81/1.49  Total                : 0.67
% 2.81/1.49  Index Insertion      : 0.00
% 2.81/1.49  Index Deletion       : 0.00
% 2.81/1.49  Index Matching       : 0.00
% 2.81/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
