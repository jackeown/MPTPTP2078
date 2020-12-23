%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:59 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 274 expanded)
%              Number of leaves         :   34 ( 110 expanded)
%              Depth                    :   11
%              Number of atoms          :  140 ( 588 expanded)
%              Number of equality atoms :   49 ( 164 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => k2_tops_1(A,k2_tops_1(A,k2_tops_1(A,B))) = k2_tops_1(A,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_tops_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,k2_tops_1(A,B)) = k2_tops_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l79_tops_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,k2_tops_1(A,k2_tops_1(A,B))) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l80_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_34,plain,(
    k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) != k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_26,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k2_tops_1(A_18,B_19),k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_237,plain,(
    ! [A_61,B_62] :
      ( m1_subset_1(k2_tops_1(A_61,B_62),k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24,plain,(
    ! [A_15,B_16,C_17] :
      ( k7_subset_1(A_15,B_16,C_17) = k4_xboole_0(B_16,C_17)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_543,plain,(
    ! [A_88,B_89,C_90] :
      ( k7_subset_1(u1_struct_0(A_88),k2_tops_1(A_88,B_89),C_90) = k4_xboole_0(k2_tops_1(A_88,B_89),C_90)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(resolution,[status(thm)],[c_237,c_24])).

tff(c_553,plain,(
    ! [C_90] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),C_90) = k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),C_90)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_543])).

tff(c_562,plain,(
    ! [C_90] : k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),C_90) = k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),C_90) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_553])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_421,plain,(
    ! [A_78,B_79] :
      ( k2_pre_topc(A_78,k2_tops_1(A_78,B_79)) = k2_tops_1(A_78,B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_431,plain,
    ( k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_421])).

tff(c_440,plain,(
    k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_431])).

tff(c_464,plain,(
    ! [A_82,B_83] :
      ( k7_subset_1(u1_struct_0(A_82),k2_pre_topc(A_82,B_83),k1_tops_1(A_82,B_83)) = k2_tops_1(A_82,B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_479,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_464])).

tff(c_492,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_479])).

tff(c_834,plain,
    ( k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_562,c_492])).

tff(c_835,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_834])).

tff(c_838,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_835])).

tff(c_842,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_838])).

tff(c_844,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_834])).

tff(c_377,plain,(
    ! [A_74,B_75] :
      ( k1_tops_1(A_74,k2_tops_1(A_74,k2_tops_1(A_74,B_75))) = k1_xboole_0
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_387,plain,
    ( k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_377])).

tff(c_396,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_387])).

tff(c_743,plain,(
    ! [A_107,B_108] :
      ( k2_pre_topc(A_107,k2_tops_1(A_107,k2_tops_1(A_107,B_108))) = k2_tops_1(A_107,k2_tops_1(A_107,B_108))
      | ~ v2_pre_topc(A_107)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_26,c_421])).

tff(c_753,plain,
    ( k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_743])).

tff(c_762,plain,(
    k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_753])).

tff(c_28,plain,(
    ! [A_20,B_22] :
      ( k7_subset_1(u1_struct_0(A_20),k2_pre_topc(A_20,B_22),k1_tops_1(A_20,B_22)) = k2_tops_1(A_20,B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_767,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_28])).

tff(c_771,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_xboole_0) = k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_396,c_767])).

tff(c_845,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_771])).

tff(c_891,plain,
    ( ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_845])).

tff(c_895,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_844,c_891])).

tff(c_897,plain,(
    m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_771])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = k1_xboole_0
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_54])).

tff(c_14,plain,(
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_10] : m1_subset_1(k2_subset_1(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_41,plain,(
    ! [A_10] : m1_subset_1(A_10,k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18])).

tff(c_102,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,B_45) = k3_subset_1(A_44,B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_108,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k3_subset_1(A_10,A_10) ),
    inference(resolution,[status(thm)],[c_41,c_102])).

tff(c_111,plain,(
    ! [A_10] : k3_subset_1(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_108])).

tff(c_119,plain,(
    ! [A_47,B_48] :
      ( k3_subset_1(A_47,k3_subset_1(A_47,B_48)) = B_48
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_123,plain,(
    ! [A_10] : k3_subset_1(A_10,k3_subset_1(A_10,A_10)) = A_10 ),
    inference(resolution,[status(thm)],[c_41,c_119])).

tff(c_126,plain,(
    ! [A_10] : k3_subset_1(A_10,k1_xboole_0) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_123])).

tff(c_154,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1(k3_subset_1(A_50,B_51),k1_zfmisc_1(A_50))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_168,plain,(
    ! [A_10] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10))
      | ~ m1_subset_1(A_10,k1_zfmisc_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_154])).

tff(c_175,plain,(
    ! [A_52] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_52)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_168])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = k3_subset_1(A_8,B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_180,plain,(
    ! [A_52] : k4_xboole_0(A_52,k1_xboole_0) = k3_subset_1(A_52,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_175,c_16])).

tff(c_184,plain,(
    ! [A_52] : k4_xboole_0(A_52,k1_xboole_0) = A_52 ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_180])).

tff(c_245,plain,(
    ! [A_61,B_62,C_17] :
      ( k7_subset_1(u1_struct_0(A_61),k2_tops_1(A_61,B_62),C_17) = k4_xboole_0(k2_tops_1(A_61,B_62),C_17)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_237,c_24])).

tff(c_903,plain,(
    ! [C_17] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),C_17) = k4_xboole_0(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),C_17)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_844,c_245])).

tff(c_927,plain,(
    ! [C_17] : k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),C_17) = k4_xboole_0(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),C_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_903])).

tff(c_488,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k1_xboole_0) = k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_464])).

tff(c_494,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k1_xboole_0) = k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_488])).

tff(c_1098,plain,(
    k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_897,c_184,c_927,c_762,c_494])).

tff(c_1099,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1098])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.62  
% 3.21/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.62  %$ r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.21/1.62  
% 3.21/1.62  %Foreground sorts:
% 3.21/1.62  
% 3.21/1.62  
% 3.21/1.62  %Background operators:
% 3.21/1.62  
% 3.21/1.62  
% 3.21/1.62  %Foreground operators:
% 3.21/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.21/1.62  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.21/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.21/1.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.21/1.62  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.21/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.21/1.62  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.21/1.62  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.21/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.21/1.62  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.21/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.21/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.21/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.62  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.21/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.21/1.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.21/1.62  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.21/1.62  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.21/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.62  
% 3.57/1.64  tff(f_98, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, k2_tops_1(A, k2_tops_1(A, B))) = k2_tops_1(A, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_tops_1)).
% 3.57/1.64  tff(f_63, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 3.57/1.64  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.57/1.64  tff(f_79, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, k2_tops_1(A, B)) = k2_tops_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l79_tops_1)).
% 3.57/1.64  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 3.57/1.64  tff(f_88, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, k2_tops_1(A, k2_tops_1(A, B))) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l80_tops_1)).
% 3.57/1.64  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.57/1.64  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.57/1.64  tff(f_39, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.57/1.64  tff(f_45, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.57/1.64  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.57/1.64  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.57/1.64  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.57/1.64  tff(c_34, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))!=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.57/1.64  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.57/1.64  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.57/1.64  tff(c_26, plain, (![A_18, B_19]: (m1_subset_1(k2_tops_1(A_18, B_19), k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.57/1.64  tff(c_237, plain, (![A_61, B_62]: (m1_subset_1(k2_tops_1(A_61, B_62), k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.57/1.64  tff(c_24, plain, (![A_15, B_16, C_17]: (k7_subset_1(A_15, B_16, C_17)=k4_xboole_0(B_16, C_17) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.57/1.64  tff(c_543, plain, (![A_88, B_89, C_90]: (k7_subset_1(u1_struct_0(A_88), k2_tops_1(A_88, B_89), C_90)=k4_xboole_0(k2_tops_1(A_88, B_89), C_90) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(resolution, [status(thm)], [c_237, c_24])).
% 3.57/1.64  tff(c_553, plain, (![C_90]: (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), C_90)=k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), C_90) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_543])).
% 3.57/1.64  tff(c_562, plain, (![C_90]: (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), C_90)=k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), C_90))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_553])).
% 3.57/1.64  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.57/1.64  tff(c_421, plain, (![A_78, B_79]: (k2_pre_topc(A_78, k2_tops_1(A_78, B_79))=k2_tops_1(A_78, B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.57/1.64  tff(c_431, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_421])).
% 3.57/1.64  tff(c_440, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_431])).
% 3.57/1.64  tff(c_464, plain, (![A_82, B_83]: (k7_subset_1(u1_struct_0(A_82), k2_pre_topc(A_82, B_83), k1_tops_1(A_82, B_83))=k2_tops_1(A_82, B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.57/1.64  tff(c_479, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_440, c_464])).
% 3.57/1.64  tff(c_492, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_479])).
% 3.57/1.64  tff(c_834, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_562, c_492])).
% 3.57/1.64  tff(c_835, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_834])).
% 3.57/1.64  tff(c_838, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_835])).
% 3.57/1.64  tff(c_842, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_838])).
% 3.57/1.64  tff(c_844, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_834])).
% 3.57/1.64  tff(c_377, plain, (![A_74, B_75]: (k1_tops_1(A_74, k2_tops_1(A_74, k2_tops_1(A_74, B_75)))=k1_xboole_0 | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.57/1.64  tff(c_387, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k1_xboole_0 | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_377])).
% 3.57/1.64  tff(c_396, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_387])).
% 3.57/1.64  tff(c_743, plain, (![A_107, B_108]: (k2_pre_topc(A_107, k2_tops_1(A_107, k2_tops_1(A_107, B_108)))=k2_tops_1(A_107, k2_tops_1(A_107, B_108)) | ~v2_pre_topc(A_107) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(resolution, [status(thm)], [c_26, c_421])).
% 3.57/1.64  tff(c_753, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_743])).
% 3.57/1.64  tff(c_762, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_753])).
% 3.57/1.64  tff(c_28, plain, (![A_20, B_22]: (k7_subset_1(u1_struct_0(A_20), k2_pre_topc(A_20, B_22), k1_tops_1(A_20, B_22))=k2_tops_1(A_20, B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.57/1.64  tff(c_767, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_762, c_28])).
% 3.57/1.64  tff(c_771, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_xboole_0)=k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_396, c_767])).
% 3.57/1.64  tff(c_845, plain, (~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_771])).
% 3.57/1.64  tff(c_891, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_845])).
% 3.57/1.64  tff(c_895, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_844, c_891])).
% 3.57/1.64  tff(c_897, plain, (m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_771])).
% 3.57/1.64  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.57/1.64  tff(c_54, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=k1_xboole_0 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.57/1.64  tff(c_58, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_54])).
% 3.57/1.64  tff(c_14, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.57/1.64  tff(c_18, plain, (![A_10]: (m1_subset_1(k2_subset_1(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.57/1.64  tff(c_41, plain, (![A_10]: (m1_subset_1(A_10, k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_18])).
% 3.57/1.64  tff(c_102, plain, (![A_44, B_45]: (k4_xboole_0(A_44, B_45)=k3_subset_1(A_44, B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.57/1.64  tff(c_108, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k3_subset_1(A_10, A_10))), inference(resolution, [status(thm)], [c_41, c_102])).
% 3.57/1.64  tff(c_111, plain, (![A_10]: (k3_subset_1(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_108])).
% 3.57/1.64  tff(c_119, plain, (![A_47, B_48]: (k3_subset_1(A_47, k3_subset_1(A_47, B_48))=B_48 | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.57/1.64  tff(c_123, plain, (![A_10]: (k3_subset_1(A_10, k3_subset_1(A_10, A_10))=A_10)), inference(resolution, [status(thm)], [c_41, c_119])).
% 3.57/1.64  tff(c_126, plain, (![A_10]: (k3_subset_1(A_10, k1_xboole_0)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_111, c_123])).
% 3.57/1.64  tff(c_154, plain, (![A_50, B_51]: (m1_subset_1(k3_subset_1(A_50, B_51), k1_zfmisc_1(A_50)) | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.57/1.64  tff(c_168, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)) | ~m1_subset_1(A_10, k1_zfmisc_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_111, c_154])).
% 3.57/1.64  tff(c_175, plain, (![A_52]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_52)))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_168])).
% 3.57/1.64  tff(c_16, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=k3_subset_1(A_8, B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.57/1.64  tff(c_180, plain, (![A_52]: (k4_xboole_0(A_52, k1_xboole_0)=k3_subset_1(A_52, k1_xboole_0))), inference(resolution, [status(thm)], [c_175, c_16])).
% 3.57/1.64  tff(c_184, plain, (![A_52]: (k4_xboole_0(A_52, k1_xboole_0)=A_52)), inference(demodulation, [status(thm), theory('equality')], [c_126, c_180])).
% 3.57/1.64  tff(c_245, plain, (![A_61, B_62, C_17]: (k7_subset_1(u1_struct_0(A_61), k2_tops_1(A_61, B_62), C_17)=k4_xboole_0(k2_tops_1(A_61, B_62), C_17) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_237, c_24])).
% 3.57/1.64  tff(c_903, plain, (![C_17]: (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), C_17)=k4_xboole_0(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), C_17) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_844, c_245])).
% 3.57/1.64  tff(c_927, plain, (![C_17]: (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), C_17)=k4_xboole_0(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), C_17))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_903])).
% 3.57/1.64  tff(c_488, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k1_xboole_0)=k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_396, c_464])).
% 3.57/1.64  tff(c_494, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k1_xboole_0)=k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_488])).
% 3.57/1.64  tff(c_1098, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_897, c_184, c_927, c_762, c_494])).
% 3.57/1.64  tff(c_1099, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1098])).
% 3.57/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.64  
% 3.57/1.64  Inference rules
% 3.57/1.64  ----------------------
% 3.57/1.64  #Ref     : 0
% 3.57/1.64  #Sup     : 255
% 3.57/1.64  #Fact    : 0
% 3.57/1.64  #Define  : 0
% 3.57/1.64  #Split   : 5
% 3.57/1.64  #Chain   : 0
% 3.57/1.64  #Close   : 0
% 3.57/1.64  
% 3.57/1.64  Ordering : KBO
% 3.57/1.64  
% 3.57/1.64  Simplification rules
% 3.57/1.64  ----------------------
% 3.57/1.64  #Subsume      : 9
% 3.57/1.64  #Demod        : 172
% 3.57/1.64  #Tautology    : 140
% 3.57/1.64  #SimpNegUnit  : 1
% 3.57/1.64  #BackRed      : 0
% 3.57/1.64  
% 3.57/1.64  #Partial instantiations: 0
% 3.57/1.64  #Strategies tried      : 1
% 3.57/1.64  
% 3.57/1.64  Timing (in seconds)
% 3.57/1.64  ----------------------
% 3.57/1.64  Preprocessing        : 0.33
% 3.57/1.64  Parsing              : 0.17
% 3.57/1.64  CNF conversion       : 0.02
% 3.57/1.64  Main loop            : 0.45
% 3.57/1.64  Inferencing          : 0.17
% 3.57/1.64  Reduction            : 0.15
% 3.57/1.64  Demodulation         : 0.11
% 3.57/1.64  BG Simplification    : 0.02
% 3.57/1.64  Subsumption          : 0.08
% 3.57/1.64  Abstraction          : 0.03
% 3.57/1.64  MUC search           : 0.00
% 3.57/1.64  Cooper               : 0.00
% 3.57/1.64  Total                : 0.82
% 3.57/1.64  Index Insertion      : 0.00
% 3.57/1.64  Index Deletion       : 0.00
% 3.57/1.64  Index Matching       : 0.00
% 3.57/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
