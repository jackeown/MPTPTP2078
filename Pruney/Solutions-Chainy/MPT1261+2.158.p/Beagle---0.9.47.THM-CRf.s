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
% DateTime   : Thu Dec  3 10:21:34 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 296 expanded)
%              Number of leaves         :   38 ( 114 expanded)
%              Depth                    :   15
%              Number of atoms          :  159 ( 644 expanded)
%              Number of equality atoms :   47 ( 155 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_78,axiom,(
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

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1277,plain,(
    ! [A_141,B_142,C_143] :
      ( k7_subset_1(A_141,B_142,C_143) = k4_xboole_0(B_142,C_143)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(A_141)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1285,plain,(
    ! [C_143] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_143) = k4_xboole_0('#skF_2',C_143) ),
    inference(resolution,[status(thm)],[c_42,c_1277])).

tff(c_128,plain,(
    ! [A_59,B_60,C_61] :
      ( k7_subset_1(A_59,B_60,C_61) = k4_xboole_0(B_60,C_61)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_147,plain,(
    ! [C_64] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_64) = k4_xboole_0('#skF_2',C_64) ),
    inference(resolution,[status(thm)],[c_42,c_128])).

tff(c_54,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_79,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_153,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_79])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_176,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_10])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_48,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_123,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_597,plain,(
    ! [B_107,A_108] :
      ( v4_pre_topc(B_107,A_108)
      | k2_pre_topc(A_108,B_107) != B_107
      | ~ v2_pre_topc(A_108)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_614,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_597])).

tff(c_627,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_614])).

tff(c_628,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_627])).

tff(c_759,plain,(
    ! [A_110,B_111] :
      ( k4_subset_1(u1_struct_0(A_110),B_111,k2_tops_1(A_110,B_111)) = k2_pre_topc(A_110,B_111)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_771,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_759])).

tff(c_783,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_771])).

tff(c_34,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(k2_tops_1(A_27,B_28),k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_405,plain,(
    ! [A_100,B_101,C_102] :
      ( m1_subset_1(k4_subset_1(A_100,B_101,C_102),k1_zfmisc_1(A_100))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(A_100))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_840,plain,(
    ! [A_116,B_117,C_118] :
      ( r1_tarski(k4_subset_1(A_116,B_117,C_118),A_116)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(A_116))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(A_116)) ) ),
    inference(resolution,[status(thm)],[c_405,c_26])).

tff(c_860,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_783,c_840])).

tff(c_887,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_860])).

tff(c_900,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_887])).

tff(c_917,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_900])).

tff(c_924,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_917])).

tff(c_926,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_887])).

tff(c_984,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_926,c_26])).

tff(c_305,plain,(
    ! [A_89,B_90,C_91] :
      ( k4_subset_1(A_89,B_90,C_91) = k2_xboole_0(B_90,C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(A_89))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1004,plain,(
    ! [B_119,B_120,A_121] :
      ( k4_subset_1(B_119,B_120,A_121) = k2_xboole_0(B_120,A_121)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(B_119))
      | ~ r1_tarski(A_121,B_119) ) ),
    inference(resolution,[status(thm)],[c_28,c_305])).

tff(c_1074,plain,(
    ! [A_124] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_124) = k2_xboole_0('#skF_2',A_124)
      | ~ r1_tarski(A_124,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_42,c_1004])).

tff(c_1077,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_984,c_1074])).

tff(c_1104,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_1077])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_95,plain,(
    ! [B_51,A_52] :
      ( B_51 = A_52
      | ~ r1_tarski(B_51,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(k2_xboole_0(A_7,B_8),A_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_95])).

tff(c_1128,plain,
    ( k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1104,c_106])).

tff(c_1136,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1104,c_1128])).

tff(c_1137,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_628,c_1136])).

tff(c_14,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_10] : m1_subset_1(k2_subset_1(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_55,plain,(
    ! [A_10] : m1_subset_1(A_10,k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_1040,plain,(
    ! [A_122,A_123] :
      ( k4_subset_1(A_122,A_122,A_123) = k2_xboole_0(A_122,A_123)
      | ~ r1_tarski(A_123,A_122) ) ),
    inference(resolution,[status(thm)],[c_55,c_1004])).

tff(c_1168,plain,(
    ! [A_127,B_128] : k4_subset_1(A_127,A_127,k4_xboole_0(A_127,B_128)) = k2_xboole_0(A_127,k4_xboole_0(A_127,B_128)) ),
    inference(resolution,[status(thm)],[c_10,c_1040])).

tff(c_1183,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2'))) = k4_subset_1('#skF_2','#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_1168])).

tff(c_1190,plain,(
    k4_subset_1('#skF_2','#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1104,c_153,c_1183])).

tff(c_444,plain,(
    ! [A_100,B_101,C_102] :
      ( r1_tarski(k4_subset_1(A_100,B_101,C_102),A_100)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(A_100))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_100)) ) ),
    inference(resolution,[status(thm)],[c_405,c_26])).

tff(c_1208,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1190,c_444])).

tff(c_1215,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_1208])).

tff(c_1216,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_1137,c_1215])).

tff(c_1222,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_1216])).

tff(c_1226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_1222])).

tff(c_1227,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1227,c_79])).

tff(c_1230,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1248,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1230,c_48])).

tff(c_1296,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1285,c_1248])).

tff(c_1353,plain,(
    ! [A_158,B_159] :
      ( k2_pre_topc(A_158,B_159) = B_159
      | ~ v4_pre_topc(B_159,A_158)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ l1_pre_topc(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1360,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1353])).

tff(c_1368,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1230,c_1360])).

tff(c_1888,plain,(
    ! [A_193,B_194] :
      ( k7_subset_1(u1_struct_0(A_193),k2_pre_topc(A_193,B_194),k1_tops_1(A_193,B_194)) = k2_tops_1(A_193,B_194)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ l1_pre_topc(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1897,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1368,c_1888])).

tff(c_1901,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1285,c_1897])).

tff(c_1903,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1296,c_1901])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.56/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.61  
% 3.56/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.61  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 3.56/1.61  
% 3.56/1.61  %Foreground sorts:
% 3.56/1.61  
% 3.56/1.61  
% 3.56/1.61  %Background operators:
% 3.56/1.61  
% 3.56/1.61  
% 3.56/1.61  %Foreground operators:
% 3.56/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.56/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.56/1.61  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.56/1.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.56/1.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.56/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.56/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.56/1.61  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.56/1.61  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.56/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.56/1.61  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.56/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.56/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.56/1.61  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.56/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.56/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.56/1.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.56/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.56/1.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.56/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.56/1.61  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.56/1.61  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.56/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.56/1.61  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.56/1.61  
% 3.78/1.63  tff(f_118, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 3.78/1.63  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.78/1.63  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.78/1.63  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.78/1.63  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.78/1.63  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 3.78/1.63  tff(f_84, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 3.78/1.63  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 3.78/1.63  tff(f_53, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.78/1.63  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.78/1.63  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.78/1.63  tff(f_39, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.78/1.63  tff(f_41, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.78/1.63  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 3.78/1.63  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.78/1.63  tff(c_1277, plain, (![A_141, B_142, C_143]: (k7_subset_1(A_141, B_142, C_143)=k4_xboole_0(B_142, C_143) | ~m1_subset_1(B_142, k1_zfmisc_1(A_141)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.78/1.63  tff(c_1285, plain, (![C_143]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_143)=k4_xboole_0('#skF_2', C_143))), inference(resolution, [status(thm)], [c_42, c_1277])).
% 3.78/1.63  tff(c_128, plain, (![A_59, B_60, C_61]: (k7_subset_1(A_59, B_60, C_61)=k4_xboole_0(B_60, C_61) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.78/1.63  tff(c_147, plain, (![C_64]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_64)=k4_xboole_0('#skF_2', C_64))), inference(resolution, [status(thm)], [c_42, c_128])).
% 3.78/1.63  tff(c_54, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.78/1.63  tff(c_79, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_54])).
% 3.78/1.63  tff(c_153, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_147, c_79])).
% 3.78/1.63  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.78/1.63  tff(c_176, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_153, c_10])).
% 3.78/1.63  tff(c_28, plain, (![A_22, B_23]: (m1_subset_1(A_22, k1_zfmisc_1(B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.78/1.63  tff(c_48, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.78/1.63  tff(c_123, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 3.78/1.63  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.78/1.63  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.78/1.63  tff(c_597, plain, (![B_107, A_108]: (v4_pre_topc(B_107, A_108) | k2_pre_topc(A_108, B_107)!=B_107 | ~v2_pre_topc(A_108) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.78/1.63  tff(c_614, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_597])).
% 3.78/1.63  tff(c_627, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_614])).
% 3.78/1.63  tff(c_628, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_123, c_627])).
% 3.78/1.63  tff(c_759, plain, (![A_110, B_111]: (k4_subset_1(u1_struct_0(A_110), B_111, k2_tops_1(A_110, B_111))=k2_pre_topc(A_110, B_111) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.78/1.63  tff(c_771, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_759])).
% 3.78/1.63  tff(c_783, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_771])).
% 3.78/1.63  tff(c_34, plain, (![A_27, B_28]: (m1_subset_1(k2_tops_1(A_27, B_28), k1_zfmisc_1(u1_struct_0(A_27))) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.78/1.63  tff(c_405, plain, (![A_100, B_101, C_102]: (m1_subset_1(k4_subset_1(A_100, B_101, C_102), k1_zfmisc_1(A_100)) | ~m1_subset_1(C_102, k1_zfmisc_1(A_100)) | ~m1_subset_1(B_101, k1_zfmisc_1(A_100)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.78/1.63  tff(c_26, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.78/1.63  tff(c_840, plain, (![A_116, B_117, C_118]: (r1_tarski(k4_subset_1(A_116, B_117, C_118), A_116) | ~m1_subset_1(C_118, k1_zfmisc_1(A_116)) | ~m1_subset_1(B_117, k1_zfmisc_1(A_116)))), inference(resolution, [status(thm)], [c_405, c_26])).
% 3.78/1.63  tff(c_860, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_783, c_840])).
% 3.78/1.63  tff(c_887, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_860])).
% 3.78/1.63  tff(c_900, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_887])).
% 3.78/1.63  tff(c_917, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_900])).
% 3.78/1.63  tff(c_924, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_917])).
% 3.78/1.63  tff(c_926, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_887])).
% 3.78/1.63  tff(c_984, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_926, c_26])).
% 3.78/1.63  tff(c_305, plain, (![A_89, B_90, C_91]: (k4_subset_1(A_89, B_90, C_91)=k2_xboole_0(B_90, C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(A_89)) | ~m1_subset_1(B_90, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.78/1.63  tff(c_1004, plain, (![B_119, B_120, A_121]: (k4_subset_1(B_119, B_120, A_121)=k2_xboole_0(B_120, A_121) | ~m1_subset_1(B_120, k1_zfmisc_1(B_119)) | ~r1_tarski(A_121, B_119))), inference(resolution, [status(thm)], [c_28, c_305])).
% 3.78/1.63  tff(c_1074, plain, (![A_124]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_124)=k2_xboole_0('#skF_2', A_124) | ~r1_tarski(A_124, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_42, c_1004])).
% 3.78/1.63  tff(c_1077, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_984, c_1074])).
% 3.78/1.63  tff(c_1104, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_783, c_1077])).
% 3.78/1.63  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.78/1.63  tff(c_95, plain, (![B_51, A_52]: (B_51=A_52 | ~r1_tarski(B_51, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.78/1.63  tff(c_106, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(k2_xboole_0(A_7, B_8), A_7))), inference(resolution, [status(thm)], [c_12, c_95])).
% 3.78/1.63  tff(c_1128, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1104, c_106])).
% 3.78/1.63  tff(c_1136, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1104, c_1128])).
% 3.78/1.63  tff(c_1137, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_628, c_1136])).
% 3.78/1.63  tff(c_14, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.78/1.63  tff(c_16, plain, (![A_10]: (m1_subset_1(k2_subset_1(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.78/1.63  tff(c_55, plain, (![A_10]: (m1_subset_1(A_10, k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 3.78/1.63  tff(c_1040, plain, (![A_122, A_123]: (k4_subset_1(A_122, A_122, A_123)=k2_xboole_0(A_122, A_123) | ~r1_tarski(A_123, A_122))), inference(resolution, [status(thm)], [c_55, c_1004])).
% 3.78/1.63  tff(c_1168, plain, (![A_127, B_128]: (k4_subset_1(A_127, A_127, k4_xboole_0(A_127, B_128))=k2_xboole_0(A_127, k4_xboole_0(A_127, B_128)))), inference(resolution, [status(thm)], [c_10, c_1040])).
% 3.78/1.63  tff(c_1183, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2')))=k4_subset_1('#skF_2', '#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_153, c_1168])).
% 3.78/1.63  tff(c_1190, plain, (k4_subset_1('#skF_2', '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1104, c_153, c_1183])).
% 3.78/1.63  tff(c_444, plain, (![A_100, B_101, C_102]: (r1_tarski(k4_subset_1(A_100, B_101, C_102), A_100) | ~m1_subset_1(C_102, k1_zfmisc_1(A_100)) | ~m1_subset_1(B_101, k1_zfmisc_1(A_100)))), inference(resolution, [status(thm)], [c_405, c_26])).
% 3.78/1.63  tff(c_1208, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1190, c_444])).
% 3.78/1.63  tff(c_1215, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_1208])).
% 3.78/1.63  tff(c_1216, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_1137, c_1215])).
% 3.78/1.63  tff(c_1222, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_28, c_1216])).
% 3.78/1.63  tff(c_1226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_176, c_1222])).
% 3.78/1.63  tff(c_1227, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 3.78/1.63  tff(c_1229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1227, c_79])).
% 3.78/1.63  tff(c_1230, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 3.78/1.63  tff(c_1248, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1230, c_48])).
% 3.78/1.63  tff(c_1296, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1285, c_1248])).
% 3.78/1.63  tff(c_1353, plain, (![A_158, B_159]: (k2_pre_topc(A_158, B_159)=B_159 | ~v4_pre_topc(B_159, A_158) | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0(A_158))) | ~l1_pre_topc(A_158))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.78/1.63  tff(c_1360, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1353])).
% 3.78/1.63  tff(c_1368, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1230, c_1360])).
% 3.78/1.63  tff(c_1888, plain, (![A_193, B_194]: (k7_subset_1(u1_struct_0(A_193), k2_pre_topc(A_193, B_194), k1_tops_1(A_193, B_194))=k2_tops_1(A_193, B_194) | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0(A_193))) | ~l1_pre_topc(A_193))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.78/1.63  tff(c_1897, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1368, c_1888])).
% 3.78/1.63  tff(c_1901, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1285, c_1897])).
% 3.78/1.63  tff(c_1903, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1296, c_1901])).
% 3.78/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/1.63  
% 3.78/1.63  Inference rules
% 3.78/1.63  ----------------------
% 3.78/1.63  #Ref     : 0
% 3.78/1.63  #Sup     : 433
% 3.78/1.63  #Fact    : 0
% 3.78/1.63  #Define  : 0
% 3.78/1.63  #Split   : 8
% 3.78/1.63  #Chain   : 0
% 3.78/1.63  #Close   : 0
% 3.78/1.63  
% 3.78/1.63  Ordering : KBO
% 3.78/1.63  
% 3.78/1.63  Simplification rules
% 3.78/1.63  ----------------------
% 3.78/1.63  #Subsume      : 8
% 3.78/1.63  #Demod        : 276
% 3.78/1.63  #Tautology    : 175
% 3.78/1.63  #SimpNegUnit  : 6
% 3.78/1.63  #BackRed      : 13
% 3.78/1.63  
% 3.78/1.63  #Partial instantiations: 0
% 3.78/1.63  #Strategies tried      : 1
% 3.78/1.63  
% 3.78/1.63  Timing (in seconds)
% 3.78/1.63  ----------------------
% 3.78/1.63  Preprocessing        : 0.33
% 3.78/1.63  Parsing              : 0.18
% 3.78/1.63  CNF conversion       : 0.02
% 3.78/1.63  Main loop            : 0.54
% 3.78/1.63  Inferencing          : 0.18
% 3.78/1.63  Reduction            : 0.18
% 3.78/1.63  Demodulation         : 0.13
% 3.78/1.63  BG Simplification    : 0.03
% 3.78/1.63  Subsumption          : 0.10
% 3.78/1.63  Abstraction          : 0.03
% 3.78/1.63  MUC search           : 0.00
% 3.78/1.63  Cooper               : 0.00
% 3.78/1.63  Total                : 0.90
% 3.78/1.63  Index Insertion      : 0.00
% 3.78/1.63  Index Deletion       : 0.00
% 3.78/1.63  Index Matching       : 0.00
% 3.78/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
