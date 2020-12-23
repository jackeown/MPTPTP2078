%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:55 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 177 expanded)
%              Number of leaves         :   31 (  74 expanded)
%              Depth                    :    9
%              Number of atoms          :  107 ( 276 expanded)
%              Number of equality atoms :   56 (  99 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_51,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_32,plain,
    ( ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_134,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_837,plain,(
    ! [B_79,A_80] :
      ( v2_tops_1(B_79,A_80)
      | k1_tops_1(A_80,B_79) != k1_xboole_0
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_840,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_837])).

tff(c_843,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_840])).

tff(c_844,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_843])).

tff(c_227,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k4_xboole_0(A_47,B_48)) = k3_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [A_32] :
      ( k1_xboole_0 = A_32
      | ~ r1_tarski(A_32,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_64,plain,(
    ! [B_4] : k4_xboole_0(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_53])).

tff(c_268,plain,(
    ! [B_49] : k3_xboole_0(k1_xboole_0,B_49) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_64])).

tff(c_16,plain,(
    ! [B_15,A_14] : k2_tarski(B_15,A_14) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_119,plain,(
    ! [A_36,B_37] : k1_setfam_1(k2_tarski(A_36,B_37)) = k3_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_153,plain,(
    ! [A_41,B_42] : k1_setfam_1(k2_tarski(A_41,B_42)) = k3_xboole_0(B_42,A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_119])).

tff(c_20,plain,(
    ! [A_19,B_20] : k1_setfam_1(k2_tarski(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_159,plain,(
    ! [B_42,A_41] : k3_xboole_0(B_42,A_41) = k3_xboole_0(A_41,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_20])).

tff(c_276,plain,(
    ! [B_49] : k3_xboole_0(B_49,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_159])).

tff(c_8,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_259,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_227])).

tff(c_485,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_259])).

tff(c_38,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_263,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_38])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_267,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_263,c_2])).

tff(c_578,plain,(
    ! [A_62,B_63,C_64] :
      ( k7_subset_1(A_62,B_63,C_64) = k4_xboole_0(B_63,C_64)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_581,plain,(
    ! [C_64] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_64) = k4_xboole_0('#skF_2',C_64) ),
    inference(resolution,[status(thm)],[c_28,c_578])).

tff(c_1161,plain,(
    ! [A_89,B_90] :
      ( k7_subset_1(u1_struct_0(A_89),B_90,k2_tops_1(A_89,B_90)) = k1_tops_1(A_89,B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1163,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1161])).

tff(c_1166,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_581,c_1163])).

tff(c_14,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1377,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1166,c_14])).

tff(c_1387,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_1377])).

tff(c_1405,plain,(
    k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1387,c_14])).

tff(c_1416,plain,(
    k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_1405])).

tff(c_135,plain,(
    ! [A_38,B_39] :
      ( k3_xboole_0(A_38,B_39) = A_38
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_143,plain,(
    ! [A_3,B_4] : k3_xboole_0(k4_xboole_0(A_3,B_4),A_3) = k4_xboole_0(A_3,B_4) ),
    inference(resolution,[status(thm)],[c_4,c_135])).

tff(c_1368,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1166,c_143])).

tff(c_1386,plain,(
    k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1166,c_159,c_1368])).

tff(c_1620,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1416,c_1386])).

tff(c_1621,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_844,c_1620])).

tff(c_1622,plain,(
    ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1958,plain,(
    ! [A_120,B_121,C_122] :
      ( k7_subset_1(A_120,B_121,C_122) = k4_xboole_0(B_121,C_122)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(A_120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1961,plain,(
    ! [C_122] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_122) = k4_xboole_0('#skF_2',C_122) ),
    inference(resolution,[status(thm)],[c_28,c_1958])).

tff(c_1623,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_2138,plain,(
    ! [A_129,B_130] :
      ( k1_tops_1(A_129,B_130) = k1_xboole_0
      | ~ v2_tops_1(B_130,A_129)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2141,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_2138])).

tff(c_2144,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1623,c_2141])).

tff(c_2417,plain,(
    ! [A_147,B_148] :
      ( k7_subset_1(u1_struct_0(A_147),B_148,k2_tops_1(A_147,B_148)) = k1_tops_1(A_147,B_148)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ l1_pre_topc(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2419,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_2417])).

tff(c_2422,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1961,c_2144,c_2419])).

tff(c_2435,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2422,c_14])).

tff(c_2443,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2435])).

tff(c_1644,plain,(
    ! [B_102,A_103] : k1_setfam_1(k2_tarski(B_102,A_103)) = k3_xboole_0(A_103,B_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_119])).

tff(c_1650,plain,(
    ! [B_102,A_103] : k3_xboole_0(B_102,A_103) = k3_xboole_0(A_103,B_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_1644,c_20])).

tff(c_1700,plain,(
    ! [A_106,B_107] : k4_xboole_0(A_106,k4_xboole_0(A_106,B_107)) = k3_xboole_0(A_106,B_107) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1832,plain,(
    ! [A_112,B_113] : r1_tarski(k3_xboole_0(A_112,B_113),A_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_1700,c_4])).

tff(c_1848,plain,(
    ! [B_102,A_103] : r1_tarski(k3_xboole_0(B_102,A_103),A_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_1650,c_1832])).

tff(c_2449,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2443,c_1848])).

tff(c_2456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1622,c_2449])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:22:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.56  
% 3.26/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.56  %$ v2_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.26/1.56  
% 3.26/1.56  %Foreground sorts:
% 3.26/1.56  
% 3.26/1.56  
% 3.26/1.56  %Background operators:
% 3.26/1.56  
% 3.26/1.56  
% 3.26/1.56  %Foreground operators:
% 3.26/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.26/1.56  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.26/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.26/1.56  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.26/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.26/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.26/1.56  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.26/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.26/1.56  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.26/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.26/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.26/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.26/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.26/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.26/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.26/1.56  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.26/1.56  
% 3.26/1.57  tff(f_77, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 3.26/1.57  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 3.26/1.57  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.26/1.57  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.26/1.57  tff(f_39, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.26/1.57  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.26/1.57  tff(f_51, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.26/1.57  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.26/1.57  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.26/1.57  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.26/1.57  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 3.26/1.57  tff(c_32, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.26/1.57  tff(c_134, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_32])).
% 3.26/1.57  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.26/1.57  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.26/1.57  tff(c_837, plain, (![B_79, A_80]: (v2_tops_1(B_79, A_80) | k1_tops_1(A_80, B_79)!=k1_xboole_0 | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.26/1.57  tff(c_840, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_837])).
% 3.26/1.57  tff(c_843, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_840])).
% 3.26/1.57  tff(c_844, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_134, c_843])).
% 3.26/1.57  tff(c_227, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k4_xboole_0(A_47, B_48))=k3_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.26/1.57  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.57  tff(c_53, plain, (![A_32]: (k1_xboole_0=A_32 | ~r1_tarski(A_32, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.26/1.57  tff(c_64, plain, (![B_4]: (k4_xboole_0(k1_xboole_0, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_53])).
% 3.26/1.57  tff(c_268, plain, (![B_49]: (k3_xboole_0(k1_xboole_0, B_49)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_227, c_64])).
% 3.26/1.57  tff(c_16, plain, (![B_15, A_14]: (k2_tarski(B_15, A_14)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.26/1.57  tff(c_119, plain, (![A_36, B_37]: (k1_setfam_1(k2_tarski(A_36, B_37))=k3_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.26/1.57  tff(c_153, plain, (![A_41, B_42]: (k1_setfam_1(k2_tarski(A_41, B_42))=k3_xboole_0(B_42, A_41))), inference(superposition, [status(thm), theory('equality')], [c_16, c_119])).
% 3.26/1.57  tff(c_20, plain, (![A_19, B_20]: (k1_setfam_1(k2_tarski(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.26/1.57  tff(c_159, plain, (![B_42, A_41]: (k3_xboole_0(B_42, A_41)=k3_xboole_0(A_41, B_42))), inference(superposition, [status(thm), theory('equality')], [c_153, c_20])).
% 3.26/1.57  tff(c_276, plain, (![B_49]: (k3_xboole_0(B_49, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_268, c_159])).
% 3.26/1.57  tff(c_8, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.26/1.57  tff(c_259, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_227])).
% 3.26/1.57  tff(c_485, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_276, c_259])).
% 3.26/1.57  tff(c_38, plain, (v2_tops_1('#skF_2', '#skF_1') | r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.26/1.57  tff(c_263, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_134, c_38])).
% 3.26/1.57  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.26/1.57  tff(c_267, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_263, c_2])).
% 3.26/1.57  tff(c_578, plain, (![A_62, B_63, C_64]: (k7_subset_1(A_62, B_63, C_64)=k4_xboole_0(B_63, C_64) | ~m1_subset_1(B_63, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.26/1.57  tff(c_581, plain, (![C_64]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_64)=k4_xboole_0('#skF_2', C_64))), inference(resolution, [status(thm)], [c_28, c_578])).
% 3.26/1.57  tff(c_1161, plain, (![A_89, B_90]: (k7_subset_1(u1_struct_0(A_89), B_90, k2_tops_1(A_89, B_90))=k1_tops_1(A_89, B_90) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.26/1.57  tff(c_1163, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_1161])).
% 3.26/1.57  tff(c_1166, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_581, c_1163])).
% 3.26/1.57  tff(c_14, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.26/1.57  tff(c_1377, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1166, c_14])).
% 3.26/1.57  tff(c_1387, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_267, c_1377])).
% 3.26/1.57  tff(c_1405, plain, (k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1387, c_14])).
% 3.26/1.57  tff(c_1416, plain, (k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_485, c_1405])).
% 3.26/1.57  tff(c_135, plain, (![A_38, B_39]: (k3_xboole_0(A_38, B_39)=A_38 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.26/1.57  tff(c_143, plain, (![A_3, B_4]: (k3_xboole_0(k4_xboole_0(A_3, B_4), A_3)=k4_xboole_0(A_3, B_4))), inference(resolution, [status(thm)], [c_4, c_135])).
% 3.26/1.57  tff(c_1368, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1166, c_143])).
% 3.26/1.57  tff(c_1386, plain, (k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1166, c_159, c_1368])).
% 3.26/1.57  tff(c_1620, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1416, c_1386])).
% 3.26/1.57  tff(c_1621, plain, $false, inference(negUnitSimplification, [status(thm)], [c_844, c_1620])).
% 3.26/1.57  tff(c_1622, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_32])).
% 3.26/1.57  tff(c_1958, plain, (![A_120, B_121, C_122]: (k7_subset_1(A_120, B_121, C_122)=k4_xboole_0(B_121, C_122) | ~m1_subset_1(B_121, k1_zfmisc_1(A_120)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.26/1.57  tff(c_1961, plain, (![C_122]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_122)=k4_xboole_0('#skF_2', C_122))), inference(resolution, [status(thm)], [c_28, c_1958])).
% 3.26/1.57  tff(c_1623, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_32])).
% 3.26/1.57  tff(c_2138, plain, (![A_129, B_130]: (k1_tops_1(A_129, B_130)=k1_xboole_0 | ~v2_tops_1(B_130, A_129) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.26/1.57  tff(c_2141, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_2138])).
% 3.26/1.57  tff(c_2144, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1623, c_2141])).
% 3.26/1.57  tff(c_2417, plain, (![A_147, B_148]: (k7_subset_1(u1_struct_0(A_147), B_148, k2_tops_1(A_147, B_148))=k1_tops_1(A_147, B_148) | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0(A_147))) | ~l1_pre_topc(A_147))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.26/1.57  tff(c_2419, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_2417])).
% 3.26/1.57  tff(c_2422, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1961, c_2144, c_2419])).
% 3.26/1.57  tff(c_2435, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2422, c_14])).
% 3.26/1.57  tff(c_2443, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2435])).
% 3.26/1.57  tff(c_1644, plain, (![B_102, A_103]: (k1_setfam_1(k2_tarski(B_102, A_103))=k3_xboole_0(A_103, B_102))), inference(superposition, [status(thm), theory('equality')], [c_16, c_119])).
% 3.26/1.57  tff(c_1650, plain, (![B_102, A_103]: (k3_xboole_0(B_102, A_103)=k3_xboole_0(A_103, B_102))), inference(superposition, [status(thm), theory('equality')], [c_1644, c_20])).
% 3.26/1.57  tff(c_1700, plain, (![A_106, B_107]: (k4_xboole_0(A_106, k4_xboole_0(A_106, B_107))=k3_xboole_0(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.26/1.57  tff(c_1832, plain, (![A_112, B_113]: (r1_tarski(k3_xboole_0(A_112, B_113), A_112))), inference(superposition, [status(thm), theory('equality')], [c_1700, c_4])).
% 3.26/1.57  tff(c_1848, plain, (![B_102, A_103]: (r1_tarski(k3_xboole_0(B_102, A_103), A_103))), inference(superposition, [status(thm), theory('equality')], [c_1650, c_1832])).
% 3.26/1.57  tff(c_2449, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2443, c_1848])).
% 3.26/1.57  tff(c_2456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1622, c_2449])).
% 3.26/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.57  
% 3.26/1.57  Inference rules
% 3.26/1.57  ----------------------
% 3.26/1.57  #Ref     : 0
% 3.26/1.57  #Sup     : 588
% 3.26/1.57  #Fact    : 0
% 3.26/1.57  #Define  : 0
% 3.26/1.57  #Split   : 1
% 3.26/1.57  #Chain   : 0
% 3.26/1.57  #Close   : 0
% 3.26/1.57  
% 3.26/1.57  Ordering : KBO
% 3.26/1.57  
% 3.26/1.57  Simplification rules
% 3.26/1.57  ----------------------
% 3.26/1.58  #Subsume      : 3
% 3.26/1.58  #Demod        : 340
% 3.26/1.58  #Tautology    : 403
% 3.26/1.58  #SimpNegUnit  : 6
% 3.26/1.58  #BackRed      : 0
% 3.26/1.58  
% 3.26/1.58  #Partial instantiations: 0
% 3.26/1.58  #Strategies tried      : 1
% 3.26/1.58  
% 3.26/1.58  Timing (in seconds)
% 3.26/1.58  ----------------------
% 3.26/1.58  Preprocessing        : 0.29
% 3.26/1.58  Parsing              : 0.15
% 3.26/1.58  CNF conversion       : 0.02
% 3.26/1.58  Main loop            : 0.48
% 3.26/1.58  Inferencing          : 0.17
% 3.26/1.58  Reduction            : 0.18
% 3.26/1.58  Demodulation         : 0.14
% 3.26/1.58  BG Simplification    : 0.02
% 3.26/1.58  Subsumption          : 0.07
% 3.26/1.58  Abstraction          : 0.03
% 3.26/1.58  MUC search           : 0.00
% 3.26/1.58  Cooper               : 0.00
% 3.26/1.58  Total                : 0.80
% 3.26/1.58  Index Insertion      : 0.00
% 3.26/1.58  Index Deletion       : 0.00
% 3.26/1.58  Index Matching       : 0.00
% 3.26/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
