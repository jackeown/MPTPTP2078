%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:25 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 127 expanded)
%              Number of leaves         :   27 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :   99 ( 215 expanded)
%              Number of equality atoms :   21 (  42 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > m1_subset_1 > l1_pre_topc > k7_subset_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(c_28,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_47,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_49,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = k3_subset_1(A_25,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_49])).

tff(c_10,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_12] :
      ( k8_setfam_1(A_12,k1_xboole_0) = A_12
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_36,plain,(
    ! [A_12] : k8_setfam_1(A_12,k1_xboole_0) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_97,plain,(
    ! [A_36,B_37] :
      ( m1_subset_1(k8_setfam_1(A_36,B_37),k1_zfmisc_1(A_36))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k1_zfmisc_1(A_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_107,plain,(
    ! [A_12] :
      ( m1_subset_1(A_12,k1_zfmisc_1(A_12))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_97])).

tff(c_112,plain,(
    ! [A_12] : m1_subset_1(A_12,k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_107])).

tff(c_164,plain,(
    ! [A_44,B_45,C_46] :
      ( k7_subset_1(A_44,B_45,C_46) = k4_xboole_0(B_45,C_46)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_173,plain,(
    ! [A_12,C_46] : k7_subset_1(A_12,A_12,C_46) = k4_xboole_0(A_12,C_46) ),
    inference(resolution,[status(thm)],[c_112,c_164])).

tff(c_214,plain,(
    ! [A_52,B_53,C_54] :
      ( m1_subset_1(k7_subset_1(A_52,B_53,C_54),k1_zfmisc_1(A_52))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_229,plain,(
    ! [A_12,C_46] :
      ( m1_subset_1(k4_xboole_0(A_12,C_46),k1_zfmisc_1(A_12))
      | ~ m1_subset_1(A_12,k1_zfmisc_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_214])).

tff(c_265,plain,(
    ! [A_57,C_58] : m1_subset_1(k4_xboole_0(A_57,C_58),k1_zfmisc_1(A_57)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_229])).

tff(c_280,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_265])).

tff(c_34,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_48,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_34])).

tff(c_71,plain,(
    ! [A_28,B_29] :
      ( k3_subset_1(A_28,k3_subset_1(A_28,B_29)) = B_29
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_76,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_24,c_71])).

tff(c_591,plain,(
    ! [A_87,B_88] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_87),B_88),A_87)
      | ~ v4_pre_topc(B_88,A_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_601,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_591])).

tff(c_610,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_280,c_48,c_601])).

tff(c_612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_610])).

tff(c_613,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_644,plain,(
    ! [A_98,B_99] :
      ( k4_xboole_0(A_98,B_99) = k3_subset_1(A_98,B_99)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_651,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_644])).

tff(c_691,plain,(
    ! [A_107,B_108] :
      ( m1_subset_1(k8_setfam_1(A_107,B_108),k1_zfmisc_1(A_107))
      | ~ m1_subset_1(B_108,k1_zfmisc_1(k1_zfmisc_1(A_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_703,plain,(
    ! [A_12] :
      ( m1_subset_1(A_12,k1_zfmisc_1(A_12))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_691])).

tff(c_709,plain,(
    ! [A_12] : m1_subset_1(A_12,k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_703])).

tff(c_710,plain,(
    ! [A_109] : m1_subset_1(A_109,k1_zfmisc_1(A_109)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_703])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] :
      ( k7_subset_1(A_8,B_9,C_10) = k4_xboole_0(B_9,C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_846,plain,(
    ! [A_121,C_122] : k7_subset_1(A_121,A_121,C_122) = k4_xboole_0(A_121,C_122) ),
    inference(resolution,[status(thm)],[c_710,c_8])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( m1_subset_1(k7_subset_1(A_3,B_4,C_5),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_852,plain,(
    ! [A_121,C_122] :
      ( m1_subset_1(k4_xboole_0(A_121,C_122),k1_zfmisc_1(A_121))
      | ~ m1_subset_1(A_121,k1_zfmisc_1(A_121)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_846,c_4])).

tff(c_870,plain,(
    ! [A_123,C_124] : m1_subset_1(k4_xboole_0(A_123,C_124),k1_zfmisc_1(A_123)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_709,c_852])).

tff(c_885,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_651,c_870])).

tff(c_614,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_617,plain,(
    ! [A_89,B_90] :
      ( k3_subset_1(A_89,k3_subset_1(A_89,B_90)) = B_90
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_622,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_24,c_617])).

tff(c_1095,plain,(
    ! [B_139,A_140] :
      ( v4_pre_topc(B_139,A_140)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_140),B_139),A_140)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1102,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_622,c_1095])).

tff(c_1110,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_885,c_614,c_1102])).

tff(c_1112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_613,c_1110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:48:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.45  
% 2.81/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.45  %$ v4_pre_topc > v3_pre_topc > r2_hidden > m1_subset_1 > l1_pre_topc > k7_subset_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.81/1.45  
% 2.81/1.45  %Foreground sorts:
% 2.81/1.45  
% 2.81/1.45  
% 2.81/1.45  %Background operators:
% 2.81/1.45  
% 2.81/1.45  
% 2.81/1.45  %Foreground operators:
% 2.81/1.45  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.81/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.81/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.45  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.81/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.81/1.45  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.81/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.81/1.45  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.81/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.81/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.81/1.45  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.81/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.45  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.81/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.81/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.81/1.45  
% 3.06/1.47  tff(f_83, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_tops_1)).
% 3.06/1.47  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.06/1.47  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.06/1.47  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 3.06/1.47  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 3.06/1.47  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.06/1.47  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 3.06/1.47  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.06/1.47  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 3.06/1.47  tff(c_28, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.06/1.47  tff(c_47, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_28])).
% 3.06/1.47  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.06/1.47  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.06/1.47  tff(c_49, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=k3_subset_1(A_25, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.06/1.47  tff(c_56, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_24, c_49])).
% 3.06/1.47  tff(c_10, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.06/1.47  tff(c_12, plain, (![A_12]: (k8_setfam_1(A_12, k1_xboole_0)=A_12 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_12))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.06/1.47  tff(c_36, plain, (![A_12]: (k8_setfam_1(A_12, k1_xboole_0)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 3.06/1.47  tff(c_97, plain, (![A_36, B_37]: (m1_subset_1(k8_setfam_1(A_36, B_37), k1_zfmisc_1(A_36)) | ~m1_subset_1(B_37, k1_zfmisc_1(k1_zfmisc_1(A_36))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.06/1.47  tff(c_107, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_12))))), inference(superposition, [status(thm), theory('equality')], [c_36, c_97])).
% 3.06/1.47  tff(c_112, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_107])).
% 3.06/1.47  tff(c_164, plain, (![A_44, B_45, C_46]: (k7_subset_1(A_44, B_45, C_46)=k4_xboole_0(B_45, C_46) | ~m1_subset_1(B_45, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.06/1.47  tff(c_173, plain, (![A_12, C_46]: (k7_subset_1(A_12, A_12, C_46)=k4_xboole_0(A_12, C_46))), inference(resolution, [status(thm)], [c_112, c_164])).
% 3.06/1.47  tff(c_214, plain, (![A_52, B_53, C_54]: (m1_subset_1(k7_subset_1(A_52, B_53, C_54), k1_zfmisc_1(A_52)) | ~m1_subset_1(B_53, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.06/1.47  tff(c_229, plain, (![A_12, C_46]: (m1_subset_1(k4_xboole_0(A_12, C_46), k1_zfmisc_1(A_12)) | ~m1_subset_1(A_12, k1_zfmisc_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_173, c_214])).
% 3.06/1.47  tff(c_265, plain, (![A_57, C_58]: (m1_subset_1(k4_xboole_0(A_57, C_58), k1_zfmisc_1(A_57)))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_229])).
% 3.06/1.47  tff(c_280, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_56, c_265])).
% 3.06/1.47  tff(c_34, plain, (v3_pre_topc('#skF_2', '#skF_1') | v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.06/1.47  tff(c_48, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_47, c_34])).
% 3.06/1.47  tff(c_71, plain, (![A_28, B_29]: (k3_subset_1(A_28, k3_subset_1(A_28, B_29))=B_29 | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.06/1.47  tff(c_76, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_24, c_71])).
% 3.06/1.47  tff(c_591, plain, (![A_87, B_88]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_87), B_88), A_87) | ~v4_pre_topc(B_88, A_87) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.06/1.47  tff(c_601, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_76, c_591])).
% 3.06/1.47  tff(c_610, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_280, c_48, c_601])).
% 3.06/1.47  tff(c_612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_610])).
% 3.06/1.47  tff(c_613, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 3.06/1.47  tff(c_644, plain, (![A_98, B_99]: (k4_xboole_0(A_98, B_99)=k3_subset_1(A_98, B_99) | ~m1_subset_1(B_99, k1_zfmisc_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.06/1.47  tff(c_651, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_24, c_644])).
% 3.06/1.47  tff(c_691, plain, (![A_107, B_108]: (m1_subset_1(k8_setfam_1(A_107, B_108), k1_zfmisc_1(A_107)) | ~m1_subset_1(B_108, k1_zfmisc_1(k1_zfmisc_1(A_107))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.06/1.47  tff(c_703, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_12))))), inference(superposition, [status(thm), theory('equality')], [c_36, c_691])).
% 3.06/1.47  tff(c_709, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_703])).
% 3.06/1.47  tff(c_710, plain, (![A_109]: (m1_subset_1(A_109, k1_zfmisc_1(A_109)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_703])).
% 3.06/1.47  tff(c_8, plain, (![A_8, B_9, C_10]: (k7_subset_1(A_8, B_9, C_10)=k4_xboole_0(B_9, C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.06/1.47  tff(c_846, plain, (![A_121, C_122]: (k7_subset_1(A_121, A_121, C_122)=k4_xboole_0(A_121, C_122))), inference(resolution, [status(thm)], [c_710, c_8])).
% 3.06/1.47  tff(c_4, plain, (![A_3, B_4, C_5]: (m1_subset_1(k7_subset_1(A_3, B_4, C_5), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.06/1.47  tff(c_852, plain, (![A_121, C_122]: (m1_subset_1(k4_xboole_0(A_121, C_122), k1_zfmisc_1(A_121)) | ~m1_subset_1(A_121, k1_zfmisc_1(A_121)))), inference(superposition, [status(thm), theory('equality')], [c_846, c_4])).
% 3.06/1.47  tff(c_870, plain, (![A_123, C_124]: (m1_subset_1(k4_xboole_0(A_123, C_124), k1_zfmisc_1(A_123)))), inference(demodulation, [status(thm), theory('equality')], [c_709, c_852])).
% 3.06/1.47  tff(c_885, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_651, c_870])).
% 3.06/1.47  tff(c_614, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 3.06/1.47  tff(c_617, plain, (![A_89, B_90]: (k3_subset_1(A_89, k3_subset_1(A_89, B_90))=B_90 | ~m1_subset_1(B_90, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.06/1.47  tff(c_622, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_24, c_617])).
% 3.06/1.47  tff(c_1095, plain, (![B_139, A_140]: (v4_pre_topc(B_139, A_140) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_140), B_139), A_140) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.06/1.47  tff(c_1102, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v3_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_622, c_1095])).
% 3.06/1.47  tff(c_1110, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_885, c_614, c_1102])).
% 3.06/1.47  tff(c_1112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_613, c_1110])).
% 3.06/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.47  
% 3.06/1.47  Inference rules
% 3.06/1.47  ----------------------
% 3.06/1.47  #Ref     : 0
% 3.06/1.47  #Sup     : 265
% 3.06/1.47  #Fact    : 0
% 3.06/1.47  #Define  : 0
% 3.06/1.47  #Split   : 1
% 3.06/1.47  #Chain   : 0
% 3.06/1.47  #Close   : 0
% 3.06/1.47  
% 3.06/1.47  Ordering : KBO
% 3.06/1.47  
% 3.06/1.47  Simplification rules
% 3.06/1.47  ----------------------
% 3.06/1.47  #Subsume      : 18
% 3.06/1.47  #Demod        : 53
% 3.06/1.47  #Tautology    : 93
% 3.06/1.47  #SimpNegUnit  : 4
% 3.06/1.47  #BackRed      : 0
% 3.06/1.47  
% 3.06/1.47  #Partial instantiations: 0
% 3.06/1.47  #Strategies tried      : 1
% 3.06/1.47  
% 3.06/1.47  Timing (in seconds)
% 3.06/1.47  ----------------------
% 3.06/1.47  Preprocessing        : 0.30
% 3.06/1.47  Parsing              : 0.16
% 3.06/1.47  CNF conversion       : 0.02
% 3.06/1.47  Main loop            : 0.39
% 3.06/1.47  Inferencing          : 0.15
% 3.06/1.47  Reduction            : 0.12
% 3.06/1.47  Demodulation         : 0.09
% 3.06/1.47  BG Simplification    : 0.02
% 3.06/1.47  Subsumption          : 0.06
% 3.06/1.47  Abstraction          : 0.03
% 3.06/1.47  MUC search           : 0.00
% 3.06/1.47  Cooper               : 0.00
% 3.06/1.47  Total                : 0.73
% 3.06/1.47  Index Insertion      : 0.00
% 3.06/1.47  Index Deletion       : 0.00
% 3.06/1.47  Index Matching       : 0.00
% 3.06/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
