%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:08 EST 2020

% Result     : Theorem 13.83s
% Output     : CNFRefutation 13.83s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 420 expanded)
%              Number of leaves         :   49 ( 162 expanded)
%              Depth                    :   16
%              Number of atoms          :  239 ( 921 expanded)
%              Number of equality atoms :   71 ( 252 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_141,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_58,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_60,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_129,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_122,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_68,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_86,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') != k2_tops_1('#skF_5','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_177,plain,(
    ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_44,plain,(
    ! [B_16] : r1_tarski(B_16,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_48,plain,(
    ! [A_19] : k2_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_50,plain,(
    ! [A_20] : k4_xboole_0(k1_xboole_0,A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_221,plain,(
    ! [A_93,B_94] : k5_xboole_0(A_93,k4_xboole_0(B_94,A_93)) = k2_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_230,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = k2_xboole_0(A_20,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_221])).

tff(c_233,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_230])).

tff(c_82,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_80,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_294,plain,(
    ! [A_107,B_108,C_109] :
      ( k7_subset_1(A_107,B_108,C_109) = k4_xboole_0(B_108,C_109)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(A_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_307,plain,(
    ! [C_109] : k7_subset_1(u1_struct_0('#skF_5'),'#skF_6',C_109) = k4_xboole_0('#skF_6',C_109) ),
    inference(resolution,[status(thm)],[c_80,c_294])).

tff(c_978,plain,(
    ! [A_178,B_179] :
      ( k7_subset_1(u1_struct_0(A_178),B_179,k2_tops_1(A_178,B_179)) = k1_tops_1(A_178,B_179)
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ l1_pre_topc(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_994,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),'#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_978])).

tff(c_1004,plain,(
    k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_307,c_994])).

tff(c_68,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(k2_tops_1(A_37,B_38),k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_843,plain,(
    ! [A_167,B_168] :
      ( k4_subset_1(u1_struct_0(A_167),B_168,k2_tops_1(A_167,B_168)) = k2_pre_topc(A_167,B_168)
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ l1_pre_topc(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_859,plain,
    ( k4_subset_1(u1_struct_0('#skF_5'),'#skF_6',k2_tops_1('#skF_5','#skF_6')) = k2_pre_topc('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_843])).

tff(c_867,plain,(
    k4_subset_1(u1_struct_0('#skF_5'),'#skF_6',k2_tops_1('#skF_5','#skF_6')) = k2_pre_topc('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_859])).

tff(c_402,plain,(
    ! [A_133,B_134,C_135] :
      ( m1_subset_1(k4_subset_1(A_133,B_134,C_135),k1_zfmisc_1(A_133))
      | ~ m1_subset_1(C_135,k1_zfmisc_1(A_133))
      | ~ m1_subset_1(B_134,k1_zfmisc_1(A_133)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_64,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | ~ m1_subset_1(A_35,k1_zfmisc_1(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_413,plain,(
    ! [A_133,B_134,C_135] :
      ( r1_tarski(k4_subset_1(A_133,B_134,C_135),A_133)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(A_133))
      | ~ m1_subset_1(B_134,k1_zfmisc_1(A_133)) ) ),
    inference(resolution,[status(thm)],[c_402,c_64])).

tff(c_890,plain,
    ( r1_tarski(k2_pre_topc('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k2_tops_1('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_867,c_413])).

tff(c_897,plain,
    ( r1_tarski(k2_pre_topc('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k2_tops_1('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_890])).

tff(c_2839,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_897])).

tff(c_2889,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_2839])).

tff(c_2896,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_2889])).

tff(c_2897,plain,(
    r1_tarski(k2_pre_topc('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_897])).

tff(c_66,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(A_35,k1_zfmisc_1(B_36))
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_303,plain,(
    ! [B_36,A_35,C_109] :
      ( k7_subset_1(B_36,A_35,C_109) = k4_xboole_0(A_35,C_109)
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(resolution,[status(thm)],[c_66,c_294])).

tff(c_2981,plain,(
    ! [C_260] : k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),C_260) = k4_xboole_0(k2_pre_topc('#skF_5','#skF_6'),C_260) ),
    inference(resolution,[status(thm)],[c_2897,c_303])).

tff(c_92,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_125,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_2991,plain,(
    k4_xboole_0(k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2981,c_125])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_478,plain,(
    ! [A_142,B_143,C_144] :
      ( r2_hidden('#skF_1'(A_142,B_143,C_144),B_143)
      | r2_hidden('#skF_2'(A_142,B_143,C_144),C_144)
      | k3_xboole_0(A_142,B_143) = C_144 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_22,plain,(
    ! [D_12,B_8,A_7] :
      ( ~ r2_hidden(D_12,B_8)
      | ~ r2_hidden(D_12,k4_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_17063,plain,(
    ! [A_609,A_610,B_611,C_612] :
      ( ~ r2_hidden('#skF_1'(A_609,k4_xboole_0(A_610,B_611),C_612),B_611)
      | r2_hidden('#skF_2'(A_609,k4_xboole_0(A_610,B_611),C_612),C_612)
      | k3_xboole_0(A_609,k4_xboole_0(A_610,B_611)) = C_612 ) ),
    inference(resolution,[status(thm)],[c_478,c_22])).

tff(c_19732,plain,(
    ! [A_653,A_654,C_655] :
      ( r2_hidden('#skF_2'(A_653,k4_xboole_0(A_654,A_653),C_655),C_655)
      | k3_xboole_0(A_653,k4_xboole_0(A_654,A_653)) = C_655 ) ),
    inference(resolution,[status(thm)],[c_18,c_17063])).

tff(c_36,plain,(
    ! [A_7,B_8,C_9] :
      ( r2_hidden('#skF_3'(A_7,B_8,C_9),A_7)
      | r2_hidden('#skF_4'(A_7,B_8,C_9),C_9)
      | k4_xboole_0(A_7,B_8) = C_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_592,plain,(
    ! [A_148,B_149,C_150] :
      ( ~ r2_hidden('#skF_3'(A_148,B_149,C_150),B_149)
      | r2_hidden('#skF_4'(A_148,B_149,C_150),C_150)
      | k4_xboole_0(A_148,B_149) = C_150 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_602,plain,(
    ! [A_7,C_9] :
      ( r2_hidden('#skF_4'(A_7,A_7,C_9),C_9)
      | k4_xboole_0(A_7,A_7) = C_9 ) ),
    inference(resolution,[status(thm)],[c_36,c_592])).

tff(c_637,plain,(
    ! [A_154,C_155] :
      ( r2_hidden('#skF_4'(A_154,A_154,C_155),C_155)
      | k4_xboole_0(A_154,A_154) = C_155 ) ),
    inference(resolution,[status(thm)],[c_36,c_592])).

tff(c_172,plain,(
    ! [D_77,B_78,A_79] :
      ( ~ r2_hidden(D_77,B_78)
      | ~ r2_hidden(D_77,k4_xboole_0(A_79,B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_175,plain,(
    ! [D_77,A_20] :
      ( ~ r2_hidden(D_77,A_20)
      | ~ r2_hidden(D_77,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_172])).

tff(c_669,plain,(
    ! [A_156,C_157] :
      ( ~ r2_hidden('#skF_4'(A_156,A_156,C_157),k1_xboole_0)
      | k4_xboole_0(A_156,A_156) = C_157 ) ),
    inference(resolution,[status(thm)],[c_637,c_175])).

tff(c_688,plain,(
    ! [A_158] : k4_xboole_0(A_158,A_158) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_602,c_669])).

tff(c_24,plain,(
    ! [D_12,A_7,B_8] :
      ( r2_hidden(D_12,A_7)
      | ~ r2_hidden(D_12,k4_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_711,plain,(
    ! [D_12,A_158] :
      ( r2_hidden(D_12,A_158)
      | ~ r2_hidden(D_12,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_688,c_24])).

tff(c_19896,plain,(
    ! [A_653,A_654,A_158] :
      ( r2_hidden('#skF_2'(A_653,k4_xboole_0(A_654,A_653),k1_xboole_0),A_158)
      | k3_xboole_0(A_653,k4_xboole_0(A_654,A_653)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_19732,c_711])).

tff(c_21144,plain,(
    ! [A_684,A_685,A_686] :
      ( r2_hidden('#skF_2'(A_684,k4_xboole_0(A_685,A_684),k1_xboole_0),A_686)
      | k3_xboole_0(A_684,k4_xboole_0(A_685,A_684)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_19732,c_711])).

tff(c_3029,plain,(
    ! [D_12] :
      ( ~ r2_hidden(D_12,'#skF_6')
      | ~ r2_hidden(D_12,k2_tops_1('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2991,c_22])).

tff(c_32584,plain,(
    ! [A_822,A_823] :
      ( ~ r2_hidden('#skF_2'(A_822,k4_xboole_0(A_823,A_822),k1_xboole_0),'#skF_6')
      | k3_xboole_0(A_822,k4_xboole_0(A_823,A_822)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_21144,c_3029])).

tff(c_32724,plain,(
    ! [A_824,A_825] : k3_xboole_0(A_824,k4_xboole_0(A_825,A_824)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_19896,c_32584])).

tff(c_33041,plain,(
    k3_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2991,c_32724])).

tff(c_46,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_33799,plain,(
    k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_33041,c_46])).

tff(c_33867,plain,(
    k1_tops_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_1004,c_33799])).

tff(c_58,plain,(
    ! [A_28,B_29] : k6_subset_1(A_28,B_29) = k4_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_56,plain,(
    ! [A_26,B_27] : m1_subset_1(k6_subset_1(A_26,B_27),k1_zfmisc_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_93,plain,(
    ! [A_26,B_27] : m1_subset_1(k4_xboole_0(A_26,B_27),k1_zfmisc_1(A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56])).

tff(c_135,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(A_66,B_67)
      | ~ m1_subset_1(A_66,k1_zfmisc_1(B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_147,plain,(
    ! [A_26,B_27] : r1_tarski(k4_xboole_0(A_26,B_27),A_26) ),
    inference(resolution,[status(thm)],[c_93,c_135])).

tff(c_178,plain,(
    ! [B_82,A_83] :
      ( B_82 = A_83
      | ~ r1_tarski(B_82,A_83)
      | ~ r1_tarski(A_83,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_185,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = A_26
      | ~ r1_tarski(A_26,k4_xboole_0(A_26,B_27)) ) ),
    inference(resolution,[status(thm)],[c_147,c_178])).

tff(c_1033,plain,
    ( k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = '#skF_6'
    | ~ r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1004,c_185])).

tff(c_1052,plain,
    ( k1_tops_1('#skF_5','#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_1033])).

tff(c_1110,plain,(
    ~ r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1052])).

tff(c_33957,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33867,c_1110])).

tff(c_33981,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_33957])).

tff(c_33982,plain,(
    k1_tops_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1052])).

tff(c_84,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_383,plain,(
    ! [A_127,B_128] :
      ( v3_pre_topc(k1_tops_1(A_127,B_128),A_127)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127)
      | ~ v2_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_393,plain,
    ( v3_pre_topc(k1_tops_1('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_383])).

tff(c_399,plain,(
    v3_pre_topc(k1_tops_1('#skF_5','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_393])).

tff(c_33988,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33982,c_399])).

tff(c_33991,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_33988])).

tff(c_33992,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') != k2_tops_1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_34075,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33992,c_125])).

tff(c_34076,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_34079,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') != k2_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34076,c_86])).

tff(c_34244,plain,(
    ! [A_890,B_891,C_892] :
      ( k7_subset_1(A_890,B_891,C_892) = k4_xboole_0(B_891,C_892)
      | ~ m1_subset_1(B_891,k1_zfmisc_1(A_890)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_34257,plain,(
    ! [C_892] : k7_subset_1(u1_struct_0('#skF_5'),'#skF_6',C_892) = k4_xboole_0('#skF_6',C_892) ),
    inference(resolution,[status(thm)],[c_80,c_34244])).

tff(c_34719,plain,(
    ! [A_945,B_946] :
      ( k7_subset_1(u1_struct_0(A_945),B_946,k2_tops_1(A_945,B_946)) = k1_tops_1(A_945,B_946)
      | ~ m1_subset_1(B_946,k1_zfmisc_1(u1_struct_0(A_945)))
      | ~ l1_pre_topc(A_945) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_34732,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),'#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_34719])).

tff(c_34740,plain,(
    k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_34257,c_34732])).

tff(c_34099,plain,(
    ! [A_850,B_851] :
      ( r1_tarski(A_850,B_851)
      | ~ m1_subset_1(A_850,k1_zfmisc_1(B_851)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34127,plain,(
    ! [A_854,B_855] : r1_tarski(k4_xboole_0(A_854,B_855),A_854) ),
    inference(resolution,[status(thm)],[c_93,c_34099])).

tff(c_40,plain,(
    ! [B_16,A_15] :
      ( B_16 = A_15
      | ~ r1_tarski(B_16,A_15)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_34133,plain,(
    ! [A_854,B_855] :
      ( k4_xboole_0(A_854,B_855) = A_854
      | ~ r1_tarski(A_854,k4_xboole_0(A_854,B_855)) ) ),
    inference(resolution,[status(thm)],[c_34127,c_40])).

tff(c_35007,plain,
    ( k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = '#skF_6'
    | ~ r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34740,c_34133])).

tff(c_35029,plain,
    ( k1_tops_1('#skF_5','#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34740,c_35007])).

tff(c_35096,plain,(
    ~ r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_35029])).

tff(c_36908,plain,(
    ! [B_1044,A_1045,C_1046] :
      ( r1_tarski(B_1044,k1_tops_1(A_1045,C_1046))
      | ~ r1_tarski(B_1044,C_1046)
      | ~ v3_pre_topc(B_1044,A_1045)
      | ~ m1_subset_1(C_1046,k1_zfmisc_1(u1_struct_0(A_1045)))
      | ~ m1_subset_1(B_1044,k1_zfmisc_1(u1_struct_0(A_1045)))
      | ~ l1_pre_topc(A_1045) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_36931,plain,(
    ! [B_1044] :
      ( r1_tarski(B_1044,k1_tops_1('#skF_5','#skF_6'))
      | ~ r1_tarski(B_1044,'#skF_6')
      | ~ v3_pre_topc(B_1044,'#skF_5')
      | ~ m1_subset_1(B_1044,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_80,c_36908])).

tff(c_36958,plain,(
    ! [B_1048] :
      ( r1_tarski(B_1048,k1_tops_1('#skF_5','#skF_6'))
      | ~ r1_tarski(B_1048,'#skF_6')
      | ~ v3_pre_topc(B_1048,'#skF_5')
      | ~ m1_subset_1(B_1048,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_36931])).

tff(c_36991,plain,
    ( r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_6','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_36958])).

tff(c_37006,plain,(
    r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34076,c_44,c_36991])).

tff(c_37008,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35096,c_37006])).

tff(c_37009,plain,(
    k1_tops_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_35029])).

tff(c_37115,plain,(
    ! [A_1050,B_1051] :
      ( k7_subset_1(u1_struct_0(A_1050),k2_pre_topc(A_1050,B_1051),k1_tops_1(A_1050,B_1051)) = k2_tops_1(A_1050,B_1051)
      | ~ m1_subset_1(B_1051,k1_zfmisc_1(u1_struct_0(A_1050)))
      | ~ l1_pre_topc(A_1050) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_37124,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_37009,c_37115])).

tff(c_37128,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_37124])).

tff(c_37130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34079,c_37128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:11:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.83/6.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.83/6.76  
% 13.83/6.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.83/6.76  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 13.83/6.76  
% 13.83/6.76  %Foreground sorts:
% 13.83/6.76  
% 13.83/6.76  
% 13.83/6.76  %Background operators:
% 13.83/6.76  
% 13.83/6.76  
% 13.83/6.76  %Foreground operators:
% 13.83/6.76  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 13.83/6.76  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 13.83/6.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.83/6.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.83/6.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.83/6.76  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 13.83/6.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.83/6.76  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 13.83/6.76  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 13.83/6.76  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.83/6.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.83/6.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.83/6.76  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 13.83/6.76  tff('#skF_5', type, '#skF_5': $i).
% 13.83/6.76  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 13.83/6.76  tff('#skF_6', type, '#skF_6': $i).
% 13.83/6.76  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 13.83/6.76  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 13.83/6.76  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 13.83/6.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.83/6.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.83/6.76  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 13.83/6.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.83/6.76  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 13.83/6.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.83/6.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.83/6.76  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 13.83/6.76  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 13.83/6.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.83/6.76  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 13.83/6.76  
% 13.83/6.78  tff(f_141, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 13.83/6.78  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.83/6.78  tff(f_56, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 13.83/6.78  tff(f_58, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 13.83/6.78  tff(f_60, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 13.83/6.78  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 13.83/6.78  tff(f_129, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 13.83/6.78  tff(f_86, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 13.83/6.78  tff(f_122, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 13.83/6.78  tff(f_66, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 13.83/6.78  tff(f_80, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 13.83/6.78  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 13.83/6.78  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 13.83/6.78  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 13.83/6.78  tff(f_70, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 13.83/6.78  tff(f_68, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 13.83/6.78  tff(f_94, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 13.83/6.78  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 13.83/6.78  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 13.83/6.78  tff(c_86, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')!=k2_tops_1('#skF_5', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 13.83/6.78  tff(c_177, plain, (~v3_pre_topc('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_86])).
% 13.83/6.78  tff(c_44, plain, (![B_16]: (r1_tarski(B_16, B_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.83/6.78  tff(c_48, plain, (![A_19]: (k2_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_56])).
% 13.83/6.78  tff(c_50, plain, (![A_20]: (k4_xboole_0(k1_xboole_0, A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 13.83/6.78  tff(c_221, plain, (![A_93, B_94]: (k5_xboole_0(A_93, k4_xboole_0(B_94, A_93))=k2_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.83/6.78  tff(c_230, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=k2_xboole_0(A_20, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_221])).
% 13.83/6.78  tff(c_233, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_230])).
% 13.83/6.78  tff(c_82, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 13.83/6.78  tff(c_80, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 13.83/6.78  tff(c_294, plain, (![A_107, B_108, C_109]: (k7_subset_1(A_107, B_108, C_109)=k4_xboole_0(B_108, C_109) | ~m1_subset_1(B_108, k1_zfmisc_1(A_107)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.83/6.78  tff(c_307, plain, (![C_109]: (k7_subset_1(u1_struct_0('#skF_5'), '#skF_6', C_109)=k4_xboole_0('#skF_6', C_109))), inference(resolution, [status(thm)], [c_80, c_294])).
% 13.83/6.78  tff(c_978, plain, (![A_178, B_179]: (k7_subset_1(u1_struct_0(A_178), B_179, k2_tops_1(A_178, B_179))=k1_tops_1(A_178, B_179) | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0(A_178))) | ~l1_pre_topc(A_178))), inference(cnfTransformation, [status(thm)], [f_129])).
% 13.83/6.78  tff(c_994, plain, (k7_subset_1(u1_struct_0('#skF_5'), '#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_80, c_978])).
% 13.83/6.78  tff(c_1004, plain, (k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_307, c_994])).
% 13.83/6.78  tff(c_68, plain, (![A_37, B_38]: (m1_subset_1(k2_tops_1(A_37, B_38), k1_zfmisc_1(u1_struct_0(A_37))) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.83/6.78  tff(c_843, plain, (![A_167, B_168]: (k4_subset_1(u1_struct_0(A_167), B_168, k2_tops_1(A_167, B_168))=k2_pre_topc(A_167, B_168) | ~m1_subset_1(B_168, k1_zfmisc_1(u1_struct_0(A_167))) | ~l1_pre_topc(A_167))), inference(cnfTransformation, [status(thm)], [f_122])).
% 13.83/6.78  tff(c_859, plain, (k4_subset_1(u1_struct_0('#skF_5'), '#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k2_pre_topc('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_80, c_843])).
% 13.83/6.78  tff(c_867, plain, (k4_subset_1(u1_struct_0('#skF_5'), '#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k2_pre_topc('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_859])).
% 13.83/6.78  tff(c_402, plain, (![A_133, B_134, C_135]: (m1_subset_1(k4_subset_1(A_133, B_134, C_135), k1_zfmisc_1(A_133)) | ~m1_subset_1(C_135, k1_zfmisc_1(A_133)) | ~m1_subset_1(B_134, k1_zfmisc_1(A_133)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 13.83/6.78  tff(c_64, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | ~m1_subset_1(A_35, k1_zfmisc_1(B_36)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 13.83/6.78  tff(c_413, plain, (![A_133, B_134, C_135]: (r1_tarski(k4_subset_1(A_133, B_134, C_135), A_133) | ~m1_subset_1(C_135, k1_zfmisc_1(A_133)) | ~m1_subset_1(B_134, k1_zfmisc_1(A_133)))), inference(resolution, [status(thm)], [c_402, c_64])).
% 13.83/6.78  tff(c_890, plain, (r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | ~m1_subset_1(k2_tops_1('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_867, c_413])).
% 13.83/6.78  tff(c_897, plain, (r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | ~m1_subset_1(k2_tops_1('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_890])).
% 13.83/6.78  tff(c_2839, plain, (~m1_subset_1(k2_tops_1('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_897])).
% 13.83/6.78  tff(c_2889, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_68, c_2839])).
% 13.83/6.78  tff(c_2896, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_2889])).
% 13.83/6.78  tff(c_2897, plain, (r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_897])).
% 13.83/6.78  tff(c_66, plain, (![A_35, B_36]: (m1_subset_1(A_35, k1_zfmisc_1(B_36)) | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_80])).
% 13.83/6.78  tff(c_303, plain, (![B_36, A_35, C_109]: (k7_subset_1(B_36, A_35, C_109)=k4_xboole_0(A_35, C_109) | ~r1_tarski(A_35, B_36))), inference(resolution, [status(thm)], [c_66, c_294])).
% 13.83/6.78  tff(c_2981, plain, (![C_260]: (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), C_260)=k4_xboole_0(k2_pre_topc('#skF_5', '#skF_6'), C_260))), inference(resolution, [status(thm)], [c_2897, c_303])).
% 13.83/6.78  tff(c_92, plain, (v3_pre_topc('#skF_6', '#skF_5') | k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_141])).
% 13.83/6.78  tff(c_125, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_92])).
% 13.83/6.78  tff(c_2991, plain, (k4_xboole_0(k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2981, c_125])).
% 13.83/6.78  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.83/6.78  tff(c_478, plain, (![A_142, B_143, C_144]: (r2_hidden('#skF_1'(A_142, B_143, C_144), B_143) | r2_hidden('#skF_2'(A_142, B_143, C_144), C_144) | k3_xboole_0(A_142, B_143)=C_144)), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.83/6.78  tff(c_22, plain, (![D_12, B_8, A_7]: (~r2_hidden(D_12, B_8) | ~r2_hidden(D_12, k4_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.83/6.78  tff(c_17063, plain, (![A_609, A_610, B_611, C_612]: (~r2_hidden('#skF_1'(A_609, k4_xboole_0(A_610, B_611), C_612), B_611) | r2_hidden('#skF_2'(A_609, k4_xboole_0(A_610, B_611), C_612), C_612) | k3_xboole_0(A_609, k4_xboole_0(A_610, B_611))=C_612)), inference(resolution, [status(thm)], [c_478, c_22])).
% 13.83/6.78  tff(c_19732, plain, (![A_653, A_654, C_655]: (r2_hidden('#skF_2'(A_653, k4_xboole_0(A_654, A_653), C_655), C_655) | k3_xboole_0(A_653, k4_xboole_0(A_654, A_653))=C_655)), inference(resolution, [status(thm)], [c_18, c_17063])).
% 13.83/6.78  tff(c_36, plain, (![A_7, B_8, C_9]: (r2_hidden('#skF_3'(A_7, B_8, C_9), A_7) | r2_hidden('#skF_4'(A_7, B_8, C_9), C_9) | k4_xboole_0(A_7, B_8)=C_9)), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.83/6.78  tff(c_592, plain, (![A_148, B_149, C_150]: (~r2_hidden('#skF_3'(A_148, B_149, C_150), B_149) | r2_hidden('#skF_4'(A_148, B_149, C_150), C_150) | k4_xboole_0(A_148, B_149)=C_150)), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.83/6.78  tff(c_602, plain, (![A_7, C_9]: (r2_hidden('#skF_4'(A_7, A_7, C_9), C_9) | k4_xboole_0(A_7, A_7)=C_9)), inference(resolution, [status(thm)], [c_36, c_592])).
% 13.83/6.78  tff(c_637, plain, (![A_154, C_155]: (r2_hidden('#skF_4'(A_154, A_154, C_155), C_155) | k4_xboole_0(A_154, A_154)=C_155)), inference(resolution, [status(thm)], [c_36, c_592])).
% 13.83/6.78  tff(c_172, plain, (![D_77, B_78, A_79]: (~r2_hidden(D_77, B_78) | ~r2_hidden(D_77, k4_xboole_0(A_79, B_78)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.83/6.78  tff(c_175, plain, (![D_77, A_20]: (~r2_hidden(D_77, A_20) | ~r2_hidden(D_77, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_172])).
% 13.83/6.78  tff(c_669, plain, (![A_156, C_157]: (~r2_hidden('#skF_4'(A_156, A_156, C_157), k1_xboole_0) | k4_xboole_0(A_156, A_156)=C_157)), inference(resolution, [status(thm)], [c_637, c_175])).
% 13.83/6.78  tff(c_688, plain, (![A_158]: (k4_xboole_0(A_158, A_158)=k1_xboole_0)), inference(resolution, [status(thm)], [c_602, c_669])).
% 13.83/6.78  tff(c_24, plain, (![D_12, A_7, B_8]: (r2_hidden(D_12, A_7) | ~r2_hidden(D_12, k4_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.83/6.78  tff(c_711, plain, (![D_12, A_158]: (r2_hidden(D_12, A_158) | ~r2_hidden(D_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_688, c_24])).
% 13.83/6.78  tff(c_19896, plain, (![A_653, A_654, A_158]: (r2_hidden('#skF_2'(A_653, k4_xboole_0(A_654, A_653), k1_xboole_0), A_158) | k3_xboole_0(A_653, k4_xboole_0(A_654, A_653))=k1_xboole_0)), inference(resolution, [status(thm)], [c_19732, c_711])).
% 13.83/6.78  tff(c_21144, plain, (![A_684, A_685, A_686]: (r2_hidden('#skF_2'(A_684, k4_xboole_0(A_685, A_684), k1_xboole_0), A_686) | k3_xboole_0(A_684, k4_xboole_0(A_685, A_684))=k1_xboole_0)), inference(resolution, [status(thm)], [c_19732, c_711])).
% 13.83/6.78  tff(c_3029, plain, (![D_12]: (~r2_hidden(D_12, '#skF_6') | ~r2_hidden(D_12, k2_tops_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_2991, c_22])).
% 13.83/6.78  tff(c_32584, plain, (![A_822, A_823]: (~r2_hidden('#skF_2'(A_822, k4_xboole_0(A_823, A_822), k1_xboole_0), '#skF_6') | k3_xboole_0(A_822, k4_xboole_0(A_823, A_822))=k1_xboole_0)), inference(resolution, [status(thm)], [c_21144, c_3029])).
% 13.83/6.78  tff(c_32724, plain, (![A_824, A_825]: (k3_xboole_0(A_824, k4_xboole_0(A_825, A_824))=k1_xboole_0)), inference(resolution, [status(thm)], [c_19896, c_32584])).
% 13.83/6.78  tff(c_33041, plain, (k3_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2991, c_32724])).
% 13.83/6.78  tff(c_46, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 13.83/6.78  tff(c_33799, plain, (k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k5_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_33041, c_46])).
% 13.83/6.78  tff(c_33867, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_233, c_1004, c_33799])).
% 13.83/6.78  tff(c_58, plain, (![A_28, B_29]: (k6_subset_1(A_28, B_29)=k4_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.83/6.78  tff(c_56, plain, (![A_26, B_27]: (m1_subset_1(k6_subset_1(A_26, B_27), k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.83/6.78  tff(c_93, plain, (![A_26, B_27]: (m1_subset_1(k4_xboole_0(A_26, B_27), k1_zfmisc_1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56])).
% 13.83/6.78  tff(c_135, plain, (![A_66, B_67]: (r1_tarski(A_66, B_67) | ~m1_subset_1(A_66, k1_zfmisc_1(B_67)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 13.83/6.78  tff(c_147, plain, (![A_26, B_27]: (r1_tarski(k4_xboole_0(A_26, B_27), A_26))), inference(resolution, [status(thm)], [c_93, c_135])).
% 13.83/6.78  tff(c_178, plain, (![B_82, A_83]: (B_82=A_83 | ~r1_tarski(B_82, A_83) | ~r1_tarski(A_83, B_82))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.83/6.78  tff(c_185, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=A_26 | ~r1_tarski(A_26, k4_xboole_0(A_26, B_27)))), inference(resolution, [status(thm)], [c_147, c_178])).
% 13.83/6.78  tff(c_1033, plain, (k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))='#skF_6' | ~r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1004, c_185])).
% 13.83/6.78  tff(c_1052, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_1033])).
% 13.83/6.78  tff(c_1110, plain, (~r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_1052])).
% 13.83/6.78  tff(c_33957, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_33867, c_1110])).
% 13.83/6.78  tff(c_33981, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_33957])).
% 13.83/6.78  tff(c_33982, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_1052])).
% 13.83/6.78  tff(c_84, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 13.83/6.78  tff(c_383, plain, (![A_127, B_128]: (v3_pre_topc(k1_tops_1(A_127, B_128), A_127) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127) | ~v2_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.83/6.78  tff(c_393, plain, (v3_pre_topc(k1_tops_1('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_80, c_383])).
% 13.83/6.78  tff(c_399, plain, (v3_pre_topc(k1_tops_1('#skF_5', '#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_393])).
% 13.83/6.78  tff(c_33988, plain, (v3_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_33982, c_399])).
% 13.83/6.78  tff(c_33991, plain, $false, inference(negUnitSimplification, [status(thm)], [c_177, c_33988])).
% 13.83/6.78  tff(c_33992, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')!=k2_tops_1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_86])).
% 13.83/6.78  tff(c_34075, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33992, c_125])).
% 13.83/6.78  tff(c_34076, plain, (v3_pre_topc('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_92])).
% 13.83/6.78  tff(c_34079, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')!=k2_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34076, c_86])).
% 13.83/6.78  tff(c_34244, plain, (![A_890, B_891, C_892]: (k7_subset_1(A_890, B_891, C_892)=k4_xboole_0(B_891, C_892) | ~m1_subset_1(B_891, k1_zfmisc_1(A_890)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.83/6.78  tff(c_34257, plain, (![C_892]: (k7_subset_1(u1_struct_0('#skF_5'), '#skF_6', C_892)=k4_xboole_0('#skF_6', C_892))), inference(resolution, [status(thm)], [c_80, c_34244])).
% 13.83/6.78  tff(c_34719, plain, (![A_945, B_946]: (k7_subset_1(u1_struct_0(A_945), B_946, k2_tops_1(A_945, B_946))=k1_tops_1(A_945, B_946) | ~m1_subset_1(B_946, k1_zfmisc_1(u1_struct_0(A_945))) | ~l1_pre_topc(A_945))), inference(cnfTransformation, [status(thm)], [f_129])).
% 13.83/6.78  tff(c_34732, plain, (k7_subset_1(u1_struct_0('#skF_5'), '#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_80, c_34719])).
% 13.83/6.78  tff(c_34740, plain, (k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_34257, c_34732])).
% 13.83/6.78  tff(c_34099, plain, (![A_850, B_851]: (r1_tarski(A_850, B_851) | ~m1_subset_1(A_850, k1_zfmisc_1(B_851)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 13.83/6.78  tff(c_34127, plain, (![A_854, B_855]: (r1_tarski(k4_xboole_0(A_854, B_855), A_854))), inference(resolution, [status(thm)], [c_93, c_34099])).
% 13.83/6.78  tff(c_40, plain, (![B_16, A_15]: (B_16=A_15 | ~r1_tarski(B_16, A_15) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.83/6.78  tff(c_34133, plain, (![A_854, B_855]: (k4_xboole_0(A_854, B_855)=A_854 | ~r1_tarski(A_854, k4_xboole_0(A_854, B_855)))), inference(resolution, [status(thm)], [c_34127, c_40])).
% 13.83/6.78  tff(c_35007, plain, (k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))='#skF_6' | ~r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_34740, c_34133])).
% 13.83/6.78  tff(c_35029, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_34740, c_35007])).
% 13.83/6.78  tff(c_35096, plain, (~r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_35029])).
% 13.83/6.78  tff(c_36908, plain, (![B_1044, A_1045, C_1046]: (r1_tarski(B_1044, k1_tops_1(A_1045, C_1046)) | ~r1_tarski(B_1044, C_1046) | ~v3_pre_topc(B_1044, A_1045) | ~m1_subset_1(C_1046, k1_zfmisc_1(u1_struct_0(A_1045))) | ~m1_subset_1(B_1044, k1_zfmisc_1(u1_struct_0(A_1045))) | ~l1_pre_topc(A_1045))), inference(cnfTransformation, [status(thm)], [f_115])).
% 13.83/6.78  tff(c_36931, plain, (![B_1044]: (r1_tarski(B_1044, k1_tops_1('#skF_5', '#skF_6')) | ~r1_tarski(B_1044, '#skF_6') | ~v3_pre_topc(B_1044, '#skF_5') | ~m1_subset_1(B_1044, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_80, c_36908])).
% 13.83/6.78  tff(c_36958, plain, (![B_1048]: (r1_tarski(B_1048, k1_tops_1('#skF_5', '#skF_6')) | ~r1_tarski(B_1048, '#skF_6') | ~v3_pre_topc(B_1048, '#skF_5') | ~m1_subset_1(B_1048, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_36931])).
% 13.83/6.78  tff(c_36991, plain, (r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6')) | ~r1_tarski('#skF_6', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_80, c_36958])).
% 13.83/6.78  tff(c_37006, plain, (r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_34076, c_44, c_36991])).
% 13.83/6.78  tff(c_37008, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35096, c_37006])).
% 13.83/6.78  tff(c_37009, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_35029])).
% 13.83/6.78  tff(c_37115, plain, (![A_1050, B_1051]: (k7_subset_1(u1_struct_0(A_1050), k2_pre_topc(A_1050, B_1051), k1_tops_1(A_1050, B_1051))=k2_tops_1(A_1050, B_1051) | ~m1_subset_1(B_1051, k1_zfmisc_1(u1_struct_0(A_1050))) | ~l1_pre_topc(A_1050))), inference(cnfTransformation, [status(thm)], [f_101])).
% 13.83/6.78  tff(c_37124, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_37009, c_37115])).
% 13.83/6.78  tff(c_37128, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_37124])).
% 13.83/6.78  tff(c_37130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34079, c_37128])).
% 13.83/6.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.83/6.78  
% 13.83/6.78  Inference rules
% 13.83/6.78  ----------------------
% 13.83/6.78  #Ref     : 0
% 13.83/6.78  #Sup     : 8564
% 13.83/6.78  #Fact    : 0
% 13.83/6.78  #Define  : 0
% 13.83/6.78  #Split   : 28
% 13.83/6.78  #Chain   : 0
% 13.83/6.78  #Close   : 0
% 13.83/6.78  
% 13.83/6.78  Ordering : KBO
% 13.83/6.78  
% 13.83/6.78  Simplification rules
% 13.83/6.78  ----------------------
% 13.83/6.78  #Subsume      : 2048
% 13.83/6.78  #Demod        : 7249
% 13.83/6.78  #Tautology    : 2666
% 13.83/6.78  #SimpNegUnit  : 226
% 13.83/6.78  #BackRed      : 210
% 13.83/6.78  
% 13.83/6.78  #Partial instantiations: 0
% 13.83/6.78  #Strategies tried      : 1
% 13.83/6.78  
% 13.83/6.78  Timing (in seconds)
% 13.83/6.78  ----------------------
% 13.83/6.79  Preprocessing        : 0.36
% 13.83/6.79  Parsing              : 0.19
% 13.83/6.79  CNF conversion       : 0.03
% 13.83/6.79  Main loop            : 5.62
% 13.83/6.79  Inferencing          : 1.13
% 13.83/6.79  Reduction            : 2.69
% 13.83/6.79  Demodulation         : 2.19
% 13.83/6.79  BG Simplification    : 0.12
% 13.83/6.79  Subsumption          : 1.35
% 13.83/6.79  Abstraction          : 0.18
% 13.83/6.79  MUC search           : 0.00
% 13.83/6.79  Cooper               : 0.00
% 13.83/6.79  Total                : 6.03
% 13.83/6.79  Index Insertion      : 0.00
% 13.83/6.79  Index Deletion       : 0.00
% 13.83/6.79  Index Matching       : 0.00
% 13.83/6.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
