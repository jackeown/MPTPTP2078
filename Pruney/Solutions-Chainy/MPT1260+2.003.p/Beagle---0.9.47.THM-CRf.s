%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:01 EST 2020

% Result     : Theorem 12.13s
% Output     : CNFRefutation 12.13s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 207 expanded)
%              Number of leaves         :   50 (  91 expanded)
%              Depth                    :   11
%              Number of atoms          :  165 ( 336 expanded)
%              Number of equality atoms :   67 ( 124 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_177,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_165,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_69,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_130,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_151,axiom,(
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

tff(f_137,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_92,plain,
    ( k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') != k2_tops_1('#skF_4','#skF_5')
    | ~ v3_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_323,plain,(
    ~ v3_pre_topc('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_88,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_86,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_1618,plain,(
    ! [A_185,B_186,C_187] :
      ( k7_subset_1(A_185,B_186,C_187) = k4_xboole_0(B_186,C_187)
      | ~ m1_subset_1(B_186,k1_zfmisc_1(A_185)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1648,plain,(
    ! [C_187] : k7_subset_1(u1_struct_0('#skF_4'),'#skF_5',C_187) = k4_xboole_0('#skF_5',C_187) ),
    inference(resolution,[status(thm)],[c_86,c_1618])).

tff(c_4996,plain,(
    ! [A_291,B_292] :
      ( k7_subset_1(u1_struct_0(A_291),B_292,k2_tops_1(A_291,B_292)) = k1_tops_1(A_291,B_292)
      | ~ m1_subset_1(B_292,k1_zfmisc_1(u1_struct_0(A_291)))
      | ~ l1_pre_topc(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_5026,plain,
    ( k7_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_tops_1('#skF_4','#skF_5')) = k1_tops_1('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_4996])).

tff(c_5046,plain,(
    k4_xboole_0('#skF_5',k2_tops_1('#skF_4','#skF_5')) = k1_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1648,c_5026])).

tff(c_36,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_195,plain,(
    ! [A_93,B_94] : k4_xboole_0(A_93,k2_xboole_0(A_93,B_94)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_56,plain,(
    ! [A_40,B_41] : k6_subset_1(A_40,B_41) = k4_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_48,plain,(
    ! [A_29,B_30] : m1_subset_1(k6_subset_1(A_29,B_30),k1_zfmisc_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_99,plain,(
    ! [A_29,B_30] : m1_subset_1(k4_xboole_0(A_29,B_30),k1_zfmisc_1(A_29)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_48])).

tff(c_200,plain,(
    ! [A_93] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_99])).

tff(c_792,plain,(
    ! [A_143,B_144] :
      ( k4_xboole_0(A_143,B_144) = k3_subset_1(A_143,B_144)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(A_143)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_801,plain,(
    ! [A_93] : k4_xboole_0(A_93,k1_xboole_0) = k3_subset_1(A_93,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_200,c_792])).

tff(c_817,plain,(
    ! [A_93] : k3_subset_1(A_93,k1_xboole_0) = A_93 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_801])).

tff(c_98,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k2_tops_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_445,plain,(
    k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k2_tops_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_323,c_98])).

tff(c_2712,plain,(
    ! [A_227,B_228] :
      ( m1_subset_1(k2_pre_topc(A_227,B_228),k1_zfmisc_1(u1_struct_0(A_227)))
      | ~ m1_subset_1(B_228,k1_zfmisc_1(u1_struct_0(A_227)))
      | ~ l1_pre_topc(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_58,plain,(
    ! [A_42,B_43,C_44] :
      ( k7_subset_1(A_42,B_43,C_44) = k4_xboole_0(B_43,C_44)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_26811,plain,(
    ! [A_563,B_564,C_565] :
      ( k7_subset_1(u1_struct_0(A_563),k2_pre_topc(A_563,B_564),C_565) = k4_xboole_0(k2_pre_topc(A_563,B_564),C_565)
      | ~ m1_subset_1(B_564,k1_zfmisc_1(u1_struct_0(A_563)))
      | ~ l1_pre_topc(A_563) ) ),
    inference(resolution,[status(thm)],[c_2712,c_58])).

tff(c_26843,plain,(
    ! [C_565] :
      ( k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),C_565) = k4_xboole_0(k2_pre_topc('#skF_4','#skF_5'),C_565)
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_86,c_26811])).

tff(c_26945,plain,(
    ! [C_567] : k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),C_567) = k4_xboole_0(k2_pre_topc('#skF_4','#skF_5'),C_567) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_26843])).

tff(c_26973,plain,(
    k4_xboole_0(k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k2_tops_1('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_26945])).

tff(c_38,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k2_xboole_0(A_18,B_19)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_9] : k3_xboole_0(A_9,A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1895,plain,(
    ! [A_205,B_206,C_207] : k2_xboole_0(k4_xboole_0(A_205,B_206),k3_xboole_0(A_205,C_207)) = k4_xboole_0(A_205,k4_xboole_0(B_206,C_207)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1964,plain,(
    ! [A_9,B_206] : k4_xboole_0(A_9,k4_xboole_0(B_206,A_9)) = k2_xboole_0(k4_xboole_0(A_9,B_206),A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1895])).

tff(c_8890,plain,(
    ! [A_354,B_355] : k4_xboole_0(A_354,k4_xboole_0(B_355,A_354)) = k2_xboole_0(A_354,k4_xboole_0(A_354,B_355)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1964])).

tff(c_32,plain,(
    ! [A_15] : k2_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_208,plain,(
    ! [B_95,A_96] : k2_xboole_0(B_95,A_96) = k2_xboole_0(A_96,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_252,plain,(
    ! [A_15] : k2_xboole_0(k1_xboole_0,A_15) = A_15 ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_208])).

tff(c_205,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_195])).

tff(c_1946,plain,(
    ! [A_15,C_207] : k4_xboole_0(A_15,k4_xboole_0(A_15,C_207)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_15,C_207)) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_1895])).

tff(c_1970,plain,(
    ! [A_15,C_207] : k4_xboole_0(A_15,k4_xboole_0(A_15,C_207)) = k3_xboole_0(A_15,C_207) ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_1946])).

tff(c_8918,plain,(
    ! [A_354,B_355] : k4_xboole_0(A_354,k2_xboole_0(A_354,k4_xboole_0(A_354,B_355))) = k3_xboole_0(A_354,k4_xboole_0(B_355,A_354)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8890,c_1970])).

tff(c_9022,plain,(
    ! [A_354,B_355] : k3_xboole_0(A_354,k4_xboole_0(B_355,A_354)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_8918])).

tff(c_27108,plain,(
    k3_xboole_0('#skF_5',k2_tops_1('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26973,c_9022])).

tff(c_820,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k3_subset_1(A_29,k4_xboole_0(A_29,B_30)) ),
    inference(resolution,[status(thm)],[c_99,c_792])).

tff(c_2379,plain,(
    ! [A_29,B_30] : k3_subset_1(A_29,k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1970,c_820])).

tff(c_913,plain,(
    ! [A_148,B_149] :
      ( k3_subset_1(A_148,k3_subset_1(A_148,B_149)) = B_149
      | ~ m1_subset_1(B_149,k1_zfmisc_1(A_148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_934,plain,(
    ! [A_29,B_30] : k3_subset_1(A_29,k3_subset_1(A_29,k4_xboole_0(A_29,B_30))) = k4_xboole_0(A_29,B_30) ),
    inference(resolution,[status(thm)],[c_99,c_913])).

tff(c_3822,plain,(
    ! [A_29,B_30] : k3_subset_1(A_29,k3_xboole_0(A_29,B_30)) = k4_xboole_0(A_29,B_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2379,c_934])).

tff(c_27239,plain,(
    k4_xboole_0('#skF_5',k2_tops_1('#skF_4','#skF_5')) = k3_subset_1('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_27108,c_3822])).

tff(c_27304,plain,(
    k1_tops_1('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5046,c_817,c_27239])).

tff(c_90,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_3067,plain,(
    ! [A_239,B_240] :
      ( v3_pre_topc(k1_tops_1(A_239,B_240),A_239)
      | ~ m1_subset_1(B_240,k1_zfmisc_1(u1_struct_0(A_239)))
      | ~ l1_pre_topc(A_239)
      | ~ v2_pre_topc(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3097,plain,
    ( v3_pre_topc(k1_tops_1('#skF_4','#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_3067])).

tff(c_3115,plain,(
    v3_pre_topc(k1_tops_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_3097])).

tff(c_27340,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27304,c_3115])).

tff(c_27360,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_323,c_27340])).

tff(c_27361,plain,(
    k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') != k2_tops_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_28227,plain,(
    ! [A_637,B_638,C_639] :
      ( k7_subset_1(A_637,B_638,C_639) = k4_xboole_0(B_638,C_639)
      | ~ m1_subset_1(B_638,k1_zfmisc_1(A_637)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_28254,plain,(
    ! [C_639] : k7_subset_1(u1_struct_0('#skF_4'),'#skF_5',C_639) = k4_xboole_0('#skF_5',C_639) ),
    inference(resolution,[status(thm)],[c_86,c_28227])).

tff(c_32070,plain,(
    ! [A_759,B_760] :
      ( k7_subset_1(u1_struct_0(A_759),B_760,k2_tops_1(A_759,B_760)) = k1_tops_1(A_759,B_760)
      | ~ m1_subset_1(B_760,k1_zfmisc_1(u1_struct_0(A_759)))
      | ~ l1_pre_topc(A_759) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_32100,plain,
    ( k7_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_tops_1('#skF_4','#skF_5')) = k1_tops_1('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_32070])).

tff(c_32120,plain,(
    k4_xboole_0('#skF_5',k2_tops_1('#skF_4','#skF_5')) = k1_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_28254,c_32100])).

tff(c_27463,plain,(
    ! [A_575,B_576] :
      ( r1_tarski(A_575,B_576)
      | ~ m1_subset_1(A_575,k1_zfmisc_1(B_576)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_27482,plain,(
    ! [A_29,B_30] : r1_tarski(k4_xboole_0(A_29,B_30),A_29) ),
    inference(resolution,[status(thm)],[c_99,c_27463])).

tff(c_32161,plain,(
    r1_tarski(k1_tops_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_32120,c_27482])).

tff(c_27362,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_28,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_35399,plain,(
    ! [B_812,A_813,C_814] :
      ( r1_tarski(B_812,k1_tops_1(A_813,C_814))
      | ~ r1_tarski(B_812,C_814)
      | ~ v3_pre_topc(B_812,A_813)
      | ~ m1_subset_1(C_814,k1_zfmisc_1(u1_struct_0(A_813)))
      | ~ m1_subset_1(B_812,k1_zfmisc_1(u1_struct_0(A_813)))
      | ~ l1_pre_topc(A_813) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_35429,plain,(
    ! [B_812] :
      ( r1_tarski(B_812,k1_tops_1('#skF_4','#skF_5'))
      | ~ r1_tarski(B_812,'#skF_5')
      | ~ v3_pre_topc(B_812,'#skF_4')
      | ~ m1_subset_1(B_812,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_86,c_35399])).

tff(c_35589,plain,(
    ! [B_817] :
      ( r1_tarski(B_817,k1_tops_1('#skF_4','#skF_5'))
      | ~ r1_tarski(B_817,'#skF_5')
      | ~ v3_pre_topc(B_817,'#skF_4')
      | ~ m1_subset_1(B_817,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_35429])).

tff(c_35631,plain,
    ( r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5'))
    | ~ r1_tarski('#skF_5','#skF_5')
    | ~ v3_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_35589])).

tff(c_35652,plain,(
    r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27362,c_28,c_35631])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_35660,plain,
    ( k1_tops_1('#skF_4','#skF_5') = '#skF_5'
    | ~ r1_tarski(k1_tops_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_35652,c_24])).

tff(c_35665,plain,(
    k1_tops_1('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32161,c_35660])).

tff(c_78,plain,(
    ! [A_62,B_64] :
      ( k7_subset_1(u1_struct_0(A_62),k2_pre_topc(A_62,B_64),k1_tops_1(A_62,B_64)) = k2_tops_1(A_62,B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_35693,plain,
    ( k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k2_tops_1('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_35665,c_78])).

tff(c_35697,plain,(
    k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k2_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_35693])).

tff(c_35699,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27361,c_35697])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.31  % Computer   : n020.cluster.edu
% 0.13/0.31  % Model      : x86_64 x86_64
% 0.13/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.31  % Memory     : 8042.1875MB
% 0.13/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.31  % CPULimit   : 60
% 0.13/0.31  % DateTime   : Tue Dec  1 13:04:22 EST 2020
% 0.17/0.31  % CPUTime    : 
% 0.17/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.13/5.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.13/5.24  
% 12.13/5.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.13/5.24  %$ v3_pre_topc > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 12.13/5.24  
% 12.13/5.24  %Foreground sorts:
% 12.13/5.24  
% 12.13/5.24  
% 12.13/5.24  %Background operators:
% 12.13/5.24  
% 12.13/5.24  
% 12.13/5.24  %Foreground operators:
% 12.13/5.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.13/5.24  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 12.13/5.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.13/5.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.13/5.24  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 12.13/5.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.13/5.24  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 12.13/5.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.13/5.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.13/5.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.13/5.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.13/5.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.13/5.24  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 12.13/5.24  tff('#skF_5', type, '#skF_5': $i).
% 12.13/5.24  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 12.13/5.24  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 12.13/5.24  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 12.13/5.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.13/5.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.13/5.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.13/5.24  tff('#skF_4', type, '#skF_4': $i).
% 12.13/5.24  tff('#skF_3', type, '#skF_3': $i > $i).
% 12.13/5.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.13/5.24  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 12.13/5.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.13/5.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.13/5.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.13/5.24  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 12.13/5.24  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 12.13/5.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.13/5.24  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 12.13/5.24  
% 12.13/5.26  tff(f_177, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 12.13/5.26  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 12.13/5.26  tff(f_165, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 12.13/5.26  tff(f_53, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 12.13/5.26  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 12.13/5.26  tff(f_86, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 12.13/5.26  tff(f_69, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 12.13/5.26  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 12.13/5.26  tff(f_115, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 12.13/5.26  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 12.13/5.26  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 12.13/5.26  tff(f_57, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 12.13/5.26  tff(f_49, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 12.13/5.26  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 12.13/5.26  tff(f_130, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 12.13/5.26  tff(f_109, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 12.13/5.26  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.13/5.26  tff(f_151, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 12.13/5.26  tff(f_137, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 12.13/5.26  tff(c_92, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')!=k2_tops_1('#skF_4', '#skF_5') | ~v3_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_177])).
% 12.13/5.26  tff(c_323, plain, (~v3_pre_topc('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_92])).
% 12.13/5.26  tff(c_88, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_177])).
% 12.13/5.26  tff(c_86, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_177])).
% 12.13/5.26  tff(c_1618, plain, (![A_185, B_186, C_187]: (k7_subset_1(A_185, B_186, C_187)=k4_xboole_0(B_186, C_187) | ~m1_subset_1(B_186, k1_zfmisc_1(A_185)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.13/5.26  tff(c_1648, plain, (![C_187]: (k7_subset_1(u1_struct_0('#skF_4'), '#skF_5', C_187)=k4_xboole_0('#skF_5', C_187))), inference(resolution, [status(thm)], [c_86, c_1618])).
% 12.13/5.26  tff(c_4996, plain, (![A_291, B_292]: (k7_subset_1(u1_struct_0(A_291), B_292, k2_tops_1(A_291, B_292))=k1_tops_1(A_291, B_292) | ~m1_subset_1(B_292, k1_zfmisc_1(u1_struct_0(A_291))) | ~l1_pre_topc(A_291))), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.13/5.26  tff(c_5026, plain, (k7_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k1_tops_1('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_86, c_4996])).
% 12.13/5.26  tff(c_5046, plain, (k4_xboole_0('#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k1_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1648, c_5026])).
% 12.13/5.26  tff(c_36, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.13/5.26  tff(c_195, plain, (![A_93, B_94]: (k4_xboole_0(A_93, k2_xboole_0(A_93, B_94))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.13/5.26  tff(c_56, plain, (![A_40, B_41]: (k6_subset_1(A_40, B_41)=k4_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.13/5.26  tff(c_48, plain, (![A_29, B_30]: (m1_subset_1(k6_subset_1(A_29, B_30), k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 12.13/5.26  tff(c_99, plain, (![A_29, B_30]: (m1_subset_1(k4_xboole_0(A_29, B_30), k1_zfmisc_1(A_29)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_48])).
% 12.13/5.26  tff(c_200, plain, (![A_93]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_93)))), inference(superposition, [status(thm), theory('equality')], [c_195, c_99])).
% 12.13/5.26  tff(c_792, plain, (![A_143, B_144]: (k4_xboole_0(A_143, B_144)=k3_subset_1(A_143, B_144) | ~m1_subset_1(B_144, k1_zfmisc_1(A_143)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.13/5.26  tff(c_801, plain, (![A_93]: (k4_xboole_0(A_93, k1_xboole_0)=k3_subset_1(A_93, k1_xboole_0))), inference(resolution, [status(thm)], [c_200, c_792])).
% 12.13/5.26  tff(c_817, plain, (![A_93]: (k3_subset_1(A_93, k1_xboole_0)=A_93)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_801])).
% 12.13/5.26  tff(c_98, plain, (v3_pre_topc('#skF_5', '#skF_4') | k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k2_tops_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_177])).
% 12.13/5.26  tff(c_445, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k2_tops_1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_323, c_98])).
% 12.13/5.26  tff(c_2712, plain, (![A_227, B_228]: (m1_subset_1(k2_pre_topc(A_227, B_228), k1_zfmisc_1(u1_struct_0(A_227))) | ~m1_subset_1(B_228, k1_zfmisc_1(u1_struct_0(A_227))) | ~l1_pre_topc(A_227))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.13/5.26  tff(c_58, plain, (![A_42, B_43, C_44]: (k7_subset_1(A_42, B_43, C_44)=k4_xboole_0(B_43, C_44) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.13/5.26  tff(c_26811, plain, (![A_563, B_564, C_565]: (k7_subset_1(u1_struct_0(A_563), k2_pre_topc(A_563, B_564), C_565)=k4_xboole_0(k2_pre_topc(A_563, B_564), C_565) | ~m1_subset_1(B_564, k1_zfmisc_1(u1_struct_0(A_563))) | ~l1_pre_topc(A_563))), inference(resolution, [status(thm)], [c_2712, c_58])).
% 12.13/5.26  tff(c_26843, plain, (![C_565]: (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), C_565)=k4_xboole_0(k2_pre_topc('#skF_4', '#skF_5'), C_565) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_86, c_26811])).
% 12.13/5.26  tff(c_26945, plain, (![C_567]: (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), C_567)=k4_xboole_0(k2_pre_topc('#skF_4', '#skF_5'), C_567))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_26843])).
% 12.13/5.26  tff(c_26973, plain, (k4_xboole_0(k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k2_tops_1('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_445, c_26945])).
% 12.13/5.26  tff(c_38, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k2_xboole_0(A_18, B_19))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.13/5.26  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.13/5.26  tff(c_22, plain, (![A_9]: (k3_xboole_0(A_9, A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.13/5.26  tff(c_1895, plain, (![A_205, B_206, C_207]: (k2_xboole_0(k4_xboole_0(A_205, B_206), k3_xboole_0(A_205, C_207))=k4_xboole_0(A_205, k4_xboole_0(B_206, C_207)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.13/5.26  tff(c_1964, plain, (![A_9, B_206]: (k4_xboole_0(A_9, k4_xboole_0(B_206, A_9))=k2_xboole_0(k4_xboole_0(A_9, B_206), A_9))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1895])).
% 12.13/5.26  tff(c_8890, plain, (![A_354, B_355]: (k4_xboole_0(A_354, k4_xboole_0(B_355, A_354))=k2_xboole_0(A_354, k4_xboole_0(A_354, B_355)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1964])).
% 12.13/5.26  tff(c_32, plain, (![A_15]: (k2_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.13/5.26  tff(c_208, plain, (![B_95, A_96]: (k2_xboole_0(B_95, A_96)=k2_xboole_0(A_96, B_95))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.13/5.26  tff(c_252, plain, (![A_15]: (k2_xboole_0(k1_xboole_0, A_15)=A_15)), inference(superposition, [status(thm), theory('equality')], [c_32, c_208])).
% 12.13/5.26  tff(c_205, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_195])).
% 12.13/5.26  tff(c_1946, plain, (![A_15, C_207]: (k4_xboole_0(A_15, k4_xboole_0(A_15, C_207))=k2_xboole_0(k1_xboole_0, k3_xboole_0(A_15, C_207)))), inference(superposition, [status(thm), theory('equality')], [c_205, c_1895])).
% 12.13/5.26  tff(c_1970, plain, (![A_15, C_207]: (k4_xboole_0(A_15, k4_xboole_0(A_15, C_207))=k3_xboole_0(A_15, C_207))), inference(demodulation, [status(thm), theory('equality')], [c_252, c_1946])).
% 12.13/5.26  tff(c_8918, plain, (![A_354, B_355]: (k4_xboole_0(A_354, k2_xboole_0(A_354, k4_xboole_0(A_354, B_355)))=k3_xboole_0(A_354, k4_xboole_0(B_355, A_354)))), inference(superposition, [status(thm), theory('equality')], [c_8890, c_1970])).
% 12.13/5.26  tff(c_9022, plain, (![A_354, B_355]: (k3_xboole_0(A_354, k4_xboole_0(B_355, A_354))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_8918])).
% 12.13/5.26  tff(c_27108, plain, (k3_xboole_0('#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_26973, c_9022])).
% 12.13/5.26  tff(c_820, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k3_subset_1(A_29, k4_xboole_0(A_29, B_30)))), inference(resolution, [status(thm)], [c_99, c_792])).
% 12.13/5.26  tff(c_2379, plain, (![A_29, B_30]: (k3_subset_1(A_29, k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(demodulation, [status(thm), theory('equality')], [c_1970, c_820])).
% 12.13/5.26  tff(c_913, plain, (![A_148, B_149]: (k3_subset_1(A_148, k3_subset_1(A_148, B_149))=B_149 | ~m1_subset_1(B_149, k1_zfmisc_1(A_148)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 12.13/5.26  tff(c_934, plain, (![A_29, B_30]: (k3_subset_1(A_29, k3_subset_1(A_29, k4_xboole_0(A_29, B_30)))=k4_xboole_0(A_29, B_30))), inference(resolution, [status(thm)], [c_99, c_913])).
% 12.13/5.26  tff(c_3822, plain, (![A_29, B_30]: (k3_subset_1(A_29, k3_xboole_0(A_29, B_30))=k4_xboole_0(A_29, B_30))), inference(demodulation, [status(thm), theory('equality')], [c_2379, c_934])).
% 12.13/5.26  tff(c_27239, plain, (k4_xboole_0('#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k3_subset_1('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_27108, c_3822])).
% 12.13/5.26  tff(c_27304, plain, (k1_tops_1('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_5046, c_817, c_27239])).
% 12.13/5.26  tff(c_90, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_177])).
% 12.13/5.26  tff(c_3067, plain, (![A_239, B_240]: (v3_pre_topc(k1_tops_1(A_239, B_240), A_239) | ~m1_subset_1(B_240, k1_zfmisc_1(u1_struct_0(A_239))) | ~l1_pre_topc(A_239) | ~v2_pre_topc(A_239))), inference(cnfTransformation, [status(thm)], [f_130])).
% 12.13/5.26  tff(c_3097, plain, (v3_pre_topc(k1_tops_1('#skF_4', '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_86, c_3067])).
% 12.13/5.26  tff(c_3115, plain, (v3_pre_topc(k1_tops_1('#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_3097])).
% 12.13/5.26  tff(c_27340, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_27304, c_3115])).
% 12.13/5.26  tff(c_27360, plain, $false, inference(negUnitSimplification, [status(thm)], [c_323, c_27340])).
% 12.13/5.26  tff(c_27361, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')!=k2_tops_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_92])).
% 12.13/5.26  tff(c_28227, plain, (![A_637, B_638, C_639]: (k7_subset_1(A_637, B_638, C_639)=k4_xboole_0(B_638, C_639) | ~m1_subset_1(B_638, k1_zfmisc_1(A_637)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.13/5.26  tff(c_28254, plain, (![C_639]: (k7_subset_1(u1_struct_0('#skF_4'), '#skF_5', C_639)=k4_xboole_0('#skF_5', C_639))), inference(resolution, [status(thm)], [c_86, c_28227])).
% 12.13/5.26  tff(c_32070, plain, (![A_759, B_760]: (k7_subset_1(u1_struct_0(A_759), B_760, k2_tops_1(A_759, B_760))=k1_tops_1(A_759, B_760) | ~m1_subset_1(B_760, k1_zfmisc_1(u1_struct_0(A_759))) | ~l1_pre_topc(A_759))), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.13/5.26  tff(c_32100, plain, (k7_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k1_tops_1('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_86, c_32070])).
% 12.13/5.26  tff(c_32120, plain, (k4_xboole_0('#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k1_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_28254, c_32100])).
% 12.13/5.26  tff(c_27463, plain, (![A_575, B_576]: (r1_tarski(A_575, B_576) | ~m1_subset_1(A_575, k1_zfmisc_1(B_576)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 12.13/5.26  tff(c_27482, plain, (![A_29, B_30]: (r1_tarski(k4_xboole_0(A_29, B_30), A_29))), inference(resolution, [status(thm)], [c_99, c_27463])).
% 12.13/5.26  tff(c_32161, plain, (r1_tarski(k1_tops_1('#skF_4', '#skF_5'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_32120, c_27482])).
% 12.13/5.26  tff(c_27362, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_92])).
% 12.13/5.26  tff(c_28, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.13/5.26  tff(c_35399, plain, (![B_812, A_813, C_814]: (r1_tarski(B_812, k1_tops_1(A_813, C_814)) | ~r1_tarski(B_812, C_814) | ~v3_pre_topc(B_812, A_813) | ~m1_subset_1(C_814, k1_zfmisc_1(u1_struct_0(A_813))) | ~m1_subset_1(B_812, k1_zfmisc_1(u1_struct_0(A_813))) | ~l1_pre_topc(A_813))), inference(cnfTransformation, [status(thm)], [f_151])).
% 12.13/5.26  tff(c_35429, plain, (![B_812]: (r1_tarski(B_812, k1_tops_1('#skF_4', '#skF_5')) | ~r1_tarski(B_812, '#skF_5') | ~v3_pre_topc(B_812, '#skF_4') | ~m1_subset_1(B_812, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_86, c_35399])).
% 12.13/5.26  tff(c_35589, plain, (![B_817]: (r1_tarski(B_817, k1_tops_1('#skF_4', '#skF_5')) | ~r1_tarski(B_817, '#skF_5') | ~v3_pre_topc(B_817, '#skF_4') | ~m1_subset_1(B_817, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_35429])).
% 12.13/5.26  tff(c_35631, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5')) | ~r1_tarski('#skF_5', '#skF_5') | ~v3_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_86, c_35589])).
% 12.13/5.26  tff(c_35652, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_27362, c_28, c_35631])).
% 12.13/5.26  tff(c_24, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.13/5.26  tff(c_35660, plain, (k1_tops_1('#skF_4', '#skF_5')='#skF_5' | ~r1_tarski(k1_tops_1('#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_35652, c_24])).
% 12.13/5.26  tff(c_35665, plain, (k1_tops_1('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_32161, c_35660])).
% 12.13/5.26  tff(c_78, plain, (![A_62, B_64]: (k7_subset_1(u1_struct_0(A_62), k2_pre_topc(A_62, B_64), k1_tops_1(A_62, B_64))=k2_tops_1(A_62, B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_137])).
% 12.13/5.26  tff(c_35693, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k2_tops_1('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_35665, c_78])).
% 12.13/5.26  tff(c_35697, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k2_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_35693])).
% 12.13/5.26  tff(c_35699, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27361, c_35697])).
% 12.13/5.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.13/5.26  
% 12.13/5.26  Inference rules
% 12.13/5.26  ----------------------
% 12.13/5.26  #Ref     : 0
% 12.13/5.26  #Sup     : 8891
% 12.13/5.26  #Fact    : 0
% 12.13/5.26  #Define  : 0
% 12.13/5.26  #Split   : 5
% 12.13/5.26  #Chain   : 0
% 12.13/5.26  #Close   : 0
% 12.13/5.26  
% 12.13/5.26  Ordering : KBO
% 12.13/5.26  
% 12.13/5.26  Simplification rules
% 12.13/5.26  ----------------------
% 12.13/5.26  #Subsume      : 351
% 12.13/5.26  #Demod        : 8086
% 12.13/5.26  #Tautology    : 5968
% 12.13/5.26  #SimpNegUnit  : 3
% 12.13/5.26  #BackRed      : 51
% 12.13/5.26  
% 12.13/5.26  #Partial instantiations: 0
% 12.13/5.26  #Strategies tried      : 1
% 12.13/5.26  
% 12.13/5.26  Timing (in seconds)
% 12.13/5.26  ----------------------
% 12.13/5.26  Preprocessing        : 0.37
% 12.13/5.26  Parsing              : 0.19
% 12.13/5.26  CNF conversion       : 0.03
% 12.13/5.26  Main loop            : 4.13
% 12.13/5.26  Inferencing          : 0.84
% 12.13/5.26  Reduction            : 2.16
% 12.13/5.26  Demodulation         : 1.83
% 12.13/5.26  BG Simplification    : 0.09
% 12.13/5.26  Subsumption          : 0.78
% 12.13/5.26  Abstraction          : 0.15
% 12.13/5.26  MUC search           : 0.00
% 12.13/5.26  Cooper               : 0.00
% 12.13/5.26  Total                : 4.54
% 12.13/5.26  Index Insertion      : 0.00
% 12.13/5.26  Index Deletion       : 0.00
% 12.13/5.26  Index Matching       : 0.00
% 12.13/5.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
