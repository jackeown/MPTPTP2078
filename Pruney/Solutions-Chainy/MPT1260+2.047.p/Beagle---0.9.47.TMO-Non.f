%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:06 EST 2020

% Result     : Timeout 58.20s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  172 (1493 expanded)
%              Number of leaves         :   48 ( 502 expanded)
%              Depth                    :   17
%              Number of atoms          :  277 (3159 expanded)
%              Number of equality atoms :   82 ( 829 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_155,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_136,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_143,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_56,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_129,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

tff(c_60,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_177,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1956,plain,(
    ! [A_173,B_174] :
      ( k4_subset_1(u1_struct_0(A_173),B_174,k2_tops_1(A_173,B_174)) = k2_pre_topc(A_173,B_174)
      | ~ m1_subset_1(B_174,k1_zfmisc_1(u1_struct_0(A_173)))
      | ~ l1_pre_topc(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1989,plain,
    ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_1956])).

tff(c_2029,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1989])).

tff(c_1035,plain,(
    ! [A_155,B_156] :
      ( m1_subset_1(k2_pre_topc(A_155,B_156),k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_pre_topc(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_66,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_114,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_551,plain,(
    ! [A_126,B_127,C_128] :
      ( m1_subset_1(k7_subset_1(A_126,B_127,C_128),k1_zfmisc_1(A_126))
      | ~ m1_subset_1(B_127,k1_zfmisc_1(A_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_625,plain,(
    ! [A_133,B_134,C_135] :
      ( r1_tarski(k7_subset_1(A_133,B_134,C_135),A_133)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(A_133)) ) ),
    inference(resolution,[status(thm)],[c_551,c_36])).

tff(c_633,plain,
    ( r1_tarski(k2_tops_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_625])).

tff(c_995,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_633])).

tff(c_1038,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1035,c_995])).

tff(c_1054,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1038])).

tff(c_1055,plain,(
    r1_tarski(k2_tops_1('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_633])).

tff(c_38,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(A_38,k1_zfmisc_1(B_39))
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1459,plain,(
    ! [A_165,B_166,C_167] :
      ( k4_subset_1(A_165,B_166,C_167) = k2_xboole_0(B_166,C_167)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(A_165))
      | ~ m1_subset_1(B_166,k1_zfmisc_1(A_165)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4659,plain,(
    ! [B_265,B_266,A_267] :
      ( k4_subset_1(B_265,B_266,A_267) = k2_xboole_0(B_266,A_267)
      | ~ m1_subset_1(B_266,k1_zfmisc_1(B_265))
      | ~ r1_tarski(A_267,B_265) ) ),
    inference(resolution,[status(thm)],[c_38,c_1459])).

tff(c_4837,plain,(
    ! [A_269] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',A_269) = k2_xboole_0('#skF_3',A_269)
      | ~ r1_tarski(A_269,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_54,c_4659])).

tff(c_4889,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1055,c_4837])).

tff(c_4955,plain,(
    k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2029,c_4889])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_181,plain,(
    ! [A_89,B_90,C_91] :
      ( r1_tarski(A_89,k2_xboole_0(B_90,C_91))
      | ~ r1_tarski(k4_xboole_0(A_89,B_90),C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_191,plain,(
    ! [A_92,B_93] : r1_tarski(A_92,k2_xboole_0(B_93,A_92)) ),
    inference(resolution,[status(thm)],[c_12,c_181])).

tff(c_200,plain,(
    ! [B_2,A_1] : r1_tarski(B_2,k2_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_191])).

tff(c_5059,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4955,c_200])).

tff(c_1261,plain,(
    ! [A_161,B_162] :
      ( m1_subset_1(k2_pre_topc(A_161,B_162),k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ l1_pre_topc(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_30,plain,(
    ! [A_29,B_30,C_31] :
      ( k7_subset_1(A_29,B_30,C_31) = k4_xboole_0(B_30,C_31)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_9865,plain,(
    ! [A_400,B_401,C_402] :
      ( k7_subset_1(u1_struct_0(A_400),k2_pre_topc(A_400,B_401),C_402) = k4_xboole_0(k2_pre_topc(A_400,B_401),C_402)
      | ~ m1_subset_1(B_401,k1_zfmisc_1(u1_struct_0(A_400)))
      | ~ l1_pre_topc(A_400) ) ),
    inference(resolution,[status(thm)],[c_1261,c_30])).

tff(c_9924,plain,(
    ! [C_402] :
      ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),C_402) = k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),C_402)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_54,c_9865])).

tff(c_10207,plain,(
    ! [C_405] : k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),C_405) = k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),C_405) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_9924])).

tff(c_10233,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10207,c_114])).

tff(c_336,plain,(
    ! [A_112,B_113] :
      ( k4_xboole_0(A_112,B_113) = k3_subset_1(A_112,B_113)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(A_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_376,plain,(
    ! [B_114,A_115] :
      ( k4_xboole_0(B_114,A_115) = k3_subset_1(B_114,A_115)
      | ~ r1_tarski(A_115,B_114) ) ),
    inference(resolution,[status(thm)],[c_38,c_336])).

tff(c_412,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),B_2) = k3_subset_1(k2_xboole_0(B_2,A_1),B_2) ),
    inference(resolution,[status(thm)],[c_200,c_376])).

tff(c_5008,plain,(
    k3_subset_1(k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')),'#skF_3') = k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4955,c_412])).

tff(c_5074,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4955,c_5008])).

tff(c_10312,plain,(
    k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10233,c_5074])).

tff(c_287,plain,(
    ! [A_108,B_109] :
      ( k3_subset_1(A_108,k3_subset_1(A_108,B_109)) = B_109
      | ~ m1_subset_1(B_109,k1_zfmisc_1(A_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_295,plain,(
    ! [B_39,A_38] :
      ( k3_subset_1(B_39,k3_subset_1(B_39,A_38)) = A_38
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(resolution,[status(thm)],[c_38,c_287])).

tff(c_10553,plain,
    ( k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10312,c_295])).

tff(c_10559,plain,(
    k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5059,c_10553])).

tff(c_44,plain,(
    ! [A_44,B_46] :
      ( k7_subset_1(u1_struct_0(A_44),k2_pre_topc(A_44,B_46),k1_tops_1(A_44,B_46)) = k2_tops_1(A_44,B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_10244,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_10207])).

tff(c_10265,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_10244])).

tff(c_417,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_subset_1(A_7,k4_xboole_0(A_7,B_8)) ),
    inference(resolution,[status(thm)],[c_12,c_376])).

tff(c_11392,plain,(
    k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),k1_tops_1('#skF_2','#skF_3'))) = k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10265,c_417])).

tff(c_11422,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10559,c_10265,c_11392])).

tff(c_419,plain,(
    ! [B_116] : k4_xboole_0(B_116,B_116) = k3_subset_1(B_116,B_116) ),
    inference(resolution,[status(thm)],[c_8,c_376])).

tff(c_440,plain,(
    ! [B_116] : r1_tarski(k3_subset_1(B_116,B_116),B_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_12])).

tff(c_418,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k3_subset_1(B_4,B_4) ),
    inference(resolution,[status(thm)],[c_8,c_376])).

tff(c_673,plain,(
    ! [A_138,B_139] : k4_xboole_0(A_138,k4_xboole_0(A_138,B_139)) = k3_subset_1(A_138,k4_xboole_0(A_138,B_139)) ),
    inference(resolution,[status(thm)],[c_12,c_376])).

tff(c_139,plain,(
    ! [B_79,A_80] :
      ( B_79 = A_80
      | ~ r1_tarski(B_79,A_80)
      | ~ r1_tarski(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_150,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,k4_xboole_0(A_7,B_8)) ) ),
    inference(resolution,[status(thm)],[c_12,c_139])).

tff(c_694,plain,(
    ! [A_138,B_139] :
      ( k4_xboole_0(A_138,k4_xboole_0(A_138,B_139)) = A_138
      | ~ r1_tarski(A_138,k3_subset_1(A_138,k4_xboole_0(A_138,B_139))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_673,c_150])).

tff(c_69555,plain,(
    ! [A_1127,B_1128] :
      ( k3_subset_1(A_1127,k4_xboole_0(A_1127,B_1128)) = A_1127
      | ~ r1_tarski(A_1127,k3_subset_1(A_1127,k4_xboole_0(A_1127,B_1128))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_694])).

tff(c_69714,plain,(
    ! [B_4] :
      ( k3_subset_1(B_4,k4_xboole_0(B_4,B_4)) = B_4
      | ~ r1_tarski(B_4,k3_subset_1(B_4,k3_subset_1(B_4,B_4))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_69555])).

tff(c_83322,plain,(
    ! [B_1276] :
      ( k3_subset_1(B_1276,k3_subset_1(B_1276,B_1276)) = B_1276
      | ~ r1_tarski(B_1276,k3_subset_1(B_1276,k3_subset_1(B_1276,B_1276))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_69714])).

tff(c_83336,plain,(
    ! [A_38] :
      ( k3_subset_1(A_38,k3_subset_1(A_38,A_38)) = A_38
      | ~ r1_tarski(A_38,A_38)
      | ~ r1_tarski(A_38,A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_83322])).

tff(c_83362,plain,(
    ! [A_1277] : k3_subset_1(A_1277,k3_subset_1(A_1277,A_1277)) = A_1277 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_83336])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k3_subset_1(A_14,B_15),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_86225,plain,(
    ! [A_1292] :
      ( m1_subset_1(A_1292,k1_zfmisc_1(A_1292))
      | ~ m1_subset_1(k3_subset_1(A_1292,A_1292),k1_zfmisc_1(A_1292)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83362,c_18])).

tff(c_86240,plain,(
    ! [B_39] :
      ( m1_subset_1(B_39,k1_zfmisc_1(B_39))
      | ~ r1_tarski(k3_subset_1(B_39,B_39),B_39) ) ),
    inference(resolution,[status(thm)],[c_38,c_86225])).

tff(c_86248,plain,(
    ! [B_39] : m1_subset_1(B_39,k1_zfmisc_1(B_39)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_86240])).

tff(c_725,plain,(
    ! [A_140,B_141,C_142] :
      ( k7_subset_1(A_140,B_141,C_142) = k4_xboole_0(B_141,C_142)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(A_140)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2198,plain,(
    ! [B_182,A_183,C_184] :
      ( k7_subset_1(B_182,A_183,C_184) = k4_xboole_0(A_183,C_184)
      | ~ r1_tarski(A_183,B_182) ) ),
    inference(resolution,[status(thm)],[c_38,c_725])).

tff(c_2329,plain,(
    ! [B_185,C_186] : k7_subset_1(B_185,B_185,C_186) = k4_xboole_0(B_185,C_186) ),
    inference(resolution,[status(thm)],[c_8,c_2198])).

tff(c_20,plain,(
    ! [A_16,B_17,C_18] :
      ( m1_subset_1(k7_subset_1(A_16,B_17,C_18),k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2338,plain,(
    ! [B_185,C_186] :
      ( m1_subset_1(k4_xboole_0(B_185,C_186),k1_zfmisc_1(B_185))
      | ~ m1_subset_1(B_185,k1_zfmisc_1(B_185)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2329,c_20])).

tff(c_86659,plain,(
    ! [B_1296,C_1297] : m1_subset_1(k4_xboole_0(B_1296,C_1297),k1_zfmisc_1(B_1296)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86248,c_2338])).

tff(c_86872,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_pre_topc('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_11422,c_86659])).

tff(c_740,plain,(
    ! [C_142] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_142) = k4_xboole_0('#skF_3',C_142) ),
    inference(resolution,[status(thm)],[c_54,c_725])).

tff(c_1649,plain,(
    ! [A_170,B_171] :
      ( k7_subset_1(u1_struct_0(A_170),B_171,k2_tops_1(A_170,B_171)) = k1_tops_1(A_170,B_171)
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ l1_pre_topc(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1680,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_1649])).

tff(c_1717,plain,(
    k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_740,c_1680])).

tff(c_2322,plain,(
    ! [B_2,A_1,C_184] : k7_subset_1(k2_xboole_0(B_2,A_1),B_2,C_184) = k4_xboole_0(B_2,C_184) ),
    inference(resolution,[status(thm)],[c_200,c_2198])).

tff(c_5041,plain,(
    ! [C_184] : k7_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3',C_184) = k4_xboole_0('#skF_3',C_184) ),
    inference(superposition,[status(thm),theory(equality)],[c_4955,c_2322])).

tff(c_2097,plain,(
    ! [A_177,B_178,C_179] :
      ( k9_subset_1(A_177,B_178,k3_subset_1(A_177,C_179)) = k7_subset_1(A_177,B_178,C_179)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(A_177))
      | ~ m1_subset_1(B_178,k1_zfmisc_1(A_177)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_12341,plain,(
    ! [A_441,B_442,B_443] :
      ( k9_subset_1(A_441,B_442,k3_subset_1(A_441,k3_subset_1(A_441,B_443))) = k7_subset_1(A_441,B_442,k3_subset_1(A_441,B_443))
      | ~ m1_subset_1(B_442,k1_zfmisc_1(A_441))
      | ~ m1_subset_1(B_443,k1_zfmisc_1(A_441)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2097])).

tff(c_22,plain,(
    ! [A_19] : m1_subset_1('#skF_1'(A_19),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_155,plain,(
    ! [A_81,B_82,C_83] :
      ( k9_subset_1(A_81,B_82,B_82) = B_82
      | ~ m1_subset_1(C_83,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_164,plain,(
    ! [A_81,B_82] : k9_subset_1(A_81,B_82,B_82) = B_82 ),
    inference(resolution,[status(thm)],[c_22,c_155])).

tff(c_103746,plain,(
    ! [A_1473,B_1474] :
      ( k7_subset_1(A_1473,k3_subset_1(A_1473,k3_subset_1(A_1473,B_1474)),k3_subset_1(A_1473,B_1474)) = k3_subset_1(A_1473,k3_subset_1(A_1473,B_1474))
      | ~ m1_subset_1(k3_subset_1(A_1473,k3_subset_1(A_1473,B_1474)),k1_zfmisc_1(A_1473))
      | ~ m1_subset_1(B_1474,k1_zfmisc_1(A_1473)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12341,c_164])).

tff(c_103821,plain,
    ( k7_subset_1(k2_pre_topc('#skF_2','#skF_3'),k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3')),k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3')) = k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3'))
    | ~ m1_subset_1(k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')),k1_zfmisc_1(k2_pre_topc('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_pre_topc('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10312,c_103746])).

tff(c_103932,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86872,c_86872,c_10559,c_1717,c_5041,c_10559,c_10312,c_10312,c_10559,c_10312,c_103821])).

tff(c_913,plain,(
    ! [A_151,B_152] :
      ( r1_tarski(k1_tops_1(A_151,B_152),B_152)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_924,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_913])).

tff(c_933,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_924])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_941,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_933,c_4])).

tff(c_1159,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_941])).

tff(c_104108,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103932,c_1159])).

tff(c_104246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_104108])).

tff(c_104247,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_941])).

tff(c_104495,plain,(
    ! [A_1482,B_1483] :
      ( v3_pre_topc(k1_tops_1(A_1482,B_1483),A_1482)
      | ~ m1_subset_1(B_1483,k1_zfmisc_1(u1_struct_0(A_1482)))
      | ~ l1_pre_topc(A_1482)
      | ~ v2_pre_topc(A_1482) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_104524,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_104495])).

tff(c_104558,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_104247,c_104524])).

tff(c_104560,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_104558])).

tff(c_104561,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_104640,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104561,c_114])).

tff(c_104641,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_104695,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104641,c_60])).

tff(c_105384,plain,(
    ! [A_1572,B_1573] :
      ( r1_tarski(k1_tops_1(A_1572,B_1573),B_1573)
      | ~ m1_subset_1(B_1573,k1_zfmisc_1(u1_struct_0(A_1572)))
      | ~ l1_pre_topc(A_1572) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_105399,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_105384])).

tff(c_105414,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_105399])).

tff(c_105422,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_105414,c_4])).

tff(c_105430,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_105422])).

tff(c_106932,plain,(
    ! [B_1624,A_1625,C_1626] :
      ( r1_tarski(B_1624,k1_tops_1(A_1625,C_1626))
      | ~ r1_tarski(B_1624,C_1626)
      | ~ v3_pre_topc(B_1624,A_1625)
      | ~ m1_subset_1(C_1626,k1_zfmisc_1(u1_struct_0(A_1625)))
      | ~ m1_subset_1(B_1624,k1_zfmisc_1(u1_struct_0(A_1625)))
      | ~ l1_pre_topc(A_1625) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_106963,plain,(
    ! [B_1624] :
      ( r1_tarski(B_1624,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_1624,'#skF_3')
      | ~ v3_pre_topc(B_1624,'#skF_2')
      | ~ m1_subset_1(B_1624,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_54,c_106932])).

tff(c_107073,plain,(
    ! [B_1629] :
      ( r1_tarski(B_1629,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_1629,'#skF_3')
      | ~ v3_pre_topc(B_1629,'#skF_2')
      | ~ m1_subset_1(B_1629,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_106963])).

tff(c_107119,plain,
    ( r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_107073])).

tff(c_107157,plain,(
    r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104641,c_8,c_107119])).

tff(c_107159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105430,c_107157])).

tff(c_107160,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_105422])).

tff(c_108579,plain,(
    ! [A_1684,B_1685] :
      ( k7_subset_1(u1_struct_0(A_1684),k2_pre_topc(A_1684,B_1685),k1_tops_1(A_1684,B_1685)) = k2_tops_1(A_1684,B_1685)
      | ~ m1_subset_1(B_1685,k1_zfmisc_1(u1_struct_0(A_1684)))
      | ~ l1_pre_topc(A_1684) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_108594,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_107160,c_108579])).

tff(c_108598,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_108594])).

tff(c_108600,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104695,c_108598])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:15:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 58.20/46.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 58.20/46.91  
% 58.20/46.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 58.20/46.92  %$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3
% 58.20/46.92  
% 58.20/46.92  %Foreground sorts:
% 58.20/46.92  
% 58.20/46.92  
% 58.20/46.92  %Background operators:
% 58.20/46.92  
% 58.20/46.92  
% 58.20/46.92  %Foreground operators:
% 58.20/46.92  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 58.20/46.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 58.20/46.92  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 58.20/46.92  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 58.20/46.92  tff('#skF_1', type, '#skF_1': $i > $i).
% 58.20/46.92  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 58.20/46.92  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 58.20/46.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 58.20/46.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 58.20/46.92  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 58.20/46.92  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 58.20/46.92  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 58.20/46.92  tff('#skF_2', type, '#skF_2': $i).
% 58.20/46.92  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 58.20/46.92  tff('#skF_3', type, '#skF_3': $i).
% 58.20/46.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 58.20/46.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 58.20/46.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 58.20/46.92  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 58.20/46.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 58.20/46.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 58.20/46.92  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 58.20/46.92  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 58.20/46.92  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 58.20/46.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 58.20/46.92  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 58.20/46.92  
% 58.20/46.94  tff(f_155, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 58.20/46.94  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 58.20/46.94  tff(f_136, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 58.20/46.94  tff(f_93, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 58.20/46.94  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 58.20/46.94  tff(f_87, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 58.20/46.94  tff(f_70, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 58.20/46.94  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 58.20/46.94  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 58.20/46.94  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 58.20/46.94  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 58.20/46.94  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 58.20/46.94  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 58.20/46.94  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 58.20/46.94  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 58.20/46.94  tff(f_143, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 58.20/46.94  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 58.20/46.94  tff(f_56, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 58.20/46.94  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 58.20/46.94  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 58.20/46.94  tff(f_101, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 58.20/46.94  tff(f_129, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 58.20/46.94  tff(c_60, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')!=k2_tops_1('#skF_2', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 58.20/46.94  tff(c_177, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_60])).
% 58.20/46.94  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 58.20/46.94  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 58.20/46.94  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 58.20/46.94  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 58.20/46.94  tff(c_1956, plain, (![A_173, B_174]: (k4_subset_1(u1_struct_0(A_173), B_174, k2_tops_1(A_173, B_174))=k2_pre_topc(A_173, B_174) | ~m1_subset_1(B_174, k1_zfmisc_1(u1_struct_0(A_173))) | ~l1_pre_topc(A_173))), inference(cnfTransformation, [status(thm)], [f_136])).
% 58.20/46.94  tff(c_1989, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_1956])).
% 58.20/46.94  tff(c_2029, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1989])).
% 58.20/46.94  tff(c_1035, plain, (![A_155, B_156]: (m1_subset_1(k2_pre_topc(A_155, B_156), k1_zfmisc_1(u1_struct_0(A_155))) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_pre_topc(A_155))), inference(cnfTransformation, [status(thm)], [f_93])).
% 58.20/46.94  tff(c_66, plain, (v3_pre_topc('#skF_3', '#skF_2') | k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 58.20/46.94  tff(c_114, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_66])).
% 58.20/46.94  tff(c_551, plain, (![A_126, B_127, C_128]: (m1_subset_1(k7_subset_1(A_126, B_127, C_128), k1_zfmisc_1(A_126)) | ~m1_subset_1(B_127, k1_zfmisc_1(A_126)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 58.20/46.94  tff(c_36, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 58.20/46.94  tff(c_625, plain, (![A_133, B_134, C_135]: (r1_tarski(k7_subset_1(A_133, B_134, C_135), A_133) | ~m1_subset_1(B_134, k1_zfmisc_1(A_133)))), inference(resolution, [status(thm)], [c_551, c_36])).
% 58.20/46.94  tff(c_633, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_114, c_625])).
% 58.20/46.94  tff(c_995, plain, (~m1_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_633])).
% 58.20/46.94  tff(c_1038, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1035, c_995])).
% 58.20/46.94  tff(c_1054, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1038])).
% 58.20/46.94  tff(c_1055, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_633])).
% 58.20/46.94  tff(c_38, plain, (![A_38, B_39]: (m1_subset_1(A_38, k1_zfmisc_1(B_39)) | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_87])).
% 58.20/46.94  tff(c_1459, plain, (![A_165, B_166, C_167]: (k4_subset_1(A_165, B_166, C_167)=k2_xboole_0(B_166, C_167) | ~m1_subset_1(C_167, k1_zfmisc_1(A_165)) | ~m1_subset_1(B_166, k1_zfmisc_1(A_165)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 58.20/46.94  tff(c_4659, plain, (![B_265, B_266, A_267]: (k4_subset_1(B_265, B_266, A_267)=k2_xboole_0(B_266, A_267) | ~m1_subset_1(B_266, k1_zfmisc_1(B_265)) | ~r1_tarski(A_267, B_265))), inference(resolution, [status(thm)], [c_38, c_1459])).
% 58.20/46.94  tff(c_4837, plain, (![A_269]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', A_269)=k2_xboole_0('#skF_3', A_269) | ~r1_tarski(A_269, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_54, c_4659])).
% 58.20/46.94  tff(c_4889, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_1055, c_4837])).
% 58.20/46.94  tff(c_4955, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2029, c_4889])).
% 58.20/46.94  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 58.20/46.94  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 58.20/46.94  tff(c_181, plain, (![A_89, B_90, C_91]: (r1_tarski(A_89, k2_xboole_0(B_90, C_91)) | ~r1_tarski(k4_xboole_0(A_89, B_90), C_91))), inference(cnfTransformation, [status(thm)], [f_41])).
% 58.20/46.94  tff(c_191, plain, (![A_92, B_93]: (r1_tarski(A_92, k2_xboole_0(B_93, A_92)))), inference(resolution, [status(thm)], [c_12, c_181])).
% 58.20/46.94  tff(c_200, plain, (![B_2, A_1]: (r1_tarski(B_2, k2_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_191])).
% 58.20/46.94  tff(c_5059, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4955, c_200])).
% 58.20/46.94  tff(c_1261, plain, (![A_161, B_162]: (m1_subset_1(k2_pre_topc(A_161, B_162), k1_zfmisc_1(u1_struct_0(A_161))) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0(A_161))) | ~l1_pre_topc(A_161))), inference(cnfTransformation, [status(thm)], [f_93])).
% 58.20/46.94  tff(c_30, plain, (![A_29, B_30, C_31]: (k7_subset_1(A_29, B_30, C_31)=k4_xboole_0(B_30, C_31) | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 58.20/46.94  tff(c_9865, plain, (![A_400, B_401, C_402]: (k7_subset_1(u1_struct_0(A_400), k2_pre_topc(A_400, B_401), C_402)=k4_xboole_0(k2_pre_topc(A_400, B_401), C_402) | ~m1_subset_1(B_401, k1_zfmisc_1(u1_struct_0(A_400))) | ~l1_pre_topc(A_400))), inference(resolution, [status(thm)], [c_1261, c_30])).
% 58.20/46.94  tff(c_9924, plain, (![C_402]: (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), C_402)=k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), C_402) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_9865])).
% 58.20/46.94  tff(c_10207, plain, (![C_405]: (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), C_405)=k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), C_405))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_9924])).
% 58.20/46.94  tff(c_10233, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10207, c_114])).
% 58.20/46.94  tff(c_336, plain, (![A_112, B_113]: (k4_xboole_0(A_112, B_113)=k3_subset_1(A_112, B_113) | ~m1_subset_1(B_113, k1_zfmisc_1(A_112)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 58.20/46.94  tff(c_376, plain, (![B_114, A_115]: (k4_xboole_0(B_114, A_115)=k3_subset_1(B_114, A_115) | ~r1_tarski(A_115, B_114))), inference(resolution, [status(thm)], [c_38, c_336])).
% 58.20/46.94  tff(c_412, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), B_2)=k3_subset_1(k2_xboole_0(B_2, A_1), B_2))), inference(resolution, [status(thm)], [c_200, c_376])).
% 58.20/46.94  tff(c_5008, plain, (k3_subset_1(k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3')), '#skF_3')=k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4955, c_412])).
% 58.20/46.94  tff(c_5074, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4955, c_5008])).
% 58.20/46.94  tff(c_10312, plain, (k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10233, c_5074])).
% 58.20/46.94  tff(c_287, plain, (![A_108, B_109]: (k3_subset_1(A_108, k3_subset_1(A_108, B_109))=B_109 | ~m1_subset_1(B_109, k1_zfmisc_1(A_108)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 58.20/46.94  tff(c_295, plain, (![B_39, A_38]: (k3_subset_1(B_39, k3_subset_1(B_39, A_38))=A_38 | ~r1_tarski(A_38, B_39))), inference(resolution, [status(thm)], [c_38, c_287])).
% 58.20/46.94  tff(c_10553, plain, (k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3'))='#skF_3' | ~r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_10312, c_295])).
% 58.20/46.94  tff(c_10559, plain, (k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5059, c_10553])).
% 58.20/46.94  tff(c_44, plain, (![A_44, B_46]: (k7_subset_1(u1_struct_0(A_44), k2_pre_topc(A_44, B_46), k1_tops_1(A_44, B_46))=k2_tops_1(A_44, B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_108])).
% 58.20/46.94  tff(c_10244, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_44, c_10207])).
% 58.20/46.94  tff(c_10265, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_10244])).
% 58.20/46.94  tff(c_417, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_subset_1(A_7, k4_xboole_0(A_7, B_8)))), inference(resolution, [status(thm)], [c_12, c_376])).
% 58.20/46.94  tff(c_11392, plain, (k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), k1_tops_1('#skF_2', '#skF_3')))=k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_10265, c_417])).
% 58.20/46.94  tff(c_11422, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10559, c_10265, c_11392])).
% 58.20/46.94  tff(c_419, plain, (![B_116]: (k4_xboole_0(B_116, B_116)=k3_subset_1(B_116, B_116))), inference(resolution, [status(thm)], [c_8, c_376])).
% 58.20/46.94  tff(c_440, plain, (![B_116]: (r1_tarski(k3_subset_1(B_116, B_116), B_116))), inference(superposition, [status(thm), theory('equality')], [c_419, c_12])).
% 58.20/46.94  tff(c_418, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k3_subset_1(B_4, B_4))), inference(resolution, [status(thm)], [c_8, c_376])).
% 58.20/46.94  tff(c_673, plain, (![A_138, B_139]: (k4_xboole_0(A_138, k4_xboole_0(A_138, B_139))=k3_subset_1(A_138, k4_xboole_0(A_138, B_139)))), inference(resolution, [status(thm)], [c_12, c_376])).
% 58.20/46.94  tff(c_139, plain, (![B_79, A_80]: (B_79=A_80 | ~r1_tarski(B_79, A_80) | ~r1_tarski(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_33])).
% 58.20/46.94  tff(c_150, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, k4_xboole_0(A_7, B_8)))), inference(resolution, [status(thm)], [c_12, c_139])).
% 58.20/46.94  tff(c_694, plain, (![A_138, B_139]: (k4_xboole_0(A_138, k4_xboole_0(A_138, B_139))=A_138 | ~r1_tarski(A_138, k3_subset_1(A_138, k4_xboole_0(A_138, B_139))))), inference(superposition, [status(thm), theory('equality')], [c_673, c_150])).
% 58.20/46.94  tff(c_69555, plain, (![A_1127, B_1128]: (k3_subset_1(A_1127, k4_xboole_0(A_1127, B_1128))=A_1127 | ~r1_tarski(A_1127, k3_subset_1(A_1127, k4_xboole_0(A_1127, B_1128))))), inference(demodulation, [status(thm), theory('equality')], [c_417, c_694])).
% 58.20/46.94  tff(c_69714, plain, (![B_4]: (k3_subset_1(B_4, k4_xboole_0(B_4, B_4))=B_4 | ~r1_tarski(B_4, k3_subset_1(B_4, k3_subset_1(B_4, B_4))))), inference(superposition, [status(thm), theory('equality')], [c_418, c_69555])).
% 58.20/46.94  tff(c_83322, plain, (![B_1276]: (k3_subset_1(B_1276, k3_subset_1(B_1276, B_1276))=B_1276 | ~r1_tarski(B_1276, k3_subset_1(B_1276, k3_subset_1(B_1276, B_1276))))), inference(demodulation, [status(thm), theory('equality')], [c_418, c_69714])).
% 58.20/46.94  tff(c_83336, plain, (![A_38]: (k3_subset_1(A_38, k3_subset_1(A_38, A_38))=A_38 | ~r1_tarski(A_38, A_38) | ~r1_tarski(A_38, A_38))), inference(superposition, [status(thm), theory('equality')], [c_295, c_83322])).
% 58.20/46.94  tff(c_83362, plain, (![A_1277]: (k3_subset_1(A_1277, k3_subset_1(A_1277, A_1277))=A_1277)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_83336])).
% 58.20/46.94  tff(c_18, plain, (![A_14, B_15]: (m1_subset_1(k3_subset_1(A_14, B_15), k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 58.20/46.94  tff(c_86225, plain, (![A_1292]: (m1_subset_1(A_1292, k1_zfmisc_1(A_1292)) | ~m1_subset_1(k3_subset_1(A_1292, A_1292), k1_zfmisc_1(A_1292)))), inference(superposition, [status(thm), theory('equality')], [c_83362, c_18])).
% 58.20/46.94  tff(c_86240, plain, (![B_39]: (m1_subset_1(B_39, k1_zfmisc_1(B_39)) | ~r1_tarski(k3_subset_1(B_39, B_39), B_39))), inference(resolution, [status(thm)], [c_38, c_86225])).
% 58.20/46.94  tff(c_86248, plain, (![B_39]: (m1_subset_1(B_39, k1_zfmisc_1(B_39)))), inference(demodulation, [status(thm), theory('equality')], [c_440, c_86240])).
% 58.20/46.94  tff(c_725, plain, (![A_140, B_141, C_142]: (k7_subset_1(A_140, B_141, C_142)=k4_xboole_0(B_141, C_142) | ~m1_subset_1(B_141, k1_zfmisc_1(A_140)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 58.20/46.94  tff(c_2198, plain, (![B_182, A_183, C_184]: (k7_subset_1(B_182, A_183, C_184)=k4_xboole_0(A_183, C_184) | ~r1_tarski(A_183, B_182))), inference(resolution, [status(thm)], [c_38, c_725])).
% 58.20/46.94  tff(c_2329, plain, (![B_185, C_186]: (k7_subset_1(B_185, B_185, C_186)=k4_xboole_0(B_185, C_186))), inference(resolution, [status(thm)], [c_8, c_2198])).
% 58.20/46.94  tff(c_20, plain, (![A_16, B_17, C_18]: (m1_subset_1(k7_subset_1(A_16, B_17, C_18), k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 58.20/46.94  tff(c_2338, plain, (![B_185, C_186]: (m1_subset_1(k4_xboole_0(B_185, C_186), k1_zfmisc_1(B_185)) | ~m1_subset_1(B_185, k1_zfmisc_1(B_185)))), inference(superposition, [status(thm), theory('equality')], [c_2329, c_20])).
% 58.20/46.94  tff(c_86659, plain, (![B_1296, C_1297]: (m1_subset_1(k4_xboole_0(B_1296, C_1297), k1_zfmisc_1(B_1296)))), inference(demodulation, [status(thm), theory('equality')], [c_86248, c_2338])).
% 58.20/46.94  tff(c_86872, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_pre_topc('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_11422, c_86659])).
% 58.20/46.94  tff(c_740, plain, (![C_142]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_142)=k4_xboole_0('#skF_3', C_142))), inference(resolution, [status(thm)], [c_54, c_725])).
% 58.20/46.94  tff(c_1649, plain, (![A_170, B_171]: (k7_subset_1(u1_struct_0(A_170), B_171, k2_tops_1(A_170, B_171))=k1_tops_1(A_170, B_171) | ~m1_subset_1(B_171, k1_zfmisc_1(u1_struct_0(A_170))) | ~l1_pre_topc(A_170))), inference(cnfTransformation, [status(thm)], [f_143])).
% 58.20/46.94  tff(c_1680, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_1649])).
% 58.20/46.94  tff(c_1717, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_740, c_1680])).
% 58.20/46.94  tff(c_2322, plain, (![B_2, A_1, C_184]: (k7_subset_1(k2_xboole_0(B_2, A_1), B_2, C_184)=k4_xboole_0(B_2, C_184))), inference(resolution, [status(thm)], [c_200, c_2198])).
% 58.20/46.94  tff(c_5041, plain, (![C_184]: (k7_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3', C_184)=k4_xboole_0('#skF_3', C_184))), inference(superposition, [status(thm), theory('equality')], [c_4955, c_2322])).
% 58.20/46.94  tff(c_2097, plain, (![A_177, B_178, C_179]: (k9_subset_1(A_177, B_178, k3_subset_1(A_177, C_179))=k7_subset_1(A_177, B_178, C_179) | ~m1_subset_1(C_179, k1_zfmisc_1(A_177)) | ~m1_subset_1(B_178, k1_zfmisc_1(A_177)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 58.20/46.94  tff(c_12341, plain, (![A_441, B_442, B_443]: (k9_subset_1(A_441, B_442, k3_subset_1(A_441, k3_subset_1(A_441, B_443)))=k7_subset_1(A_441, B_442, k3_subset_1(A_441, B_443)) | ~m1_subset_1(B_442, k1_zfmisc_1(A_441)) | ~m1_subset_1(B_443, k1_zfmisc_1(A_441)))), inference(resolution, [status(thm)], [c_18, c_2097])).
% 58.20/46.94  tff(c_22, plain, (![A_19]: (m1_subset_1('#skF_1'(A_19), A_19))), inference(cnfTransformation, [status(thm)], [f_56])).
% 58.20/46.94  tff(c_155, plain, (![A_81, B_82, C_83]: (k9_subset_1(A_81, B_82, B_82)=B_82 | ~m1_subset_1(C_83, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 58.20/46.94  tff(c_164, plain, (![A_81, B_82]: (k9_subset_1(A_81, B_82, B_82)=B_82)), inference(resolution, [status(thm)], [c_22, c_155])).
% 58.20/46.94  tff(c_103746, plain, (![A_1473, B_1474]: (k7_subset_1(A_1473, k3_subset_1(A_1473, k3_subset_1(A_1473, B_1474)), k3_subset_1(A_1473, B_1474))=k3_subset_1(A_1473, k3_subset_1(A_1473, B_1474)) | ~m1_subset_1(k3_subset_1(A_1473, k3_subset_1(A_1473, B_1474)), k1_zfmisc_1(A_1473)) | ~m1_subset_1(B_1474, k1_zfmisc_1(A_1473)))), inference(superposition, [status(thm), theory('equality')], [c_12341, c_164])).
% 58.20/46.94  tff(c_103821, plain, (k7_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')), k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3'))=k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')) | ~m1_subset_1(k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3')), k1_zfmisc_1(k2_pre_topc('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_pre_topc('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_10312, c_103746])).
% 58.20/46.94  tff(c_103932, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_86872, c_86872, c_10559, c_1717, c_5041, c_10559, c_10312, c_10312, c_10559, c_10312, c_103821])).
% 58.20/46.94  tff(c_913, plain, (![A_151, B_152]: (r1_tarski(k1_tops_1(A_151, B_152), B_152) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151))), inference(cnfTransformation, [status(thm)], [f_115])).
% 58.20/46.94  tff(c_924, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_913])).
% 58.20/46.94  tff(c_933, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_924])).
% 58.20/46.94  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 58.20/46.94  tff(c_941, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_933, c_4])).
% 58.20/46.94  tff(c_1159, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_941])).
% 58.20/46.94  tff(c_104108, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_103932, c_1159])).
% 58.20/46.94  tff(c_104246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_104108])).
% 58.20/46.94  tff(c_104247, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_941])).
% 58.20/46.94  tff(c_104495, plain, (![A_1482, B_1483]: (v3_pre_topc(k1_tops_1(A_1482, B_1483), A_1482) | ~m1_subset_1(B_1483, k1_zfmisc_1(u1_struct_0(A_1482))) | ~l1_pre_topc(A_1482) | ~v2_pre_topc(A_1482))), inference(cnfTransformation, [status(thm)], [f_101])).
% 58.20/46.94  tff(c_104524, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_104495])).
% 58.20/46.94  tff(c_104558, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_104247, c_104524])).
% 58.20/46.94  tff(c_104560, plain, $false, inference(negUnitSimplification, [status(thm)], [c_177, c_104558])).
% 58.20/46.94  tff(c_104561, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')!=k2_tops_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_60])).
% 58.20/46.94  tff(c_104640, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104561, c_114])).
% 58.20/46.94  tff(c_104641, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_66])).
% 58.20/46.94  tff(c_104695, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')!=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104641, c_60])).
% 58.20/46.94  tff(c_105384, plain, (![A_1572, B_1573]: (r1_tarski(k1_tops_1(A_1572, B_1573), B_1573) | ~m1_subset_1(B_1573, k1_zfmisc_1(u1_struct_0(A_1572))) | ~l1_pre_topc(A_1572))), inference(cnfTransformation, [status(thm)], [f_115])).
% 58.20/46.94  tff(c_105399, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_105384])).
% 58.20/46.94  tff(c_105414, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_105399])).
% 58.20/46.94  tff(c_105422, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_105414, c_4])).
% 58.20/46.94  tff(c_105430, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_105422])).
% 58.20/46.94  tff(c_106932, plain, (![B_1624, A_1625, C_1626]: (r1_tarski(B_1624, k1_tops_1(A_1625, C_1626)) | ~r1_tarski(B_1624, C_1626) | ~v3_pre_topc(B_1624, A_1625) | ~m1_subset_1(C_1626, k1_zfmisc_1(u1_struct_0(A_1625))) | ~m1_subset_1(B_1624, k1_zfmisc_1(u1_struct_0(A_1625))) | ~l1_pre_topc(A_1625))), inference(cnfTransformation, [status(thm)], [f_129])).
% 58.20/46.94  tff(c_106963, plain, (![B_1624]: (r1_tarski(B_1624, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_1624, '#skF_3') | ~v3_pre_topc(B_1624, '#skF_2') | ~m1_subset_1(B_1624, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_106932])).
% 58.20/46.94  tff(c_107073, plain, (![B_1629]: (r1_tarski(B_1629, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_1629, '#skF_3') | ~v3_pre_topc(B_1629, '#skF_2') | ~m1_subset_1(B_1629, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_106963])).
% 58.20/46.94  tff(c_107119, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_3', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_107073])).
% 58.20/46.94  tff(c_107157, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_104641, c_8, c_107119])).
% 58.20/46.94  tff(c_107159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105430, c_107157])).
% 58.20/46.94  tff(c_107160, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_105422])).
% 58.20/46.94  tff(c_108579, plain, (![A_1684, B_1685]: (k7_subset_1(u1_struct_0(A_1684), k2_pre_topc(A_1684, B_1685), k1_tops_1(A_1684, B_1685))=k2_tops_1(A_1684, B_1685) | ~m1_subset_1(B_1685, k1_zfmisc_1(u1_struct_0(A_1684))) | ~l1_pre_topc(A_1684))), inference(cnfTransformation, [status(thm)], [f_108])).
% 58.20/46.94  tff(c_108594, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_107160, c_108579])).
% 58.20/46.94  tff(c_108598, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_108594])).
% 58.20/46.94  tff(c_108600, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104695, c_108598])).
% 58.20/46.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 58.20/46.94  
% 58.20/46.94  Inference rules
% 58.20/46.94  ----------------------
% 58.20/46.94  #Ref     : 0
% 58.20/46.94  #Sup     : 26633
% 58.20/46.94  #Fact    : 0
% 58.20/46.94  #Define  : 0
% 58.20/46.94  #Split   : 22
% 58.20/46.94  #Chain   : 0
% 58.20/46.94  #Close   : 0
% 58.20/46.94  
% 58.20/46.94  Ordering : KBO
% 58.20/46.94  
% 58.20/46.94  Simplification rules
% 58.20/46.94  ----------------------
% 58.20/46.94  #Subsume      : 513
% 58.20/46.94  #Demod        : 17238
% 58.20/46.94  #Tautology    : 6547
% 58.20/46.94  #SimpNegUnit  : 8
% 58.20/46.94  #BackRed      : 185
% 58.20/46.94  
% 58.20/46.94  #Partial instantiations: 0
% 58.20/46.94  #Strategies tried      : 1
% 58.20/46.94  
% 58.20/46.94  Timing (in seconds)
% 58.20/46.94  ----------------------
% 58.20/46.95  Preprocessing        : 0.37
% 58.20/46.95  Parsing              : 0.19
% 58.20/46.95  CNF conversion       : 0.03
% 58.20/46.95  Main loop            : 45.78
% 58.20/46.95  Inferencing          : 4.71
% 58.20/46.95  Reduction            : 27.94
% 58.20/46.95  Demodulation         : 25.33
% 58.20/46.95  BG Simplification    : 0.54
% 58.20/46.95  Subsumption          : 10.25
% 58.20/46.95  Abstraction          : 0.89
% 58.20/46.95  MUC search           : 0.00
% 58.20/46.95  Cooper               : 0.00
% 58.20/46.95  Total                : 46.21
% 58.20/46.95  Index Insertion      : 0.00
% 58.20/46.95  Index Deletion       : 0.00
% 58.20/46.95  Index Matching       : 0.00
% 58.20/46.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
