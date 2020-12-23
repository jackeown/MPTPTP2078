%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:03 EST 2020

% Result     : Theorem 12.24s
% Output     : CNFRefutation 12.41s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 263 expanded)
%              Number of leaves         :   50 ( 110 expanded)
%              Depth                    :   11
%              Number of atoms          :  192 ( 507 expanded)
%              Number of equality atoms :   64 ( 135 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_180,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_168,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_95,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_73,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_140,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_108,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_133,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_154,axiom,(
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

tff(c_100,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k2_tops_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_144,plain,(
    k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k2_tops_1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_94,plain,
    ( k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') != k2_tops_1('#skF_4','#skF_5')
    | ~ v3_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_224,plain,(
    ~ v3_pre_topc('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_90,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_88,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_1552,plain,(
    ! [A_182,B_183,C_184] :
      ( k7_subset_1(A_182,B_183,C_184) = k4_xboole_0(B_183,C_184)
      | ~ m1_subset_1(B_183,k1_zfmisc_1(A_182)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1579,plain,(
    ! [C_184] : k7_subset_1(u1_struct_0('#skF_4'),'#skF_5',C_184) = k4_xboole_0('#skF_5',C_184) ),
    inference(resolution,[status(thm)],[c_88,c_1552])).

tff(c_4417,plain,(
    ! [A_270,B_271] :
      ( k7_subset_1(u1_struct_0(A_270),B_271,k2_tops_1(A_270,B_271)) = k1_tops_1(A_270,B_271)
      | ~ m1_subset_1(B_271,k1_zfmisc_1(u1_struct_0(A_270)))
      | ~ l1_pre_topc(A_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_4450,plain,
    ( k7_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_tops_1('#skF_4','#skF_5')) = k1_tops_1('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_4417])).

tff(c_4468,plain,(
    k4_xboole_0('#skF_5',k2_tops_1('#skF_4','#skF_5')) = k1_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1579,c_4450])).

tff(c_62,plain,(
    ! [A_43,B_44] : k6_subset_1(A_43,B_44) = k4_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_50,plain,(
    ! [A_30,B_31] : m1_subset_1(k6_subset_1(A_30,B_31),k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_101,plain,(
    ! [A_30,B_31] : m1_subset_1(k4_xboole_0(A_30,B_31),k1_zfmisc_1(A_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50])).

tff(c_255,plain,(
    ! [A_102,B_103] :
      ( r1_tarski(A_102,B_103)
      | ~ m1_subset_1(A_102,k1_zfmisc_1(B_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_270,plain,(
    ! [A_30,B_31] : r1_tarski(k4_xboole_0(A_30,B_31),A_30) ),
    inference(resolution,[status(thm)],[c_101,c_255])).

tff(c_4505,plain,(
    r1_tarski(k1_tops_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4468,c_270])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4520,plain,
    ( k1_tops_1('#skF_4','#skF_5') = '#skF_5'
    | ~ r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_4505,c_20])).

tff(c_6706,plain,(
    ~ r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4520])).

tff(c_1993,plain,(
    ! [B_207,A_208] :
      ( r1_tarski(B_207,k2_pre_topc(A_208,B_207))
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0(A_208)))
      | ~ l1_pre_topc(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2018,plain,
    ( r1_tarski('#skF_5',k2_pre_topc('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_1993])).

tff(c_2031,plain,(
    r1_tarski('#skF_5',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_2018])).

tff(c_2492,plain,(
    ! [A_228,B_229] :
      ( m1_subset_1(k2_pre_topc(A_228,B_229),k1_zfmisc_1(u1_struct_0(A_228)))
      | ~ m1_subset_1(B_229,k1_zfmisc_1(u1_struct_0(A_228)))
      | ~ l1_pre_topc(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_64,plain,(
    ! [A_45,B_46,C_47] :
      ( k7_subset_1(A_45,B_46,C_47) = k4_xboole_0(B_46,C_47)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_18898,plain,(
    ! [A_480,B_481,C_482] :
      ( k7_subset_1(u1_struct_0(A_480),k2_pre_topc(A_480,B_481),C_482) = k4_xboole_0(k2_pre_topc(A_480,B_481),C_482)
      | ~ m1_subset_1(B_481,k1_zfmisc_1(u1_struct_0(A_480)))
      | ~ l1_pre_topc(A_480) ) ),
    inference(resolution,[status(thm)],[c_2492,c_64])).

tff(c_18931,plain,(
    ! [C_482] :
      ( k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),C_482) = k4_xboole_0(k2_pre_topc('#skF_4','#skF_5'),C_482)
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_88,c_18898])).

tff(c_18951,plain,(
    ! [C_483] : k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),C_483) = k4_xboole_0(k2_pre_topc('#skF_4','#skF_5'),C_483) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_18931])).

tff(c_18965,plain,(
    k4_xboole_0(k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k2_tops_1('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_18951,c_144])).

tff(c_72,plain,(
    ! [A_54,B_55] :
      ( m1_subset_1(A_54,k1_zfmisc_1(B_55))
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1133,plain,(
    ! [A_165,B_166] :
      ( k4_xboole_0(A_165,B_166) = k3_subset_1(A_165,B_166)
      | ~ m1_subset_1(B_166,k1_zfmisc_1(A_165)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1153,plain,(
    ! [B_55,A_54] :
      ( k4_xboole_0(B_55,A_54) = k3_subset_1(B_55,A_54)
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_72,c_1133])).

tff(c_2037,plain,(
    k4_xboole_0(k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k3_subset_1(k2_pre_topc('#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_2031,c_1153])).

tff(c_18993,plain,(
    k3_subset_1(k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k2_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18965,c_2037])).

tff(c_1367,plain,(
    ! [A_172,B_173] :
      ( k3_subset_1(A_172,k3_subset_1(A_172,B_173)) = B_173
      | ~ m1_subset_1(B_173,k1_zfmisc_1(A_172)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1384,plain,(
    ! [B_55,A_54] :
      ( k3_subset_1(B_55,k3_subset_1(B_55,A_54)) = A_54
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_72,c_1367])).

tff(c_19158,plain,
    ( k3_subset_1(k2_pre_topc('#skF_4','#skF_5'),k2_tops_1('#skF_4','#skF_5')) = '#skF_5'
    | ~ r1_tarski('#skF_5',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18993,c_1384])).

tff(c_19171,plain,(
    k3_subset_1(k2_pre_topc('#skF_4','#skF_5'),k2_tops_1('#skF_4','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2031,c_19158])).

tff(c_80,plain,(
    ! [A_63,B_65] :
      ( k7_subset_1(u1_struct_0(A_63),k2_pre_topc(A_63,B_65),k1_tops_1(A_63,B_65)) = k2_tops_1(A_63,B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_18962,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_4','#skF_5'),k1_tops_1('#skF_4','#skF_5')) = k2_tops_1('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18951,c_80])).

tff(c_18984,plain,(
    k4_xboole_0(k2_pre_topc('#skF_4','#skF_5'),k1_tops_1('#skF_4','#skF_5')) = k2_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_18962])).

tff(c_28,plain,(
    ! [A_11,B_12] : r1_tarski(k3_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_36,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1636,plain,(
    ! [B_192,A_193] :
      ( k4_xboole_0(B_192,A_193) = k3_subset_1(B_192,A_193)
      | ~ r1_tarski(A_193,B_192) ) ),
    inference(resolution,[status(thm)],[c_72,c_1133])).

tff(c_1666,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k3_subset_1(A_11,k3_xboole_0(A_11,B_12)) ),
    inference(resolution,[status(thm)],[c_28,c_1636])).

tff(c_1687,plain,(
    ! [A_11,B_12] : k3_subset_1(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1666])).

tff(c_2068,plain,(
    ! [B_214,A_215] :
      ( k3_subset_1(B_214,k3_subset_1(B_214,A_215)) = A_215
      | ~ r1_tarski(A_215,B_214) ) ),
    inference(resolution,[status(thm)],[c_72,c_1367])).

tff(c_2103,plain,(
    ! [A_11,B_12] :
      ( k3_subset_1(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12)
      | ~ r1_tarski(k3_xboole_0(A_11,B_12),A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1687,c_2068])).

tff(c_2141,plain,(
    ! [A_11,B_12] : k3_subset_1(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2103])).

tff(c_21772,plain,(
    k3_xboole_0(k2_pre_topc('#skF_4','#skF_5'),k1_tops_1('#skF_4','#skF_5')) = k3_subset_1(k2_pre_topc('#skF_4','#skF_5'),k2_tops_1('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18984,c_2141])).

tff(c_21813,plain,(
    k3_xboole_0(k2_pre_topc('#skF_4','#skF_5'),k1_tops_1('#skF_4','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19171,c_21772])).

tff(c_42,plain,(
    ! [B_23,A_22] : k2_tarski(B_23,A_22) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_225,plain,(
    ! [A_98,B_99] : k1_setfam_1(k2_tarski(A_98,B_99)) = k3_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_317,plain,(
    ! [A_109,B_110] : k1_setfam_1(k2_tarski(A_109,B_110)) = k3_xboole_0(B_110,A_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_225])).

tff(c_68,plain,(
    ! [A_52,B_53] : k1_setfam_1(k2_tarski(A_52,B_53)) = k3_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_340,plain,(
    ! [B_111,A_112] : k3_xboole_0(B_111,A_112) = k3_xboole_0(A_112,B_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_68])).

tff(c_369,plain,(
    ! [B_111,A_112] : r1_tarski(k3_xboole_0(B_111,A_112),A_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_28])).

tff(c_22024,plain,(
    r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_21813,c_369])).

tff(c_22078,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6706,c_22024])).

tff(c_22079,plain,(
    k1_tops_1('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4520])).

tff(c_92,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_2268,plain,(
    ! [A_219,B_220] :
      ( v3_pre_topc(k1_tops_1(A_219,B_220),A_219)
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2293,plain,
    ( v3_pre_topc(k1_tops_1('#skF_4','#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_2268])).

tff(c_2306,plain,(
    v3_pre_topc(k1_tops_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_2293])).

tff(c_22091,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22079,c_2306])).

tff(c_22100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_22091])).

tff(c_22101,plain,(
    k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') != k2_tops_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_22459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_22101])).

tff(c_22460,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_22533,plain,(
    k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') != k2_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22460,c_94])).

tff(c_23613,plain,(
    ! [A_628,B_629,C_630] :
      ( k7_subset_1(A_628,B_629,C_630) = k4_xboole_0(B_629,C_630)
      | ~ m1_subset_1(B_629,k1_zfmisc_1(A_628)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_23631,plain,(
    ! [C_630] : k7_subset_1(u1_struct_0('#skF_4'),'#skF_5',C_630) = k4_xboole_0('#skF_5',C_630) ),
    inference(resolution,[status(thm)],[c_88,c_23613])).

tff(c_25912,plain,(
    ! [A_716,B_717] :
      ( k7_subset_1(u1_struct_0(A_716),B_717,k2_tops_1(A_716,B_717)) = k1_tops_1(A_716,B_717)
      | ~ m1_subset_1(B_717,k1_zfmisc_1(u1_struct_0(A_716)))
      | ~ l1_pre_topc(A_716) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_25945,plain,
    ( k7_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_tops_1('#skF_4','#skF_5')) = k1_tops_1('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_25912])).

tff(c_25964,plain,(
    k4_xboole_0('#skF_5',k2_tops_1('#skF_4','#skF_5')) = k1_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_23631,c_25945])).

tff(c_22559,plain,(
    ! [A_555,B_556] :
      ( r1_tarski(A_555,B_556)
      | ~ m1_subset_1(A_555,k1_zfmisc_1(B_556)) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_22578,plain,(
    ! [A_30,B_31] : r1_tarski(k4_xboole_0(A_30,B_31),A_30) ),
    inference(resolution,[status(thm)],[c_101,c_22559])).

tff(c_25998,plain,(
    r1_tarski(k1_tops_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_25964,c_22578])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28711,plain,(
    ! [B_766,A_767,C_768] :
      ( r1_tarski(B_766,k1_tops_1(A_767,C_768))
      | ~ r1_tarski(B_766,C_768)
      | ~ v3_pre_topc(B_766,A_767)
      | ~ m1_subset_1(C_768,k1_zfmisc_1(u1_struct_0(A_767)))
      | ~ m1_subset_1(B_766,k1_zfmisc_1(u1_struct_0(A_767)))
      | ~ l1_pre_topc(A_767) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_28744,plain,(
    ! [B_766] :
      ( r1_tarski(B_766,k1_tops_1('#skF_4','#skF_5'))
      | ~ r1_tarski(B_766,'#skF_5')
      | ~ v3_pre_topc(B_766,'#skF_4')
      | ~ m1_subset_1(B_766,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_88,c_28711])).

tff(c_28764,plain,(
    ! [B_769] :
      ( r1_tarski(B_769,k1_tops_1('#skF_4','#skF_5'))
      | ~ r1_tarski(B_769,'#skF_5')
      | ~ v3_pre_topc(B_769,'#skF_4')
      | ~ m1_subset_1(B_769,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_28744])).

tff(c_28810,plain,
    ( r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5'))
    | ~ r1_tarski('#skF_5','#skF_5')
    | ~ v3_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_28764])).

tff(c_28828,plain,(
    r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22460,c_24,c_28810])).

tff(c_28833,plain,
    ( k1_tops_1('#skF_4','#skF_5') = '#skF_5'
    | ~ r1_tarski(k1_tops_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_28828,c_20])).

tff(c_28837,plain,(
    k1_tops_1('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25998,c_28833])).

tff(c_28854,plain,
    ( k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k2_tops_1('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_28837,c_80])).

tff(c_28858,plain,(
    k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k2_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_28854])).

tff(c_28860,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22533,c_28858])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:24:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.24/5.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.24/5.07  
% 12.24/5.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.24/5.07  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 12.24/5.07  
% 12.24/5.07  %Foreground sorts:
% 12.24/5.07  
% 12.24/5.07  
% 12.24/5.07  %Background operators:
% 12.24/5.07  
% 12.24/5.07  
% 12.24/5.07  %Foreground operators:
% 12.24/5.07  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.24/5.07  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 12.24/5.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.24/5.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.24/5.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.24/5.07  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 12.24/5.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.24/5.07  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.24/5.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.24/5.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.24/5.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.24/5.07  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 12.24/5.07  tff('#skF_5', type, '#skF_5': $i).
% 12.24/5.07  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 12.24/5.07  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 12.24/5.07  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 12.24/5.07  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.24/5.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.24/5.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.24/5.07  tff(k3_tarski, type, k3_tarski: $i > $i).
% 12.24/5.07  tff('#skF_4', type, '#skF_4': $i).
% 12.24/5.07  tff('#skF_3', type, '#skF_3': $i > $i).
% 12.24/5.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.24/5.07  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 12.24/5.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.24/5.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.24/5.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.24/5.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.24/5.07  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 12.24/5.07  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 12.24/5.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.24/5.07  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 12.24/5.07  
% 12.41/5.09  tff(f_180, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 12.41/5.09  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 12.41/5.09  tff(f_168, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 12.41/5.09  tff(f_95, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 12.41/5.09  tff(f_73, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 12.41/5.09  tff(f_112, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 12.41/5.09  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.41/5.09  tff(f_125, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 12.41/5.09  tff(f_118, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 12.41/5.09  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 12.41/5.09  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 12.41/5.09  tff(f_140, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 12.41/5.09  tff(f_45, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 12.41/5.09  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 12.41/5.09  tff(f_61, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 12.41/5.09  tff(f_108, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 12.41/5.09  tff(f_133, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 12.41/5.09  tff(f_154, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 12.41/5.09  tff(c_100, plain, (v3_pre_topc('#skF_5', '#skF_4') | k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k2_tops_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.41/5.09  tff(c_144, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k2_tops_1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_100])).
% 12.41/5.09  tff(c_94, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')!=k2_tops_1('#skF_4', '#skF_5') | ~v3_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.41/5.09  tff(c_224, plain, (~v3_pre_topc('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_94])).
% 12.41/5.09  tff(c_90, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.41/5.09  tff(c_88, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.41/5.09  tff(c_1552, plain, (![A_182, B_183, C_184]: (k7_subset_1(A_182, B_183, C_184)=k4_xboole_0(B_183, C_184) | ~m1_subset_1(B_183, k1_zfmisc_1(A_182)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 12.41/5.09  tff(c_1579, plain, (![C_184]: (k7_subset_1(u1_struct_0('#skF_4'), '#skF_5', C_184)=k4_xboole_0('#skF_5', C_184))), inference(resolution, [status(thm)], [c_88, c_1552])).
% 12.41/5.09  tff(c_4417, plain, (![A_270, B_271]: (k7_subset_1(u1_struct_0(A_270), B_271, k2_tops_1(A_270, B_271))=k1_tops_1(A_270, B_271) | ~m1_subset_1(B_271, k1_zfmisc_1(u1_struct_0(A_270))) | ~l1_pre_topc(A_270))), inference(cnfTransformation, [status(thm)], [f_168])).
% 12.41/5.09  tff(c_4450, plain, (k7_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k1_tops_1('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_88, c_4417])).
% 12.41/5.09  tff(c_4468, plain, (k4_xboole_0('#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k1_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_1579, c_4450])).
% 12.41/5.09  tff(c_62, plain, (![A_43, B_44]: (k6_subset_1(A_43, B_44)=k4_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.41/5.09  tff(c_50, plain, (![A_30, B_31]: (m1_subset_1(k6_subset_1(A_30, B_31), k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.41/5.09  tff(c_101, plain, (![A_30, B_31]: (m1_subset_1(k4_xboole_0(A_30, B_31), k1_zfmisc_1(A_30)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_50])).
% 12.41/5.09  tff(c_255, plain, (![A_102, B_103]: (r1_tarski(A_102, B_103) | ~m1_subset_1(A_102, k1_zfmisc_1(B_103)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 12.41/5.09  tff(c_270, plain, (![A_30, B_31]: (r1_tarski(k4_xboole_0(A_30, B_31), A_30))), inference(resolution, [status(thm)], [c_101, c_255])).
% 12.41/5.09  tff(c_4505, plain, (r1_tarski(k1_tops_1('#skF_4', '#skF_5'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4468, c_270])).
% 12.41/5.09  tff(c_20, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.41/5.09  tff(c_4520, plain, (k1_tops_1('#skF_4', '#skF_5')='#skF_5' | ~r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_4505, c_20])).
% 12.41/5.09  tff(c_6706, plain, (~r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_4520])).
% 12.41/5.09  tff(c_1993, plain, (![B_207, A_208]: (r1_tarski(B_207, k2_pre_topc(A_208, B_207)) | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0(A_208))) | ~l1_pre_topc(A_208))), inference(cnfTransformation, [status(thm)], [f_125])).
% 12.41/5.09  tff(c_2018, plain, (r1_tarski('#skF_5', k2_pre_topc('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_88, c_1993])).
% 12.41/5.09  tff(c_2031, plain, (r1_tarski('#skF_5', k2_pre_topc('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_2018])).
% 12.41/5.09  tff(c_2492, plain, (![A_228, B_229]: (m1_subset_1(k2_pre_topc(A_228, B_229), k1_zfmisc_1(u1_struct_0(A_228))) | ~m1_subset_1(B_229, k1_zfmisc_1(u1_struct_0(A_228))) | ~l1_pre_topc(A_228))), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.41/5.09  tff(c_64, plain, (![A_45, B_46, C_47]: (k7_subset_1(A_45, B_46, C_47)=k4_xboole_0(B_46, C_47) | ~m1_subset_1(B_46, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 12.41/5.09  tff(c_18898, plain, (![A_480, B_481, C_482]: (k7_subset_1(u1_struct_0(A_480), k2_pre_topc(A_480, B_481), C_482)=k4_xboole_0(k2_pre_topc(A_480, B_481), C_482) | ~m1_subset_1(B_481, k1_zfmisc_1(u1_struct_0(A_480))) | ~l1_pre_topc(A_480))), inference(resolution, [status(thm)], [c_2492, c_64])).
% 12.41/5.09  tff(c_18931, plain, (![C_482]: (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), C_482)=k4_xboole_0(k2_pre_topc('#skF_4', '#skF_5'), C_482) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_88, c_18898])).
% 12.41/5.09  tff(c_18951, plain, (![C_483]: (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), C_483)=k4_xboole_0(k2_pre_topc('#skF_4', '#skF_5'), C_483))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_18931])).
% 12.41/5.09  tff(c_18965, plain, (k4_xboole_0(k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k2_tops_1('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_18951, c_144])).
% 12.41/5.09  tff(c_72, plain, (![A_54, B_55]: (m1_subset_1(A_54, k1_zfmisc_1(B_55)) | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_112])).
% 12.41/5.09  tff(c_1133, plain, (![A_165, B_166]: (k4_xboole_0(A_165, B_166)=k3_subset_1(A_165, B_166) | ~m1_subset_1(B_166, k1_zfmisc_1(A_165)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.41/5.09  tff(c_1153, plain, (![B_55, A_54]: (k4_xboole_0(B_55, A_54)=k3_subset_1(B_55, A_54) | ~r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_72, c_1133])).
% 12.41/5.09  tff(c_2037, plain, (k4_xboole_0(k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k3_subset_1(k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_2031, c_1153])).
% 12.41/5.09  tff(c_18993, plain, (k3_subset_1(k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k2_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18965, c_2037])).
% 12.41/5.09  tff(c_1367, plain, (![A_172, B_173]: (k3_subset_1(A_172, k3_subset_1(A_172, B_173))=B_173 | ~m1_subset_1(B_173, k1_zfmisc_1(A_172)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 12.41/5.09  tff(c_1384, plain, (![B_55, A_54]: (k3_subset_1(B_55, k3_subset_1(B_55, A_54))=A_54 | ~r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_72, c_1367])).
% 12.41/5.09  tff(c_19158, plain, (k3_subset_1(k2_pre_topc('#skF_4', '#skF_5'), k2_tops_1('#skF_4', '#skF_5'))='#skF_5' | ~r1_tarski('#skF_5', k2_pre_topc('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_18993, c_1384])).
% 12.41/5.09  tff(c_19171, plain, (k3_subset_1(k2_pre_topc('#skF_4', '#skF_5'), k2_tops_1('#skF_4', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2031, c_19158])).
% 12.41/5.09  tff(c_80, plain, (![A_63, B_65]: (k7_subset_1(u1_struct_0(A_63), k2_pre_topc(A_63, B_65), k1_tops_1(A_63, B_65))=k2_tops_1(A_63, B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_140])).
% 12.41/5.09  tff(c_18962, plain, (k4_xboole_0(k2_pre_topc('#skF_4', '#skF_5'), k1_tops_1('#skF_4', '#skF_5'))=k2_tops_1('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18951, c_80])).
% 12.41/5.09  tff(c_18984, plain, (k4_xboole_0(k2_pre_topc('#skF_4', '#skF_5'), k1_tops_1('#skF_4', '#skF_5'))=k2_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_18962])).
% 12.41/5.09  tff(c_28, plain, (![A_11, B_12]: (r1_tarski(k3_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.41/5.09  tff(c_36, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.41/5.09  tff(c_1636, plain, (![B_192, A_193]: (k4_xboole_0(B_192, A_193)=k3_subset_1(B_192, A_193) | ~r1_tarski(A_193, B_192))), inference(resolution, [status(thm)], [c_72, c_1133])).
% 12.41/5.09  tff(c_1666, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k3_subset_1(A_11, k3_xboole_0(A_11, B_12)))), inference(resolution, [status(thm)], [c_28, c_1636])).
% 12.41/5.09  tff(c_1687, plain, (![A_11, B_12]: (k3_subset_1(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1666])).
% 12.41/5.09  tff(c_2068, plain, (![B_214, A_215]: (k3_subset_1(B_214, k3_subset_1(B_214, A_215))=A_215 | ~r1_tarski(A_215, B_214))), inference(resolution, [status(thm)], [c_72, c_1367])).
% 12.41/5.09  tff(c_2103, plain, (![A_11, B_12]: (k3_subset_1(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12) | ~r1_tarski(k3_xboole_0(A_11, B_12), A_11))), inference(superposition, [status(thm), theory('equality')], [c_1687, c_2068])).
% 12.41/5.09  tff(c_2141, plain, (![A_11, B_12]: (k3_subset_1(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2103])).
% 12.41/5.09  tff(c_21772, plain, (k3_xboole_0(k2_pre_topc('#skF_4', '#skF_5'), k1_tops_1('#skF_4', '#skF_5'))=k3_subset_1(k2_pre_topc('#skF_4', '#skF_5'), k2_tops_1('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_18984, c_2141])).
% 12.41/5.09  tff(c_21813, plain, (k3_xboole_0(k2_pre_topc('#skF_4', '#skF_5'), k1_tops_1('#skF_4', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_19171, c_21772])).
% 12.41/5.09  tff(c_42, plain, (![B_23, A_22]: (k2_tarski(B_23, A_22)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.41/5.09  tff(c_225, plain, (![A_98, B_99]: (k1_setfam_1(k2_tarski(A_98, B_99))=k3_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_108])).
% 12.41/5.09  tff(c_317, plain, (![A_109, B_110]: (k1_setfam_1(k2_tarski(A_109, B_110))=k3_xboole_0(B_110, A_109))), inference(superposition, [status(thm), theory('equality')], [c_42, c_225])).
% 12.41/5.09  tff(c_68, plain, (![A_52, B_53]: (k1_setfam_1(k2_tarski(A_52, B_53))=k3_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_108])).
% 12.41/5.09  tff(c_340, plain, (![B_111, A_112]: (k3_xboole_0(B_111, A_112)=k3_xboole_0(A_112, B_111))), inference(superposition, [status(thm), theory('equality')], [c_317, c_68])).
% 12.41/5.09  tff(c_369, plain, (![B_111, A_112]: (r1_tarski(k3_xboole_0(B_111, A_112), A_112))), inference(superposition, [status(thm), theory('equality')], [c_340, c_28])).
% 12.41/5.09  tff(c_22024, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_21813, c_369])).
% 12.41/5.09  tff(c_22078, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6706, c_22024])).
% 12.41/5.09  tff(c_22079, plain, (k1_tops_1('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_4520])).
% 12.41/5.09  tff(c_92, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.41/5.09  tff(c_2268, plain, (![A_219, B_220]: (v3_pre_topc(k1_tops_1(A_219, B_220), A_219) | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0(A_219))) | ~l1_pre_topc(A_219) | ~v2_pre_topc(A_219))), inference(cnfTransformation, [status(thm)], [f_133])).
% 12.41/5.09  tff(c_2293, plain, (v3_pre_topc(k1_tops_1('#skF_4', '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_88, c_2268])).
% 12.41/5.09  tff(c_2306, plain, (v3_pre_topc(k1_tops_1('#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_2293])).
% 12.41/5.09  tff(c_22091, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22079, c_2306])).
% 12.41/5.09  tff(c_22100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_224, c_22091])).
% 12.41/5.09  tff(c_22101, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')!=k2_tops_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_94])).
% 12.41/5.09  tff(c_22459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_144, c_22101])).
% 12.41/5.09  tff(c_22460, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_100])).
% 12.41/5.09  tff(c_22533, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')!=k2_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_22460, c_94])).
% 12.41/5.09  tff(c_23613, plain, (![A_628, B_629, C_630]: (k7_subset_1(A_628, B_629, C_630)=k4_xboole_0(B_629, C_630) | ~m1_subset_1(B_629, k1_zfmisc_1(A_628)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 12.41/5.09  tff(c_23631, plain, (![C_630]: (k7_subset_1(u1_struct_0('#skF_4'), '#skF_5', C_630)=k4_xboole_0('#skF_5', C_630))), inference(resolution, [status(thm)], [c_88, c_23613])).
% 12.41/5.09  tff(c_25912, plain, (![A_716, B_717]: (k7_subset_1(u1_struct_0(A_716), B_717, k2_tops_1(A_716, B_717))=k1_tops_1(A_716, B_717) | ~m1_subset_1(B_717, k1_zfmisc_1(u1_struct_0(A_716))) | ~l1_pre_topc(A_716))), inference(cnfTransformation, [status(thm)], [f_168])).
% 12.41/5.09  tff(c_25945, plain, (k7_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k1_tops_1('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_88, c_25912])).
% 12.41/5.09  tff(c_25964, plain, (k4_xboole_0('#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k1_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_23631, c_25945])).
% 12.41/5.09  tff(c_22559, plain, (![A_555, B_556]: (r1_tarski(A_555, B_556) | ~m1_subset_1(A_555, k1_zfmisc_1(B_556)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 12.41/5.09  tff(c_22578, plain, (![A_30, B_31]: (r1_tarski(k4_xboole_0(A_30, B_31), A_30))), inference(resolution, [status(thm)], [c_101, c_22559])).
% 12.41/5.09  tff(c_25998, plain, (r1_tarski(k1_tops_1('#skF_4', '#skF_5'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_25964, c_22578])).
% 12.41/5.09  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.41/5.09  tff(c_28711, plain, (![B_766, A_767, C_768]: (r1_tarski(B_766, k1_tops_1(A_767, C_768)) | ~r1_tarski(B_766, C_768) | ~v3_pre_topc(B_766, A_767) | ~m1_subset_1(C_768, k1_zfmisc_1(u1_struct_0(A_767))) | ~m1_subset_1(B_766, k1_zfmisc_1(u1_struct_0(A_767))) | ~l1_pre_topc(A_767))), inference(cnfTransformation, [status(thm)], [f_154])).
% 12.41/5.09  tff(c_28744, plain, (![B_766]: (r1_tarski(B_766, k1_tops_1('#skF_4', '#skF_5')) | ~r1_tarski(B_766, '#skF_5') | ~v3_pre_topc(B_766, '#skF_4') | ~m1_subset_1(B_766, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_88, c_28711])).
% 12.41/5.09  tff(c_28764, plain, (![B_769]: (r1_tarski(B_769, k1_tops_1('#skF_4', '#skF_5')) | ~r1_tarski(B_769, '#skF_5') | ~v3_pre_topc(B_769, '#skF_4') | ~m1_subset_1(B_769, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_28744])).
% 12.41/5.09  tff(c_28810, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5')) | ~r1_tarski('#skF_5', '#skF_5') | ~v3_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_88, c_28764])).
% 12.41/5.09  tff(c_28828, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_22460, c_24, c_28810])).
% 12.41/5.09  tff(c_28833, plain, (k1_tops_1('#skF_4', '#skF_5')='#skF_5' | ~r1_tarski(k1_tops_1('#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_28828, c_20])).
% 12.41/5.09  tff(c_28837, plain, (k1_tops_1('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_25998, c_28833])).
% 12.41/5.09  tff(c_28854, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k2_tops_1('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_28837, c_80])).
% 12.41/5.09  tff(c_28858, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k2_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_28854])).
% 12.41/5.09  tff(c_28860, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22533, c_28858])).
% 12.41/5.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.41/5.09  
% 12.41/5.09  Inference rules
% 12.41/5.09  ----------------------
% 12.41/5.09  #Ref     : 0
% 12.41/5.09  #Sup     : 7055
% 12.41/5.09  #Fact    : 0
% 12.41/5.09  #Define  : 0
% 12.41/5.09  #Split   : 9
% 12.41/5.09  #Chain   : 0
% 12.41/5.09  #Close   : 0
% 12.41/5.09  
% 12.41/5.09  Ordering : KBO
% 12.41/5.09  
% 12.41/5.09  Simplification rules
% 12.41/5.09  ----------------------
% 12.41/5.09  #Subsume      : 552
% 12.41/5.09  #Demod        : 8741
% 12.41/5.09  #Tautology    : 4758
% 12.41/5.09  #SimpNegUnit  : 4
% 12.41/5.09  #BackRed      : 48
% 12.41/5.09  
% 12.41/5.09  #Partial instantiations: 0
% 12.41/5.09  #Strategies tried      : 1
% 12.41/5.09  
% 12.41/5.09  Timing (in seconds)
% 12.41/5.09  ----------------------
% 12.41/5.09  Preprocessing        : 0.37
% 12.41/5.09  Parsing              : 0.19
% 12.41/5.09  CNF conversion       : 0.03
% 12.41/5.09  Main loop            : 3.95
% 12.41/5.09  Inferencing          : 0.83
% 12.41/5.09  Reduction            : 2.10
% 12.41/5.09  Demodulation         : 1.80
% 12.41/5.09  BG Simplification    : 0.08
% 12.41/5.09  Subsumption          : 0.72
% 12.41/5.09  Abstraction          : 0.14
% 12.41/5.09  MUC search           : 0.00
% 12.41/5.09  Cooper               : 0.00
% 12.41/5.09  Total                : 4.37
% 12.41/5.09  Index Insertion      : 0.00
% 12.41/5.09  Index Deletion       : 0.00
% 12.41/5.10  Index Matching       : 0.00
% 12.41/5.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
