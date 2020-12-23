%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:03 EST 2020

% Result     : Theorem 21.82s
% Output     : CNFRefutation 21.82s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 458 expanded)
%              Number of leaves         :   47 ( 178 expanded)
%              Depth                    :   11
%              Number of atoms          :  203 ( 972 expanded)
%              Number of equality atoms :   66 ( 265 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff(f_178,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_166,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_110,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_138,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_93,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_71,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(f_131,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_152,axiom,(
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

tff(c_98,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k2_tops_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_251,plain,(
    k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k2_tops_1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_92,plain,
    ( k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') != k2_tops_1('#skF_4','#skF_5')
    | ~ v3_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_381,plain,(
    ~ v3_pre_topc('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_88,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_86,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_1750,plain,(
    ! [A_187,B_188,C_189] :
      ( k7_subset_1(A_187,B_188,C_189) = k4_xboole_0(B_188,C_189)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(A_187)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1776,plain,(
    ! [C_189] : k7_subset_1(u1_struct_0('#skF_4'),'#skF_5',C_189) = k4_xboole_0('#skF_5',C_189) ),
    inference(resolution,[status(thm)],[c_86,c_1750])).

tff(c_3561,plain,(
    ! [A_278,B_279] :
      ( k7_subset_1(u1_struct_0(A_278),B_279,k2_tops_1(A_278,B_279)) = k1_tops_1(A_278,B_279)
      | ~ m1_subset_1(B_279,k1_zfmisc_1(u1_struct_0(A_278)))
      | ~ l1_pre_topc(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_3594,plain,
    ( k7_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_tops_1('#skF_4','#skF_5')) = k1_tops_1('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_3561])).

tff(c_3615,plain,(
    k4_xboole_0('#skF_5',k2_tops_1('#skF_4','#skF_5')) = k1_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1776,c_3594])).

tff(c_1861,plain,(
    ! [B_202,A_203] :
      ( r1_tarski(B_202,k2_pre_topc(A_203,B_202))
      | ~ m1_subset_1(B_202,k1_zfmisc_1(u1_struct_0(A_203)))
      | ~ l1_pre_topc(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1883,plain,
    ( r1_tarski('#skF_5',k2_pre_topc('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_1861])).

tff(c_1898,plain,(
    r1_tarski('#skF_5',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1883])).

tff(c_70,plain,(
    ! [A_52,B_53] :
      ( m1_subset_1(A_52,k1_zfmisc_1(B_53))
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2481,plain,(
    ! [B_237,A_238,C_239] :
      ( k7_subset_1(B_237,A_238,C_239) = k4_xboole_0(A_238,C_239)
      | ~ r1_tarski(A_238,B_237) ) ),
    inference(resolution,[status(thm)],[c_70,c_1750])).

tff(c_2507,plain,(
    ! [C_239] : k7_subset_1(k2_pre_topc('#skF_4','#skF_5'),'#skF_5',C_239) = k4_xboole_0('#skF_5',C_239) ),
    inference(resolution,[status(thm)],[c_1898,c_2481])).

tff(c_2218,plain,(
    ! [A_213,B_214] :
      ( m1_subset_1(k2_pre_topc(A_213,B_214),k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ m1_subset_1(B_214,k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ l1_pre_topc(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_62,plain,(
    ! [A_43,B_44,C_45] :
      ( k7_subset_1(A_43,B_44,C_45) = k4_xboole_0(B_44,C_45)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_14786,plain,(
    ! [A_556,B_557,C_558] :
      ( k7_subset_1(u1_struct_0(A_556),k2_pre_topc(A_556,B_557),C_558) = k4_xboole_0(k2_pre_topc(A_556,B_557),C_558)
      | ~ m1_subset_1(B_557,k1_zfmisc_1(u1_struct_0(A_556)))
      | ~ l1_pre_topc(A_556) ) ),
    inference(resolution,[status(thm)],[c_2218,c_62])).

tff(c_14825,plain,(
    ! [C_558] :
      ( k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),C_558) = k4_xboole_0(k2_pre_topc('#skF_4','#skF_5'),C_558)
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_86,c_14786])).

tff(c_14851,plain,(
    ! [C_559] : k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),C_559) = k4_xboole_0(k2_pre_topc('#skF_4','#skF_5'),C_559) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_14825])).

tff(c_14869,plain,(
    k4_xboole_0(k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k2_tops_1('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_14851,c_251])).

tff(c_1248,plain,(
    ! [A_169,B_170] :
      ( k4_xboole_0(A_169,B_170) = k3_subset_1(A_169,B_170)
      | ~ m1_subset_1(B_170,k1_zfmisc_1(A_169)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1903,plain,(
    ! [B_204,A_205] :
      ( k4_xboole_0(B_204,A_205) = k3_subset_1(B_204,A_205)
      | ~ r1_tarski(A_205,B_204) ) ),
    inference(resolution,[status(thm)],[c_70,c_1248])).

tff(c_1940,plain,(
    k4_xboole_0(k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k3_subset_1(k2_pre_topc('#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_1898,c_1903])).

tff(c_14898,plain,(
    k3_subset_1(k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k2_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14869,c_1940])).

tff(c_983,plain,(
    ! [A_156,B_157] :
      ( k3_subset_1(A_156,k3_subset_1(A_156,B_157)) = B_157
      | ~ m1_subset_1(B_157,k1_zfmisc_1(A_156)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_998,plain,(
    ! [B_53,A_52] :
      ( k3_subset_1(B_53,k3_subset_1(B_53,A_52)) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_70,c_983])).

tff(c_15015,plain,
    ( k3_subset_1(k2_pre_topc('#skF_4','#skF_5'),k2_tops_1('#skF_4','#skF_5')) = '#skF_5'
    | ~ r1_tarski('#skF_5',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14898,c_998])).

tff(c_15028,plain,(
    k3_subset_1(k2_pre_topc('#skF_4','#skF_5'),k2_tops_1('#skF_4','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1898,c_15015])).

tff(c_78,plain,(
    ! [A_61,B_63] :
      ( k7_subset_1(u1_struct_0(A_61),k2_pre_topc(A_61,B_63),k1_tops_1(A_61,B_63)) = k2_tops_1(A_61,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_14884,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_4','#skF_5'),k1_tops_1('#skF_4','#skF_5')) = k2_tops_1('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_14851])).

tff(c_14897,plain,(
    k4_xboole_0(k2_pre_topc('#skF_4','#skF_5'),k1_tops_1('#skF_4','#skF_5')) = k2_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_14884])).

tff(c_60,plain,(
    ! [A_41,B_42] : k6_subset_1(A_41,B_42) = k4_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_48,plain,(
    ! [A_28,B_29] : m1_subset_1(k6_subset_1(A_28,B_29),k1_zfmisc_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_99,plain,(
    ! [A_28,B_29] : m1_subset_1(k4_xboole_0(A_28,B_29),k1_zfmisc_1(A_28)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_48])).

tff(c_2544,plain,(
    ! [A_244,B_245] : k4_xboole_0(A_244,k4_xboole_0(A_244,B_245)) = k3_subset_1(A_244,k4_xboole_0(A_244,B_245)) ),
    inference(resolution,[status(thm)],[c_99,c_1248])).

tff(c_2580,plain,(
    ! [A_244,B_245] : m1_subset_1(k3_subset_1(A_244,k4_xboole_0(A_244,B_245)),k1_zfmisc_1(A_244)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2544,c_99])).

tff(c_3754,plain,(
    ! [A_282,B_283,C_284] :
      ( k9_subset_1(A_282,B_283,k3_subset_1(A_282,C_284)) = k7_subset_1(A_282,B_283,C_284)
      | ~ m1_subset_1(C_284,k1_zfmisc_1(A_282))
      | ~ m1_subset_1(B_283,k1_zfmisc_1(A_282)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_14078,plain,(
    ! [A_541,B_542,B_543] :
      ( k9_subset_1(A_541,B_542,k3_subset_1(A_541,k4_xboole_0(A_541,B_543))) = k7_subset_1(A_541,B_542,k4_xboole_0(A_541,B_543))
      | ~ m1_subset_1(B_542,k1_zfmisc_1(A_541)) ) ),
    inference(resolution,[status(thm)],[c_99,c_3754])).

tff(c_689,plain,(
    ! [A_135,B_136,C_137] :
      ( k9_subset_1(A_135,B_136,B_136) = B_136
      | ~ m1_subset_1(C_137,k1_zfmisc_1(A_135)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_702,plain,(
    ! [A_28,B_136] : k9_subset_1(A_28,B_136,B_136) = B_136 ),
    inference(resolution,[status(thm)],[c_99,c_689])).

tff(c_14093,plain,(
    ! [A_541,B_543] :
      ( k7_subset_1(A_541,k3_subset_1(A_541,k4_xboole_0(A_541,B_543)),k4_xboole_0(A_541,B_543)) = k3_subset_1(A_541,k4_xboole_0(A_541,B_543))
      | ~ m1_subset_1(k3_subset_1(A_541,k4_xboole_0(A_541,B_543)),k1_zfmisc_1(A_541)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14078,c_702])).

tff(c_50907,plain,(
    ! [A_1015,B_1016] : k7_subset_1(A_1015,k3_subset_1(A_1015,k4_xboole_0(A_1015,B_1016)),k4_xboole_0(A_1015,B_1016)) = k3_subset_1(A_1015,k4_xboole_0(A_1015,B_1016)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2580,c_14093])).

tff(c_50995,plain,(
    k7_subset_1(k2_pre_topc('#skF_4','#skF_5'),k3_subset_1(k2_pre_topc('#skF_4','#skF_5'),k2_tops_1('#skF_4','#skF_5')),k4_xboole_0(k2_pre_topc('#skF_4','#skF_5'),k1_tops_1('#skF_4','#skF_5'))) = k3_subset_1(k2_pre_topc('#skF_4','#skF_5'),k4_xboole_0(k2_pre_topc('#skF_4','#skF_5'),k1_tops_1('#skF_4','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_14897,c_50907])).

tff(c_51192,plain,(
    k1_tops_1('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3615,c_2507,c_15028,c_15028,c_14897,c_14897,c_50995])).

tff(c_229,plain,(
    ! [A_98,B_99] :
      ( r1_tarski(A_98,B_99)
      | ~ m1_subset_1(A_98,k1_zfmisc_1(B_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_248,plain,(
    ! [A_28,B_29] : r1_tarski(k4_xboole_0(A_28,B_29),A_28) ),
    inference(resolution,[status(thm)],[c_99,c_229])).

tff(c_616,plain,(
    ! [B_128,A_129] :
      ( B_128 = A_129
      | ~ r1_tarski(B_128,A_129)
      | ~ r1_tarski(A_129,B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_633,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = A_28
      | ~ r1_tarski(A_28,k4_xboole_0(A_28,B_29)) ) ),
    inference(resolution,[status(thm)],[c_248,c_616])).

tff(c_3653,plain,
    ( k4_xboole_0('#skF_5',k2_tops_1('#skF_4','#skF_5')) = '#skF_5'
    | ~ r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3615,c_633])).

tff(c_3680,plain,
    ( k1_tops_1('#skF_4','#skF_5') = '#skF_5'
    | ~ r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3615,c_3653])).

tff(c_3805,plain,(
    ~ r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_3680])).

tff(c_51286,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51192,c_3805])).

tff(c_51314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_51286])).

tff(c_51315,plain,(
    k1_tops_1('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3680])).

tff(c_90,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_2275,plain,(
    ! [A_221,B_222] :
      ( v3_pre_topc(k1_tops_1(A_221,B_222),A_221)
      | ~ m1_subset_1(B_222,k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ l1_pre_topc(A_221)
      | ~ v2_pre_topc(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2299,plain,
    ( v3_pre_topc(k1_tops_1('#skF_4','#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_2275])).

tff(c_2315,plain,(
    v3_pre_topc(k1_tops_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_2299])).

tff(c_51323,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51315,c_2315])).

tff(c_51329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_51323])).

tff(c_51330,plain,(
    k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') != k2_tops_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_51446,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_51330])).

tff(c_51447,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_51526,plain,(
    k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') != k2_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51447,c_92])).

tff(c_52872,plain,(
    ! [A_1107,B_1108,C_1109] :
      ( k7_subset_1(A_1107,B_1108,C_1109) = k4_xboole_0(B_1108,C_1109)
      | ~ m1_subset_1(B_1108,k1_zfmisc_1(A_1107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_52895,plain,(
    ! [C_1109] : k7_subset_1(u1_struct_0('#skF_4'),'#skF_5',C_1109) = k4_xboole_0('#skF_5',C_1109) ),
    inference(resolution,[status(thm)],[c_86,c_52872])).

tff(c_55137,plain,(
    ! [A_1212,B_1213] :
      ( k7_subset_1(u1_struct_0(A_1212),B_1213,k2_tops_1(A_1212,B_1213)) = k1_tops_1(A_1212,B_1213)
      | ~ m1_subset_1(B_1213,k1_zfmisc_1(u1_struct_0(A_1212)))
      | ~ l1_pre_topc(A_1212) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_55173,plain,
    ( k7_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_tops_1('#skF_4','#skF_5')) = k1_tops_1('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_55137])).

tff(c_55195,plain,(
    k4_xboole_0('#skF_5',k2_tops_1('#skF_4','#skF_5')) = k1_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_52895,c_55173])).

tff(c_51944,plain,(
    ! [B_1058,A_1059] :
      ( B_1058 = A_1059
      | ~ r1_tarski(B_1058,A_1059)
      | ~ r1_tarski(A_1059,B_1058) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_51961,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = A_28
      | ~ r1_tarski(A_28,k4_xboole_0(A_28,B_29)) ) ),
    inference(resolution,[status(thm)],[c_248,c_51944])).

tff(c_55347,plain,
    ( k4_xboole_0('#skF_5',k2_tops_1('#skF_4','#skF_5')) = '#skF_5'
    | ~ r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_55195,c_51961])).

tff(c_55377,plain,
    ( k1_tops_1('#skF_4','#skF_5') = '#skF_5'
    | ~ r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55195,c_55347])).

tff(c_55549,plain,(
    ~ r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_55377])).

tff(c_56825,plain,(
    ! [B_1259,A_1260,C_1261] :
      ( r1_tarski(B_1259,k1_tops_1(A_1260,C_1261))
      | ~ r1_tarski(B_1259,C_1261)
      | ~ v3_pre_topc(B_1259,A_1260)
      | ~ m1_subset_1(C_1261,k1_zfmisc_1(u1_struct_0(A_1260)))
      | ~ m1_subset_1(B_1259,k1_zfmisc_1(u1_struct_0(A_1260)))
      | ~ l1_pre_topc(A_1260) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_56867,plain,(
    ! [B_1259] :
      ( r1_tarski(B_1259,k1_tops_1('#skF_4','#skF_5'))
      | ~ r1_tarski(B_1259,'#skF_5')
      | ~ v3_pre_topc(B_1259,'#skF_4')
      | ~ m1_subset_1(B_1259,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_86,c_56825])).

tff(c_56983,plain,(
    ! [B_1264] :
      ( r1_tarski(B_1264,k1_tops_1('#skF_4','#skF_5'))
      | ~ r1_tarski(B_1264,'#skF_5')
      | ~ v3_pre_topc(B_1264,'#skF_4')
      | ~ m1_subset_1(B_1264,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_56867])).

tff(c_57037,plain,
    ( r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5'))
    | ~ r1_tarski('#skF_5','#skF_5')
    | ~ v3_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_56983])).

tff(c_57061,plain,(
    r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51447,c_26,c_57037])).

tff(c_57063,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55549,c_57061])).

tff(c_57064,plain,(
    k1_tops_1('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_55377])).

tff(c_57148,plain,(
    ! [A_1265,B_1266] :
      ( k7_subset_1(u1_struct_0(A_1265),k2_pre_topc(A_1265,B_1266),k1_tops_1(A_1265,B_1266)) = k2_tops_1(A_1265,B_1266)
      | ~ m1_subset_1(B_1266,k1_zfmisc_1(u1_struct_0(A_1265)))
      | ~ l1_pre_topc(A_1265) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_57157,plain,
    ( k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k2_tops_1('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_57064,c_57148])).

tff(c_57164,plain,(
    k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k2_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_57157])).

tff(c_57166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51526,c_57164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:35:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.82/12.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.82/12.10  
% 21.82/12.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.82/12.11  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 21.82/12.11  
% 21.82/12.11  %Foreground sorts:
% 21.82/12.11  
% 21.82/12.11  
% 21.82/12.11  %Background operators:
% 21.82/12.11  
% 21.82/12.11  
% 21.82/12.11  %Foreground operators:
% 21.82/12.11  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 21.82/12.11  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 21.82/12.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.82/12.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 21.82/12.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 21.82/12.11  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 21.82/12.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 21.82/12.11  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 21.82/12.11  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 21.82/12.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.82/12.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 21.82/12.11  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 21.82/12.11  tff('#skF_5', type, '#skF_5': $i).
% 21.82/12.11  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 21.82/12.11  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 21.82/12.11  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 21.82/12.11  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 21.82/12.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 21.82/12.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.82/12.11  tff('#skF_4', type, '#skF_4': $i).
% 21.82/12.11  tff('#skF_3', type, '#skF_3': $i > $i).
% 21.82/12.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.82/12.11  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 21.82/12.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 21.82/12.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 21.82/12.11  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 21.82/12.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 21.82/12.11  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 21.82/12.11  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 21.82/12.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 21.82/12.11  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 21.82/12.11  
% 21.82/12.13  tff(f_178, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 21.82/12.13  tff(f_43, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 21.82/12.13  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 21.82/12.13  tff(f_166, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 21.82/12.13  tff(f_123, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 21.82/12.13  tff(f_110, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 21.82/12.13  tff(f_116, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 21.82/12.13  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 21.82/12.13  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 21.82/12.13  tff(f_138, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 21.82/12.13  tff(f_93, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 21.82/12.13  tff(f_71, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 21.82/12.13  tff(f_104, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 21.82/12.13  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 21.82/12.13  tff(f_131, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 21.82/12.13  tff(f_152, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 21.82/12.13  tff(c_98, plain, (v3_pre_topc('#skF_5', '#skF_4') | k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k2_tops_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_178])).
% 21.82/12.13  tff(c_251, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k2_tops_1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_98])).
% 21.82/12.13  tff(c_92, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')!=k2_tops_1('#skF_4', '#skF_5') | ~v3_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_178])).
% 21.82/12.13  tff(c_381, plain, (~v3_pre_topc('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_92])).
% 21.82/12.13  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 21.82/12.13  tff(c_88, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_178])).
% 21.82/12.13  tff(c_86, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 21.82/12.13  tff(c_1750, plain, (![A_187, B_188, C_189]: (k7_subset_1(A_187, B_188, C_189)=k4_xboole_0(B_188, C_189) | ~m1_subset_1(B_188, k1_zfmisc_1(A_187)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 21.82/12.13  tff(c_1776, plain, (![C_189]: (k7_subset_1(u1_struct_0('#skF_4'), '#skF_5', C_189)=k4_xboole_0('#skF_5', C_189))), inference(resolution, [status(thm)], [c_86, c_1750])).
% 21.82/12.13  tff(c_3561, plain, (![A_278, B_279]: (k7_subset_1(u1_struct_0(A_278), B_279, k2_tops_1(A_278, B_279))=k1_tops_1(A_278, B_279) | ~m1_subset_1(B_279, k1_zfmisc_1(u1_struct_0(A_278))) | ~l1_pre_topc(A_278))), inference(cnfTransformation, [status(thm)], [f_166])).
% 21.82/12.13  tff(c_3594, plain, (k7_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k1_tops_1('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_86, c_3561])).
% 21.82/12.13  tff(c_3615, plain, (k4_xboole_0('#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k1_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1776, c_3594])).
% 21.82/12.13  tff(c_1861, plain, (![B_202, A_203]: (r1_tarski(B_202, k2_pre_topc(A_203, B_202)) | ~m1_subset_1(B_202, k1_zfmisc_1(u1_struct_0(A_203))) | ~l1_pre_topc(A_203))), inference(cnfTransformation, [status(thm)], [f_123])).
% 21.82/12.13  tff(c_1883, plain, (r1_tarski('#skF_5', k2_pre_topc('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_86, c_1861])).
% 21.82/12.13  tff(c_1898, plain, (r1_tarski('#skF_5', k2_pre_topc('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1883])).
% 21.82/12.13  tff(c_70, plain, (![A_52, B_53]: (m1_subset_1(A_52, k1_zfmisc_1(B_53)) | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_110])).
% 21.82/12.13  tff(c_2481, plain, (![B_237, A_238, C_239]: (k7_subset_1(B_237, A_238, C_239)=k4_xboole_0(A_238, C_239) | ~r1_tarski(A_238, B_237))), inference(resolution, [status(thm)], [c_70, c_1750])).
% 21.82/12.13  tff(c_2507, plain, (![C_239]: (k7_subset_1(k2_pre_topc('#skF_4', '#skF_5'), '#skF_5', C_239)=k4_xboole_0('#skF_5', C_239))), inference(resolution, [status(thm)], [c_1898, c_2481])).
% 21.82/12.13  tff(c_2218, plain, (![A_213, B_214]: (m1_subset_1(k2_pre_topc(A_213, B_214), k1_zfmisc_1(u1_struct_0(A_213))) | ~m1_subset_1(B_214, k1_zfmisc_1(u1_struct_0(A_213))) | ~l1_pre_topc(A_213))), inference(cnfTransformation, [status(thm)], [f_116])).
% 21.82/12.13  tff(c_62, plain, (![A_43, B_44, C_45]: (k7_subset_1(A_43, B_44, C_45)=k4_xboole_0(B_44, C_45) | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 21.82/12.13  tff(c_14786, plain, (![A_556, B_557, C_558]: (k7_subset_1(u1_struct_0(A_556), k2_pre_topc(A_556, B_557), C_558)=k4_xboole_0(k2_pre_topc(A_556, B_557), C_558) | ~m1_subset_1(B_557, k1_zfmisc_1(u1_struct_0(A_556))) | ~l1_pre_topc(A_556))), inference(resolution, [status(thm)], [c_2218, c_62])).
% 21.82/12.13  tff(c_14825, plain, (![C_558]: (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), C_558)=k4_xboole_0(k2_pre_topc('#skF_4', '#skF_5'), C_558) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_86, c_14786])).
% 21.82/12.13  tff(c_14851, plain, (![C_559]: (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), C_559)=k4_xboole_0(k2_pre_topc('#skF_4', '#skF_5'), C_559))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_14825])).
% 21.82/12.13  tff(c_14869, plain, (k4_xboole_0(k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k2_tops_1('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_14851, c_251])).
% 21.82/12.13  tff(c_1248, plain, (![A_169, B_170]: (k4_xboole_0(A_169, B_170)=k3_subset_1(A_169, B_170) | ~m1_subset_1(B_170, k1_zfmisc_1(A_169)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 21.82/12.13  tff(c_1903, plain, (![B_204, A_205]: (k4_xboole_0(B_204, A_205)=k3_subset_1(B_204, A_205) | ~r1_tarski(A_205, B_204))), inference(resolution, [status(thm)], [c_70, c_1248])).
% 21.82/12.13  tff(c_1940, plain, (k4_xboole_0(k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k3_subset_1(k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_1898, c_1903])).
% 21.82/12.13  tff(c_14898, plain, (k3_subset_1(k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k2_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14869, c_1940])).
% 21.82/12.13  tff(c_983, plain, (![A_156, B_157]: (k3_subset_1(A_156, k3_subset_1(A_156, B_157))=B_157 | ~m1_subset_1(B_157, k1_zfmisc_1(A_156)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 21.82/12.13  tff(c_998, plain, (![B_53, A_52]: (k3_subset_1(B_53, k3_subset_1(B_53, A_52))=A_52 | ~r1_tarski(A_52, B_53))), inference(resolution, [status(thm)], [c_70, c_983])).
% 21.82/12.13  tff(c_15015, plain, (k3_subset_1(k2_pre_topc('#skF_4', '#skF_5'), k2_tops_1('#skF_4', '#skF_5'))='#skF_5' | ~r1_tarski('#skF_5', k2_pre_topc('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_14898, c_998])).
% 21.82/12.13  tff(c_15028, plain, (k3_subset_1(k2_pre_topc('#skF_4', '#skF_5'), k2_tops_1('#skF_4', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1898, c_15015])).
% 21.82/12.13  tff(c_78, plain, (![A_61, B_63]: (k7_subset_1(u1_struct_0(A_61), k2_pre_topc(A_61, B_63), k1_tops_1(A_61, B_63))=k2_tops_1(A_61, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_138])).
% 21.82/12.13  tff(c_14884, plain, (k4_xboole_0(k2_pre_topc('#skF_4', '#skF_5'), k1_tops_1('#skF_4', '#skF_5'))=k2_tops_1('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_78, c_14851])).
% 21.82/12.13  tff(c_14897, plain, (k4_xboole_0(k2_pre_topc('#skF_4', '#skF_5'), k1_tops_1('#skF_4', '#skF_5'))=k2_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_14884])).
% 21.82/12.13  tff(c_60, plain, (![A_41, B_42]: (k6_subset_1(A_41, B_42)=k4_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_93])).
% 21.82/12.13  tff(c_48, plain, (![A_28, B_29]: (m1_subset_1(k6_subset_1(A_28, B_29), k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 21.82/12.13  tff(c_99, plain, (![A_28, B_29]: (m1_subset_1(k4_xboole_0(A_28, B_29), k1_zfmisc_1(A_28)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_48])).
% 21.82/12.13  tff(c_2544, plain, (![A_244, B_245]: (k4_xboole_0(A_244, k4_xboole_0(A_244, B_245))=k3_subset_1(A_244, k4_xboole_0(A_244, B_245)))), inference(resolution, [status(thm)], [c_99, c_1248])).
% 21.82/12.13  tff(c_2580, plain, (![A_244, B_245]: (m1_subset_1(k3_subset_1(A_244, k4_xboole_0(A_244, B_245)), k1_zfmisc_1(A_244)))), inference(superposition, [status(thm), theory('equality')], [c_2544, c_99])).
% 21.82/12.13  tff(c_3754, plain, (![A_282, B_283, C_284]: (k9_subset_1(A_282, B_283, k3_subset_1(A_282, C_284))=k7_subset_1(A_282, B_283, C_284) | ~m1_subset_1(C_284, k1_zfmisc_1(A_282)) | ~m1_subset_1(B_283, k1_zfmisc_1(A_282)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 21.82/12.13  tff(c_14078, plain, (![A_541, B_542, B_543]: (k9_subset_1(A_541, B_542, k3_subset_1(A_541, k4_xboole_0(A_541, B_543)))=k7_subset_1(A_541, B_542, k4_xboole_0(A_541, B_543)) | ~m1_subset_1(B_542, k1_zfmisc_1(A_541)))), inference(resolution, [status(thm)], [c_99, c_3754])).
% 21.82/12.13  tff(c_689, plain, (![A_135, B_136, C_137]: (k9_subset_1(A_135, B_136, B_136)=B_136 | ~m1_subset_1(C_137, k1_zfmisc_1(A_135)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 21.82/12.13  tff(c_702, plain, (![A_28, B_136]: (k9_subset_1(A_28, B_136, B_136)=B_136)), inference(resolution, [status(thm)], [c_99, c_689])).
% 21.82/12.13  tff(c_14093, plain, (![A_541, B_543]: (k7_subset_1(A_541, k3_subset_1(A_541, k4_xboole_0(A_541, B_543)), k4_xboole_0(A_541, B_543))=k3_subset_1(A_541, k4_xboole_0(A_541, B_543)) | ~m1_subset_1(k3_subset_1(A_541, k4_xboole_0(A_541, B_543)), k1_zfmisc_1(A_541)))), inference(superposition, [status(thm), theory('equality')], [c_14078, c_702])).
% 21.82/12.13  tff(c_50907, plain, (![A_1015, B_1016]: (k7_subset_1(A_1015, k3_subset_1(A_1015, k4_xboole_0(A_1015, B_1016)), k4_xboole_0(A_1015, B_1016))=k3_subset_1(A_1015, k4_xboole_0(A_1015, B_1016)))), inference(demodulation, [status(thm), theory('equality')], [c_2580, c_14093])).
% 21.82/12.13  tff(c_50995, plain, (k7_subset_1(k2_pre_topc('#skF_4', '#skF_5'), k3_subset_1(k2_pre_topc('#skF_4', '#skF_5'), k2_tops_1('#skF_4', '#skF_5')), k4_xboole_0(k2_pre_topc('#skF_4', '#skF_5'), k1_tops_1('#skF_4', '#skF_5')))=k3_subset_1(k2_pre_topc('#skF_4', '#skF_5'), k4_xboole_0(k2_pre_topc('#skF_4', '#skF_5'), k1_tops_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_14897, c_50907])).
% 21.82/12.13  tff(c_51192, plain, (k1_tops_1('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3615, c_2507, c_15028, c_15028, c_14897, c_14897, c_50995])).
% 21.82/12.13  tff(c_229, plain, (![A_98, B_99]: (r1_tarski(A_98, B_99) | ~m1_subset_1(A_98, k1_zfmisc_1(B_99)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 21.82/12.13  tff(c_248, plain, (![A_28, B_29]: (r1_tarski(k4_xboole_0(A_28, B_29), A_28))), inference(resolution, [status(thm)], [c_99, c_229])).
% 21.82/12.13  tff(c_616, plain, (![B_128, A_129]: (B_128=A_129 | ~r1_tarski(B_128, A_129) | ~r1_tarski(A_129, B_128))), inference(cnfTransformation, [status(thm)], [f_43])).
% 21.82/12.13  tff(c_633, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=A_28 | ~r1_tarski(A_28, k4_xboole_0(A_28, B_29)))), inference(resolution, [status(thm)], [c_248, c_616])).
% 21.82/12.13  tff(c_3653, plain, (k4_xboole_0('#skF_5', k2_tops_1('#skF_4', '#skF_5'))='#skF_5' | ~r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3615, c_633])).
% 21.82/12.13  tff(c_3680, plain, (k1_tops_1('#skF_4', '#skF_5')='#skF_5' | ~r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3615, c_3653])).
% 21.82/12.13  tff(c_3805, plain, (~r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_3680])).
% 21.82/12.13  tff(c_51286, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_51192, c_3805])).
% 21.82/12.13  tff(c_51314, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_51286])).
% 21.82/12.13  tff(c_51315, plain, (k1_tops_1('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_3680])).
% 21.82/12.13  tff(c_90, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_178])).
% 21.82/12.13  tff(c_2275, plain, (![A_221, B_222]: (v3_pre_topc(k1_tops_1(A_221, B_222), A_221) | ~m1_subset_1(B_222, k1_zfmisc_1(u1_struct_0(A_221))) | ~l1_pre_topc(A_221) | ~v2_pre_topc(A_221))), inference(cnfTransformation, [status(thm)], [f_131])).
% 21.82/12.13  tff(c_2299, plain, (v3_pre_topc(k1_tops_1('#skF_4', '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_86, c_2275])).
% 21.82/12.13  tff(c_2315, plain, (v3_pre_topc(k1_tops_1('#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_2299])).
% 21.82/12.13  tff(c_51323, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_51315, c_2315])).
% 21.82/12.13  tff(c_51329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_381, c_51323])).
% 21.82/12.13  tff(c_51330, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')!=k2_tops_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_92])).
% 21.82/12.13  tff(c_51446, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_251, c_51330])).
% 21.82/12.13  tff(c_51447, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_98])).
% 21.82/12.13  tff(c_51526, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')!=k2_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_51447, c_92])).
% 21.82/12.13  tff(c_52872, plain, (![A_1107, B_1108, C_1109]: (k7_subset_1(A_1107, B_1108, C_1109)=k4_xboole_0(B_1108, C_1109) | ~m1_subset_1(B_1108, k1_zfmisc_1(A_1107)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 21.82/12.13  tff(c_52895, plain, (![C_1109]: (k7_subset_1(u1_struct_0('#skF_4'), '#skF_5', C_1109)=k4_xboole_0('#skF_5', C_1109))), inference(resolution, [status(thm)], [c_86, c_52872])).
% 21.82/12.13  tff(c_55137, plain, (![A_1212, B_1213]: (k7_subset_1(u1_struct_0(A_1212), B_1213, k2_tops_1(A_1212, B_1213))=k1_tops_1(A_1212, B_1213) | ~m1_subset_1(B_1213, k1_zfmisc_1(u1_struct_0(A_1212))) | ~l1_pre_topc(A_1212))), inference(cnfTransformation, [status(thm)], [f_166])).
% 21.82/12.13  tff(c_55173, plain, (k7_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k1_tops_1('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_86, c_55137])).
% 21.82/12.13  tff(c_55195, plain, (k4_xboole_0('#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k1_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_52895, c_55173])).
% 21.82/12.13  tff(c_51944, plain, (![B_1058, A_1059]: (B_1058=A_1059 | ~r1_tarski(B_1058, A_1059) | ~r1_tarski(A_1059, B_1058))), inference(cnfTransformation, [status(thm)], [f_43])).
% 21.82/12.13  tff(c_51961, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=A_28 | ~r1_tarski(A_28, k4_xboole_0(A_28, B_29)))), inference(resolution, [status(thm)], [c_248, c_51944])).
% 21.82/12.13  tff(c_55347, plain, (k4_xboole_0('#skF_5', k2_tops_1('#skF_4', '#skF_5'))='#skF_5' | ~r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_55195, c_51961])).
% 21.82/12.13  tff(c_55377, plain, (k1_tops_1('#skF_4', '#skF_5')='#skF_5' | ~r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_55195, c_55347])).
% 21.82/12.13  tff(c_55549, plain, (~r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_55377])).
% 21.82/12.13  tff(c_56825, plain, (![B_1259, A_1260, C_1261]: (r1_tarski(B_1259, k1_tops_1(A_1260, C_1261)) | ~r1_tarski(B_1259, C_1261) | ~v3_pre_topc(B_1259, A_1260) | ~m1_subset_1(C_1261, k1_zfmisc_1(u1_struct_0(A_1260))) | ~m1_subset_1(B_1259, k1_zfmisc_1(u1_struct_0(A_1260))) | ~l1_pre_topc(A_1260))), inference(cnfTransformation, [status(thm)], [f_152])).
% 21.82/12.13  tff(c_56867, plain, (![B_1259]: (r1_tarski(B_1259, k1_tops_1('#skF_4', '#skF_5')) | ~r1_tarski(B_1259, '#skF_5') | ~v3_pre_topc(B_1259, '#skF_4') | ~m1_subset_1(B_1259, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_86, c_56825])).
% 21.82/12.13  tff(c_56983, plain, (![B_1264]: (r1_tarski(B_1264, k1_tops_1('#skF_4', '#skF_5')) | ~r1_tarski(B_1264, '#skF_5') | ~v3_pre_topc(B_1264, '#skF_4') | ~m1_subset_1(B_1264, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_56867])).
% 21.82/12.13  tff(c_57037, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5')) | ~r1_tarski('#skF_5', '#skF_5') | ~v3_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_86, c_56983])).
% 21.82/12.13  tff(c_57061, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_51447, c_26, c_57037])).
% 21.82/12.13  tff(c_57063, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55549, c_57061])).
% 21.82/12.13  tff(c_57064, plain, (k1_tops_1('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_55377])).
% 21.82/12.13  tff(c_57148, plain, (![A_1265, B_1266]: (k7_subset_1(u1_struct_0(A_1265), k2_pre_topc(A_1265, B_1266), k1_tops_1(A_1265, B_1266))=k2_tops_1(A_1265, B_1266) | ~m1_subset_1(B_1266, k1_zfmisc_1(u1_struct_0(A_1265))) | ~l1_pre_topc(A_1265))), inference(cnfTransformation, [status(thm)], [f_138])).
% 21.82/12.13  tff(c_57157, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k2_tops_1('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_57064, c_57148])).
% 21.82/12.13  tff(c_57164, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k2_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_57157])).
% 21.82/12.13  tff(c_57166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51526, c_57164])).
% 21.82/12.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.82/12.13  
% 21.82/12.13  Inference rules
% 21.82/12.13  ----------------------
% 21.82/12.13  #Ref     : 0
% 21.82/12.13  #Sup     : 13183
% 21.82/12.13  #Fact    : 0
% 21.82/12.13  #Define  : 0
% 21.82/12.13  #Split   : 28
% 21.82/12.13  #Chain   : 0
% 21.82/12.13  #Close   : 0
% 21.82/12.13  
% 21.82/12.13  Ordering : KBO
% 21.82/12.13  
% 21.82/12.13  Simplification rules
% 21.82/12.13  ----------------------
% 21.82/12.13  #Subsume      : 1617
% 21.82/12.13  #Demod        : 16882
% 21.82/12.13  #Tautology    : 5812
% 21.82/12.13  #SimpNegUnit  : 312
% 21.82/12.13  #BackRed      : 372
% 21.82/12.13  
% 21.82/12.13  #Partial instantiations: 0
% 21.82/12.13  #Strategies tried      : 1
% 21.82/12.13  
% 21.82/12.13  Timing (in seconds)
% 21.82/12.13  ----------------------
% 21.82/12.13  Preprocessing        : 0.38
% 21.82/12.13  Parsing              : 0.20
% 21.82/12.13  CNF conversion       : 0.03
% 21.82/12.13  Main loop            : 10.96
% 21.82/12.13  Inferencing          : 1.70
% 21.82/12.13  Reduction            : 6.13
% 21.82/12.13  Demodulation         : 5.31
% 21.82/12.13  BG Simplification    : 0.17
% 21.82/12.13  Subsumption          : 2.38
% 21.82/12.13  Abstraction          : 0.29
% 21.82/12.13  MUC search           : 0.00
% 21.82/12.13  Cooper               : 0.00
% 21.82/12.13  Total                : 11.37
% 21.82/12.13  Index Insertion      : 0.00
% 21.82/12.13  Index Deletion       : 0.00
% 21.82/12.13  Index Matching       : 0.00
% 21.82/12.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
