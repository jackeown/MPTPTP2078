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
% DateTime   : Thu Dec  3 10:21:09 EST 2020

% Result     : Theorem 10.39s
% Output     : CNFRefutation 10.39s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 488 expanded)
%              Number of leaves         :   44 ( 182 expanded)
%              Depth                    :   14
%              Number of atoms          :  217 (1044 expanded)
%              Number of equality atoms :   62 ( 246 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(f_147,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_135,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_128,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_62,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_49,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_121,axiom,(
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

tff(c_56,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_147,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_393,plain,(
    ! [A_103,B_104,C_105] :
      ( k7_subset_1(A_103,B_104,C_105) = k4_xboole_0(B_104,C_105)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_414,plain,(
    ! [C_105] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_105) = k4_xboole_0('#skF_3',C_105) ),
    inference(resolution,[status(thm)],[c_50,c_393])).

tff(c_1243,plain,(
    ! [A_149,B_150] :
      ( k7_subset_1(u1_struct_0(A_149),B_150,k2_tops_1(A_149,B_150)) = k1_tops_1(A_149,B_150)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_pre_topc(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1273,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1243])).

tff(c_1293,plain,(
    k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_414,c_1273])).

tff(c_38,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(k2_tops_1(A_37,B_38),k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1421,plain,(
    ! [A_151,B_152] :
      ( k4_subset_1(u1_struct_0(A_151),B_152,k2_tops_1(A_151,B_152)) = k2_pre_topc(A_151,B_152)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1451,plain,
    ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1421])).

tff(c_1469,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1451])).

tff(c_1149,plain,(
    ! [A_138,B_139,C_140] :
      ( m1_subset_1(k4_subset_1(A_138,B_139,C_140),k1_zfmisc_1(A_138))
      | ~ m1_subset_1(C_140,k1_zfmisc_1(A_138))
      | ~ m1_subset_1(B_139,k1_zfmisc_1(A_138)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_32,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | ~ m1_subset_1(A_32,k1_zfmisc_1(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2939,plain,(
    ! [A_203,B_204,C_205] :
      ( r1_tarski(k4_subset_1(A_203,B_204,C_205),A_203)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(A_203))
      | ~ m1_subset_1(B_204,k1_zfmisc_1(A_203)) ) ),
    inference(resolution,[status(thm)],[c_1149,c_32])).

tff(c_2949,plain,
    ( r1_tarski(k2_pre_topc('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1469,c_2939])).

tff(c_2954,plain,
    ( r1_tarski(k2_pre_topc('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2949])).

tff(c_2955,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2954])).

tff(c_2958,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_2955])).

tff(c_2965,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_2958])).

tff(c_2966,plain,(
    r1_tarski(k2_pre_topc('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2954])).

tff(c_34,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(A_32,k1_zfmisc_1(B_33))
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_412,plain,(
    ! [B_33,A_32,C_105] :
      ( k7_subset_1(B_33,A_32,C_105) = k4_xboole_0(A_32,C_105)
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_34,c_393])).

tff(c_3489,plain,(
    ! [C_213] : k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),C_213) = k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),C_213) ),
    inference(resolution,[status(thm)],[c_2966,c_412])).

tff(c_42,plain,(
    ! [A_41,B_43] :
      ( k7_subset_1(u1_struct_0(A_41),k2_pre_topc(A_41,B_43),k1_tops_1(A_41,B_43)) = k2_tops_1(A_41,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3496,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3489,c_42])).

tff(c_3512,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_3496])).

tff(c_604,plain,(
    ! [B_118,A_119] :
      ( r1_tarski(B_118,k2_pre_topc(A_119,B_118))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_623,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_604])).

tff(c_637,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_623])).

tff(c_62,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_100,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_3499,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3489,c_100])).

tff(c_176,plain,(
    ! [A_89,B_90] :
      ( k4_xboole_0(A_89,B_90) = k3_subset_1(A_89,B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_194,plain,(
    ! [B_33,A_32] :
      ( k4_xboole_0(B_33,A_32) = k3_subset_1(B_33,A_32)
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_34,c_176])).

tff(c_647,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_637,c_194])).

tff(c_3527,plain,(
    k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3499,c_647])).

tff(c_250,plain,(
    ! [A_93,B_94] :
      ( k3_subset_1(A_93,k3_subset_1(A_93,B_94)) = B_94
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_266,plain,(
    ! [B_33,A_32] :
      ( k3_subset_1(B_33,k3_subset_1(B_33,A_32)) = A_32
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_34,c_250])).

tff(c_3641,plain,
    ( k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3527,c_266])).

tff(c_3669,plain,(
    k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_637,c_3641])).

tff(c_646,plain,(
    ! [C_105] : k7_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3',C_105) = k4_xboole_0('#skF_3',C_105) ),
    inference(resolution,[status(thm)],[c_637,c_412])).

tff(c_24,plain,(
    ! [A_21,B_22] : k6_subset_1(A_21,B_22) = k4_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    ! [A_12,B_13] : m1_subset_1(k6_subset_1(A_12,B_13),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_63,plain,(
    ! [A_12,B_13] : m1_subset_1(k4_xboole_0(A_12,B_13),k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_16])).

tff(c_561,plain,(
    ! [A_116,B_117] : k4_xboole_0(A_116,k4_xboole_0(A_116,B_117)) = k3_subset_1(A_116,k4_xboole_0(A_116,B_117)) ),
    inference(resolution,[status(thm)],[c_63,c_176])).

tff(c_579,plain,(
    ! [A_116,B_117] : m1_subset_1(k3_subset_1(A_116,k4_xboole_0(A_116,B_117)),k1_zfmisc_1(A_116)) ),
    inference(superposition,[status(thm),theory(equality)],[c_561,c_63])).

tff(c_1582,plain,(
    ! [A_154,B_155,C_156] :
      ( k9_subset_1(A_154,B_155,k3_subset_1(A_154,C_156)) = k7_subset_1(A_154,B_155,C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(A_154))
      | ~ m1_subset_1(B_155,k1_zfmisc_1(A_154)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5290,plain,(
    ! [A_245,B_246,B_247] :
      ( k9_subset_1(A_245,B_246,k3_subset_1(A_245,k4_xboole_0(A_245,B_247))) = k7_subset_1(A_245,B_246,k4_xboole_0(A_245,B_247))
      | ~ m1_subset_1(B_246,k1_zfmisc_1(A_245)) ) ),
    inference(resolution,[status(thm)],[c_63,c_1582])).

tff(c_134,plain,(
    ! [A_77,B_78,C_79] :
      ( k9_subset_1(A_77,B_78,B_78) = B_78
      | ~ m1_subset_1(C_79,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_144,plain,(
    ! [A_12,B_78] : k9_subset_1(A_12,B_78,B_78) = B_78 ),
    inference(resolution,[status(thm)],[c_63,c_134])).

tff(c_5305,plain,(
    ! [A_245,B_247] :
      ( k7_subset_1(A_245,k3_subset_1(A_245,k4_xboole_0(A_245,B_247)),k4_xboole_0(A_245,B_247)) = k3_subset_1(A_245,k4_xboole_0(A_245,B_247))
      | ~ m1_subset_1(k3_subset_1(A_245,k4_xboole_0(A_245,B_247)),k1_zfmisc_1(A_245)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5290,c_144])).

tff(c_13343,plain,(
    ! [A_377,B_378] : k7_subset_1(A_377,k3_subset_1(A_377,k4_xboole_0(A_377,B_378)),k4_xboole_0(A_377,B_378)) = k3_subset_1(A_377,k4_xboole_0(A_377,B_378)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_5305])).

tff(c_13461,plain,(
    k7_subset_1(k2_pre_topc('#skF_2','#skF_3'),k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')),k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),k1_tops_1('#skF_2','#skF_3'))) = k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),k1_tops_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3512,c_13343])).

tff(c_13596,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1293,c_3512,c_3669,c_3512,c_646,c_3669,c_13461])).

tff(c_86,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(A_66,B_67)
      | ~ m1_subset_1(A_66,k1_zfmisc_1(B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_97,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(resolution,[status(thm)],[c_63,c_86])).

tff(c_1320,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1293,c_97])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1341,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1320,c_2])).

tff(c_1382,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1341])).

tff(c_13649,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13596,c_1382])).

tff(c_13672,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_13649])).

tff(c_13673,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1341])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1041,plain,(
    ! [A_135,B_136] :
      ( v3_pre_topc(k1_tops_1(A_135,B_136),A_135)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135)
      | ~ v2_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1068,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1041])).

tff(c_1085,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1068])).

tff(c_13730,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13673,c_1085])).

tff(c_13736,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_13730])).

tff(c_13737,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_13953,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13737,c_100])).

tff(c_13954,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_13990,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13954,c_56])).

tff(c_14219,plain,(
    ! [A_435,B_436,C_437] :
      ( k7_subset_1(A_435,B_436,C_437) = k4_xboole_0(B_436,C_437)
      | ~ m1_subset_1(B_436,k1_zfmisc_1(A_435)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14240,plain,(
    ! [C_437] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_437) = k4_xboole_0('#skF_3',C_437) ),
    inference(resolution,[status(thm)],[c_50,c_14219])).

tff(c_15108,plain,(
    ! [A_489,B_490] :
      ( k7_subset_1(u1_struct_0(A_489),B_490,k2_tops_1(A_489,B_490)) = k1_tops_1(A_489,B_490)
      | ~ m1_subset_1(B_490,k1_zfmisc_1(u1_struct_0(A_489)))
      | ~ l1_pre_topc(A_489) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_15138,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_15108])).

tff(c_15159,plain,(
    k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_14240,c_15138])).

tff(c_15183,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_15159,c_97])).

tff(c_15203,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_15183,c_2])).

tff(c_15244,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_15203])).

tff(c_15584,plain,(
    ! [B_507,A_508,C_509] :
      ( r1_tarski(B_507,k1_tops_1(A_508,C_509))
      | ~ r1_tarski(B_507,C_509)
      | ~ v3_pre_topc(B_507,A_508)
      | ~ m1_subset_1(C_509,k1_zfmisc_1(u1_struct_0(A_508)))
      | ~ m1_subset_1(B_507,k1_zfmisc_1(u1_struct_0(A_508)))
      | ~ l1_pre_topc(A_508) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_15614,plain,(
    ! [B_507] :
      ( r1_tarski(B_507,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_507,'#skF_3')
      | ~ v3_pre_topc(B_507,'#skF_2')
      | ~ m1_subset_1(B_507,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_50,c_15584])).

tff(c_15706,plain,(
    ! [B_515] :
      ( r1_tarski(B_515,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_515,'#skF_3')
      | ~ v3_pre_topc(B_515,'#skF_2')
      | ~ m1_subset_1(B_515,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_15614])).

tff(c_15748,plain,
    ( r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_15706])).

tff(c_15767,plain,(
    r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13954,c_6,c_15748])).

tff(c_15769,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15244,c_15767])).

tff(c_15770,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_15203])).

tff(c_15938,plain,(
    ! [A_520,B_521] :
      ( k7_subset_1(u1_struct_0(A_520),k2_pre_topc(A_520,B_521),k1_tops_1(A_520,B_521)) = k2_tops_1(A_520,B_521)
      | ~ m1_subset_1(B_521,k1_zfmisc_1(u1_struct_0(A_520)))
      | ~ l1_pre_topc(A_520) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_15947,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_15770,c_15938])).

tff(c_15951,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_15947])).

tff(c_15953,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13990,c_15951])).
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
% 0.12/0.34  % DateTime   : Tue Dec  1 20:58:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.39/3.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.39/3.94  
% 10.39/3.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.39/3.94  %$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3
% 10.39/3.94  
% 10.39/3.94  %Foreground sorts:
% 10.39/3.94  
% 10.39/3.94  
% 10.39/3.94  %Background operators:
% 10.39/3.94  
% 10.39/3.94  
% 10.39/3.94  %Foreground operators:
% 10.39/3.94  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 10.39/3.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.39/3.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.39/3.94  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 10.39/3.94  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.39/3.94  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.39/3.94  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.39/3.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.39/3.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.39/3.94  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.39/3.94  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 10.39/3.94  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 10.39/3.94  tff('#skF_2', type, '#skF_2': $i).
% 10.39/3.94  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 10.39/3.94  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 10.39/3.94  tff('#skF_3', type, '#skF_3': $i).
% 10.39/3.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.39/3.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.39/3.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.39/3.94  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.39/3.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.39/3.94  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.39/3.94  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.39/3.94  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 10.39/3.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.39/3.94  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.39/3.94  
% 10.39/3.96  tff(f_147, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 10.39/3.96  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.39/3.96  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 10.39/3.96  tff(f_135, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 10.39/3.96  tff(f_92, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 10.39/3.96  tff(f_128, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 10.39/3.96  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 10.39/3.96  tff(f_79, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.39/3.96  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 10.39/3.96  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 10.39/3.96  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 10.39/3.96  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 10.39/3.96  tff(f_62, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 10.39/3.96  tff(f_49, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 10.39/3.96  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 10.39/3.96  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 10.39/3.96  tff(f_100, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 10.39/3.96  tff(f_121, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 10.39/3.96  tff(c_56, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')!=k2_tops_1('#skF_2', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 10.39/3.96  tff(c_147, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_56])).
% 10.39/3.96  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.39/3.96  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 10.39/3.96  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 10.39/3.96  tff(c_393, plain, (![A_103, B_104, C_105]: (k7_subset_1(A_103, B_104, C_105)=k4_xboole_0(B_104, C_105) | ~m1_subset_1(B_104, k1_zfmisc_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.39/3.96  tff(c_414, plain, (![C_105]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_105)=k4_xboole_0('#skF_3', C_105))), inference(resolution, [status(thm)], [c_50, c_393])).
% 10.39/3.96  tff(c_1243, plain, (![A_149, B_150]: (k7_subset_1(u1_struct_0(A_149), B_150, k2_tops_1(A_149, B_150))=k1_tops_1(A_149, B_150) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_pre_topc(A_149))), inference(cnfTransformation, [status(thm)], [f_135])).
% 10.39/3.96  tff(c_1273, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1243])).
% 10.39/3.96  tff(c_1293, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_414, c_1273])).
% 10.39/3.96  tff(c_38, plain, (![A_37, B_38]: (m1_subset_1(k2_tops_1(A_37, B_38), k1_zfmisc_1(u1_struct_0(A_37))) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.39/3.96  tff(c_1421, plain, (![A_151, B_152]: (k4_subset_1(u1_struct_0(A_151), B_152, k2_tops_1(A_151, B_152))=k2_pre_topc(A_151, B_152) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151))), inference(cnfTransformation, [status(thm)], [f_128])).
% 10.39/3.96  tff(c_1451, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1421])).
% 10.39/3.96  tff(c_1469, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1451])).
% 10.39/3.96  tff(c_1149, plain, (![A_138, B_139, C_140]: (m1_subset_1(k4_subset_1(A_138, B_139, C_140), k1_zfmisc_1(A_138)) | ~m1_subset_1(C_140, k1_zfmisc_1(A_138)) | ~m1_subset_1(B_139, k1_zfmisc_1(A_138)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.39/3.96  tff(c_32, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | ~m1_subset_1(A_32, k1_zfmisc_1(B_33)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.39/3.96  tff(c_2939, plain, (![A_203, B_204, C_205]: (r1_tarski(k4_subset_1(A_203, B_204, C_205), A_203) | ~m1_subset_1(C_205, k1_zfmisc_1(A_203)) | ~m1_subset_1(B_204, k1_zfmisc_1(A_203)))), inference(resolution, [status(thm)], [c_1149, c_32])).
% 10.39/3.96  tff(c_2949, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1469, c_2939])).
% 10.39/3.96  tff(c_2954, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2949])).
% 10.39/3.96  tff(c_2955, plain, (~m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_2954])).
% 10.39/3.96  tff(c_2958, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_2955])).
% 10.39/3.96  tff(c_2965, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_2958])).
% 10.39/3.96  tff(c_2966, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_2954])).
% 10.39/3.96  tff(c_34, plain, (![A_32, B_33]: (m1_subset_1(A_32, k1_zfmisc_1(B_33)) | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.39/3.96  tff(c_412, plain, (![B_33, A_32, C_105]: (k7_subset_1(B_33, A_32, C_105)=k4_xboole_0(A_32, C_105) | ~r1_tarski(A_32, B_33))), inference(resolution, [status(thm)], [c_34, c_393])).
% 10.39/3.96  tff(c_3489, plain, (![C_213]: (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), C_213)=k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), C_213))), inference(resolution, [status(thm)], [c_2966, c_412])).
% 10.39/3.96  tff(c_42, plain, (![A_41, B_43]: (k7_subset_1(u1_struct_0(A_41), k2_pre_topc(A_41, B_43), k1_tops_1(A_41, B_43))=k2_tops_1(A_41, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.39/3.96  tff(c_3496, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3489, c_42])).
% 10.39/3.96  tff(c_3512, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_3496])).
% 10.39/3.96  tff(c_604, plain, (![B_118, A_119]: (r1_tarski(B_118, k2_pre_topc(A_119, B_118)) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.39/3.96  tff(c_623, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_604])).
% 10.39/3.96  tff(c_637, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_623])).
% 10.39/3.96  tff(c_62, plain, (v3_pre_topc('#skF_3', '#skF_2') | k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 10.39/3.96  tff(c_100, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_62])).
% 10.39/3.96  tff(c_3499, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3489, c_100])).
% 10.39/3.96  tff(c_176, plain, (![A_89, B_90]: (k4_xboole_0(A_89, B_90)=k3_subset_1(A_89, B_90) | ~m1_subset_1(B_90, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.39/3.96  tff(c_194, plain, (![B_33, A_32]: (k4_xboole_0(B_33, A_32)=k3_subset_1(B_33, A_32) | ~r1_tarski(A_32, B_33))), inference(resolution, [status(thm)], [c_34, c_176])).
% 10.39/3.96  tff(c_647, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_637, c_194])).
% 10.39/3.96  tff(c_3527, plain, (k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3499, c_647])).
% 10.39/3.96  tff(c_250, plain, (![A_93, B_94]: (k3_subset_1(A_93, k3_subset_1(A_93, B_94))=B_94 | ~m1_subset_1(B_94, k1_zfmisc_1(A_93)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.39/3.96  tff(c_266, plain, (![B_33, A_32]: (k3_subset_1(B_33, k3_subset_1(B_33, A_32))=A_32 | ~r1_tarski(A_32, B_33))), inference(resolution, [status(thm)], [c_34, c_250])).
% 10.39/3.96  tff(c_3641, plain, (k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3'))='#skF_3' | ~r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3527, c_266])).
% 10.39/3.96  tff(c_3669, plain, (k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_637, c_3641])).
% 10.39/3.96  tff(c_646, plain, (![C_105]: (k7_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3', C_105)=k4_xboole_0('#skF_3', C_105))), inference(resolution, [status(thm)], [c_637, c_412])).
% 10.39/3.96  tff(c_24, plain, (![A_21, B_22]: (k6_subset_1(A_21, B_22)=k4_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.39/3.96  tff(c_16, plain, (![A_12, B_13]: (m1_subset_1(k6_subset_1(A_12, B_13), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.39/3.96  tff(c_63, plain, (![A_12, B_13]: (m1_subset_1(k4_xboole_0(A_12, B_13), k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_16])).
% 10.39/3.96  tff(c_561, plain, (![A_116, B_117]: (k4_xboole_0(A_116, k4_xboole_0(A_116, B_117))=k3_subset_1(A_116, k4_xboole_0(A_116, B_117)))), inference(resolution, [status(thm)], [c_63, c_176])).
% 10.39/3.96  tff(c_579, plain, (![A_116, B_117]: (m1_subset_1(k3_subset_1(A_116, k4_xboole_0(A_116, B_117)), k1_zfmisc_1(A_116)))), inference(superposition, [status(thm), theory('equality')], [c_561, c_63])).
% 10.39/3.96  tff(c_1582, plain, (![A_154, B_155, C_156]: (k9_subset_1(A_154, B_155, k3_subset_1(A_154, C_156))=k7_subset_1(A_154, B_155, C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(A_154)) | ~m1_subset_1(B_155, k1_zfmisc_1(A_154)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.39/3.96  tff(c_5290, plain, (![A_245, B_246, B_247]: (k9_subset_1(A_245, B_246, k3_subset_1(A_245, k4_xboole_0(A_245, B_247)))=k7_subset_1(A_245, B_246, k4_xboole_0(A_245, B_247)) | ~m1_subset_1(B_246, k1_zfmisc_1(A_245)))), inference(resolution, [status(thm)], [c_63, c_1582])).
% 10.39/3.96  tff(c_134, plain, (![A_77, B_78, C_79]: (k9_subset_1(A_77, B_78, B_78)=B_78 | ~m1_subset_1(C_79, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.39/3.96  tff(c_144, plain, (![A_12, B_78]: (k9_subset_1(A_12, B_78, B_78)=B_78)), inference(resolution, [status(thm)], [c_63, c_134])).
% 10.39/3.96  tff(c_5305, plain, (![A_245, B_247]: (k7_subset_1(A_245, k3_subset_1(A_245, k4_xboole_0(A_245, B_247)), k4_xboole_0(A_245, B_247))=k3_subset_1(A_245, k4_xboole_0(A_245, B_247)) | ~m1_subset_1(k3_subset_1(A_245, k4_xboole_0(A_245, B_247)), k1_zfmisc_1(A_245)))), inference(superposition, [status(thm), theory('equality')], [c_5290, c_144])).
% 10.39/3.96  tff(c_13343, plain, (![A_377, B_378]: (k7_subset_1(A_377, k3_subset_1(A_377, k4_xboole_0(A_377, B_378)), k4_xboole_0(A_377, B_378))=k3_subset_1(A_377, k4_xboole_0(A_377, B_378)))), inference(demodulation, [status(thm), theory('equality')], [c_579, c_5305])).
% 10.39/3.96  tff(c_13461, plain, (k7_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3')), k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), k1_tops_1('#skF_2', '#skF_3')))=k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), k1_tops_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3512, c_13343])).
% 10.39/3.96  tff(c_13596, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1293, c_3512, c_3669, c_3512, c_646, c_3669, c_13461])).
% 10.39/3.96  tff(c_86, plain, (![A_66, B_67]: (r1_tarski(A_66, B_67) | ~m1_subset_1(A_66, k1_zfmisc_1(B_67)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.39/3.96  tff(c_97, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(resolution, [status(thm)], [c_63, c_86])).
% 10.39/3.96  tff(c_1320, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1293, c_97])).
% 10.39/3.96  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.39/3.96  tff(c_1341, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_1320, c_2])).
% 10.39/3.96  tff(c_1382, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1341])).
% 10.39/3.96  tff(c_13649, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13596, c_1382])).
% 10.39/3.96  tff(c_13672, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_13649])).
% 10.39/3.96  tff(c_13673, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_1341])).
% 10.39/3.96  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 10.39/3.96  tff(c_1041, plain, (![A_135, B_136]: (v3_pre_topc(k1_tops_1(A_135, B_136), A_135) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135) | ~v2_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.39/3.96  tff(c_1068, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1041])).
% 10.39/3.96  tff(c_1085, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1068])).
% 10.39/3.96  tff(c_13730, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13673, c_1085])).
% 10.39/3.96  tff(c_13736, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_13730])).
% 10.39/3.96  tff(c_13737, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')!=k2_tops_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_56])).
% 10.39/3.96  tff(c_13953, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13737, c_100])).
% 10.39/3.96  tff(c_13954, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_62])).
% 10.39/3.96  tff(c_13990, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')!=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13954, c_56])).
% 10.39/3.96  tff(c_14219, plain, (![A_435, B_436, C_437]: (k7_subset_1(A_435, B_436, C_437)=k4_xboole_0(B_436, C_437) | ~m1_subset_1(B_436, k1_zfmisc_1(A_435)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.39/3.96  tff(c_14240, plain, (![C_437]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_437)=k4_xboole_0('#skF_3', C_437))), inference(resolution, [status(thm)], [c_50, c_14219])).
% 10.39/3.96  tff(c_15108, plain, (![A_489, B_490]: (k7_subset_1(u1_struct_0(A_489), B_490, k2_tops_1(A_489, B_490))=k1_tops_1(A_489, B_490) | ~m1_subset_1(B_490, k1_zfmisc_1(u1_struct_0(A_489))) | ~l1_pre_topc(A_489))), inference(cnfTransformation, [status(thm)], [f_135])).
% 10.39/3.96  tff(c_15138, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_15108])).
% 10.39/3.96  tff(c_15159, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_14240, c_15138])).
% 10.39/3.96  tff(c_15183, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_15159, c_97])).
% 10.39/3.96  tff(c_15203, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_15183, c_2])).
% 10.39/3.96  tff(c_15244, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_15203])).
% 10.39/3.96  tff(c_15584, plain, (![B_507, A_508, C_509]: (r1_tarski(B_507, k1_tops_1(A_508, C_509)) | ~r1_tarski(B_507, C_509) | ~v3_pre_topc(B_507, A_508) | ~m1_subset_1(C_509, k1_zfmisc_1(u1_struct_0(A_508))) | ~m1_subset_1(B_507, k1_zfmisc_1(u1_struct_0(A_508))) | ~l1_pre_topc(A_508))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.39/3.97  tff(c_15614, plain, (![B_507]: (r1_tarski(B_507, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_507, '#skF_3') | ~v3_pre_topc(B_507, '#skF_2') | ~m1_subset_1(B_507, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_15584])).
% 10.39/3.97  tff(c_15706, plain, (![B_515]: (r1_tarski(B_515, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_515, '#skF_3') | ~v3_pre_topc(B_515, '#skF_2') | ~m1_subset_1(B_515, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_15614])).
% 10.39/3.97  tff(c_15748, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_3', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_50, c_15706])).
% 10.39/3.97  tff(c_15767, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_13954, c_6, c_15748])).
% 10.39/3.97  tff(c_15769, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15244, c_15767])).
% 10.39/3.97  tff(c_15770, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_15203])).
% 10.39/3.97  tff(c_15938, plain, (![A_520, B_521]: (k7_subset_1(u1_struct_0(A_520), k2_pre_topc(A_520, B_521), k1_tops_1(A_520, B_521))=k2_tops_1(A_520, B_521) | ~m1_subset_1(B_521, k1_zfmisc_1(u1_struct_0(A_520))) | ~l1_pre_topc(A_520))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.39/3.97  tff(c_15947, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_15770, c_15938])).
% 10.39/3.97  tff(c_15951, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_15947])).
% 10.39/3.97  tff(c_15953, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13990, c_15951])).
% 10.39/3.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.39/3.97  
% 10.39/3.97  Inference rules
% 10.39/3.97  ----------------------
% 10.39/3.97  #Ref     : 0
% 10.39/3.97  #Sup     : 3837
% 10.39/3.97  #Fact    : 0
% 10.39/3.97  #Define  : 0
% 10.39/3.97  #Split   : 19
% 10.39/3.97  #Chain   : 0
% 10.39/3.97  #Close   : 0
% 10.39/3.97  
% 10.39/3.97  Ordering : KBO
% 10.39/3.97  
% 10.39/3.97  Simplification rules
% 10.39/3.97  ----------------------
% 10.39/3.97  #Subsume      : 221
% 10.39/3.97  #Demod        : 3832
% 10.39/3.97  #Tautology    : 1464
% 10.39/3.97  #SimpNegUnit  : 6
% 10.39/3.97  #BackRed      : 49
% 10.39/3.97  
% 10.39/3.97  #Partial instantiations: 0
% 10.39/3.97  #Strategies tried      : 1
% 10.39/3.97  
% 10.39/3.97  Timing (in seconds)
% 10.39/3.97  ----------------------
% 10.39/3.97  Preprocessing        : 0.35
% 10.39/3.97  Parsing              : 0.18
% 10.39/3.97  CNF conversion       : 0.02
% 10.39/3.97  Main loop            : 2.84
% 10.39/3.97  Inferencing          : 0.71
% 10.39/3.97  Reduction            : 1.28
% 10.39/3.97  Demodulation         : 1.03
% 10.39/3.97  BG Simplification    : 0.09
% 10.39/3.97  Subsumption          : 0.56
% 10.39/3.97  Abstraction          : 0.15
% 10.39/3.97  MUC search           : 0.00
% 10.39/3.97  Cooper               : 0.00
% 10.39/3.97  Total                : 3.23
% 10.39/3.97  Index Insertion      : 0.00
% 10.39/3.97  Index Deletion       : 0.00
% 10.39/3.97  Index Matching       : 0.00
% 10.39/3.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
