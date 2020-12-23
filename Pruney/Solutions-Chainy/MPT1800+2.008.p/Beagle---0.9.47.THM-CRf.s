%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:58 EST 2020

% Result     : Theorem 5.35s
% Output     : CNFRefutation 5.79s
% Verified   : 
% Statistics : Number of formulae       :  234 (4649 expanded)
%              Number of leaves         :   38 (1600 expanded)
%              Depth                    :   33
%              Number of atoms          :  610 (13413 expanded)
%              Number of equality atoms :  105 (2610 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tsep_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k8_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k8_tmap_1,type,(
    k8_tmap_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_154,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ( ( v1_tsep_1(B,A)
                & m1_pre_topc(B,A) )
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k8_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_tmap_1)).

tff(f_134,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_101,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_123,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ( u1_struct_0(k8_tmap_1(A,B)) = u1_struct_0(A)
            & ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => u1_pre_topc(k8_tmap_1(A,B)) = k5_tmap_1(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_tmap_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(f_130,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tsep_1(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tsep_1)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_42,plain,(
    ! [A_35] :
      ( m1_pre_topc(A_35,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_16,plain,(
    ! [A_9] :
      ( v3_pre_topc(k2_struct_0(A_9),A_9)
      | ~ l1_pre_topc(A_9)
      | ~ v2_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1889,plain,(
    ! [A_126] :
      ( u1_struct_0(A_126) = k2_struct_0(A_126)
      | ~ l1_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1894,plain,(
    ! [A_127] :
      ( u1_struct_0(A_127) = k2_struct_0(A_127)
      | ~ l1_pre_topc(A_127) ) ),
    inference(resolution,[status(thm)],[c_14,c_1889])).

tff(c_1898,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1894])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_68,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_1951,plain,(
    ! [B_144,A_145] :
      ( v3_pre_topc(B_144,A_145)
      | ~ r2_hidden(B_144,u1_pre_topc(A_145))
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1970,plain,(
    ! [A_146] :
      ( v3_pre_topc(u1_struct_0(A_146),A_146)
      | ~ r2_hidden(u1_struct_0(A_146),u1_pre_topc(A_146))
      | ~ l1_pre_topc(A_146) ) ),
    inference(resolution,[status(thm)],[c_68,c_1951])).

tff(c_1973,plain,
    ( v3_pre_topc(u1_struct_0('#skF_2'),'#skF_2')
    | ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1898,c_1970])).

tff(c_1975,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1898,c_1973])).

tff(c_1976,plain,(
    ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1975])).

tff(c_1992,plain,(
    ! [B_149,A_150] :
      ( r2_hidden(B_149,u1_pre_topc(A_150))
      | ~ v3_pre_topc(B_149,A_150)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ l1_pre_topc(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2011,plain,(
    ! [A_151] :
      ( r2_hidden(u1_struct_0(A_151),u1_pre_topc(A_151))
      | ~ v3_pre_topc(u1_struct_0(A_151),A_151)
      | ~ l1_pre_topc(A_151) ) ),
    inference(resolution,[status(thm)],[c_68,c_1992])).

tff(c_2021,plain,
    ( r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc(u1_struct_0('#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1898,c_2011])).

tff(c_2027,plain,
    ( r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1898,c_2021])).

tff(c_2028,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1976,c_2027])).

tff(c_2045,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_2028])).

tff(c_2049,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2045])).

tff(c_2051,plain,(
    r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1975])).

tff(c_2541,plain,(
    ! [A_195,B_196] :
      ( k5_tmap_1(A_195,B_196) = u1_pre_topc(A_195)
      | ~ r2_hidden(B_196,u1_pre_topc(A_195))
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ l1_pre_topc(A_195)
      | ~ v2_pre_topc(A_195)
      | v2_struct_0(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2559,plain,(
    ! [B_196] :
      ( k5_tmap_1('#skF_2',B_196) = u1_pre_topc('#skF_2')
      | ~ r2_hidden(B_196,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_196,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1898,c_2541])).

tff(c_2568,plain,(
    ! [B_196] :
      ( k5_tmap_1('#skF_2',B_196) = u1_pre_topc('#skF_2')
      | ~ r2_hidden(B_196,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_196,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2559])).

tff(c_2571,plain,(
    ! [B_197] :
      ( k5_tmap_1('#skF_2',B_197) = u1_pre_topc('#skF_2')
      | ~ r2_hidden(B_197,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_197,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2568])).

tff(c_2581,plain,
    ( k5_tmap_1('#skF_2',k2_struct_0('#skF_2')) = u1_pre_topc('#skF_2')
    | ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_2571])).

tff(c_2586,plain,(
    k5_tmap_1('#skF_2',k2_struct_0('#skF_2')) = u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2051,c_2581])).

tff(c_2734,plain,(
    ! [A_203,B_204] :
      ( k5_tmap_1(A_203,u1_struct_0(B_204)) = u1_pre_topc(k8_tmap_1(A_203,B_204))
      | ~ m1_subset_1(u1_struct_0(B_204),k1_zfmisc_1(u1_struct_0(A_203)))
      | ~ m1_pre_topc(B_204,A_203)
      | v2_struct_0(B_204)
      | ~ l1_pre_topc(A_203)
      | ~ v2_pre_topc(A_203)
      | v2_struct_0(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2805,plain,(
    ! [B_206] :
      ( k5_tmap_1(B_206,u1_struct_0(B_206)) = u1_pre_topc(k8_tmap_1(B_206,B_206))
      | ~ m1_pre_topc(B_206,B_206)
      | ~ l1_pre_topc(B_206)
      | ~ v2_pre_topc(B_206)
      | v2_struct_0(B_206) ) ),
    inference(resolution,[status(thm)],[c_68,c_2734])).

tff(c_2828,plain,
    ( k5_tmap_1('#skF_2',k2_struct_0('#skF_2')) = u1_pre_topc(k8_tmap_1('#skF_2','#skF_2'))
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1898,c_2805])).

tff(c_2838,plain,
    ( u1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) = u1_pre_topc('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2586,c_2828])).

tff(c_2839,plain,
    ( u1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) = u1_pre_topc('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2838])).

tff(c_2840,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2839])).

tff(c_2844,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_2840])).

tff(c_2848,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2844])).

tff(c_2850,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2839])).

tff(c_30,plain,(
    ! [A_20,B_21] :
      ( v1_pre_topc(k8_tmap_1(A_20,B_21))
      | ~ m1_pre_topc(B_21,A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( l1_pre_topc(k8_tmap_1(A_20,B_21))
      | ~ m1_pre_topc(B_21,A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2849,plain,(
    u1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) = u1_pre_topc('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2839])).

tff(c_40,plain,(
    ! [B_34,A_32] :
      ( m1_subset_1(u1_struct_0(B_34),k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_pre_topc(B_34,A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2158,plain,(
    ! [B_164,A_165] :
      ( v3_pre_topc(u1_struct_0(B_164),A_165)
      | ~ r2_hidden(u1_struct_0(B_164),u1_pre_topc(A_165))
      | ~ m1_pre_topc(B_164,A_165)
      | ~ l1_pre_topc(A_165) ) ),
    inference(resolution,[status(thm)],[c_40,c_1951])).

tff(c_2167,plain,(
    ! [A_165] :
      ( v3_pre_topc(u1_struct_0('#skF_2'),A_165)
      | ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc(A_165))
      | ~ m1_pre_topc('#skF_2',A_165)
      | ~ l1_pre_topc(A_165) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1898,c_2158])).

tff(c_2172,plain,(
    ! [A_165] :
      ( v3_pre_topc(k2_struct_0('#skF_2'),A_165)
      | ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc(A_165))
      | ~ m1_pre_topc('#skF_2',A_165)
      | ~ l1_pre_topc(A_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1898,c_2167])).

tff(c_2866,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),k8_tmap_1('#skF_2','#skF_2'))
    | ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
    | ~ m1_pre_topc('#skF_2',k8_tmap_1('#skF_2','#skF_2'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2849,c_2172])).

tff(c_2888,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),k8_tmap_1('#skF_2','#skF_2'))
    | ~ m1_pre_topc('#skF_2',k8_tmap_1('#skF_2','#skF_2'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2051,c_2866])).

tff(c_2991,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2888])).

tff(c_3015,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_2991])).

tff(c_3018,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2850,c_3015])).

tff(c_3020,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3018])).

tff(c_3022,plain,(
    l1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2888])).

tff(c_1893,plain,(
    ! [A_8] :
      ( u1_struct_0(A_8) = k2_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_1889])).

tff(c_3026,plain,(
    u1_struct_0(k8_tmap_1('#skF_2','#skF_2')) = k2_struct_0(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_3022,c_1893])).

tff(c_38,plain,(
    ! [A_25,B_29] :
      ( u1_struct_0(k8_tmap_1(A_25,B_29)) = u1_struct_0(A_25)
      | ~ m1_pre_topc(B_29,A_25)
      | v2_struct_0(B_29)
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_3078,plain,
    ( k2_struct_0(k8_tmap_1('#skF_2','#skF_2')) = u1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3026,c_38])).

tff(c_3152,plain,
    ( k2_struct_0(k8_tmap_1('#skF_2','#skF_2')) = k2_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2850,c_1898,c_3078])).

tff(c_3153,plain,(
    k2_struct_0(k8_tmap_1('#skF_2','#skF_2')) = k2_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3152])).

tff(c_3182,plain,(
    u1_struct_0(k8_tmap_1('#skF_2','#skF_2')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3153,c_3026])).

tff(c_6,plain,(
    ! [A_3] :
      ( g1_pre_topc(u1_struct_0(A_3),u1_pre_topc(A_3)) = A_3
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3334,plain,
    ( g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc(k8_tmap_1('#skF_2','#skF_2'))) = k8_tmap_1('#skF_2','#skF_2')
    | ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_2'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3182,c_6])).

tff(c_3396,plain,
    ( g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k8_tmap_1('#skF_2','#skF_2')
    | ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3022,c_2849,c_3334])).

tff(c_3458,plain,(
    ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3396])).

tff(c_3461,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_3458])).

tff(c_3464,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2850,c_3461])).

tff(c_3466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3464])).

tff(c_3467,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k8_tmap_1('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_3396])).

tff(c_82,plain,(
    ! [A_41] :
      ( u1_struct_0(A_41) = k2_struct_0(A_41)
      | ~ l1_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_87,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(resolution,[status(thm)],[c_14,c_82])).

tff(c_91,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_87])).

tff(c_64,plain,
    ( v1_tsep_1('#skF_3','#skF_2')
    | g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k8_tmap_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_81,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k8_tmap_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_97,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k8_tmap_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_81])).

tff(c_44,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_54,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k8_tmap_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ v1_tsep_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_67,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k8_tmap_1('#skF_2','#skF_3')
    | ~ v1_tsep_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_54])).

tff(c_118,plain,(
    ~ v1_tsep_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_91,c_67])).

tff(c_139,plain,(
    ! [B_49,A_50] :
      ( u1_struct_0(B_49) = '#skF_1'(A_50,B_49)
      | v1_tsep_1(B_49,A_50)
      | ~ m1_pre_topc(B_49,A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_142,plain,
    ( u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_139,c_118])).

tff(c_145,plain,(
    u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_142])).

tff(c_119,plain,(
    ! [B_45,A_46] :
      ( m1_subset_1(u1_struct_0(B_45),k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ m1_pre_topc(B_45,A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_125,plain,(
    ! [B_45] :
      ( m1_subset_1(u1_struct_0(B_45),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_45,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_119])).

tff(c_127,plain,(
    ! [B_45] :
      ( m1_subset_1(u1_struct_0(B_45),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_45,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_125])).

tff(c_152,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_127])).

tff(c_165,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_152])).

tff(c_1114,plain,(
    ! [A_114,B_115] :
      ( k5_tmap_1(A_114,u1_struct_0(B_115)) = u1_pre_topc(k8_tmap_1(A_114,B_115))
      | ~ m1_subset_1(u1_struct_0(B_115),k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ m1_pre_topc(B_115,A_114)
      | v2_struct_0(B_115)
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1141,plain,(
    ! [B_115] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_115)) = u1_pre_topc(k8_tmap_1('#skF_2',B_115))
      | ~ m1_subset_1(u1_struct_0(B_115),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_115,'#skF_2')
      | v2_struct_0(B_115)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_1114])).

tff(c_1153,plain,(
    ! [B_115] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_115)) = u1_pre_topc(k8_tmap_1('#skF_2',B_115))
      | ~ m1_subset_1(u1_struct_0(B_115),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_115,'#skF_2')
      | v2_struct_0(B_115)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_1141])).

tff(c_1329,plain,(
    ! [B_120] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_120)) = u1_pre_topc(k8_tmap_1('#skF_2',B_120))
      | ~ m1_subset_1(u1_struct_0(B_120),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_120,'#skF_2')
      | v2_struct_0(B_120) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1153])).

tff(c_1338,plain,
    ( k5_tmap_1('#skF_2',u1_struct_0('#skF_3')) = u1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_1329])).

tff(c_1346,plain,
    ( k5_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) = u1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_165,c_145,c_1338])).

tff(c_1347,plain,(
    k5_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) = u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1346])).

tff(c_212,plain,(
    ! [B_62,A_63] :
      ( v3_pre_topc(B_62,A_63)
      | ~ r2_hidden(B_62,u1_pre_topc(A_63))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_227,plain,(
    ! [B_62] :
      ( v3_pre_topc(B_62,'#skF_2')
      | ~ r2_hidden(B_62,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_212])).

tff(c_258,plain,(
    ! [B_65] :
      ( v3_pre_topc(B_65,'#skF_2')
      | ~ r2_hidden(B_65,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_227])).

tff(c_269,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_165,c_258])).

tff(c_288,plain,(
    ~ r2_hidden('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_269])).

tff(c_693,plain,(
    ! [B_97,A_98] :
      ( r2_hidden(B_97,u1_pre_topc(A_98))
      | k5_tmap_1(A_98,B_97) != u1_pre_topc(A_98)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98)
      | ~ v2_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_717,plain,(
    ! [B_97] :
      ( r2_hidden(B_97,u1_pre_topc('#skF_2'))
      | k5_tmap_1('#skF_2',B_97) != u1_pre_topc('#skF_2')
      | ~ m1_subset_1(B_97,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_693])).

tff(c_728,plain,(
    ! [B_97] :
      ( r2_hidden(B_97,u1_pre_topc('#skF_2'))
      | k5_tmap_1('#skF_2',B_97) != u1_pre_topc('#skF_2')
      | ~ m1_subset_1(B_97,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_717])).

tff(c_731,plain,(
    ! [B_99] :
      ( r2_hidden(B_99,u1_pre_topc('#skF_2'))
      | k5_tmap_1('#skF_2',B_99) != u1_pre_topc('#skF_2')
      | ~ m1_subset_1(B_99,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_728])).

tff(c_737,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_2'))
    | k5_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) != u1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_165,c_731])).

tff(c_748,plain,(
    k5_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) != u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_288,c_737])).

tff(c_1759,plain,(
    u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) != u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1347,c_748])).

tff(c_186,plain,(
    ! [B_60,A_61] :
      ( r2_hidden(B_60,u1_pre_topc(A_61))
      | ~ v3_pre_topc(B_60,A_61)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_238,plain,(
    ! [A_64] :
      ( r2_hidden(u1_struct_0(A_64),u1_pre_topc(A_64))
      | ~ v3_pre_topc(u1_struct_0(A_64),A_64)
      | ~ l1_pre_topc(A_64) ) ),
    inference(resolution,[status(thm)],[c_68,c_186])).

tff(c_244,plain,
    ( r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc(u1_struct_0('#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_238])).

tff(c_247,plain,
    ( r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_91,c_244])).

tff(c_248,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_247])).

tff(c_251,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_248])).

tff(c_255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_251])).

tff(c_256,plain,(
    r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_889,plain,(
    ! [A_106,B_107] :
      ( k5_tmap_1(A_106,B_107) = u1_pre_topc(A_106)
      | ~ r2_hidden(B_107,u1_pre_topc(A_106))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_913,plain,(
    ! [B_107] :
      ( k5_tmap_1('#skF_2',B_107) = u1_pre_topc('#skF_2')
      | ~ r2_hidden(B_107,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_889])).

tff(c_924,plain,(
    ! [B_107] :
      ( k5_tmap_1('#skF_2',B_107) = u1_pre_topc('#skF_2')
      | ~ r2_hidden(B_107,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_913])).

tff(c_928,plain,(
    ! [B_109] :
      ( k5_tmap_1('#skF_2',B_109) = u1_pre_topc('#skF_2')
      | ~ r2_hidden(B_109,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_924])).

tff(c_941,plain,
    ( k5_tmap_1('#skF_2',k2_struct_0('#skF_2')) = u1_pre_topc('#skF_2')
    | ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_928])).

tff(c_948,plain,(
    k5_tmap_1('#skF_2',k2_struct_0('#skF_2')) = u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_941])).

tff(c_1199,plain,(
    ! [B_117] :
      ( k5_tmap_1(B_117,u1_struct_0(B_117)) = u1_pre_topc(k8_tmap_1(B_117,B_117))
      | ~ m1_pre_topc(B_117,B_117)
      | ~ l1_pre_topc(B_117)
      | ~ v2_pre_topc(B_117)
      | v2_struct_0(B_117) ) ),
    inference(resolution,[status(thm)],[c_68,c_1114])).

tff(c_1225,plain,
    ( k5_tmap_1('#skF_2',k2_struct_0('#skF_2')) = u1_pre_topc(k8_tmap_1('#skF_2','#skF_2'))
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_1199])).

tff(c_1236,plain,
    ( u1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) = u1_pre_topc('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_948,c_1225])).

tff(c_1237,plain,
    ( u1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) = u1_pre_topc('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1236])).

tff(c_1238,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1237])).

tff(c_1242,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_1238])).

tff(c_1246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1242])).

tff(c_1248,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1237])).

tff(c_1247,plain,(
    u1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) = u1_pre_topc('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1237])).

tff(c_375,plain,(
    ! [B_73,A_74] :
      ( v3_pre_topc(u1_struct_0(B_73),A_74)
      | ~ r2_hidden(u1_struct_0(B_73),u1_pre_topc(A_74))
      | ~ m1_pre_topc(B_73,A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_40,c_212])).

tff(c_387,plain,(
    ! [A_74] :
      ( v3_pre_topc(u1_struct_0('#skF_2'),A_74)
      | ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc(A_74))
      | ~ m1_pre_topc('#skF_2',A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_375])).

tff(c_393,plain,(
    ! [A_74] :
      ( v3_pre_topc(k2_struct_0('#skF_2'),A_74)
      | ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc(A_74))
      | ~ m1_pre_topc('#skF_2',A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_387])).

tff(c_1267,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),k8_tmap_1('#skF_2','#skF_2'))
    | ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
    | ~ m1_pre_topc('#skF_2',k8_tmap_1('#skF_2','#skF_2'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1247,c_393])).

tff(c_1290,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),k8_tmap_1('#skF_2','#skF_2'))
    | ~ m1_pre_topc('#skF_2',k8_tmap_1('#skF_2','#skF_2'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_1267])).

tff(c_1314,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1290])).

tff(c_1317,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_1314])).

tff(c_1320,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_1248,c_1317])).

tff(c_1322,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1320])).

tff(c_1324,plain,(
    l1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1290])).

tff(c_86,plain,(
    ! [A_8] :
      ( u1_struct_0(A_8) = k2_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_82])).

tff(c_1328,plain,(
    u1_struct_0(k8_tmap_1('#skF_2','#skF_2')) = k2_struct_0(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1324,c_86])).

tff(c_1409,plain,
    ( k2_struct_0(k8_tmap_1('#skF_2','#skF_2')) = u1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1328,c_38])).

tff(c_1490,plain,
    ( k2_struct_0(k8_tmap_1('#skF_2','#skF_2')) = k2_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_1248,c_91,c_1409])).

tff(c_1491,plain,(
    k2_struct_0(k8_tmap_1('#skF_2','#skF_2')) = k2_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1490])).

tff(c_1522,plain,(
    u1_struct_0(k8_tmap_1('#skF_2','#skF_2')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1491,c_1328])).

tff(c_1635,plain,
    ( g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc(k8_tmap_1('#skF_2','#skF_2'))) = k8_tmap_1('#skF_2','#skF_2')
    | ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_2'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1522,c_6])).

tff(c_1703,plain,
    ( k8_tmap_1('#skF_2','#skF_2') = k8_tmap_1('#skF_2','#skF_3')
    | ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1324,c_97,c_1247,c_1635])).

tff(c_1841,plain,(
    ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1703])).

tff(c_1844,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_1841])).

tff(c_1847,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_1248,c_1844])).

tff(c_1849,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1847])).

tff(c_1850,plain,(
    k8_tmap_1('#skF_2','#skF_2') = k8_tmap_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1703])).

tff(c_1857,plain,(
    u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) = u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1850,c_1247])).

tff(c_1859,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1759,c_1857])).

tff(c_1860,plain,(
    v3_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_269])).

tff(c_20,plain,(
    ! [A_10,B_16] :
      ( ~ v3_pre_topc('#skF_1'(A_10,B_16),A_10)
      | v1_tsep_1(B_16,A_10)
      | ~ m1_pre_topc(B_16,A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1881,plain,
    ( v1_tsep_1('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1860,c_20])).

tff(c_1884,plain,(
    v1_tsep_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_1881])).

tff(c_1886,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_1884])).

tff(c_1888,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k8_tmap_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1899,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k8_tmap_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1898,c_1888])).

tff(c_3526,plain,(
    k8_tmap_1('#skF_2','#skF_2') != k8_tmap_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3467,c_1899])).

tff(c_1887,plain,(
    v1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_2894,plain,(
    ! [A_207,B_208] :
      ( k5_tmap_1(A_207,u1_struct_0(B_208)) = u1_pre_topc(k8_tmap_1(A_207,B_208))
      | v2_struct_0(B_208)
      | ~ v2_pre_topc(A_207)
      | v2_struct_0(A_207)
      | ~ m1_pre_topc(B_208,A_207)
      | ~ l1_pre_topc(A_207) ) ),
    inference(resolution,[status(thm)],[c_40,c_2734])).

tff(c_1922,plain,(
    ! [B_130,A_131] :
      ( m1_subset_1(u1_struct_0(B_130),k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ m1_pre_topc(B_130,A_131)
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1928,plain,(
    ! [B_130] :
      ( m1_subset_1(u1_struct_0(B_130),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_130,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1898,c_1922])).

tff(c_1930,plain,(
    ! [B_130] :
      ( m1_subset_1(u1_struct_0(B_130),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_130,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1928])).

tff(c_2314,plain,(
    ! [B_174,A_175] :
      ( v3_pre_topc(u1_struct_0(B_174),A_175)
      | ~ m1_subset_1(u1_struct_0(B_174),k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ v1_tsep_1(B_174,A_175)
      | ~ m1_pre_topc(B_174,A_175)
      | ~ l1_pre_topc(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2335,plain,(
    ! [B_174] :
      ( v3_pre_topc(u1_struct_0(B_174),'#skF_2')
      | ~ m1_subset_1(u1_struct_0(B_174),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v1_tsep_1(B_174,'#skF_2')
      | ~ m1_pre_topc(B_174,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1898,c_2314])).

tff(c_2356,plain,(
    ! [B_179] :
      ( v3_pre_topc(u1_struct_0(B_179),'#skF_2')
      | ~ m1_subset_1(u1_struct_0(B_179),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v1_tsep_1(B_179,'#skF_2')
      | ~ m1_pre_topc(B_179,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2335])).

tff(c_2369,plain,(
    ! [B_130] :
      ( v3_pre_topc(u1_struct_0(B_130),'#skF_2')
      | ~ v1_tsep_1(B_130,'#skF_2')
      | ~ m1_pre_topc(B_130,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1930,c_2356])).

tff(c_2070,plain,(
    ! [B_156,A_157] :
      ( r2_hidden(B_156,u1_pre_topc(A_157))
      | ~ v3_pre_topc(B_156,A_157)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ l1_pre_topc(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2079,plain,(
    ! [B_156] :
      ( r2_hidden(B_156,u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(B_156,'#skF_2')
      | ~ m1_subset_1(B_156,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1898,c_2070])).

tff(c_2106,plain,(
    ! [B_159] :
      ( r2_hidden(B_159,u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(B_159,'#skF_2')
      | ~ m1_subset_1(B_159,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2079])).

tff(c_2114,plain,(
    ! [B_130] :
      ( r2_hidden(u1_struct_0(B_130),u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(u1_struct_0(B_130),'#skF_2')
      | ~ m1_pre_topc(B_130,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1930,c_2106])).

tff(c_2591,plain,(
    ! [B_198] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_198)) = u1_pre_topc('#skF_2')
      | ~ r2_hidden(u1_struct_0(B_198),u1_pre_topc('#skF_2'))
      | ~ m1_pre_topc(B_198,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1930,c_2571])).

tff(c_2638,plain,(
    ! [B_200] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_200)) = u1_pre_topc('#skF_2')
      | ~ v3_pre_topc(u1_struct_0(B_200),'#skF_2')
      | ~ m1_pre_topc(B_200,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2114,c_2591])).

tff(c_2667,plain,(
    ! [B_130] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_130)) = u1_pre_topc('#skF_2')
      | ~ v1_tsep_1(B_130,'#skF_2')
      | ~ m1_pre_topc(B_130,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2369,c_2638])).

tff(c_2905,plain,(
    ! [B_208] :
      ( u1_pre_topc(k8_tmap_1('#skF_2',B_208)) = u1_pre_topc('#skF_2')
      | ~ v1_tsep_1(B_208,'#skF_2')
      | ~ m1_pre_topc(B_208,'#skF_2')
      | v2_struct_0(B_208)
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_208,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2894,c_2667])).

tff(c_2927,plain,(
    ! [B_208] :
      ( u1_pre_topc(k8_tmap_1('#skF_2',B_208)) = u1_pre_topc('#skF_2')
      | ~ v1_tsep_1(B_208,'#skF_2')
      | v2_struct_0(B_208)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_208,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_2905])).

tff(c_2928,plain,(
    ! [B_208] :
      ( u1_pre_topc(k8_tmap_1('#skF_2',B_208)) = u1_pre_topc('#skF_2')
      | ~ v1_tsep_1(B_208,'#skF_2')
      | v2_struct_0(B_208)
      | ~ m1_pre_topc(B_208,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2927])).

tff(c_2206,plain,(
    ! [A_170,B_171] :
      ( u1_struct_0(k8_tmap_1(A_170,B_171)) = u1_struct_0(A_170)
      | ~ m1_pre_topc(B_171,A_170)
      | v2_struct_0(B_171)
      | ~ l1_pre_topc(A_170)
      | ~ v2_pre_topc(A_170)
      | v2_struct_0(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_4359,plain,(
    ! [A_249,B_250] :
      ( g1_pre_topc(u1_struct_0(A_249),u1_pre_topc(k8_tmap_1(A_249,B_250))) = k8_tmap_1(A_249,B_250)
      | ~ v1_pre_topc(k8_tmap_1(A_249,B_250))
      | ~ l1_pre_topc(k8_tmap_1(A_249,B_250))
      | ~ m1_pre_topc(B_250,A_249)
      | v2_struct_0(B_250)
      | ~ l1_pre_topc(A_249)
      | ~ v2_pre_topc(A_249)
      | v2_struct_0(A_249) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2206,c_6])).

tff(c_4371,plain,(
    ! [B_208] :
      ( k8_tmap_1('#skF_2',B_208) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ v1_pre_topc(k8_tmap_1('#skF_2',B_208))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_208))
      | ~ m1_pre_topc(B_208,'#skF_2')
      | v2_struct_0(B_208)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v1_tsep_1(B_208,'#skF_2')
      | v2_struct_0(B_208)
      | ~ m1_pre_topc(B_208,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2928,c_4359])).

tff(c_4389,plain,(
    ! [B_208] :
      ( k8_tmap_1('#skF_2',B_208) = k8_tmap_1('#skF_2','#skF_2')
      | ~ v1_pre_topc(k8_tmap_1('#skF_2',B_208))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_208))
      | v2_struct_0('#skF_2')
      | ~ v1_tsep_1(B_208,'#skF_2')
      | v2_struct_0(B_208)
      | ~ m1_pre_topc(B_208,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_3467,c_1898,c_4371])).

tff(c_4517,plain,(
    ! [B_255] :
      ( k8_tmap_1('#skF_2',B_255) = k8_tmap_1('#skF_2','#skF_2')
      | ~ v1_pre_topc(k8_tmap_1('#skF_2',B_255))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_255))
      | ~ v1_tsep_1(B_255,'#skF_2')
      | v2_struct_0(B_255)
      | ~ m1_pre_topc(B_255,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_4389])).

tff(c_4524,plain,(
    ! [B_21] :
      ( k8_tmap_1('#skF_2',B_21) = k8_tmap_1('#skF_2','#skF_2')
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_21))
      | ~ v1_tsep_1(B_21,'#skF_2')
      | v2_struct_0(B_21)
      | ~ m1_pre_topc(B_21,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_4517])).

tff(c_4532,plain,(
    ! [B_21] :
      ( k8_tmap_1('#skF_2',B_21) = k8_tmap_1('#skF_2','#skF_2')
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_21))
      | ~ v1_tsep_1(B_21,'#skF_2')
      | v2_struct_0(B_21)
      | ~ m1_pre_topc(B_21,'#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4524])).

tff(c_4540,plain,(
    ! [B_256] :
      ( k8_tmap_1('#skF_2',B_256) = k8_tmap_1('#skF_2','#skF_2')
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_256))
      | ~ v1_tsep_1(B_256,'#skF_2')
      | v2_struct_0(B_256)
      | ~ m1_pre_topc(B_256,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_4532])).

tff(c_4547,plain,(
    ! [B_21] :
      ( k8_tmap_1('#skF_2',B_21) = k8_tmap_1('#skF_2','#skF_2')
      | ~ v1_tsep_1(B_21,'#skF_2')
      | v2_struct_0(B_21)
      | ~ m1_pre_topc(B_21,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_4540])).

tff(c_4555,plain,(
    ! [B_21] :
      ( k8_tmap_1('#skF_2',B_21) = k8_tmap_1('#skF_2','#skF_2')
      | ~ v1_tsep_1(B_21,'#skF_2')
      | v2_struct_0(B_21)
      | ~ m1_pre_topc(B_21,'#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4547])).

tff(c_4614,plain,(
    ! [B_260] :
      ( k8_tmap_1('#skF_2',B_260) = k8_tmap_1('#skF_2','#skF_2')
      | ~ v1_tsep_1(B_260,'#skF_2')
      | v2_struct_0(B_260)
      | ~ m1_pre_topc(B_260,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_4555])).

tff(c_4621,plain,
    ( k8_tmap_1('#skF_2','#skF_2') = k8_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1887,c_4614])).

tff(c_4627,plain,
    ( k8_tmap_1('#skF_2','#skF_2') = k8_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_4621])).

tff(c_4629,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_3526,c_4627])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:27:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.35/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.35/2.06  
% 5.35/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.35/2.06  %$ v3_pre_topc > v1_tsep_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k8_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 5.35/2.06  
% 5.35/2.06  %Foreground sorts:
% 5.35/2.06  
% 5.35/2.06  
% 5.35/2.06  %Background operators:
% 5.35/2.06  
% 5.35/2.06  
% 5.35/2.06  %Foreground operators:
% 5.35/2.06  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.35/2.06  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 5.35/2.06  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.35/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.35/2.06  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 5.35/2.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.35/2.06  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.35/2.06  tff(k8_tmap_1, type, k8_tmap_1: ($i * $i) > $i).
% 5.35/2.06  tff('#skF_2', type, '#skF_2': $i).
% 5.35/2.06  tff('#skF_3', type, '#skF_3': $i).
% 5.35/2.06  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.35/2.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.35/2.06  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.35/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.35/2.06  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 5.35/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.35/2.06  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.35/2.06  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.35/2.06  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 5.35/2.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.35/2.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.35/2.06  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.35/2.06  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.35/2.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.35/2.06  
% 5.79/2.09  tff(f_154, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k8_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_tmap_1)).
% 5.79/2.09  tff(f_134, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.79/2.09  tff(f_58, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 5.79/2.09  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.79/2.09  tff(f_39, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.79/2.09  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.79/2.09  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.79/2.09  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 5.79/2.09  tff(f_101, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 5.79/2.09  tff(f_123, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => ((u1_struct_0(k8_tmap_1(A, B)) = u1_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (u1_pre_topc(k8_tmap_1(A, B)) = k5_tmap_1(A, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_tmap_1)).
% 5.79/2.09  tff(f_87, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_pre_topc(k8_tmap_1(A, B)) & v2_pre_topc(k8_tmap_1(A, B))) & l1_pre_topc(k8_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 5.79/2.09  tff(f_130, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.79/2.09  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 5.79/2.09  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tsep_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tsep_1)).
% 5.79/2.09  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.79/2.09  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.79/2.09  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.79/2.09  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.79/2.09  tff(c_42, plain, (![A_35]: (m1_pre_topc(A_35, A_35) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.79/2.09  tff(c_16, plain, (![A_9]: (v3_pre_topc(k2_struct_0(A_9), A_9) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.79/2.09  tff(c_14, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.79/2.09  tff(c_1889, plain, (![A_126]: (u1_struct_0(A_126)=k2_struct_0(A_126) | ~l1_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.79/2.09  tff(c_1894, plain, (![A_127]: (u1_struct_0(A_127)=k2_struct_0(A_127) | ~l1_pre_topc(A_127))), inference(resolution, [status(thm)], [c_14, c_1889])).
% 5.79/2.09  tff(c_1898, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1894])).
% 5.79/2.09  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.79/2.09  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.79/2.09  tff(c_68, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 5.79/2.09  tff(c_1951, plain, (![B_144, A_145]: (v3_pre_topc(B_144, A_145) | ~r2_hidden(B_144, u1_pre_topc(A_145)) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.79/2.09  tff(c_1970, plain, (![A_146]: (v3_pre_topc(u1_struct_0(A_146), A_146) | ~r2_hidden(u1_struct_0(A_146), u1_pre_topc(A_146)) | ~l1_pre_topc(A_146))), inference(resolution, [status(thm)], [c_68, c_1951])).
% 5.79/2.09  tff(c_1973, plain, (v3_pre_topc(u1_struct_0('#skF_2'), '#skF_2') | ~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1898, c_1970])).
% 5.79/2.09  tff(c_1975, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1898, c_1973])).
% 5.79/2.09  tff(c_1976, plain, (~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), inference(splitLeft, [status(thm)], [c_1975])).
% 5.79/2.09  tff(c_1992, plain, (![B_149, A_150]: (r2_hidden(B_149, u1_pre_topc(A_150)) | ~v3_pre_topc(B_149, A_150) | ~m1_subset_1(B_149, k1_zfmisc_1(u1_struct_0(A_150))) | ~l1_pre_topc(A_150))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.79/2.09  tff(c_2011, plain, (![A_151]: (r2_hidden(u1_struct_0(A_151), u1_pre_topc(A_151)) | ~v3_pre_topc(u1_struct_0(A_151), A_151) | ~l1_pre_topc(A_151))), inference(resolution, [status(thm)], [c_68, c_1992])).
% 5.79/2.09  tff(c_2021, plain, (r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v3_pre_topc(u1_struct_0('#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1898, c_2011])).
% 5.79/2.09  tff(c_2027, plain, (r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1898, c_2021])).
% 5.79/2.09  tff(c_2028, plain, (~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_1976, c_2027])).
% 5.79/2.09  tff(c_2045, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_2028])).
% 5.79/2.09  tff(c_2049, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2045])).
% 5.79/2.09  tff(c_2051, plain, (r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), inference(splitRight, [status(thm)], [c_1975])).
% 5.79/2.09  tff(c_2541, plain, (![A_195, B_196]: (k5_tmap_1(A_195, B_196)=u1_pre_topc(A_195) | ~r2_hidden(B_196, u1_pre_topc(A_195)) | ~m1_subset_1(B_196, k1_zfmisc_1(u1_struct_0(A_195))) | ~l1_pre_topc(A_195) | ~v2_pre_topc(A_195) | v2_struct_0(A_195))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.79/2.09  tff(c_2559, plain, (![B_196]: (k5_tmap_1('#skF_2', B_196)=u1_pre_topc('#skF_2') | ~r2_hidden(B_196, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_196, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1898, c_2541])).
% 5.79/2.09  tff(c_2568, plain, (![B_196]: (k5_tmap_1('#skF_2', B_196)=u1_pre_topc('#skF_2') | ~r2_hidden(B_196, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_196, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2559])).
% 5.79/2.09  tff(c_2571, plain, (![B_197]: (k5_tmap_1('#skF_2', B_197)=u1_pre_topc('#skF_2') | ~r2_hidden(B_197, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_197, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_2568])).
% 5.79/2.09  tff(c_2581, plain, (k5_tmap_1('#skF_2', k2_struct_0('#skF_2'))=u1_pre_topc('#skF_2') | ~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_68, c_2571])).
% 5.79/2.09  tff(c_2586, plain, (k5_tmap_1('#skF_2', k2_struct_0('#skF_2'))=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2051, c_2581])).
% 5.79/2.09  tff(c_2734, plain, (![A_203, B_204]: (k5_tmap_1(A_203, u1_struct_0(B_204))=u1_pre_topc(k8_tmap_1(A_203, B_204)) | ~m1_subset_1(u1_struct_0(B_204), k1_zfmisc_1(u1_struct_0(A_203))) | ~m1_pre_topc(B_204, A_203) | v2_struct_0(B_204) | ~l1_pre_topc(A_203) | ~v2_pre_topc(A_203) | v2_struct_0(A_203))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.79/2.09  tff(c_2805, plain, (![B_206]: (k5_tmap_1(B_206, u1_struct_0(B_206))=u1_pre_topc(k8_tmap_1(B_206, B_206)) | ~m1_pre_topc(B_206, B_206) | ~l1_pre_topc(B_206) | ~v2_pre_topc(B_206) | v2_struct_0(B_206))), inference(resolution, [status(thm)], [c_68, c_2734])).
% 5.79/2.09  tff(c_2828, plain, (k5_tmap_1('#skF_2', k2_struct_0('#skF_2'))=u1_pre_topc(k8_tmap_1('#skF_2', '#skF_2')) | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1898, c_2805])).
% 5.79/2.09  tff(c_2838, plain, (u1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))=u1_pre_topc('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2586, c_2828])).
% 5.79/2.09  tff(c_2839, plain, (u1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))=u1_pre_topc('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_2838])).
% 5.79/2.09  tff(c_2840, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_2839])).
% 5.79/2.09  tff(c_2844, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_2840])).
% 5.79/2.09  tff(c_2848, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_2844])).
% 5.79/2.09  tff(c_2850, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_2839])).
% 5.79/2.09  tff(c_30, plain, (![A_20, B_21]: (v1_pre_topc(k8_tmap_1(A_20, B_21)) | ~m1_pre_topc(B_21, A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.79/2.09  tff(c_26, plain, (![A_20, B_21]: (l1_pre_topc(k8_tmap_1(A_20, B_21)) | ~m1_pre_topc(B_21, A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.79/2.09  tff(c_2849, plain, (u1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))=u1_pre_topc('#skF_2')), inference(splitRight, [status(thm)], [c_2839])).
% 5.79/2.09  tff(c_40, plain, (![B_34, A_32]: (m1_subset_1(u1_struct_0(B_34), k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_pre_topc(B_34, A_32) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.79/2.09  tff(c_2158, plain, (![B_164, A_165]: (v3_pre_topc(u1_struct_0(B_164), A_165) | ~r2_hidden(u1_struct_0(B_164), u1_pre_topc(A_165)) | ~m1_pre_topc(B_164, A_165) | ~l1_pre_topc(A_165))), inference(resolution, [status(thm)], [c_40, c_1951])).
% 5.79/2.09  tff(c_2167, plain, (![A_165]: (v3_pre_topc(u1_struct_0('#skF_2'), A_165) | ~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc(A_165)) | ~m1_pre_topc('#skF_2', A_165) | ~l1_pre_topc(A_165))), inference(superposition, [status(thm), theory('equality')], [c_1898, c_2158])).
% 5.79/2.09  tff(c_2172, plain, (![A_165]: (v3_pre_topc(k2_struct_0('#skF_2'), A_165) | ~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc(A_165)) | ~m1_pre_topc('#skF_2', A_165) | ~l1_pre_topc(A_165))), inference(demodulation, [status(thm), theory('equality')], [c_1898, c_2167])).
% 5.79/2.09  tff(c_2866, plain, (v3_pre_topc(k2_struct_0('#skF_2'), k8_tmap_1('#skF_2', '#skF_2')) | ~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~m1_pre_topc('#skF_2', k8_tmap_1('#skF_2', '#skF_2')) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2849, c_2172])).
% 5.79/2.09  tff(c_2888, plain, (v3_pre_topc(k2_struct_0('#skF_2'), k8_tmap_1('#skF_2', '#skF_2')) | ~m1_pre_topc('#skF_2', k8_tmap_1('#skF_2', '#skF_2')) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2051, c_2866])).
% 5.79/2.09  tff(c_2991, plain, (~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(splitLeft, [status(thm)], [c_2888])).
% 5.79/2.09  tff(c_3015, plain, (~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_2991])).
% 5.79/2.09  tff(c_3018, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2850, c_3015])).
% 5.79/2.09  tff(c_3020, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_3018])).
% 5.79/2.09  tff(c_3022, plain, (l1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(splitRight, [status(thm)], [c_2888])).
% 5.79/2.09  tff(c_1893, plain, (![A_8]: (u1_struct_0(A_8)=k2_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(resolution, [status(thm)], [c_14, c_1889])).
% 5.79/2.09  tff(c_3026, plain, (u1_struct_0(k8_tmap_1('#skF_2', '#skF_2'))=k2_struct_0(k8_tmap_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_3022, c_1893])).
% 5.79/2.09  tff(c_38, plain, (![A_25, B_29]: (u1_struct_0(k8_tmap_1(A_25, B_29))=u1_struct_0(A_25) | ~m1_pre_topc(B_29, A_25) | v2_struct_0(B_29) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.79/2.09  tff(c_3078, plain, (k2_struct_0(k8_tmap_1('#skF_2', '#skF_2'))=u1_struct_0('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3026, c_38])).
% 5.79/2.09  tff(c_3152, plain, (k2_struct_0(k8_tmap_1('#skF_2', '#skF_2'))=k2_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2850, c_1898, c_3078])).
% 5.79/2.09  tff(c_3153, plain, (k2_struct_0(k8_tmap_1('#skF_2', '#skF_2'))=k2_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_3152])).
% 5.79/2.09  tff(c_3182, plain, (u1_struct_0(k8_tmap_1('#skF_2', '#skF_2'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3153, c_3026])).
% 5.79/2.09  tff(c_6, plain, (![A_3]: (g1_pre_topc(u1_struct_0(A_3), u1_pre_topc(A_3))=A_3 | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.79/2.09  tff(c_3334, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc(k8_tmap_1('#skF_2', '#skF_2')))=k8_tmap_1('#skF_2', '#skF_2') | ~v1_pre_topc(k8_tmap_1('#skF_2', '#skF_2')) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3182, c_6])).
% 5.79/2.09  tff(c_3396, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k8_tmap_1('#skF_2', '#skF_2') | ~v1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3022, c_2849, c_3334])).
% 5.79/2.09  tff(c_3458, plain, (~v1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(splitLeft, [status(thm)], [c_3396])).
% 5.79/2.09  tff(c_3461, plain, (~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_3458])).
% 5.79/2.09  tff(c_3464, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2850, c_3461])).
% 5.79/2.09  tff(c_3466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_3464])).
% 5.79/2.09  tff(c_3467, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k8_tmap_1('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_3396])).
% 5.79/2.09  tff(c_82, plain, (![A_41]: (u1_struct_0(A_41)=k2_struct_0(A_41) | ~l1_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.79/2.09  tff(c_87, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_pre_topc(A_42))), inference(resolution, [status(thm)], [c_14, c_82])).
% 5.79/2.09  tff(c_91, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_87])).
% 5.79/2.09  tff(c_64, plain, (v1_tsep_1('#skF_3', '#skF_2') | g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.79/2.09  tff(c_81, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_64])).
% 5.79/2.09  tff(c_97, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_81])).
% 5.79/2.09  tff(c_44, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.79/2.09  tff(c_54, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~v1_tsep_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.79/2.09  tff(c_67, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3') | ~v1_tsep_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_54])).
% 5.79/2.09  tff(c_118, plain, (~v1_tsep_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_91, c_67])).
% 5.79/2.09  tff(c_139, plain, (![B_49, A_50]: (u1_struct_0(B_49)='#skF_1'(A_50, B_49) | v1_tsep_1(B_49, A_50) | ~m1_pre_topc(B_49, A_50) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.79/2.09  tff(c_142, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_139, c_118])).
% 5.79/2.09  tff(c_145, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_142])).
% 5.79/2.09  tff(c_119, plain, (![B_45, A_46]: (m1_subset_1(u1_struct_0(B_45), k1_zfmisc_1(u1_struct_0(A_46))) | ~m1_pre_topc(B_45, A_46) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.79/2.09  tff(c_125, plain, (![B_45]: (m1_subset_1(u1_struct_0(B_45), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_45, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_91, c_119])).
% 5.79/2.09  tff(c_127, plain, (![B_45]: (m1_subset_1(u1_struct_0(B_45), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_45, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_125])).
% 5.79/2.09  tff(c_152, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_145, c_127])).
% 5.79/2.09  tff(c_165, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_152])).
% 5.79/2.09  tff(c_1114, plain, (![A_114, B_115]: (k5_tmap_1(A_114, u1_struct_0(B_115))=u1_pre_topc(k8_tmap_1(A_114, B_115)) | ~m1_subset_1(u1_struct_0(B_115), k1_zfmisc_1(u1_struct_0(A_114))) | ~m1_pre_topc(B_115, A_114) | v2_struct_0(B_115) | ~l1_pre_topc(A_114) | ~v2_pre_topc(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.79/2.09  tff(c_1141, plain, (![B_115]: (k5_tmap_1('#skF_2', u1_struct_0(B_115))=u1_pre_topc(k8_tmap_1('#skF_2', B_115)) | ~m1_subset_1(u1_struct_0(B_115), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_115, '#skF_2') | v2_struct_0(B_115) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_91, c_1114])).
% 5.79/2.09  tff(c_1153, plain, (![B_115]: (k5_tmap_1('#skF_2', u1_struct_0(B_115))=u1_pre_topc(k8_tmap_1('#skF_2', B_115)) | ~m1_subset_1(u1_struct_0(B_115), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_115, '#skF_2') | v2_struct_0(B_115) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1141])).
% 5.79/2.09  tff(c_1329, plain, (![B_120]: (k5_tmap_1('#skF_2', u1_struct_0(B_120))=u1_pre_topc(k8_tmap_1('#skF_2', B_120)) | ~m1_subset_1(u1_struct_0(B_120), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_120, '#skF_2') | v2_struct_0(B_120))), inference(negUnitSimplification, [status(thm)], [c_52, c_1153])).
% 5.79/2.09  tff(c_1338, plain, (k5_tmap_1('#skF_2', u1_struct_0('#skF_3'))=u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_145, c_1329])).
% 5.79/2.09  tff(c_1346, plain, (k5_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))=u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_165, c_145, c_1338])).
% 5.79/2.09  tff(c_1347, plain, (k5_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))=u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_1346])).
% 5.79/2.09  tff(c_212, plain, (![B_62, A_63]: (v3_pre_topc(B_62, A_63) | ~r2_hidden(B_62, u1_pre_topc(A_63)) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.79/2.09  tff(c_227, plain, (![B_62]: (v3_pre_topc(B_62, '#skF_2') | ~r2_hidden(B_62, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_62, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_91, c_212])).
% 5.79/2.09  tff(c_258, plain, (![B_65]: (v3_pre_topc(B_65, '#skF_2') | ~r2_hidden(B_65, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_65, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_227])).
% 5.79/2.09  tff(c_269, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~r2_hidden('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_165, c_258])).
% 5.79/2.09  tff(c_288, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_2'))), inference(splitLeft, [status(thm)], [c_269])).
% 5.79/2.09  tff(c_693, plain, (![B_97, A_98]: (r2_hidden(B_97, u1_pre_topc(A_98)) | k5_tmap_1(A_98, B_97)!=u1_pre_topc(A_98) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98) | ~v2_pre_topc(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.79/2.09  tff(c_717, plain, (![B_97]: (r2_hidden(B_97, u1_pre_topc('#skF_2')) | k5_tmap_1('#skF_2', B_97)!=u1_pre_topc('#skF_2') | ~m1_subset_1(B_97, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_91, c_693])).
% 5.79/2.09  tff(c_728, plain, (![B_97]: (r2_hidden(B_97, u1_pre_topc('#skF_2')) | k5_tmap_1('#skF_2', B_97)!=u1_pre_topc('#skF_2') | ~m1_subset_1(B_97, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_717])).
% 5.79/2.09  tff(c_731, plain, (![B_99]: (r2_hidden(B_99, u1_pre_topc('#skF_2')) | k5_tmap_1('#skF_2', B_99)!=u1_pre_topc('#skF_2') | ~m1_subset_1(B_99, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_728])).
% 5.79/2.09  tff(c_737, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_2')) | k5_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))!=u1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_165, c_731])).
% 5.79/2.09  tff(c_748, plain, (k5_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))!=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_288, c_737])).
% 5.79/2.09  tff(c_1759, plain, (u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))!=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1347, c_748])).
% 5.79/2.09  tff(c_186, plain, (![B_60, A_61]: (r2_hidden(B_60, u1_pre_topc(A_61)) | ~v3_pre_topc(B_60, A_61) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.79/2.09  tff(c_238, plain, (![A_64]: (r2_hidden(u1_struct_0(A_64), u1_pre_topc(A_64)) | ~v3_pre_topc(u1_struct_0(A_64), A_64) | ~l1_pre_topc(A_64))), inference(resolution, [status(thm)], [c_68, c_186])).
% 5.79/2.09  tff(c_244, plain, (r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v3_pre_topc(u1_struct_0('#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_91, c_238])).
% 5.79/2.09  tff(c_247, plain, (r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_91, c_244])).
% 5.79/2.09  tff(c_248, plain, (~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_247])).
% 5.79/2.09  tff(c_251, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_248])).
% 5.79/2.09  tff(c_255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_251])).
% 5.79/2.09  tff(c_256, plain, (r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), inference(splitRight, [status(thm)], [c_247])).
% 5.79/2.09  tff(c_889, plain, (![A_106, B_107]: (k5_tmap_1(A_106, B_107)=u1_pre_topc(A_106) | ~r2_hidden(B_107, u1_pre_topc(A_106)) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.79/2.09  tff(c_913, plain, (![B_107]: (k5_tmap_1('#skF_2', B_107)=u1_pre_topc('#skF_2') | ~r2_hidden(B_107, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_107, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_91, c_889])).
% 5.79/2.09  tff(c_924, plain, (![B_107]: (k5_tmap_1('#skF_2', B_107)=u1_pre_topc('#skF_2') | ~r2_hidden(B_107, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_107, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_913])).
% 5.79/2.09  tff(c_928, plain, (![B_109]: (k5_tmap_1('#skF_2', B_109)=u1_pre_topc('#skF_2') | ~r2_hidden(B_109, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_109, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_924])).
% 5.79/2.09  tff(c_941, plain, (k5_tmap_1('#skF_2', k2_struct_0('#skF_2'))=u1_pre_topc('#skF_2') | ~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_68, c_928])).
% 5.79/2.09  tff(c_948, plain, (k5_tmap_1('#skF_2', k2_struct_0('#skF_2'))=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_256, c_941])).
% 5.79/2.09  tff(c_1199, plain, (![B_117]: (k5_tmap_1(B_117, u1_struct_0(B_117))=u1_pre_topc(k8_tmap_1(B_117, B_117)) | ~m1_pre_topc(B_117, B_117) | ~l1_pre_topc(B_117) | ~v2_pre_topc(B_117) | v2_struct_0(B_117))), inference(resolution, [status(thm)], [c_68, c_1114])).
% 5.79/2.09  tff(c_1225, plain, (k5_tmap_1('#skF_2', k2_struct_0('#skF_2'))=u1_pre_topc(k8_tmap_1('#skF_2', '#skF_2')) | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_91, c_1199])).
% 5.79/2.09  tff(c_1236, plain, (u1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))=u1_pre_topc('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_948, c_1225])).
% 5.79/2.09  tff(c_1237, plain, (u1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))=u1_pre_topc('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_1236])).
% 5.79/2.09  tff(c_1238, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_1237])).
% 5.79/2.09  tff(c_1242, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_1238])).
% 5.79/2.09  tff(c_1246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1242])).
% 5.79/2.09  tff(c_1248, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_1237])).
% 5.79/2.09  tff(c_1247, plain, (u1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))=u1_pre_topc('#skF_2')), inference(splitRight, [status(thm)], [c_1237])).
% 5.79/2.09  tff(c_375, plain, (![B_73, A_74]: (v3_pre_topc(u1_struct_0(B_73), A_74) | ~r2_hidden(u1_struct_0(B_73), u1_pre_topc(A_74)) | ~m1_pre_topc(B_73, A_74) | ~l1_pre_topc(A_74))), inference(resolution, [status(thm)], [c_40, c_212])).
% 5.79/2.09  tff(c_387, plain, (![A_74]: (v3_pre_topc(u1_struct_0('#skF_2'), A_74) | ~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc(A_74)) | ~m1_pre_topc('#skF_2', A_74) | ~l1_pre_topc(A_74))), inference(superposition, [status(thm), theory('equality')], [c_91, c_375])).
% 5.79/2.09  tff(c_393, plain, (![A_74]: (v3_pre_topc(k2_struct_0('#skF_2'), A_74) | ~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc(A_74)) | ~m1_pre_topc('#skF_2', A_74) | ~l1_pre_topc(A_74))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_387])).
% 5.79/2.09  tff(c_1267, plain, (v3_pre_topc(k2_struct_0('#skF_2'), k8_tmap_1('#skF_2', '#skF_2')) | ~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~m1_pre_topc('#skF_2', k8_tmap_1('#skF_2', '#skF_2')) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1247, c_393])).
% 5.79/2.09  tff(c_1290, plain, (v3_pre_topc(k2_struct_0('#skF_2'), k8_tmap_1('#skF_2', '#skF_2')) | ~m1_pre_topc('#skF_2', k8_tmap_1('#skF_2', '#skF_2')) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_256, c_1267])).
% 5.79/2.09  tff(c_1314, plain, (~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1290])).
% 5.79/2.09  tff(c_1317, plain, (~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_1314])).
% 5.79/2.09  tff(c_1320, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1248, c_1317])).
% 5.79/2.09  tff(c_1322, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1320])).
% 5.79/2.09  tff(c_1324, plain, (l1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(splitRight, [status(thm)], [c_1290])).
% 5.79/2.09  tff(c_86, plain, (![A_8]: (u1_struct_0(A_8)=k2_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(resolution, [status(thm)], [c_14, c_82])).
% 5.79/2.09  tff(c_1328, plain, (u1_struct_0(k8_tmap_1('#skF_2', '#skF_2'))=k2_struct_0(k8_tmap_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_1324, c_86])).
% 5.79/2.09  tff(c_1409, plain, (k2_struct_0(k8_tmap_1('#skF_2', '#skF_2'))=u1_struct_0('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1328, c_38])).
% 5.79/2.09  tff(c_1490, plain, (k2_struct_0(k8_tmap_1('#skF_2', '#skF_2'))=k2_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1248, c_91, c_1409])).
% 5.79/2.09  tff(c_1491, plain, (k2_struct_0(k8_tmap_1('#skF_2', '#skF_2'))=k2_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_1490])).
% 5.79/2.09  tff(c_1522, plain, (u1_struct_0(k8_tmap_1('#skF_2', '#skF_2'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1491, c_1328])).
% 5.79/2.09  tff(c_1635, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc(k8_tmap_1('#skF_2', '#skF_2')))=k8_tmap_1('#skF_2', '#skF_2') | ~v1_pre_topc(k8_tmap_1('#skF_2', '#skF_2')) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1522, c_6])).
% 5.79/2.09  tff(c_1703, plain, (k8_tmap_1('#skF_2', '#skF_2')=k8_tmap_1('#skF_2', '#skF_3') | ~v1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1324, c_97, c_1247, c_1635])).
% 5.79/2.09  tff(c_1841, plain, (~v1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1703])).
% 5.79/2.09  tff(c_1844, plain, (~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_1841])).
% 5.79/2.09  tff(c_1847, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1248, c_1844])).
% 5.79/2.09  tff(c_1849, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1847])).
% 5.79/2.09  tff(c_1850, plain, (k8_tmap_1('#skF_2', '#skF_2')=k8_tmap_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_1703])).
% 5.79/2.09  tff(c_1857, plain, (u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1850, c_1247])).
% 5.79/2.09  tff(c_1859, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1759, c_1857])).
% 5.79/2.09  tff(c_1860, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_269])).
% 5.79/2.09  tff(c_20, plain, (![A_10, B_16]: (~v3_pre_topc('#skF_1'(A_10, B_16), A_10) | v1_tsep_1(B_16, A_10) | ~m1_pre_topc(B_16, A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.79/2.09  tff(c_1881, plain, (v1_tsep_1('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1860, c_20])).
% 5.79/2.09  tff(c_1884, plain, (v1_tsep_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_1881])).
% 5.79/2.09  tff(c_1886, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_1884])).
% 5.79/2.09  tff(c_1888, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_64])).
% 5.79/2.09  tff(c_1899, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1898, c_1888])).
% 5.79/2.09  tff(c_3526, plain, (k8_tmap_1('#skF_2', '#skF_2')!=k8_tmap_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3467, c_1899])).
% 5.79/2.09  tff(c_1887, plain, (v1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_64])).
% 5.79/2.09  tff(c_2894, plain, (![A_207, B_208]: (k5_tmap_1(A_207, u1_struct_0(B_208))=u1_pre_topc(k8_tmap_1(A_207, B_208)) | v2_struct_0(B_208) | ~v2_pre_topc(A_207) | v2_struct_0(A_207) | ~m1_pre_topc(B_208, A_207) | ~l1_pre_topc(A_207))), inference(resolution, [status(thm)], [c_40, c_2734])).
% 5.79/2.09  tff(c_1922, plain, (![B_130, A_131]: (m1_subset_1(u1_struct_0(B_130), k1_zfmisc_1(u1_struct_0(A_131))) | ~m1_pre_topc(B_130, A_131) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.79/2.09  tff(c_1928, plain, (![B_130]: (m1_subset_1(u1_struct_0(B_130), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_130, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1898, c_1922])).
% 5.79/2.09  tff(c_1930, plain, (![B_130]: (m1_subset_1(u1_struct_0(B_130), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_130, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1928])).
% 5.79/2.09  tff(c_2314, plain, (![B_174, A_175]: (v3_pre_topc(u1_struct_0(B_174), A_175) | ~m1_subset_1(u1_struct_0(B_174), k1_zfmisc_1(u1_struct_0(A_175))) | ~v1_tsep_1(B_174, A_175) | ~m1_pre_topc(B_174, A_175) | ~l1_pre_topc(A_175))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.79/2.09  tff(c_2335, plain, (![B_174]: (v3_pre_topc(u1_struct_0(B_174), '#skF_2') | ~m1_subset_1(u1_struct_0(B_174), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v1_tsep_1(B_174, '#skF_2') | ~m1_pre_topc(B_174, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1898, c_2314])).
% 5.79/2.09  tff(c_2356, plain, (![B_179]: (v3_pre_topc(u1_struct_0(B_179), '#skF_2') | ~m1_subset_1(u1_struct_0(B_179), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v1_tsep_1(B_179, '#skF_2') | ~m1_pre_topc(B_179, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2335])).
% 5.79/2.09  tff(c_2369, plain, (![B_130]: (v3_pre_topc(u1_struct_0(B_130), '#skF_2') | ~v1_tsep_1(B_130, '#skF_2') | ~m1_pre_topc(B_130, '#skF_2'))), inference(resolution, [status(thm)], [c_1930, c_2356])).
% 5.79/2.09  tff(c_2070, plain, (![B_156, A_157]: (r2_hidden(B_156, u1_pre_topc(A_157)) | ~v3_pre_topc(B_156, A_157) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0(A_157))) | ~l1_pre_topc(A_157))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.79/2.09  tff(c_2079, plain, (![B_156]: (r2_hidden(B_156, u1_pre_topc('#skF_2')) | ~v3_pre_topc(B_156, '#skF_2') | ~m1_subset_1(B_156, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1898, c_2070])).
% 5.79/2.09  tff(c_2106, plain, (![B_159]: (r2_hidden(B_159, u1_pre_topc('#skF_2')) | ~v3_pre_topc(B_159, '#skF_2') | ~m1_subset_1(B_159, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2079])).
% 5.79/2.09  tff(c_2114, plain, (![B_130]: (r2_hidden(u1_struct_0(B_130), u1_pre_topc('#skF_2')) | ~v3_pre_topc(u1_struct_0(B_130), '#skF_2') | ~m1_pre_topc(B_130, '#skF_2'))), inference(resolution, [status(thm)], [c_1930, c_2106])).
% 5.79/2.09  tff(c_2591, plain, (![B_198]: (k5_tmap_1('#skF_2', u1_struct_0(B_198))=u1_pre_topc('#skF_2') | ~r2_hidden(u1_struct_0(B_198), u1_pre_topc('#skF_2')) | ~m1_pre_topc(B_198, '#skF_2'))), inference(resolution, [status(thm)], [c_1930, c_2571])).
% 5.79/2.09  tff(c_2638, plain, (![B_200]: (k5_tmap_1('#skF_2', u1_struct_0(B_200))=u1_pre_topc('#skF_2') | ~v3_pre_topc(u1_struct_0(B_200), '#skF_2') | ~m1_pre_topc(B_200, '#skF_2'))), inference(resolution, [status(thm)], [c_2114, c_2591])).
% 5.79/2.09  tff(c_2667, plain, (![B_130]: (k5_tmap_1('#skF_2', u1_struct_0(B_130))=u1_pre_topc('#skF_2') | ~v1_tsep_1(B_130, '#skF_2') | ~m1_pre_topc(B_130, '#skF_2'))), inference(resolution, [status(thm)], [c_2369, c_2638])).
% 5.79/2.09  tff(c_2905, plain, (![B_208]: (u1_pre_topc(k8_tmap_1('#skF_2', B_208))=u1_pre_topc('#skF_2') | ~v1_tsep_1(B_208, '#skF_2') | ~m1_pre_topc(B_208, '#skF_2') | v2_struct_0(B_208) | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_208, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2894, c_2667])).
% 5.79/2.09  tff(c_2927, plain, (![B_208]: (u1_pre_topc(k8_tmap_1('#skF_2', B_208))=u1_pre_topc('#skF_2') | ~v1_tsep_1(B_208, '#skF_2') | v2_struct_0(B_208) | v2_struct_0('#skF_2') | ~m1_pre_topc(B_208, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_2905])).
% 5.79/2.09  tff(c_2928, plain, (![B_208]: (u1_pre_topc(k8_tmap_1('#skF_2', B_208))=u1_pre_topc('#skF_2') | ~v1_tsep_1(B_208, '#skF_2') | v2_struct_0(B_208) | ~m1_pre_topc(B_208, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_2927])).
% 5.79/2.09  tff(c_2206, plain, (![A_170, B_171]: (u1_struct_0(k8_tmap_1(A_170, B_171))=u1_struct_0(A_170) | ~m1_pre_topc(B_171, A_170) | v2_struct_0(B_171) | ~l1_pre_topc(A_170) | ~v2_pre_topc(A_170) | v2_struct_0(A_170))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.79/2.09  tff(c_4359, plain, (![A_249, B_250]: (g1_pre_topc(u1_struct_0(A_249), u1_pre_topc(k8_tmap_1(A_249, B_250)))=k8_tmap_1(A_249, B_250) | ~v1_pre_topc(k8_tmap_1(A_249, B_250)) | ~l1_pre_topc(k8_tmap_1(A_249, B_250)) | ~m1_pre_topc(B_250, A_249) | v2_struct_0(B_250) | ~l1_pre_topc(A_249) | ~v2_pre_topc(A_249) | v2_struct_0(A_249))), inference(superposition, [status(thm), theory('equality')], [c_2206, c_6])).
% 5.79/2.09  tff(c_4371, plain, (![B_208]: (k8_tmap_1('#skF_2', B_208)=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v1_pre_topc(k8_tmap_1('#skF_2', B_208)) | ~l1_pre_topc(k8_tmap_1('#skF_2', B_208)) | ~m1_pre_topc(B_208, '#skF_2') | v2_struct_0(B_208) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~v1_tsep_1(B_208, '#skF_2') | v2_struct_0(B_208) | ~m1_pre_topc(B_208, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2928, c_4359])).
% 5.79/2.09  tff(c_4389, plain, (![B_208]: (k8_tmap_1('#skF_2', B_208)=k8_tmap_1('#skF_2', '#skF_2') | ~v1_pre_topc(k8_tmap_1('#skF_2', B_208)) | ~l1_pre_topc(k8_tmap_1('#skF_2', B_208)) | v2_struct_0('#skF_2') | ~v1_tsep_1(B_208, '#skF_2') | v2_struct_0(B_208) | ~m1_pre_topc(B_208, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_3467, c_1898, c_4371])).
% 5.79/2.09  tff(c_4517, plain, (![B_255]: (k8_tmap_1('#skF_2', B_255)=k8_tmap_1('#skF_2', '#skF_2') | ~v1_pre_topc(k8_tmap_1('#skF_2', B_255)) | ~l1_pre_topc(k8_tmap_1('#skF_2', B_255)) | ~v1_tsep_1(B_255, '#skF_2') | v2_struct_0(B_255) | ~m1_pre_topc(B_255, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_4389])).
% 5.79/2.09  tff(c_4524, plain, (![B_21]: (k8_tmap_1('#skF_2', B_21)=k8_tmap_1('#skF_2', '#skF_2') | ~l1_pre_topc(k8_tmap_1('#skF_2', B_21)) | ~v1_tsep_1(B_21, '#skF_2') | v2_struct_0(B_21) | ~m1_pre_topc(B_21, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_4517])).
% 5.79/2.09  tff(c_4532, plain, (![B_21]: (k8_tmap_1('#skF_2', B_21)=k8_tmap_1('#skF_2', '#skF_2') | ~l1_pre_topc(k8_tmap_1('#skF_2', B_21)) | ~v1_tsep_1(B_21, '#skF_2') | v2_struct_0(B_21) | ~m1_pre_topc(B_21, '#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4524])).
% 5.79/2.09  tff(c_4540, plain, (![B_256]: (k8_tmap_1('#skF_2', B_256)=k8_tmap_1('#skF_2', '#skF_2') | ~l1_pre_topc(k8_tmap_1('#skF_2', B_256)) | ~v1_tsep_1(B_256, '#skF_2') | v2_struct_0(B_256) | ~m1_pre_topc(B_256, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_4532])).
% 5.79/2.09  tff(c_4547, plain, (![B_21]: (k8_tmap_1('#skF_2', B_21)=k8_tmap_1('#skF_2', '#skF_2') | ~v1_tsep_1(B_21, '#skF_2') | v2_struct_0(B_21) | ~m1_pre_topc(B_21, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_4540])).
% 5.79/2.09  tff(c_4555, plain, (![B_21]: (k8_tmap_1('#skF_2', B_21)=k8_tmap_1('#skF_2', '#skF_2') | ~v1_tsep_1(B_21, '#skF_2') | v2_struct_0(B_21) | ~m1_pre_topc(B_21, '#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4547])).
% 5.79/2.09  tff(c_4614, plain, (![B_260]: (k8_tmap_1('#skF_2', B_260)=k8_tmap_1('#skF_2', '#skF_2') | ~v1_tsep_1(B_260, '#skF_2') | v2_struct_0(B_260) | ~m1_pre_topc(B_260, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_4555])).
% 5.79/2.09  tff(c_4621, plain, (k8_tmap_1('#skF_2', '#skF_2')=k8_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1887, c_4614])).
% 5.79/2.09  tff(c_4627, plain, (k8_tmap_1('#skF_2', '#skF_2')=k8_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_4621])).
% 5.79/2.09  tff(c_4629, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_3526, c_4627])).
% 5.79/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.79/2.09  
% 5.79/2.09  Inference rules
% 5.79/2.09  ----------------------
% 5.79/2.09  #Ref     : 0
% 5.79/2.09  #Sup     : 966
% 5.79/2.09  #Fact    : 0
% 5.79/2.09  #Define  : 0
% 5.79/2.09  #Split   : 19
% 5.79/2.09  #Chain   : 0
% 5.79/2.09  #Close   : 0
% 5.79/2.09  
% 5.79/2.09  Ordering : KBO
% 5.79/2.09  
% 5.79/2.09  Simplification rules
% 5.79/2.09  ----------------------
% 5.79/2.09  #Subsume      : 125
% 5.79/2.09  #Demod        : 1101
% 5.79/2.09  #Tautology    : 342
% 5.79/2.09  #SimpNegUnit  : 153
% 5.79/2.09  #BackRed      : 11
% 5.79/2.09  
% 5.79/2.09  #Partial instantiations: 0
% 5.79/2.09  #Strategies tried      : 1
% 5.79/2.09  
% 5.79/2.09  Timing (in seconds)
% 5.79/2.09  ----------------------
% 5.79/2.09  Preprocessing        : 0.35
% 5.79/2.09  Parsing              : 0.19
% 5.79/2.09  CNF conversion       : 0.02
% 5.79/2.09  Main loop            : 0.93
% 5.79/2.09  Inferencing          : 0.33
% 5.79/2.09  Reduction            : 0.31
% 5.79/2.09  Demodulation         : 0.21
% 5.79/2.09  BG Simplification    : 0.04
% 5.79/2.09  Subsumption          : 0.19
% 5.79/2.09  Abstraction          : 0.05
% 5.79/2.09  MUC search           : 0.00
% 5.79/2.09  Cooper               : 0.00
% 5.79/2.09  Total                : 1.35
% 5.79/2.09  Index Insertion      : 0.00
% 5.79/2.09  Index Deletion       : 0.00
% 5.79/2.09  Index Matching       : 0.00
% 5.79/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
