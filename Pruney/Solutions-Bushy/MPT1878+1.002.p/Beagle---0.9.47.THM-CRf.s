%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1878+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:36 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 4.20s
% Verified   : 
% Statistics : Number of formulae       :  142 (1393 expanded)
%              Number of leaves         :   34 ( 454 expanded)
%              Depth                    :   21
%              Number of atoms          :  296 (3460 expanded)
%              Number of equality atoms :   36 ( 572 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_77,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_68,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_42,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_38,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_16,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_20,plain,(
    ! [A_14] : m1_subset_1('#skF_2'(A_14),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_104,plain,(
    ! [A_41,B_42] :
      ( k6_domain_1(A_41,B_42) = k1_tarski(B_42)
      | ~ m1_subset_1(B_42,A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_116,plain,(
    ! [A_14] :
      ( k6_domain_1(A_14,'#skF_2'(A_14)) = k1_tarski('#skF_2'(A_14))
      | v1_xboole_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_20,c_104])).

tff(c_126,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1(k6_domain_1(A_44,B_45),k1_zfmisc_1(A_44))
      | ~ m1_subset_1(B_45,A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_135,plain,(
    ! [A_14] :
      ( m1_subset_1(k1_tarski('#skF_2'(A_14)),k1_zfmisc_1(A_14))
      | ~ m1_subset_1('#skF_2'(A_14),A_14)
      | v1_xboole_0(A_14)
      | v1_xboole_0(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_126])).

tff(c_162,plain,(
    ! [A_48] :
      ( m1_subset_1(k1_tarski('#skF_2'(A_48)),k1_zfmisc_1(A_48))
      | v1_xboole_0(A_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_135])).

tff(c_32,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ m1_subset_1(A_24,k1_zfmisc_1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_175,plain,(
    ! [A_48] :
      ( r1_tarski(k1_tarski('#skF_2'(A_48)),A_48)
      | v1_xboole_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_162,c_32])).

tff(c_34,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,k1_zfmisc_1(B_25))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_115,plain,
    ( k6_domain_1(k1_zfmisc_1(u1_struct_0('#skF_3')),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_40,c_104])).

tff(c_177,plain,(
    v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_53,plain,(
    ! [A_32] :
      ( k1_xboole_0 = A_32
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_61,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_53])).

tff(c_36,plain,(
    ! [A_26] :
      ( k1_xboole_0 = A_26
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_68,plain,(
    ! [A_26] :
      ( A_26 = '#skF_4'
      | ~ v1_xboole_0(A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_36])).

tff(c_181,plain,(
    k1_zfmisc_1(u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_177,c_68])).

tff(c_139,plain,(
    ! [A_14] :
      ( m1_subset_1(k1_tarski('#skF_2'(A_14)),k1_zfmisc_1(A_14))
      | v1_xboole_0(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_135])).

tff(c_188,plain,
    ( m1_subset_1(k1_tarski('#skF_2'(u1_struct_0('#skF_3'))),'#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_139])).

tff(c_256,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_22,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(u1_struct_0(A_16))
      | ~ l1_struct_0(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_260,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_256,c_22])).

tff(c_266,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_260])).

tff(c_270,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_266])).

tff(c_274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_270])).

tff(c_276,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_275,plain,(
    m1_subset_1(k1_tarski('#skF_2'(u1_struct_0('#skF_3'))),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_215,plain,(
    ! [A_51,B_52] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_51),B_52),A_51)
      | ~ m1_subset_1(B_52,u1_struct_0(A_51))
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_219,plain,(
    ! [A_51] :
      ( v2_tex_2(k1_tarski('#skF_2'(u1_struct_0(A_51))),A_51)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_51)),u1_struct_0(A_51))
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51)
      | v1_xboole_0(u1_struct_0(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_215])).

tff(c_221,plain,(
    ! [A_51] :
      ( v2_tex_2(k1_tarski('#skF_2'(u1_struct_0(A_51))),A_51)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51)
      | v1_xboole_0(u1_struct_0(A_51)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_219])).

tff(c_183,plain,(
    m1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_40])).

tff(c_28,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,A_20) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_69,plain,(
    ! [A_20] : r1_tarski('#skF_4',A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_28])).

tff(c_754,plain,(
    ! [C_90,B_91,A_92] :
      ( C_90 = B_91
      | ~ r1_tarski(B_91,C_90)
      | ~ v2_tex_2(C_90,A_92)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ v3_tex_2(B_91,A_92)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_944,plain,(
    ! [A_108,A_109] :
      ( A_108 = '#skF_4'
      | ~ v2_tex_2(A_108,A_109)
      | ~ m1_subset_1(A_108,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ v3_tex_2('#skF_4',A_109)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(resolution,[status(thm)],[c_69,c_754])).

tff(c_948,plain,(
    ! [A_108] :
      ( A_108 = '#skF_4'
      | ~ v2_tex_2(A_108,'#skF_3')
      | ~ m1_subset_1(A_108,'#skF_4')
      | ~ v3_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_944])).

tff(c_968,plain,(
    ! [A_110] :
      ( A_110 = '#skF_4'
      | ~ v2_tex_2(A_110,'#skF_3')
      | ~ m1_subset_1(A_110,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_183,c_181,c_38,c_948])).

tff(c_980,plain,
    ( k1_tarski('#skF_2'(u1_struct_0('#skF_3'))) = '#skF_4'
    | ~ m1_subset_1(k1_tarski('#skF_2'(u1_struct_0('#skF_3'))),'#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_221,c_968])).

tff(c_1000,plain,
    ( k1_tarski('#skF_2'(u1_struct_0('#skF_3'))) = '#skF_4'
    | v2_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_275,c_980])).

tff(c_1001,plain,(
    k1_tarski('#skF_2'(u1_struct_0('#skF_3'))) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_276,c_48,c_1000])).

tff(c_24,plain,(
    ! [A_17] : ~ v1_xboole_0(k1_tarski(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1045,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1001,c_24])).

tff(c_1066,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1045])).

tff(c_1068,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_1067,plain,(
    k6_domain_1(k1_zfmisc_1(u1_struct_0('#skF_3')),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k6_domain_1(A_11,B_12),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1072,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1067,c_14])).

tff(c_1076,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1072])).

tff(c_1077,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(negUnitSimplification,[status(thm)],[c_1068,c_1076])).

tff(c_26,plain,(
    ! [A_18,B_19] :
      ( k6_domain_1(A_18,B_19) = k1_tarski(B_19)
      | ~ m1_subset_1(B_19,A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1085,plain,
    ( k6_domain_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))),k1_tarski('#skF_4')) = k1_tarski(k1_tarski('#skF_4'))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_1077,c_26])).

tff(c_1362,plain,(
    v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_1085])).

tff(c_1366,plain,(
    k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1362,c_68])).

tff(c_1134,plain,(
    ! [B_118,A_119] :
      ( k6_domain_1(k1_zfmisc_1(B_118),A_119) = k1_tarski(A_119)
      | v1_xboole_0(k1_zfmisc_1(B_118))
      | ~ r1_tarski(A_119,B_118) ) ),
    inference(resolution,[status(thm)],[c_34,c_104])).

tff(c_1173,plain,(
    ! [A_120] :
      ( k6_domain_1(k1_zfmisc_1(u1_struct_0('#skF_3')),A_120) = k1_tarski(A_120)
      | ~ r1_tarski(A_120,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1134,c_1068])).

tff(c_1188,plain,(
    ! [A_120] :
      ( m1_subset_1(k1_tarski(A_120),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | ~ m1_subset_1(A_120,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_120,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1173,c_14])).

tff(c_1214,plain,(
    ! [A_120] :
      ( m1_subset_1(k1_tarski(A_120),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | ~ m1_subset_1(A_120,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_120,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1068,c_1188])).

tff(c_1536,plain,(
    ! [A_135] :
      ( m1_subset_1(k1_tarski(A_135),'#skF_4')
      | ~ m1_subset_1(A_135,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_135,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1366,c_1214])).

tff(c_1565,plain,(
    ! [A_136] :
      ( m1_subset_1(k1_tarski(A_136),'#skF_4')
      | ~ r1_tarski(A_136,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_34,c_1536])).

tff(c_1583,plain,
    ( m1_subset_1(k1_tarski(k1_tarski('#skF_2'(u1_struct_0('#skF_3')))),'#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_175,c_1565])).

tff(c_1588,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1583])).

tff(c_1591,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1588,c_22])).

tff(c_1597,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1591])).

tff(c_1601,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_1597])).

tff(c_1605,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1601])).

tff(c_1607,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1583])).

tff(c_1099,plain,(
    ! [A_113,B_114] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_113),B_114),A_113)
      | ~ m1_subset_1(B_114,u1_struct_0(A_113))
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1103,plain,(
    ! [A_113] :
      ( v2_tex_2(k1_tarski('#skF_2'(u1_struct_0(A_113))),A_113)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_113)),u1_struct_0(A_113))
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113)
      | v2_struct_0(A_113)
      | v1_xboole_0(u1_struct_0(A_113)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_1099])).

tff(c_1105,plain,(
    ! [A_113] :
      ( v2_tex_2(k1_tarski('#skF_2'(u1_struct_0(A_113))),A_113)
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113)
      | v2_struct_0(A_113)
      | v1_xboole_0(u1_struct_0(A_113)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1103])).

tff(c_1722,plain,(
    ! [A_150,B_151] :
      ( k6_domain_1(k1_zfmisc_1(A_150),k6_domain_1(A_150,B_151)) = k1_tarski(k6_domain_1(A_150,B_151))
      | v1_xboole_0(k1_zfmisc_1(A_150))
      | ~ m1_subset_1(B_151,A_150)
      | v1_xboole_0(A_150) ) ),
    inference(resolution,[status(thm)],[c_126,c_26])).

tff(c_1787,plain,(
    ! [A_14] :
      ( k6_domain_1(k1_zfmisc_1(A_14),k1_tarski('#skF_2'(A_14))) = k1_tarski(k6_domain_1(A_14,'#skF_2'(A_14)))
      | v1_xboole_0(k1_zfmisc_1(A_14))
      | ~ m1_subset_1('#skF_2'(A_14),A_14)
      | v1_xboole_0(A_14)
      | v1_xboole_0(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_1722])).

tff(c_1808,plain,(
    ! [A_152] :
      ( k6_domain_1(k1_zfmisc_1(A_152),k1_tarski('#skF_2'(A_152))) = k1_tarski(k6_domain_1(A_152,'#skF_2'(A_152)))
      | v1_xboole_0(k1_zfmisc_1(A_152))
      | v1_xboole_0(A_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1787])).

tff(c_1399,plain,(
    ! [B_12] :
      ( m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0('#skF_3')),B_12),'#skF_4')
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1366,c_14])).

tff(c_1417,plain,(
    ! [B_12] :
      ( m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0('#skF_3')),B_12),'#skF_4')
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1068,c_1399])).

tff(c_1818,plain,
    ( m1_subset_1(k1_tarski(k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'(u1_struct_0('#skF_3')))),'#skF_4')
    | ~ m1_subset_1(k1_tarski('#skF_2'(u1_struct_0('#skF_3'))),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1808,c_1417])).

tff(c_1860,plain,
    ( m1_subset_1(k1_tarski(k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'(u1_struct_0('#skF_3')))),'#skF_4')
    | ~ m1_subset_1(k1_tarski('#skF_2'(u1_struct_0('#skF_3'))),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1607,c_1068,c_1818])).

tff(c_1866,plain,(
    ~ m1_subset_1(k1_tarski('#skF_2'(u1_struct_0('#skF_3'))),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1860])).

tff(c_1894,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_139,c_1866])).

tff(c_1901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1607,c_1894])).

tff(c_1903,plain,(
    m1_subset_1(k1_tarski('#skF_2'(u1_struct_0('#skF_3'))),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1860])).

tff(c_2079,plain,(
    ! [C_156,B_157,A_158] :
      ( C_156 = B_157
      | ~ r1_tarski(B_157,C_156)
      | ~ v2_tex_2(C_156,A_158)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ v3_tex_2(B_157,A_158)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ l1_pre_topc(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2312,plain,(
    ! [A_175,A_176] :
      ( A_175 = '#skF_4'
      | ~ v2_tex_2(A_175,A_176)
      | ~ m1_subset_1(A_175,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ v3_tex_2('#skF_4',A_176)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ l1_pre_topc(A_176) ) ),
    inference(resolution,[status(thm)],[c_69,c_2079])).

tff(c_2314,plain,
    ( k1_tarski('#skF_2'(u1_struct_0('#skF_3'))) = '#skF_4'
    | ~ v2_tex_2(k1_tarski('#skF_2'(u1_struct_0('#skF_3'))),'#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1903,c_2312])).

tff(c_2333,plain,
    ( k1_tarski('#skF_2'(u1_struct_0('#skF_3'))) = '#skF_4'
    | ~ v2_tex_2(k1_tarski('#skF_2'(u1_struct_0('#skF_3'))),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_38,c_2314])).

tff(c_2343,plain,(
    ~ v2_tex_2(k1_tarski('#skF_2'(u1_struct_0('#skF_3'))),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2333])).

tff(c_2346,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1105,c_2343])).

tff(c_2349,plain,
    ( v2_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_2346])).

tff(c_2351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1607,c_48,c_2349])).

tff(c_2352,plain,(
    k1_tarski('#skF_2'(u1_struct_0('#skF_3'))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2333])).

tff(c_12,plain,(
    ! [B_7,A_1] :
      ( v2_tex_2(B_7,A_1)
      | ~ v3_tex_2(B_7,A_1)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1913,plain,
    ( v2_tex_2(k1_tarski('#skF_2'(u1_struct_0('#skF_3'))),'#skF_3')
    | ~ v3_tex_2(k1_tarski('#skF_2'(u1_struct_0('#skF_3'))),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1903,c_12])).

tff(c_1931,plain,
    ( v2_tex_2(k1_tarski('#skF_2'(u1_struct_0('#skF_3'))),'#skF_3')
    | ~ v3_tex_2(k1_tarski('#skF_2'(u1_struct_0('#skF_3'))),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1913])).

tff(c_2056,plain,(
    ~ v3_tex_2(k1_tarski('#skF_2'(u1_struct_0('#skF_3'))),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1931])).

tff(c_2356,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2352,c_2056])).

tff(c_2364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2356])).

tff(c_2365,plain,(
    v2_tex_2(k1_tarski('#skF_2'(u1_struct_0('#skF_3'))),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1931])).

tff(c_2367,plain,(
    ! [C_177,B_178,A_179] :
      ( C_177 = B_178
      | ~ r1_tarski(B_178,C_177)
      | ~ v2_tex_2(C_177,A_179)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ v3_tex_2(B_178,A_179)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ l1_pre_topc(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2616,plain,(
    ! [A_195,A_196] :
      ( A_195 = '#skF_4'
      | ~ v2_tex_2(A_195,A_196)
      | ~ m1_subset_1(A_195,k1_zfmisc_1(u1_struct_0(A_196)))
      | ~ v3_tex_2('#skF_4',A_196)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_196)))
      | ~ l1_pre_topc(A_196) ) ),
    inference(resolution,[status(thm)],[c_69,c_2367])).

tff(c_2618,plain,
    ( k1_tarski('#skF_2'(u1_struct_0('#skF_3'))) = '#skF_4'
    | ~ v2_tex_2(k1_tarski('#skF_2'(u1_struct_0('#skF_3'))),'#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1903,c_2616])).

tff(c_2637,plain,(
    k1_tarski('#skF_2'(u1_struct_0('#skF_3'))) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_38,c_2365,c_2618])).

tff(c_2697,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2637,c_24])).

tff(c_2719,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2697])).

%------------------------------------------------------------------------------
