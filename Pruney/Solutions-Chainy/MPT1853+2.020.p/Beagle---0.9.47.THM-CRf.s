%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:02 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 445 expanded)
%              Number of leaves         :   41 ( 157 expanded)
%              Depth                    :   12
%              Number of atoms          :  275 (1142 expanded)
%              Number of equality atoms :   27 ( 133 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_179,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_106,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_127,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_166,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => ~ ( v1_subset_1(k6_domain_1(A,B),A)
              & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_141,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_120,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_155,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v7_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ~ v2_struct_0(B)
           => ( ~ v2_struct_0(B)
              & ~ v1_tex_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_tex_2)).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_58,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_8,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_703,plain,(
    ! [A_128,B_129] :
      ( k6_domain_1(A_128,B_129) = k1_tarski(B_129)
      | ~ m1_subset_1(B_129,A_128)
      | v1_xboole_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_715,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_703])).

tff(c_716,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_715])).

tff(c_12,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_719,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_716,c_12])).

tff(c_722,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_719])).

tff(c_725,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_722])).

tff(c_729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_725])).

tff(c_731,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_715])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_730,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_715])).

tff(c_737,plain,(
    ! [A_130,B_131] :
      ( v1_zfmisc_1(A_130)
      | k6_domain_1(A_130,B_131) != A_130
      | ~ m1_subset_1(B_131,A_130)
      | v1_xboole_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_746,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_3'))
    | k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') != u1_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_737])).

tff(c_750,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_3'))
    | u1_struct_0('#skF_3') != k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_730,c_746])).

tff(c_751,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_3'))
    | u1_struct_0('#skF_3') != k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_731,c_750])).

tff(c_752,plain,(
    u1_struct_0('#skF_3') != k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_751])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(k1_tarski(A_2),k1_zfmisc_1(B_3))
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_692,plain,(
    ! [B_125,A_126] :
      ( v1_subset_1(B_125,A_126)
      | B_125 = A_126
      | ~ m1_subset_1(B_125,k1_zfmisc_1(A_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_753,plain,(
    ! [A_132,B_133] :
      ( v1_subset_1(k1_tarski(A_132),B_133)
      | k1_tarski(A_132) = B_133
      | ~ r2_hidden(A_132,B_133) ) ),
    inference(resolution,[status(thm)],[c_4,c_692])).

tff(c_117,plain,(
    ! [A_59,B_60] :
      ( k6_domain_1(A_59,B_60) = k1_tarski(B_60)
      | ~ m1_subset_1(B_60,A_59)
      | v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_129,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_117])).

tff(c_132,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_135,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_132,c_12])).

tff(c_138,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_135])).

tff(c_141,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_138])).

tff(c_145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_141])).

tff(c_147,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_146,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_68,plain,
    ( v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_83,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_148,plain,(
    v1_subset_1(k1_tarski('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_83])).

tff(c_217,plain,(
    ! [A_70,B_71] :
      ( ~ v1_zfmisc_1(A_70)
      | ~ v1_subset_1(k6_domain_1(A_70,B_71),A_70)
      | ~ m1_subset_1(B_71,A_70)
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_223,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_3'))
    | ~ v1_subset_1(k1_tarski('#skF_4'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_217])).

tff(c_228,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_148,c_223])).

tff(c_229,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_228])).

tff(c_269,plain,(
    ! [A_75,B_76] :
      ( m1_pre_topc(k1_tex_2(A_75,B_76),A_75)
      | ~ m1_subset_1(B_76,u1_struct_0(A_75))
      | ~ l1_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_274,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_269])).

tff(c_278,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_274])).

tff(c_279,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_278])).

tff(c_399,plain,(
    ! [A_88,B_89] :
      ( m1_subset_1('#skF_2'(A_88,B_89),k1_zfmisc_1(u1_struct_0(A_88)))
      | v1_tex_2(B_89,A_88)
      | ~ m1_pre_topc(B_89,A_88)
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_38,plain,(
    ! [B_33,A_32] :
      ( v1_subset_1(B_33,A_32)
      | B_33 = A_32
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_624,plain,(
    ! [A_114,B_115] :
      ( v1_subset_1('#skF_2'(A_114,B_115),u1_struct_0(A_114))
      | u1_struct_0(A_114) = '#skF_2'(A_114,B_115)
      | v1_tex_2(B_115,A_114)
      | ~ m1_pre_topc(B_115,A_114)
      | ~ l1_pre_topc(A_114) ) ),
    inference(resolution,[status(thm)],[c_399,c_38])).

tff(c_32,plain,(
    ! [A_22,B_28] :
      ( ~ v1_subset_1('#skF_2'(A_22,B_28),u1_struct_0(A_22))
      | v1_tex_2(B_28,A_22)
      | ~ m1_pre_topc(B_28,A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_639,plain,(
    ! [A_116,B_117] :
      ( u1_struct_0(A_116) = '#skF_2'(A_116,B_117)
      | v1_tex_2(B_117,A_116)
      | ~ m1_pre_topc(B_117,A_116)
      | ~ l1_pre_topc(A_116) ) ),
    inference(resolution,[status(thm)],[c_624,c_32])).

tff(c_62,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_131,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_62])).

tff(c_645,plain,
    ( '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) = u1_struct_0('#skF_3')
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_639,c_131])).

tff(c_649,plain,(
    '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_279,c_645])).

tff(c_10,plain,(
    ! [B_9,A_7] :
      ( l1_pre_topc(B_9)
      | ~ m1_pre_topc(B_9,A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_282,plain,
    ( l1_pre_topc(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_279,c_10])).

tff(c_285,plain,(
    l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_282])).

tff(c_235,plain,(
    ! [A_72,B_73] :
      ( v7_struct_0(k1_tex_2(A_72,B_73))
      | ~ m1_subset_1(B_73,u1_struct_0(A_72))
      | ~ l1_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_242,plain,
    ( v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_235])).

tff(c_246,plain,
    ( v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_242])).

tff(c_247,plain,(
    v7_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_246])).

tff(c_286,plain,(
    ! [B_77,A_78] :
      ( u1_struct_0(B_77) = '#skF_2'(A_78,B_77)
      | v1_tex_2(B_77,A_78)
      | ~ m1_pre_topc(B_77,A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_289,plain,
    ( u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_286,c_131])).

tff(c_292,plain,(
    u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_279,c_289])).

tff(c_16,plain,(
    ! [A_12] :
      ( v1_zfmisc_1(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | ~ v7_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_307,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ v7_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_16])).

tff(c_329,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_307])).

tff(c_333,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_329])).

tff(c_337,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_333])).

tff(c_341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_337])).

tff(c_342,plain,(
    v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_329])).

tff(c_662,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_649,c_342])).

tff(c_665,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_229,c_662])).

tff(c_666,plain,(
    v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_669,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_666,c_62])).

tff(c_732,plain,(
    ~ v1_subset_1(k1_tarski('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_730,c_669])).

tff(c_756,plain,
    ( u1_struct_0('#skF_3') = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_753,c_732])).

tff(c_763,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_752,c_756])).

tff(c_768,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_763])).

tff(c_771,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_768])).

tff(c_773,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_731,c_771])).

tff(c_775,plain,(
    u1_struct_0('#skF_3') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_751])).

tff(c_784,plain,(
    m1_subset_1('#skF_4',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_775,c_56])).

tff(c_838,plain,(
    ! [A_136,B_137] :
      ( ~ v2_struct_0(k1_tex_2(A_136,B_137))
      | ~ m1_subset_1(B_137,u1_struct_0(A_136))
      | ~ l1_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_841,plain,(
    ! [B_137] :
      ( ~ v2_struct_0(k1_tex_2('#skF_3',B_137))
      | ~ m1_subset_1(B_137,k1_tarski('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_775,c_838])).

tff(c_847,plain,(
    ! [B_137] :
      ( ~ v2_struct_0(k1_tex_2('#skF_3',B_137))
      | ~ m1_subset_1(B_137,k1_tarski('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_841])).

tff(c_852,plain,(
    ! [B_138] :
      ( ~ v2_struct_0(k1_tex_2('#skF_3',B_138))
      | ~ m1_subset_1(B_138,k1_tarski('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_847])).

tff(c_860,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_784,c_852])).

tff(c_774,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_751])).

tff(c_14,plain,(
    ! [A_11] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_11))
      | ~ l1_struct_0(A_11)
      | v7_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_779,plain,
    ( ~ l1_struct_0('#skF_3')
    | v7_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_774,c_14])).

tff(c_815,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_779])).

tff(c_818,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_815])).

tff(c_822,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_818])).

tff(c_823,plain,(
    v7_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_779])).

tff(c_967,plain,(
    ! [A_151,B_152] :
      ( m1_pre_topc(k1_tex_2(A_151,B_152),A_151)
      | ~ m1_subset_1(B_152,u1_struct_0(A_151))
      | ~ l1_pre_topc(A_151)
      | v2_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_969,plain,(
    ! [B_152] :
      ( m1_pre_topc(k1_tex_2('#skF_3',B_152),'#skF_3')
      | ~ m1_subset_1(B_152,k1_tarski('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_775,c_967])).

tff(c_974,plain,(
    ! [B_152] :
      ( m1_pre_topc(k1_tex_2('#skF_3',B_152),'#skF_3')
      | ~ m1_subset_1(B_152,k1_tarski('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_969])).

tff(c_977,plain,(
    ! [B_153] :
      ( m1_pre_topc(k1_tex_2('#skF_3',B_153),'#skF_3')
      | ~ m1_subset_1(B_153,k1_tarski('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_974])).

tff(c_985,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_784,c_977])).

tff(c_1009,plain,(
    ! [B_157,A_158] :
      ( ~ v1_tex_2(B_157,A_158)
      | v2_struct_0(B_157)
      | ~ m1_pre_topc(B_157,A_158)
      | ~ l1_pre_topc(A_158)
      | ~ v7_struct_0(A_158)
      | v2_struct_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1015,plain,
    ( v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v7_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_666,c_1009])).

tff(c_1019,plain,
    ( v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_823,c_58,c_985,c_1015])).

tff(c_1021,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_860,c_1019])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:49:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.51  
% 3.42/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.51  %$ v1_tex_2 > v1_subset_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.42/1.51  
% 3.42/1.51  %Foreground sorts:
% 3.42/1.51  
% 3.42/1.51  
% 3.42/1.51  %Background operators:
% 3.42/1.51  
% 3.42/1.51  
% 3.42/1.51  %Foreground operators:
% 3.42/1.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.42/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.42/1.51  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.42/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.42/1.51  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.42/1.51  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 3.42/1.51  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 3.42/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.42/1.51  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.42/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.42/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.42/1.51  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.42/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.42/1.51  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.42/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.51  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 3.42/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.42/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.42/1.51  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.42/1.51  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.42/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.42/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.42/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.42/1.51  
% 3.42/1.53  tff(f_179, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 3.42/1.53  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.42/1.53  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.42/1.53  tff(f_56, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.42/1.53  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.42/1.53  tff(f_106, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 3.42/1.53  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 3.42/1.53  tff(f_127, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 3.42/1.53  tff(f_166, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 3.42/1.53  tff(f_141, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 3.42/1.53  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 3.42/1.53  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.42/1.53  tff(f_155, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 3.42/1.53  tff(f_70, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 3.42/1.53  tff(f_64, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_struct_0)).
% 3.42/1.53  tff(f_96, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & ~v1_tex_2(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc10_tex_2)).
% 3.42/1.53  tff(c_60, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.42/1.53  tff(c_58, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.42/1.53  tff(c_8, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.42/1.53  tff(c_56, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.42/1.53  tff(c_703, plain, (![A_128, B_129]: (k6_domain_1(A_128, B_129)=k1_tarski(B_129) | ~m1_subset_1(B_129, A_128) | v1_xboole_0(A_128))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.42/1.53  tff(c_715, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_56, c_703])).
% 3.42/1.53  tff(c_716, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_715])).
% 3.42/1.53  tff(c_12, plain, (![A_10]: (~v1_xboole_0(u1_struct_0(A_10)) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.42/1.53  tff(c_719, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_716, c_12])).
% 3.42/1.53  tff(c_722, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_719])).
% 3.42/1.53  tff(c_725, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_8, c_722])).
% 3.42/1.53  tff(c_729, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_725])).
% 3.42/1.53  tff(c_731, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_715])).
% 3.42/1.53  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.42/1.53  tff(c_730, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_715])).
% 3.42/1.53  tff(c_737, plain, (![A_130, B_131]: (v1_zfmisc_1(A_130) | k6_domain_1(A_130, B_131)!=A_130 | ~m1_subset_1(B_131, A_130) | v1_xboole_0(A_130))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.42/1.53  tff(c_746, plain, (v1_zfmisc_1(u1_struct_0('#skF_3')) | k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')!=u1_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_56, c_737])).
% 3.42/1.53  tff(c_750, plain, (v1_zfmisc_1(u1_struct_0('#skF_3')) | u1_struct_0('#skF_3')!=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_730, c_746])).
% 3.42/1.53  tff(c_751, plain, (v1_zfmisc_1(u1_struct_0('#skF_3')) | u1_struct_0('#skF_3')!=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_731, c_750])).
% 3.42/1.53  tff(c_752, plain, (u1_struct_0('#skF_3')!=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_751])).
% 3.42/1.53  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(k1_tarski(A_2), k1_zfmisc_1(B_3)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.42/1.53  tff(c_692, plain, (![B_125, A_126]: (v1_subset_1(B_125, A_126) | B_125=A_126 | ~m1_subset_1(B_125, k1_zfmisc_1(A_126)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.42/1.53  tff(c_753, plain, (![A_132, B_133]: (v1_subset_1(k1_tarski(A_132), B_133) | k1_tarski(A_132)=B_133 | ~r2_hidden(A_132, B_133))), inference(resolution, [status(thm)], [c_4, c_692])).
% 3.42/1.53  tff(c_117, plain, (![A_59, B_60]: (k6_domain_1(A_59, B_60)=k1_tarski(B_60) | ~m1_subset_1(B_60, A_59) | v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.42/1.53  tff(c_129, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_56, c_117])).
% 3.42/1.53  tff(c_132, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_129])).
% 3.42/1.53  tff(c_135, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_132, c_12])).
% 3.42/1.53  tff(c_138, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_135])).
% 3.42/1.53  tff(c_141, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_8, c_138])).
% 3.42/1.53  tff(c_145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_141])).
% 3.42/1.53  tff(c_147, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_129])).
% 3.42/1.53  tff(c_146, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_129])).
% 3.42/1.53  tff(c_68, plain, (v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.42/1.53  tff(c_83, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_68])).
% 3.42/1.53  tff(c_148, plain, (v1_subset_1(k1_tarski('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_83])).
% 3.42/1.53  tff(c_217, plain, (![A_70, B_71]: (~v1_zfmisc_1(A_70) | ~v1_subset_1(k6_domain_1(A_70, B_71), A_70) | ~m1_subset_1(B_71, A_70) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.42/1.53  tff(c_223, plain, (~v1_zfmisc_1(u1_struct_0('#skF_3')) | ~v1_subset_1(k1_tarski('#skF_4'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_146, c_217])).
% 3.42/1.53  tff(c_228, plain, (~v1_zfmisc_1(u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_148, c_223])).
% 3.42/1.53  tff(c_229, plain, (~v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_147, c_228])).
% 3.42/1.53  tff(c_269, plain, (![A_75, B_76]: (m1_pre_topc(k1_tex_2(A_75, B_76), A_75) | ~m1_subset_1(B_76, u1_struct_0(A_75)) | ~l1_pre_topc(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.42/1.53  tff(c_274, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_269])).
% 3.42/1.53  tff(c_278, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_274])).
% 3.42/1.53  tff(c_279, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_278])).
% 3.42/1.53  tff(c_399, plain, (![A_88, B_89]: (m1_subset_1('#skF_2'(A_88, B_89), k1_zfmisc_1(u1_struct_0(A_88))) | v1_tex_2(B_89, A_88) | ~m1_pre_topc(B_89, A_88) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.42/1.53  tff(c_38, plain, (![B_33, A_32]: (v1_subset_1(B_33, A_32) | B_33=A_32 | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.42/1.53  tff(c_624, plain, (![A_114, B_115]: (v1_subset_1('#skF_2'(A_114, B_115), u1_struct_0(A_114)) | u1_struct_0(A_114)='#skF_2'(A_114, B_115) | v1_tex_2(B_115, A_114) | ~m1_pre_topc(B_115, A_114) | ~l1_pre_topc(A_114))), inference(resolution, [status(thm)], [c_399, c_38])).
% 3.42/1.53  tff(c_32, plain, (![A_22, B_28]: (~v1_subset_1('#skF_2'(A_22, B_28), u1_struct_0(A_22)) | v1_tex_2(B_28, A_22) | ~m1_pre_topc(B_28, A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.42/1.53  tff(c_639, plain, (![A_116, B_117]: (u1_struct_0(A_116)='#skF_2'(A_116, B_117) | v1_tex_2(B_117, A_116) | ~m1_pre_topc(B_117, A_116) | ~l1_pre_topc(A_116))), inference(resolution, [status(thm)], [c_624, c_32])).
% 3.42/1.53  tff(c_62, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | ~v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.42/1.53  tff(c_131, plain, (~v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_62])).
% 3.42/1.53  tff(c_645, plain, ('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))=u1_struct_0('#skF_3') | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_639, c_131])).
% 3.42/1.53  tff(c_649, plain, ('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_279, c_645])).
% 3.42/1.53  tff(c_10, plain, (![B_9, A_7]: (l1_pre_topc(B_9) | ~m1_pre_topc(B_9, A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.42/1.53  tff(c_282, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_279, c_10])).
% 3.42/1.53  tff(c_285, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_282])).
% 3.42/1.53  tff(c_235, plain, (![A_72, B_73]: (v7_struct_0(k1_tex_2(A_72, B_73)) | ~m1_subset_1(B_73, u1_struct_0(A_72)) | ~l1_pre_topc(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.42/1.53  tff(c_242, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_235])).
% 3.42/1.53  tff(c_246, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_242])).
% 3.42/1.53  tff(c_247, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_246])).
% 3.42/1.53  tff(c_286, plain, (![B_77, A_78]: (u1_struct_0(B_77)='#skF_2'(A_78, B_77) | v1_tex_2(B_77, A_78) | ~m1_pre_topc(B_77, A_78) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.42/1.53  tff(c_289, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_286, c_131])).
% 3.42/1.53  tff(c_292, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_279, c_289])).
% 3.42/1.53  tff(c_16, plain, (![A_12]: (v1_zfmisc_1(u1_struct_0(A_12)) | ~l1_struct_0(A_12) | ~v7_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.42/1.53  tff(c_307, plain, (v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~v7_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_292, c_16])).
% 3.42/1.53  tff(c_329, plain, (v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_247, c_307])).
% 3.42/1.53  tff(c_333, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_329])).
% 3.42/1.53  tff(c_337, plain, (~l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_8, c_333])).
% 3.42/1.53  tff(c_341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_285, c_337])).
% 3.42/1.53  tff(c_342, plain, (v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_329])).
% 3.42/1.53  tff(c_662, plain, (v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_649, c_342])).
% 3.42/1.53  tff(c_665, plain, $false, inference(negUnitSimplification, [status(thm)], [c_229, c_662])).
% 3.42/1.53  tff(c_666, plain, (v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_68])).
% 3.42/1.53  tff(c_669, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_666, c_62])).
% 3.42/1.53  tff(c_732, plain, (~v1_subset_1(k1_tarski('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_730, c_669])).
% 3.42/1.53  tff(c_756, plain, (u1_struct_0('#skF_3')=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_753, c_732])).
% 3.42/1.53  tff(c_763, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_752, c_756])).
% 3.42/1.53  tff(c_768, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_763])).
% 3.42/1.53  tff(c_771, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_768])).
% 3.42/1.53  tff(c_773, plain, $false, inference(negUnitSimplification, [status(thm)], [c_731, c_771])).
% 3.42/1.53  tff(c_775, plain, (u1_struct_0('#skF_3')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_751])).
% 3.42/1.53  tff(c_784, plain, (m1_subset_1('#skF_4', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_775, c_56])).
% 3.42/1.53  tff(c_838, plain, (![A_136, B_137]: (~v2_struct_0(k1_tex_2(A_136, B_137)) | ~m1_subset_1(B_137, u1_struct_0(A_136)) | ~l1_pre_topc(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.42/1.53  tff(c_841, plain, (![B_137]: (~v2_struct_0(k1_tex_2('#skF_3', B_137)) | ~m1_subset_1(B_137, k1_tarski('#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_775, c_838])).
% 3.42/1.53  tff(c_847, plain, (![B_137]: (~v2_struct_0(k1_tex_2('#skF_3', B_137)) | ~m1_subset_1(B_137, k1_tarski('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_841])).
% 3.42/1.53  tff(c_852, plain, (![B_138]: (~v2_struct_0(k1_tex_2('#skF_3', B_138)) | ~m1_subset_1(B_138, k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_847])).
% 3.42/1.53  tff(c_860, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_784, c_852])).
% 3.42/1.53  tff(c_774, plain, (v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_751])).
% 3.42/1.53  tff(c_14, plain, (![A_11]: (~v1_zfmisc_1(u1_struct_0(A_11)) | ~l1_struct_0(A_11) | v7_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.42/1.53  tff(c_779, plain, (~l1_struct_0('#skF_3') | v7_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_774, c_14])).
% 3.42/1.53  tff(c_815, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_779])).
% 3.42/1.53  tff(c_818, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_8, c_815])).
% 3.42/1.53  tff(c_822, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_818])).
% 3.42/1.53  tff(c_823, plain, (v7_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_779])).
% 3.42/1.53  tff(c_967, plain, (![A_151, B_152]: (m1_pre_topc(k1_tex_2(A_151, B_152), A_151) | ~m1_subset_1(B_152, u1_struct_0(A_151)) | ~l1_pre_topc(A_151) | v2_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.42/1.53  tff(c_969, plain, (![B_152]: (m1_pre_topc(k1_tex_2('#skF_3', B_152), '#skF_3') | ~m1_subset_1(B_152, k1_tarski('#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_775, c_967])).
% 3.42/1.53  tff(c_974, plain, (![B_152]: (m1_pre_topc(k1_tex_2('#skF_3', B_152), '#skF_3') | ~m1_subset_1(B_152, k1_tarski('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_969])).
% 3.42/1.53  tff(c_977, plain, (![B_153]: (m1_pre_topc(k1_tex_2('#skF_3', B_153), '#skF_3') | ~m1_subset_1(B_153, k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_974])).
% 3.42/1.53  tff(c_985, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_784, c_977])).
% 3.42/1.53  tff(c_1009, plain, (![B_157, A_158]: (~v1_tex_2(B_157, A_158) | v2_struct_0(B_157) | ~m1_pre_topc(B_157, A_158) | ~l1_pre_topc(A_158) | ~v7_struct_0(A_158) | v2_struct_0(A_158))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.42/1.53  tff(c_1015, plain, (v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v7_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_666, c_1009])).
% 3.42/1.53  tff(c_1019, plain, (v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_823, c_58, c_985, c_1015])).
% 3.42/1.53  tff(c_1021, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_860, c_1019])).
% 3.42/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.53  
% 3.42/1.53  Inference rules
% 3.42/1.53  ----------------------
% 3.42/1.53  #Ref     : 0
% 3.42/1.53  #Sup     : 176
% 3.42/1.53  #Fact    : 0
% 3.42/1.53  #Define  : 0
% 3.42/1.53  #Split   : 9
% 3.42/1.53  #Chain   : 0
% 3.42/1.53  #Close   : 0
% 3.42/1.53  
% 3.42/1.53  Ordering : KBO
% 3.42/1.53  
% 3.42/1.53  Simplification rules
% 3.42/1.53  ----------------------
% 3.42/1.53  #Subsume      : 13
% 3.42/1.53  #Demod        : 122
% 3.42/1.53  #Tautology    : 54
% 3.42/1.53  #SimpNegUnit  : 42
% 3.42/1.53  #BackRed      : 21
% 3.42/1.53  
% 3.42/1.53  #Partial instantiations: 0
% 3.42/1.53  #Strategies tried      : 1
% 3.42/1.53  
% 3.42/1.53  Timing (in seconds)
% 3.42/1.53  ----------------------
% 3.57/1.54  Preprocessing        : 0.35
% 3.57/1.54  Parsing              : 0.18
% 3.57/1.54  CNF conversion       : 0.02
% 3.57/1.54  Main loop            : 0.41
% 3.57/1.54  Inferencing          : 0.16
% 3.57/1.54  Reduction            : 0.12
% 3.57/1.54  Demodulation         : 0.08
% 3.57/1.54  BG Simplification    : 0.02
% 3.57/1.54  Subsumption          : 0.06
% 3.57/1.54  Abstraction          : 0.02
% 3.57/1.54  MUC search           : 0.00
% 3.57/1.54  Cooper               : 0.00
% 3.57/1.54  Total                : 0.81
% 3.57/1.54  Index Insertion      : 0.00
% 3.57/1.54  Index Deletion       : 0.00
% 3.57/1.54  Index Matching       : 0.00
% 3.57/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
