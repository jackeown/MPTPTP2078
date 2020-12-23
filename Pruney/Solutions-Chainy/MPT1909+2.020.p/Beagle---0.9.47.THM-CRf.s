%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:40 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 333 expanded)
%              Number of leaves         :   43 ( 137 expanded)
%              Depth                    :   15
%              Number of atoms          :  280 (1675 expanded)
%              Number of equality atoms :   31 ( 199 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_borsuk_1,type,(
    v3_borsuk_1: ( $i * $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_184,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_tex_2(B,A)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & v5_pre_topc(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( v3_borsuk_1(C,A,B)
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(B))
                     => ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( D = E
                           => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k6_domain_1(u1_struct_0(B),D)) = k2_pre_topc(A,k6_domain_1(u1_struct_0(A),E)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tex_2)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_73,axiom,(
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

tff(f_107,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_tex_2(A,B)
              <=> u1_struct_0(C) = k6_domain_1(u1_struct_0(A),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tex_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_145,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_tex_2(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & v5_pre_topc(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v3_borsuk_1(C,A,B)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                       => ( D = E
                         => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D) = k2_pre_topc(A,E) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tex_2)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_60,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_54,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_86,plain,(
    ! [B_91,A_92] :
      ( l1_pre_topc(B_91)
      | ~ m1_pre_topc(B_91,A_92)
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_89,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_86])).

tff(c_92,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_89])).

tff(c_14,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_113,plain,(
    ! [A_98,B_99] :
      ( k6_domain_1(A_98,B_99) = k1_tarski(B_99)
      | ~ m1_subset_1(B_99,A_98)
      | v1_xboole_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_129,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_113])).

tff(c_146,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_18,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_149,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_146,c_18])).

tff(c_152,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_149])).

tff(c_155,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_152])).

tff(c_159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_155])).

tff(c_160,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_38,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_67,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40])).

tff(c_128,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_67,c_113])).

tff(c_130,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_133,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_130,c_18])).

tff(c_136,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_133])).

tff(c_139,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_136])).

tff(c_143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_139])).

tff(c_144,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_36,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_68,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36])).

tff(c_181,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_68])).

tff(c_182,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) != k2_pre_topc('#skF_1',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_181])).

tff(c_56,plain,(
    v4_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_50,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_48,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_44,plain,(
    v3_borsuk_1('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_162,plain,(
    ! [A_100,B_101] :
      ( ~ v2_struct_0(k1_tex_2(A_100,B_101))
      | ~ m1_subset_1(B_101,u1_struct_0(A_100))
      | ~ l1_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_168,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_162])).

tff(c_175,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_168])).

tff(c_176,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_175])).

tff(c_187,plain,(
    ! [A_102,B_103] :
      ( v1_pre_topc(k1_tex_2(A_102,B_103))
      | ~ m1_subset_1(B_103,u1_struct_0(A_102))
      | ~ l1_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_193,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_187])).

tff(c_200,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_193])).

tff(c_201,plain,(
    v1_pre_topc(k1_tex_2('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_200])).

tff(c_202,plain,(
    ! [A_104,B_105] :
      ( m1_pre_topc(k1_tex_2(A_104,B_105),A_104)
      | ~ m1_subset_1(B_105,u1_struct_0(A_104))
      | ~ l1_pre_topc(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_206,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_202])).

tff(c_213,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_4'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_206])).

tff(c_214,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_213])).

tff(c_392,plain,(
    ! [A_124,B_125] :
      ( k6_domain_1(u1_struct_0(A_124),B_125) = u1_struct_0(k1_tex_2(A_124,B_125))
      | ~ m1_pre_topc(k1_tex_2(A_124,B_125),A_124)
      | ~ v1_pre_topc(k1_tex_2(A_124,B_125))
      | v2_struct_0(k1_tex_2(A_124,B_125))
      | ~ m1_subset_1(B_125,u1_struct_0(A_124))
      | ~ l1_pre_topc(A_124)
      | v2_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_394,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = u1_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | ~ v1_pre_topc(k1_tex_2('#skF_2','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_214,c_392])).

tff(c_399,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_4')) = k1_tarski('#skF_4')
    | v2_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_42,c_201,c_160,c_394])).

tff(c_400,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_4')) = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_176,c_399])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_238,plain,(
    ! [C_108,A_109,B_110] :
      ( m1_subset_1(C_108,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ m1_subset_1(C_108,k1_zfmisc_1(u1_struct_0(B_110)))
      | ~ m1_pre_topc(B_110,A_109)
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_243,plain,(
    ! [A_111,A_112,B_113] :
      ( m1_subset_1(A_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ m1_pre_topc(B_113,A_112)
      | ~ l1_pre_topc(A_112)
      | ~ r1_tarski(A_111,u1_struct_0(B_113)) ) ),
    inference(resolution,[status(thm)],[c_12,c_238])).

tff(c_245,plain,(
    ! [A_111] :
      ( m1_subset_1(A_111,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_111,u1_struct_0(k1_tex_2('#skF_2','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_214,c_243])).

tff(c_312,plain,(
    ! [A_120] :
      ( m1_subset_1(A_120,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_120,u1_struct_0(k1_tex_2('#skF_2','#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_245])).

tff(c_317,plain,(
    m1_subset_1(u1_struct_0(k1_tex_2('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_6,c_312])).

tff(c_407,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_317])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_64,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_62,plain,(
    v3_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_165,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_4'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_67,c_162])).

tff(c_171,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_4'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_165])).

tff(c_172,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_171])).

tff(c_190,plain,
    ( v1_pre_topc(k1_tex_2('#skF_1','#skF_4'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_67,c_187])).

tff(c_196,plain,
    ( v1_pre_topc(k1_tex_2('#skF_1','#skF_4'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_190])).

tff(c_197,plain,(
    v1_pre_topc(k1_tex_2('#skF_1','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_196])).

tff(c_204,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_67,c_202])).

tff(c_209,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_204])).

tff(c_210,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_209])).

tff(c_396,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = u1_struct_0(k1_tex_2('#skF_1','#skF_4'))
    | ~ v1_pre_topc(k1_tex_2('#skF_1','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_210,c_392])).

tff(c_403,plain,
    ( u1_struct_0(k1_tex_2('#skF_1','#skF_4')) = k1_tarski('#skF_4')
    | v2_struct_0(k1_tex_2('#skF_1','#skF_4'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_67,c_197,c_144,c_396])).

tff(c_404,plain,(
    u1_struct_0(k1_tex_2('#skF_1','#skF_4')) = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_172,c_403])).

tff(c_247,plain,(
    ! [A_111] :
      ( m1_subset_1(A_111,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_111,u1_struct_0(k1_tex_2('#skF_1','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_210,c_243])).

tff(c_277,plain,(
    ! [A_116] :
      ( m1_subset_1(A_116,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_116,u1_struct_0(k1_tex_2('#skF_1','#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_247])).

tff(c_282,plain,(
    m1_subset_1(u1_struct_0(k1_tex_2('#skF_1','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6,c_277])).

tff(c_464,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_282])).

tff(c_534,plain,(
    ! [A_126,B_127,C_128,E_129] :
      ( k8_relset_1(u1_struct_0(A_126),u1_struct_0(B_127),C_128,E_129) = k2_pre_topc(A_126,E_129)
      | ~ m1_subset_1(E_129,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ m1_subset_1(E_129,k1_zfmisc_1(u1_struct_0(B_127)))
      | ~ v3_borsuk_1(C_128,A_126,B_127)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_126),u1_struct_0(B_127))))
      | ~ v5_pre_topc(C_128,A_126,B_127)
      | ~ v1_funct_2(C_128,u1_struct_0(A_126),u1_struct_0(B_127))
      | ~ v1_funct_1(C_128)
      | ~ m1_pre_topc(B_127,A_126)
      | ~ v4_tex_2(B_127,A_126)
      | v2_struct_0(B_127)
      | ~ l1_pre_topc(A_126)
      | ~ v3_tdlat_3(A_126)
      | ~ v2_pre_topc(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_536,plain,(
    ! [B_127,C_128] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_127),C_128,k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
      | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0(B_127)))
      | ~ v3_borsuk_1(C_128,'#skF_1',B_127)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_127))))
      | ~ v5_pre_topc(C_128,'#skF_1',B_127)
      | ~ v1_funct_2(C_128,u1_struct_0('#skF_1'),u1_struct_0(B_127))
      | ~ v1_funct_1(C_128)
      | ~ m1_pre_topc(B_127,'#skF_1')
      | ~ v4_tex_2(B_127,'#skF_1')
      | v2_struct_0(B_127)
      | ~ l1_pre_topc('#skF_1')
      | ~ v3_tdlat_3('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_464,c_534])).

tff(c_550,plain,(
    ! [B_127,C_128] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_127),C_128,k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
      | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0(B_127)))
      | ~ v3_borsuk_1(C_128,'#skF_1',B_127)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_127))))
      | ~ v5_pre_topc(C_128,'#skF_1',B_127)
      | ~ v1_funct_2(C_128,u1_struct_0('#skF_1'),u1_struct_0(B_127))
      | ~ v1_funct_1(C_128)
      | ~ m1_pre_topc(B_127,'#skF_1')
      | ~ v4_tex_2(B_127,'#skF_1')
      | v2_struct_0(B_127)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_536])).

tff(c_667,plain,(
    ! [B_139,C_140] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_139),C_140,k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
      | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0(B_139)))
      | ~ v3_borsuk_1(C_140,'#skF_1',B_139)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_139))))
      | ~ v5_pre_topc(C_140,'#skF_1',B_139)
      | ~ v1_funct_2(C_140,u1_struct_0('#skF_1'),u1_struct_0(B_139))
      | ~ v1_funct_1(C_140)
      | ~ m1_pre_topc(B_139,'#skF_1')
      | ~ v4_tex_2(B_139,'#skF_1')
      | v2_struct_0(B_139) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_550])).

tff(c_680,plain,
    ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v3_borsuk_1('#skF_3','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v4_tex_2('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_667])).

tff(c_689,plain,
    ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_44,c_407,c_680])).

tff(c_691,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_182,c_689])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.61  
% 3.27/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.61  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.27/1.61  
% 3.27/1.61  %Foreground sorts:
% 3.27/1.61  
% 3.27/1.61  
% 3.27/1.61  %Background operators:
% 3.27/1.61  
% 3.27/1.61  
% 3.27/1.61  %Foreground operators:
% 3.27/1.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.27/1.61  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 3.27/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.27/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.27/1.61  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.27/1.61  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 3.27/1.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.27/1.61  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.27/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.27/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.27/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.27/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.27/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.27/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.27/1.61  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.27/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.27/1.61  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.27/1.61  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.27/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.27/1.61  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 3.27/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.27/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.61  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.27/1.61  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.27/1.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.27/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.27/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.27/1.61  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.27/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.27/1.61  
% 3.27/1.63  tff(f_184, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tex_2)).
% 3.27/1.63  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.27/1.63  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.27/1.63  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.27/1.63  tff(f_56, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.27/1.63  tff(f_107, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 3.27/1.63  tff(f_93, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ((C = k1_tex_2(A, B)) <=> (u1_struct_0(C) = k6_domain_1(u1_struct_0(A), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tex_2)).
% 3.27/1.63  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.27/1.63  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.27/1.63  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 3.27/1.63  tff(f_145, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tex_2)).
% 3.27/1.63  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.27/1.63  tff(c_60, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.27/1.63  tff(c_54, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.27/1.63  tff(c_86, plain, (![B_91, A_92]: (l1_pre_topc(B_91) | ~m1_pre_topc(B_91, A_92) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.27/1.63  tff(c_89, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_86])).
% 3.27/1.63  tff(c_92, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_89])).
% 3.27/1.63  tff(c_14, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.27/1.63  tff(c_42, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.27/1.63  tff(c_113, plain, (![A_98, B_99]: (k6_domain_1(A_98, B_99)=k1_tarski(B_99) | ~m1_subset_1(B_99, A_98) | v1_xboole_0(A_98))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.27/1.63  tff(c_129, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_113])).
% 3.27/1.63  tff(c_146, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_129])).
% 3.27/1.63  tff(c_18, plain, (![A_10]: (~v1_xboole_0(u1_struct_0(A_10)) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.27/1.63  tff(c_149, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_146, c_18])).
% 3.27/1.63  tff(c_152, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_58, c_149])).
% 3.27/1.63  tff(c_155, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_152])).
% 3.27/1.63  tff(c_159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_155])).
% 3.27/1.63  tff(c_160, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_129])).
% 3.27/1.63  tff(c_66, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.27/1.63  tff(c_38, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.27/1.63  tff(c_40, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.27/1.63  tff(c_67, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40])).
% 3.27/1.63  tff(c_128, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_67, c_113])).
% 3.27/1.63  tff(c_130, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_128])).
% 3.27/1.63  tff(c_133, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_130, c_18])).
% 3.27/1.63  tff(c_136, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_133])).
% 3.27/1.63  tff(c_139, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_136])).
% 3.27/1.63  tff(c_143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_139])).
% 3.27/1.63  tff(c_144, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_128])).
% 3.27/1.63  tff(c_36, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.27/1.63  tff(c_68, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36])).
% 3.27/1.63  tff(c_181, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_68])).
% 3.27/1.63  tff(c_182, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))!=k2_pre_topc('#skF_1', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_181])).
% 3.27/1.63  tff(c_56, plain, (v4_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.27/1.63  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.27/1.63  tff(c_50, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.27/1.63  tff(c_48, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.27/1.63  tff(c_44, plain, (v3_borsuk_1('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.27/1.63  tff(c_162, plain, (![A_100, B_101]: (~v2_struct_0(k1_tex_2(A_100, B_101)) | ~m1_subset_1(B_101, u1_struct_0(A_100)) | ~l1_pre_topc(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.27/1.63  tff(c_168, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_162])).
% 3.27/1.63  tff(c_175, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_168])).
% 3.27/1.63  tff(c_176, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_175])).
% 3.27/1.63  tff(c_187, plain, (![A_102, B_103]: (v1_pre_topc(k1_tex_2(A_102, B_103)) | ~m1_subset_1(B_103, u1_struct_0(A_102)) | ~l1_pre_topc(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.27/1.63  tff(c_193, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_187])).
% 3.27/1.63  tff(c_200, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_193])).
% 3.27/1.63  tff(c_201, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_200])).
% 3.27/1.63  tff(c_202, plain, (![A_104, B_105]: (m1_pre_topc(k1_tex_2(A_104, B_105), A_104) | ~m1_subset_1(B_105, u1_struct_0(A_104)) | ~l1_pre_topc(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.27/1.63  tff(c_206, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_202])).
% 3.27/1.63  tff(c_213, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_4'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_206])).
% 3.27/1.63  tff(c_214, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_58, c_213])).
% 3.27/1.63  tff(c_392, plain, (![A_124, B_125]: (k6_domain_1(u1_struct_0(A_124), B_125)=u1_struct_0(k1_tex_2(A_124, B_125)) | ~m1_pre_topc(k1_tex_2(A_124, B_125), A_124) | ~v1_pre_topc(k1_tex_2(A_124, B_125)) | v2_struct_0(k1_tex_2(A_124, B_125)) | ~m1_subset_1(B_125, u1_struct_0(A_124)) | ~l1_pre_topc(A_124) | v2_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.27/1.63  tff(c_394, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=u1_struct_0(k1_tex_2('#skF_2', '#skF_4')) | ~v1_pre_topc(k1_tex_2('#skF_2', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_214, c_392])).
% 3.27/1.63  tff(c_399, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))=k1_tarski('#skF_4') | v2_struct_0(k1_tex_2('#skF_2', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_42, c_201, c_160, c_394])).
% 3.27/1.63  tff(c_400, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_176, c_399])).
% 3.27/1.63  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.27/1.63  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.27/1.63  tff(c_238, plain, (![C_108, A_109, B_110]: (m1_subset_1(C_108, k1_zfmisc_1(u1_struct_0(A_109))) | ~m1_subset_1(C_108, k1_zfmisc_1(u1_struct_0(B_110))) | ~m1_pre_topc(B_110, A_109) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.27/1.63  tff(c_243, plain, (![A_111, A_112, B_113]: (m1_subset_1(A_111, k1_zfmisc_1(u1_struct_0(A_112))) | ~m1_pre_topc(B_113, A_112) | ~l1_pre_topc(A_112) | ~r1_tarski(A_111, u1_struct_0(B_113)))), inference(resolution, [status(thm)], [c_12, c_238])).
% 3.27/1.63  tff(c_245, plain, (![A_111]: (m1_subset_1(A_111, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_111, u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))))), inference(resolution, [status(thm)], [c_214, c_243])).
% 3.27/1.63  tff(c_312, plain, (![A_120]: (m1_subset_1(A_120, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_120, u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_245])).
% 3.27/1.63  tff(c_317, plain, (m1_subset_1(u1_struct_0(k1_tex_2('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_6, c_312])).
% 3.27/1.63  tff(c_407, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_400, c_317])).
% 3.27/1.63  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.27/1.63  tff(c_64, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.27/1.63  tff(c_62, plain, (v3_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.27/1.63  tff(c_165, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_4')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_67, c_162])).
% 3.27/1.63  tff(c_171, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_4')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_165])).
% 3.27/1.63  tff(c_172, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_171])).
% 3.27/1.63  tff(c_190, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_4')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_67, c_187])).
% 3.27/1.63  tff(c_196, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_4')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_190])).
% 3.27/1.63  tff(c_197, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_196])).
% 3.27/1.63  tff(c_204, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_67, c_202])).
% 3.27/1.63  tff(c_209, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_4'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_204])).
% 3.27/1.63  tff(c_210, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_209])).
% 3.27/1.63  tff(c_396, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=u1_struct_0(k1_tex_2('#skF_1', '#skF_4')) | ~v1_pre_topc(k1_tex_2('#skF_1', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_210, c_392])).
% 3.27/1.63  tff(c_403, plain, (u1_struct_0(k1_tex_2('#skF_1', '#skF_4'))=k1_tarski('#skF_4') | v2_struct_0(k1_tex_2('#skF_1', '#skF_4')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_67, c_197, c_144, c_396])).
% 3.27/1.63  tff(c_404, plain, (u1_struct_0(k1_tex_2('#skF_1', '#skF_4'))=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_66, c_172, c_403])).
% 3.27/1.63  tff(c_247, plain, (![A_111]: (m1_subset_1(A_111, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_111, u1_struct_0(k1_tex_2('#skF_1', '#skF_4'))))), inference(resolution, [status(thm)], [c_210, c_243])).
% 3.27/1.63  tff(c_277, plain, (![A_116]: (m1_subset_1(A_116, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_116, u1_struct_0(k1_tex_2('#skF_1', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_247])).
% 3.27/1.63  tff(c_282, plain, (m1_subset_1(u1_struct_0(k1_tex_2('#skF_1', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_277])).
% 3.27/1.63  tff(c_464, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_404, c_282])).
% 3.27/1.63  tff(c_534, plain, (![A_126, B_127, C_128, E_129]: (k8_relset_1(u1_struct_0(A_126), u1_struct_0(B_127), C_128, E_129)=k2_pre_topc(A_126, E_129) | ~m1_subset_1(E_129, k1_zfmisc_1(u1_struct_0(A_126))) | ~m1_subset_1(E_129, k1_zfmisc_1(u1_struct_0(B_127))) | ~v3_borsuk_1(C_128, A_126, B_127) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_126), u1_struct_0(B_127)))) | ~v5_pre_topc(C_128, A_126, B_127) | ~v1_funct_2(C_128, u1_struct_0(A_126), u1_struct_0(B_127)) | ~v1_funct_1(C_128) | ~m1_pre_topc(B_127, A_126) | ~v4_tex_2(B_127, A_126) | v2_struct_0(B_127) | ~l1_pre_topc(A_126) | ~v3_tdlat_3(A_126) | ~v2_pre_topc(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.27/1.63  tff(c_536, plain, (![B_127, C_128]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_127), C_128, k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0(B_127))) | ~v3_borsuk_1(C_128, '#skF_1', B_127) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_127)))) | ~v5_pre_topc(C_128, '#skF_1', B_127) | ~v1_funct_2(C_128, u1_struct_0('#skF_1'), u1_struct_0(B_127)) | ~v1_funct_1(C_128) | ~m1_pre_topc(B_127, '#skF_1') | ~v4_tex_2(B_127, '#skF_1') | v2_struct_0(B_127) | ~l1_pre_topc('#skF_1') | ~v3_tdlat_3('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_464, c_534])).
% 3.27/1.63  tff(c_550, plain, (![B_127, C_128]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_127), C_128, k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0(B_127))) | ~v3_borsuk_1(C_128, '#skF_1', B_127) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_127)))) | ~v5_pre_topc(C_128, '#skF_1', B_127) | ~v1_funct_2(C_128, u1_struct_0('#skF_1'), u1_struct_0(B_127)) | ~v1_funct_1(C_128) | ~m1_pre_topc(B_127, '#skF_1') | ~v4_tex_2(B_127, '#skF_1') | v2_struct_0(B_127) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_536])).
% 3.27/1.63  tff(c_667, plain, (![B_139, C_140]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_139), C_140, k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0(B_139))) | ~v3_borsuk_1(C_140, '#skF_1', B_139) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_139)))) | ~v5_pre_topc(C_140, '#skF_1', B_139) | ~v1_funct_2(C_140, u1_struct_0('#skF_1'), u1_struct_0(B_139)) | ~v1_funct_1(C_140) | ~m1_pre_topc(B_139, '#skF_1') | ~v4_tex_2(B_139, '#skF_1') | v2_struct_0(B_139))), inference(negUnitSimplification, [status(thm)], [c_66, c_550])).
% 3.27/1.63  tff(c_680, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_borsuk_1('#skF_3', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | ~v4_tex_2('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_667])).
% 3.27/1.63  tff(c_689, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_44, c_407, c_680])).
% 3.27/1.63  tff(c_691, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_182, c_689])).
% 3.27/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.63  
% 3.27/1.63  Inference rules
% 3.27/1.63  ----------------------
% 3.27/1.63  #Ref     : 0
% 3.27/1.63  #Sup     : 124
% 3.27/1.63  #Fact    : 0
% 3.27/1.63  #Define  : 0
% 3.27/1.63  #Split   : 8
% 3.27/1.64  #Chain   : 0
% 3.27/1.64  #Close   : 0
% 3.27/1.64  
% 3.27/1.64  Ordering : KBO
% 3.27/1.64  
% 3.27/1.64  Simplification rules
% 3.27/1.64  ----------------------
% 3.27/1.64  #Subsume      : 3
% 3.27/1.64  #Demod        : 105
% 3.27/1.64  #Tautology    : 25
% 3.27/1.64  #SimpNegUnit  : 42
% 3.27/1.64  #BackRed      : 10
% 3.27/1.64  
% 3.27/1.64  #Partial instantiations: 0
% 3.27/1.64  #Strategies tried      : 1
% 3.27/1.64  
% 3.27/1.64  Timing (in seconds)
% 3.27/1.64  ----------------------
% 3.70/1.64  Preprocessing        : 0.40
% 3.70/1.64  Parsing              : 0.20
% 3.70/1.64  CNF conversion       : 0.03
% 3.70/1.64  Main loop            : 0.39
% 3.70/1.64  Inferencing          : 0.12
% 3.70/1.64  Reduction            : 0.14
% 3.70/1.64  Demodulation         : 0.10
% 3.70/1.64  BG Simplification    : 0.02
% 3.70/1.64  Subsumption          : 0.08
% 3.70/1.64  Abstraction          : 0.02
% 3.70/1.64  MUC search           : 0.00
% 3.70/1.64  Cooper               : 0.00
% 3.70/1.64  Total                : 0.84
% 3.70/1.64  Index Insertion      : 0.00
% 3.70/1.64  Index Deletion       : 0.00
% 3.70/1.64  Index Matching       : 0.00
% 3.70/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
