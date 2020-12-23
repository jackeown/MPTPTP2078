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
% DateTime   : Thu Dec  3 10:24:00 EST 2020

% Result     : Theorem 13.46s
% Output     : CNFRefutation 13.46s
% Verified   : 
% Statistics : Number of formulae       :  194 (15126 expanded)
%              Number of leaves         :   56 (5233 expanded)
%              Depth                    :   24
%              Number of atoms          :  605 (52498 expanded)
%              Number of equality atoms :  100 (10420 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_tops_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v4_pre_topc > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_struct_0 > v2_pre_topc > v2_funct_1 > v1_relat_1 > v1_funct_1 > v1_compts_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v3_tops_2,type,(
    v3_tops_2: ( $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_212,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( v1_compts_1(A)
                    & v8_pre_topc(B)
                    & k1_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(A)
                    & k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C)
                    & v5_pre_topc(C,A,B) )
                 => v3_tops_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_compts_1)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_144,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v3_tops_2(C,A,B)
              <=> ( k1_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(A)
                  & k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                  & v2_funct_1(C)
                  & ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                     => ( v4_pre_topc(D,A)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tops_2)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_178,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( ( v1_compts_1(A)
                  & v8_pre_topc(B)
                  & k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                  & v5_pre_topc(C,A,B) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( v4_pre_topc(D,A)
                     => v4_pre_topc(k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_compts_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v5_pre_topc(C,A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( v4_pre_topc(D,B)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_pre_topc)).

tff(c_66,plain,(
    ~ v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_84,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_92,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_42,plain,(
    ! [A_56] :
      ( l1_struct_0(A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_96,plain,(
    ! [A_99] :
      ( u1_struct_0(A_99) = k2_struct_0(A_99)
      | ~ l1_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_101,plain,(
    ! [A_100] :
      ( u1_struct_0(A_100) = k2_struct_0(A_100)
      | ~ l1_pre_topc(A_100) ) ),
    inference(resolution,[status(thm)],[c_42,c_96])).

tff(c_109,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_101])).

tff(c_86,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_108,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_101])).

tff(c_80,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_121,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_108,c_80])).

tff(c_141,plain,(
    ! [C_105,A_106,B_107] :
      ( v1_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_149,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_121,c_141])).

tff(c_207,plain,(
    ! [A_129,B_130,C_131] :
      ( k2_relset_1(A_129,B_130,C_131) = k2_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_215,plain,(
    k2_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_121,c_207])).

tff(c_72,plain,(
    k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_136,plain,(
    k2_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_108,c_72])).

tff(c_217,plain,(
    k2_struct_0('#skF_4') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_136])).

tff(c_167,plain,(
    ! [C_114,B_115,A_116] :
      ( v5_relat_1(C_114,B_115)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_116,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_175,plain,(
    v5_relat_1('#skF_5',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_121,c_167])).

tff(c_224,plain,(
    v5_relat_1('#skF_5',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_175])).

tff(c_24,plain,(
    ! [B_30] :
      ( v2_funct_2(B_30,k2_relat_1(B_30))
      | ~ v5_relat_1(B_30,k2_relat_1(B_30))
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_239,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_224,c_24])).

tff(c_246,plain,(
    v2_funct_2('#skF_5',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_239])).

tff(c_191,plain,(
    ! [B_125,A_126] :
      ( k2_relat_1(B_125) = A_126
      | ~ v2_funct_2(B_125,A_126)
      | ~ v5_relat_1(B_125,A_126)
      | ~ v1_relat_1(B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_194,plain,
    ( k2_struct_0('#skF_4') = k2_relat_1('#skF_5')
    | ~ v2_funct_2('#skF_5',k2_struct_0('#skF_4'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_175,c_191])).

tff(c_197,plain,
    ( k2_struct_0('#skF_4') = k2_relat_1('#skF_5')
    | ~ v2_funct_2('#skF_5',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_194])).

tff(c_198,plain,(
    ~ v2_funct_2('#skF_5',k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_197])).

tff(c_223,plain,(
    ~ v2_funct_2('#skF_5',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_198])).

tff(c_258,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_223])).

tff(c_259,plain,(
    k2_struct_0('#skF_4') = k2_relat_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_265,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_121])).

tff(c_341,plain,(
    ! [A_137,B_138,C_139] :
      ( k1_relset_1(A_137,B_138,C_139) = k1_relat_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_349,plain,(
    k1_relset_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'),'#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_265,c_341])).

tff(c_74,plain,(
    k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_131,plain,(
    k1_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_108,c_74])).

tff(c_263,plain,(
    k1_relset_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'),'#skF_5') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_131])).

tff(c_351,plain,(
    k2_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_263])).

tff(c_151,plain,(
    ! [C_108,A_109,B_110] :
      ( v4_relat_1(C_108,A_109)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_159,plain,(
    v4_relat_1('#skF_5',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_121,c_151])).

tff(c_305,plain,(
    ! [B_135,A_136] :
      ( k1_relat_1(B_135) = A_136
      | ~ v1_partfun1(B_135,A_136)
      | ~ v4_relat_1(B_135,A_136)
      | ~ v1_relat_1(B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_308,plain,
    ( k2_struct_0('#skF_3') = k1_relat_1('#skF_5')
    | ~ v1_partfun1('#skF_5',k2_struct_0('#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_159,c_305])).

tff(c_311,plain,
    ( k2_struct_0('#skF_3') = k1_relat_1('#skF_5')
    | ~ v1_partfun1('#skF_5',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_308])).

tff(c_340,plain,(
    ~ v1_partfun1('#skF_5',k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_311])).

tff(c_357,plain,(
    ~ v1_partfun1('#skF_5',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_340])).

tff(c_362,plain,(
    v4_relat_1('#skF_5',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_159])).

tff(c_28,plain,(
    ! [B_32] :
      ( v1_partfun1(B_32,k1_relat_1(B_32))
      | ~ v4_relat_1(B_32,k1_relat_1(B_32))
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_373,plain,
    ( v1_partfun1('#skF_5',k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_362,c_28])).

tff(c_380,plain,(
    v1_partfun1('#skF_5',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_373])).

tff(c_391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_357,c_380])).

tff(c_392,plain,(
    k2_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_311])).

tff(c_82,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_111,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_82])).

tff(c_120,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_111])).

tff(c_266,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_120])).

tff(c_398,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_266])).

tff(c_395,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_265])).

tff(c_394,plain,(
    k1_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_392,c_263])).

tff(c_262,plain,(
    k2_relset_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_259,c_136])).

tff(c_396,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_262])).

tff(c_70,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_122,plain,(
    ! [A_103,B_104] :
      ( r1_tarski(A_103,B_104)
      | ~ m1_subset_1(A_103,k1_zfmisc_1(B_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_129,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_121,c_122])).

tff(c_264,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_129])).

tff(c_397,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_264])).

tff(c_400,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_109])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_90,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_267,plain,(
    u1_struct_0('#skF_4') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_108])).

tff(c_2004,plain,(
    ! [A_424,B_425,C_426] :
      ( m1_subset_1('#skF_2'(A_424,B_425,C_426),k1_zfmisc_1(u1_struct_0(A_424)))
      | v3_tops_2(C_426,A_424,B_425)
      | ~ v2_funct_1(C_426)
      | k2_relset_1(u1_struct_0(A_424),u1_struct_0(B_425),C_426) != k2_struct_0(B_425)
      | k1_relset_1(u1_struct_0(A_424),u1_struct_0(B_425),C_426) != k2_struct_0(A_424)
      | ~ m1_subset_1(C_426,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_424),u1_struct_0(B_425))))
      | ~ v1_funct_2(C_426,u1_struct_0(A_424),u1_struct_0(B_425))
      | ~ v1_funct_1(C_426)
      | ~ l1_pre_topc(B_425)
      | v2_struct_0(B_425)
      | ~ l1_pre_topc(A_424) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2015,plain,(
    ! [A_424,C_426] :
      ( m1_subset_1('#skF_2'(A_424,'#skF_4',C_426),k1_zfmisc_1(u1_struct_0(A_424)))
      | v3_tops_2(C_426,A_424,'#skF_4')
      | ~ v2_funct_1(C_426)
      | k2_relset_1(u1_struct_0(A_424),u1_struct_0('#skF_4'),C_426) != k2_struct_0('#skF_4')
      | k1_relset_1(u1_struct_0(A_424),u1_struct_0('#skF_4'),C_426) != k2_struct_0(A_424)
      | ~ m1_subset_1(C_426,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_424),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_426,u1_struct_0(A_424),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_426)
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_424) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_2004])).

tff(c_2027,plain,(
    ! [A_424,C_426] :
      ( m1_subset_1('#skF_2'(A_424,'#skF_4',C_426),k1_zfmisc_1(u1_struct_0(A_424)))
      | v3_tops_2(C_426,A_424,'#skF_4')
      | ~ v2_funct_1(C_426)
      | k2_relset_1(u1_struct_0(A_424),k2_relat_1('#skF_5'),C_426) != k2_relat_1('#skF_5')
      | k1_relset_1(u1_struct_0(A_424),k2_relat_1('#skF_5'),C_426) != k2_struct_0(A_424)
      | ~ m1_subset_1(C_426,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_424),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_426,u1_struct_0(A_424),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(C_426)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_424) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_267,c_267,c_259,c_267,c_2015])).

tff(c_2085,plain,(
    ! [A_432,C_433] :
      ( m1_subset_1('#skF_2'(A_432,'#skF_4',C_433),k1_zfmisc_1(u1_struct_0(A_432)))
      | v3_tops_2(C_433,A_432,'#skF_4')
      | ~ v2_funct_1(C_433)
      | k2_relset_1(u1_struct_0(A_432),k2_relat_1('#skF_5'),C_433) != k2_relat_1('#skF_5')
      | k1_relset_1(u1_struct_0(A_432),k2_relat_1('#skF_5'),C_433) != k2_struct_0(A_432)
      | ~ m1_subset_1(C_433,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_432),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_433,u1_struct_0(A_432),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(C_433)
      | ~ l1_pre_topc(A_432) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2027])).

tff(c_2772,plain,(
    ! [A_553,A_554] :
      ( m1_subset_1('#skF_2'(A_553,'#skF_4',A_554),k1_zfmisc_1(u1_struct_0(A_553)))
      | v3_tops_2(A_554,A_553,'#skF_4')
      | ~ v2_funct_1(A_554)
      | k2_relset_1(u1_struct_0(A_553),k2_relat_1('#skF_5'),A_554) != k2_relat_1('#skF_5')
      | k1_relset_1(u1_struct_0(A_553),k2_relat_1('#skF_5'),A_554) != k2_struct_0(A_553)
      | ~ v1_funct_2(A_554,u1_struct_0(A_553),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(A_554)
      | ~ l1_pre_topc(A_553)
      | ~ r1_tarski(A_554,k2_zfmisc_1(u1_struct_0(A_553),k2_relat_1('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_2085])).

tff(c_2780,plain,(
    ! [A_554] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_4',A_554),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v3_tops_2(A_554,'#skF_3','#skF_4')
      | ~ v2_funct_1(A_554)
      | k2_relset_1(u1_struct_0('#skF_3'),k2_relat_1('#skF_5'),A_554) != k2_relat_1('#skF_5')
      | k1_relset_1(u1_struct_0('#skF_3'),k2_relat_1('#skF_5'),A_554) != k2_struct_0('#skF_3')
      | ~ v1_funct_2(A_554,u1_struct_0('#skF_3'),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(A_554)
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_554,k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_2772])).

tff(c_3969,plain,(
    ! [A_712] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_4',A_712),k1_zfmisc_1(k1_relat_1('#skF_5')))
      | v3_tops_2(A_712,'#skF_3','#skF_4')
      | ~ v2_funct_1(A_712)
      | k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),A_712) != k2_relat_1('#skF_5')
      | k1_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),A_712) != k1_relat_1('#skF_5')
      | ~ v1_funct_2(A_712,k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(A_712)
      | ~ r1_tarski(A_712,k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_400,c_400,c_392,c_400,c_400,c_2780])).

tff(c_3984,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k1_relat_1('#skF_5')))
    | v3_tops_2('#skF_5','#skF_3','#skF_4')
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') != k2_relat_1('#skF_5')
    | k1_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') != k1_relat_1('#skF_5')
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_397,c_3969])).

tff(c_3990,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k1_relat_1('#skF_5')))
    | v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_398,c_394,c_396,c_70,c_3984])).

tff(c_3991,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k1_relat_1('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3990])).

tff(c_68,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_522,plain,(
    ! [A_164,B_165,C_166,D_167] :
      ( k7_relset_1(A_164,B_165,C_166,D_167) = k9_relat_1(C_166,D_167)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_528,plain,(
    ! [D_167] : k7_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5',D_167) = k9_relat_1('#skF_5',D_167) ),
    inference(resolution,[status(thm)],[c_395,c_522])).

tff(c_94,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_78,plain,(
    v1_compts_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_88,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_76,plain,(
    v8_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_2210,plain,(
    ! [A_445,B_446,C_447,D_448] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0(A_445),u1_struct_0(B_446),C_447,D_448),B_446)
      | ~ v4_pre_topc(D_448,A_445)
      | ~ m1_subset_1(D_448,k1_zfmisc_1(u1_struct_0(A_445)))
      | ~ v5_pre_topc(C_447,A_445,B_446)
      | k2_relset_1(u1_struct_0(A_445),u1_struct_0(B_446),C_447) != k2_struct_0(B_446)
      | ~ v8_pre_topc(B_446)
      | ~ v1_compts_1(A_445)
      | ~ m1_subset_1(C_447,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_445),u1_struct_0(B_446))))
      | ~ v1_funct_2(C_447,u1_struct_0(A_445),u1_struct_0(B_446))
      | ~ v1_funct_1(C_447)
      | ~ l1_pre_topc(B_446)
      | ~ v2_pre_topc(B_446)
      | v2_struct_0(B_446)
      | ~ l1_pre_topc(A_445)
      | ~ v2_pre_topc(A_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_2221,plain,(
    ! [A_445,C_447,D_448] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0(A_445),u1_struct_0('#skF_4'),C_447,D_448),'#skF_4')
      | ~ v4_pre_topc(D_448,A_445)
      | ~ m1_subset_1(D_448,k1_zfmisc_1(u1_struct_0(A_445)))
      | ~ v5_pre_topc(C_447,A_445,'#skF_4')
      | k2_relset_1(u1_struct_0(A_445),u1_struct_0('#skF_4'),C_447) != k2_struct_0('#skF_4')
      | ~ v8_pre_topc('#skF_4')
      | ~ v1_compts_1(A_445)
      | ~ m1_subset_1(C_447,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_445),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_447,u1_struct_0(A_445),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_447)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_445)
      | ~ v2_pre_topc(A_445) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_2210])).

tff(c_2233,plain,(
    ! [A_445,C_447,D_448] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0(A_445),k2_relat_1('#skF_5'),C_447,D_448),'#skF_4')
      | ~ v4_pre_topc(D_448,A_445)
      | ~ m1_subset_1(D_448,k1_zfmisc_1(u1_struct_0(A_445)))
      | ~ v5_pre_topc(C_447,A_445,'#skF_4')
      | k2_relset_1(u1_struct_0(A_445),k2_relat_1('#skF_5'),C_447) != k2_relat_1('#skF_5')
      | ~ v1_compts_1(A_445)
      | ~ m1_subset_1(C_447,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_445),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_447,u1_struct_0(A_445),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(C_447)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_445)
      | ~ v2_pre_topc(A_445) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_267,c_76,c_259,c_267,c_267,c_2221])).

tff(c_2302,plain,(
    ! [A_455,C_456,D_457] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0(A_455),k2_relat_1('#skF_5'),C_456,D_457),'#skF_4')
      | ~ v4_pre_topc(D_457,A_455)
      | ~ m1_subset_1(D_457,k1_zfmisc_1(u1_struct_0(A_455)))
      | ~ v5_pre_topc(C_456,A_455,'#skF_4')
      | k2_relset_1(u1_struct_0(A_455),k2_relat_1('#skF_5'),C_456) != k2_relat_1('#skF_5')
      | ~ v1_compts_1(A_455)
      | ~ m1_subset_1(C_456,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_455),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_456,u1_struct_0(A_455),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(C_456)
      | ~ l1_pre_topc(A_455)
      | ~ v2_pre_topc(A_455) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2233])).

tff(c_2919,plain,(
    ! [A_578,A_579,D_580] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0(A_578),k2_relat_1('#skF_5'),A_579,D_580),'#skF_4')
      | ~ v4_pre_topc(D_580,A_578)
      | ~ m1_subset_1(D_580,k1_zfmisc_1(u1_struct_0(A_578)))
      | ~ v5_pre_topc(A_579,A_578,'#skF_4')
      | k2_relset_1(u1_struct_0(A_578),k2_relat_1('#skF_5'),A_579) != k2_relat_1('#skF_5')
      | ~ v1_compts_1(A_578)
      | ~ v1_funct_2(A_579,u1_struct_0(A_578),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(A_579)
      | ~ l1_pre_topc(A_578)
      | ~ v2_pre_topc(A_578)
      | ~ r1_tarski(A_579,k2_zfmisc_1(u1_struct_0(A_578),k2_relat_1('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_2302])).

tff(c_2928,plain,(
    ! [A_579,D_580] :
      ( v4_pre_topc(k7_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),A_579,D_580),'#skF_4')
      | ~ v4_pre_topc(D_580,'#skF_3')
      | ~ m1_subset_1(D_580,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v5_pre_topc(A_579,'#skF_3','#skF_4')
      | k2_relset_1(u1_struct_0('#skF_3'),k2_relat_1('#skF_5'),A_579) != k2_relat_1('#skF_5')
      | ~ v1_compts_1('#skF_3')
      | ~ v1_funct_2(A_579,u1_struct_0('#skF_3'),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(A_579)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ r1_tarski(A_579,k2_zfmisc_1(u1_struct_0('#skF_3'),k2_relat_1('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_2919])).

tff(c_3213,plain,(
    ! [A_648,D_649] :
      ( v4_pre_topc(k7_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),A_648,D_649),'#skF_4')
      | ~ v4_pre_topc(D_649,'#skF_3')
      | ~ m1_subset_1(D_649,k1_zfmisc_1(k1_relat_1('#skF_5')))
      | ~ v5_pre_topc(A_648,'#skF_3','#skF_4')
      | k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),A_648) != k2_relat_1('#skF_5')
      | ~ v1_funct_2(A_648,k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(A_648)
      | ~ r1_tarski(A_648,k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_94,c_92,c_400,c_78,c_400,c_400,c_2928])).

tff(c_3218,plain,(
    ! [D_167] :
      ( v4_pre_topc(k9_relat_1('#skF_5',D_167),'#skF_4')
      | ~ v4_pre_topc(D_167,'#skF_3')
      | ~ m1_subset_1(D_167,k1_zfmisc_1(k1_relat_1('#skF_5')))
      | ~ v5_pre_topc('#skF_5','#skF_3','#skF_4')
      | k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') != k2_relat_1('#skF_5')
      | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ r1_tarski('#skF_5',k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_528,c_3213])).

tff(c_3221,plain,(
    ! [D_167] :
      ( v4_pre_topc(k9_relat_1('#skF_5',D_167),'#skF_4')
      | ~ v4_pre_topc(D_167,'#skF_3')
      | ~ m1_subset_1(D_167,k1_zfmisc_1(k1_relat_1('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_84,c_398,c_396,c_68,c_3218])).

tff(c_3998,plain,
    ( v4_pre_topc(k9_relat_1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | ~ v4_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_3991,c_3221])).

tff(c_4056,plain,(
    ~ v4_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3998])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3999,plain,(
    r1_tarski('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_3991,c_2])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k10_relat_1(B_4,k9_relat_1(B_4,A_3)) = A_3
      | ~ v2_funct_1(B_4)
      | ~ r1_tarski(A_3,k1_relat_1(B_4))
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4040,plain,
    ( k10_relat_1('#skF_5',k9_relat_1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) = '#skF_2'('#skF_3','#skF_4','#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3999,c_6])).

tff(c_4043,plain,(
    k10_relat_1('#skF_5',k9_relat_1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) = '#skF_2'('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_84,c_70,c_4040])).

tff(c_544,plain,(
    ! [A_173,B_174,C_175,D_176] :
      ( m1_subset_1(k7_relset_1(A_173,B_174,C_175,D_176),k1_zfmisc_1(B_174))
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_576,plain,(
    ! [D_167] :
      ( m1_subset_1(k9_relat_1('#skF_5',D_167),k1_zfmisc_1(k2_relat_1('#skF_5')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_528,c_544])).

tff(c_586,plain,(
    ! [D_167] : m1_subset_1(k9_relat_1('#skF_5',D_167),k1_zfmisc_1(k2_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_576])).

tff(c_500,plain,(
    ! [A_155,B_156,C_157,D_158] :
      ( k8_relset_1(A_155,B_156,C_157,D_158) = k10_relat_1(C_157,D_158)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_506,plain,(
    ! [D_158] : k8_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5',D_158) = k10_relat_1('#skF_5',D_158) ),
    inference(resolution,[status(thm)],[c_395,c_500])).

tff(c_1506,plain,(
    ! [A_370,B_371,C_372,D_373] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_370),u1_struct_0(B_371),C_372,D_373),A_370)
      | ~ v4_pre_topc(D_373,B_371)
      | ~ m1_subset_1(D_373,k1_zfmisc_1(u1_struct_0(B_371)))
      | ~ v5_pre_topc(C_372,A_370,B_371)
      | ~ m1_subset_1(C_372,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_370),u1_struct_0(B_371))))
      | ~ v1_funct_2(C_372,u1_struct_0(A_370),u1_struct_0(B_371))
      | ~ v1_funct_1(C_372)
      | ~ l1_pre_topc(B_371)
      | ~ l1_pre_topc(A_370) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2606,plain,(
    ! [A_521,B_522,A_523,D_524] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_521),u1_struct_0(B_522),A_523,D_524),A_521)
      | ~ v4_pre_topc(D_524,B_522)
      | ~ m1_subset_1(D_524,k1_zfmisc_1(u1_struct_0(B_522)))
      | ~ v5_pre_topc(A_523,A_521,B_522)
      | ~ v1_funct_2(A_523,u1_struct_0(A_521),u1_struct_0(B_522))
      | ~ v1_funct_1(A_523)
      | ~ l1_pre_topc(B_522)
      | ~ l1_pre_topc(A_521)
      | ~ r1_tarski(A_523,k2_zfmisc_1(u1_struct_0(A_521),u1_struct_0(B_522))) ) ),
    inference(resolution,[status(thm)],[c_4,c_1506])).

tff(c_2613,plain,(
    ! [B_522,A_523,D_524] :
      ( v4_pre_topc(k8_relset_1(k1_relat_1('#skF_5'),u1_struct_0(B_522),A_523,D_524),'#skF_3')
      | ~ v4_pre_topc(D_524,B_522)
      | ~ m1_subset_1(D_524,k1_zfmisc_1(u1_struct_0(B_522)))
      | ~ v5_pre_topc(A_523,'#skF_3',B_522)
      | ~ v1_funct_2(A_523,u1_struct_0('#skF_3'),u1_struct_0(B_522))
      | ~ v1_funct_1(A_523)
      | ~ l1_pre_topc(B_522)
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_523,k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_522))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_2606])).

tff(c_2632,plain,(
    ! [B_525,A_526,D_527] :
      ( v4_pre_topc(k8_relset_1(k1_relat_1('#skF_5'),u1_struct_0(B_525),A_526,D_527),'#skF_3')
      | ~ v4_pre_topc(D_527,B_525)
      | ~ m1_subset_1(D_527,k1_zfmisc_1(u1_struct_0(B_525)))
      | ~ v5_pre_topc(A_526,'#skF_3',B_525)
      | ~ v1_funct_2(A_526,k1_relat_1('#skF_5'),u1_struct_0(B_525))
      | ~ v1_funct_1(A_526)
      | ~ l1_pre_topc(B_525)
      | ~ r1_tarski(A_526,k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0(B_525))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_92,c_400,c_2613])).

tff(c_2642,plain,(
    ! [A_526,D_527] :
      ( v4_pre_topc(k8_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),A_526,D_527),'#skF_3')
      | ~ v4_pre_topc(D_527,'#skF_4')
      | ~ m1_subset_1(D_527,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v5_pre_topc(A_526,'#skF_3','#skF_4')
      | ~ v1_funct_2(A_526,k1_relat_1('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(A_526)
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_526,k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_2632])).

tff(c_2654,plain,(
    ! [A_530,D_531] :
      ( v4_pre_topc(k8_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),A_530,D_531),'#skF_3')
      | ~ v4_pre_topc(D_531,'#skF_4')
      | ~ m1_subset_1(D_531,k1_zfmisc_1(k2_relat_1('#skF_5')))
      | ~ v5_pre_topc(A_530,'#skF_3','#skF_4')
      | ~ v1_funct_2(A_530,k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(A_530)
      | ~ r1_tarski(A_530,k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_86,c_267,c_267,c_2642])).

tff(c_2661,plain,(
    ! [D_158] :
      ( v4_pre_topc(k10_relat_1('#skF_5',D_158),'#skF_3')
      | ~ v4_pre_topc(D_158,'#skF_4')
      | ~ m1_subset_1(D_158,k1_zfmisc_1(k2_relat_1('#skF_5')))
      | ~ v5_pre_topc('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ r1_tarski('#skF_5',k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_2654])).

tff(c_2684,plain,(
    ! [D_535] :
      ( v4_pre_topc(k10_relat_1('#skF_5',D_535),'#skF_3')
      | ~ v4_pre_topc(D_535,'#skF_4')
      | ~ m1_subset_1(D_535,k1_zfmisc_1(k2_relat_1('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_84,c_398,c_68,c_2661])).

tff(c_2696,plain,(
    ! [D_167] :
      ( v4_pre_topc(k10_relat_1('#skF_5',k9_relat_1('#skF_5',D_167)),'#skF_3')
      | ~ v4_pre_topc(k9_relat_1('#skF_5',D_167),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_586,c_2684])).

tff(c_4050,plain,
    ( v4_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ v4_pre_topc(k9_relat_1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4043,c_2696])).

tff(c_4094,plain,(
    ~ v4_pre_topc(k9_relat_1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_4056,c_4050])).

tff(c_2505,plain,(
    ! [A_493,B_494,C_495] :
      ( v4_pre_topc('#skF_2'(A_493,B_494,C_495),A_493)
      | v4_pre_topc(k7_relset_1(u1_struct_0(A_493),u1_struct_0(B_494),C_495,'#skF_2'(A_493,B_494,C_495)),B_494)
      | v3_tops_2(C_495,A_493,B_494)
      | ~ v2_funct_1(C_495)
      | k2_relset_1(u1_struct_0(A_493),u1_struct_0(B_494),C_495) != k2_struct_0(B_494)
      | k1_relset_1(u1_struct_0(A_493),u1_struct_0(B_494),C_495) != k2_struct_0(A_493)
      | ~ m1_subset_1(C_495,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_493),u1_struct_0(B_494))))
      | ~ v1_funct_2(C_495,u1_struct_0(A_493),u1_struct_0(B_494))
      | ~ v1_funct_1(C_495)
      | ~ l1_pre_topc(B_494)
      | v2_struct_0(B_494)
      | ~ l1_pre_topc(A_493) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2522,plain,(
    ! [A_493,C_495] :
      ( v4_pre_topc('#skF_2'(A_493,'#skF_4',C_495),A_493)
      | v4_pre_topc(k7_relset_1(u1_struct_0(A_493),k2_relat_1('#skF_5'),C_495,'#skF_2'(A_493,'#skF_4',C_495)),'#skF_4')
      | v3_tops_2(C_495,A_493,'#skF_4')
      | ~ v2_funct_1(C_495)
      | k2_relset_1(u1_struct_0(A_493),u1_struct_0('#skF_4'),C_495) != k2_struct_0('#skF_4')
      | k1_relset_1(u1_struct_0(A_493),u1_struct_0('#skF_4'),C_495) != k2_struct_0(A_493)
      | ~ m1_subset_1(C_495,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_493),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_495,u1_struct_0(A_493),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_495)
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_493) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_2505])).

tff(c_2532,plain,(
    ! [A_493,C_495] :
      ( v4_pre_topc('#skF_2'(A_493,'#skF_4',C_495),A_493)
      | v4_pre_topc(k7_relset_1(u1_struct_0(A_493),k2_relat_1('#skF_5'),C_495,'#skF_2'(A_493,'#skF_4',C_495)),'#skF_4')
      | v3_tops_2(C_495,A_493,'#skF_4')
      | ~ v2_funct_1(C_495)
      | k2_relset_1(u1_struct_0(A_493),k2_relat_1('#skF_5'),C_495) != k2_relat_1('#skF_5')
      | k1_relset_1(u1_struct_0(A_493),k2_relat_1('#skF_5'),C_495) != k2_struct_0(A_493)
      | ~ m1_subset_1(C_495,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_493),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_495,u1_struct_0(A_493),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(C_495)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_493) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_267,c_267,c_267,c_259,c_267,c_2522])).

tff(c_2551,plain,(
    ! [A_502,C_503] :
      ( v4_pre_topc('#skF_2'(A_502,'#skF_4',C_503),A_502)
      | v4_pre_topc(k7_relset_1(u1_struct_0(A_502),k2_relat_1('#skF_5'),C_503,'#skF_2'(A_502,'#skF_4',C_503)),'#skF_4')
      | v3_tops_2(C_503,A_502,'#skF_4')
      | ~ v2_funct_1(C_503)
      | k2_relset_1(u1_struct_0(A_502),k2_relat_1('#skF_5'),C_503) != k2_relat_1('#skF_5')
      | k1_relset_1(u1_struct_0(A_502),k2_relat_1('#skF_5'),C_503) != k2_struct_0(A_502)
      | ~ m1_subset_1(C_503,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_502),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_503,u1_struct_0(A_502),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(C_503)
      | ~ l1_pre_topc(A_502) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2532])).

tff(c_2559,plain,(
    ! [C_503] :
      ( v4_pre_topc('#skF_2'('#skF_3','#skF_4',C_503),'#skF_3')
      | v4_pre_topc(k7_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),C_503,'#skF_2'('#skF_3','#skF_4',C_503)),'#skF_4')
      | v3_tops_2(C_503,'#skF_3','#skF_4')
      | ~ v2_funct_1(C_503)
      | k2_relset_1(u1_struct_0('#skF_3'),k2_relat_1('#skF_5'),C_503) != k2_relat_1('#skF_5')
      | k1_relset_1(u1_struct_0('#skF_3'),k2_relat_1('#skF_5'),C_503) != k2_struct_0('#skF_3')
      | ~ m1_subset_1(C_503,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_503,u1_struct_0('#skF_3'),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(C_503)
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_2551])).

tff(c_9558,plain,(
    ! [C_1169] :
      ( v4_pre_topc('#skF_2'('#skF_3','#skF_4',C_1169),'#skF_3')
      | v4_pre_topc(k7_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),C_1169,'#skF_2'('#skF_3','#skF_4',C_1169)),'#skF_4')
      | v3_tops_2(C_1169,'#skF_3','#skF_4')
      | ~ v2_funct_1(C_1169)
      | k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),C_1169) != k2_relat_1('#skF_5')
      | k1_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),C_1169) != k1_relat_1('#skF_5')
      | ~ m1_subset_1(C_1169,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_1169,k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(C_1169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_400,c_400,c_400,c_392,c_400,c_2559])).

tff(c_9575,plain,
    ( v4_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v4_pre_topc(k9_relat_1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | v3_tops_2('#skF_5','#skF_3','#skF_4')
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') != k2_relat_1('#skF_5')
    | k1_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') != k1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))))
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_528,c_9558])).

tff(c_9579,plain,
    ( v4_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v4_pre_topc(k9_relat_1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_398,c_395,c_394,c_396,c_70,c_9575])).

tff(c_9581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_4094,c_4056,c_9579])).

tff(c_9583,plain,(
    v4_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_3998])).

tff(c_9582,plain,(
    v4_pre_topc(k9_relat_1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_3998])).

tff(c_2428,plain,(
    ! [A_473,B_474,C_475] :
      ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(A_473),u1_struct_0(B_474),C_475,'#skF_2'(A_473,B_474,C_475)),B_474)
      | ~ v4_pre_topc('#skF_2'(A_473,B_474,C_475),A_473)
      | v3_tops_2(C_475,A_473,B_474)
      | ~ v2_funct_1(C_475)
      | k2_relset_1(u1_struct_0(A_473),u1_struct_0(B_474),C_475) != k2_struct_0(B_474)
      | k1_relset_1(u1_struct_0(A_473),u1_struct_0(B_474),C_475) != k2_struct_0(A_473)
      | ~ m1_subset_1(C_475,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_473),u1_struct_0(B_474))))
      | ~ v1_funct_2(C_475,u1_struct_0(A_473),u1_struct_0(B_474))
      | ~ v1_funct_1(C_475)
      | ~ l1_pre_topc(B_474)
      | v2_struct_0(B_474)
      | ~ l1_pre_topc(A_473) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2440,plain,(
    ! [A_473,C_475] :
      ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(A_473),k2_relat_1('#skF_5'),C_475,'#skF_2'(A_473,'#skF_4',C_475)),'#skF_4')
      | ~ v4_pre_topc('#skF_2'(A_473,'#skF_4',C_475),A_473)
      | v3_tops_2(C_475,A_473,'#skF_4')
      | ~ v2_funct_1(C_475)
      | k2_relset_1(u1_struct_0(A_473),u1_struct_0('#skF_4'),C_475) != k2_struct_0('#skF_4')
      | k1_relset_1(u1_struct_0(A_473),u1_struct_0('#skF_4'),C_475) != k2_struct_0(A_473)
      | ~ m1_subset_1(C_475,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_473),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_475,u1_struct_0(A_473),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_475)
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_473) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_2428])).

tff(c_2448,plain,(
    ! [A_473,C_475] :
      ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(A_473),k2_relat_1('#skF_5'),C_475,'#skF_2'(A_473,'#skF_4',C_475)),'#skF_4')
      | ~ v4_pre_topc('#skF_2'(A_473,'#skF_4',C_475),A_473)
      | v3_tops_2(C_475,A_473,'#skF_4')
      | ~ v2_funct_1(C_475)
      | k2_relset_1(u1_struct_0(A_473),k2_relat_1('#skF_5'),C_475) != k2_relat_1('#skF_5')
      | k1_relset_1(u1_struct_0(A_473),k2_relat_1('#skF_5'),C_475) != k2_struct_0(A_473)
      | ~ m1_subset_1(C_475,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_473),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_475,u1_struct_0(A_473),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(C_475)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_473) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_267,c_267,c_267,c_259,c_267,c_2440])).

tff(c_2469,plain,(
    ! [A_484,C_485] :
      ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(A_484),k2_relat_1('#skF_5'),C_485,'#skF_2'(A_484,'#skF_4',C_485)),'#skF_4')
      | ~ v4_pre_topc('#skF_2'(A_484,'#skF_4',C_485),A_484)
      | v3_tops_2(C_485,A_484,'#skF_4')
      | ~ v2_funct_1(C_485)
      | k2_relset_1(u1_struct_0(A_484),k2_relat_1('#skF_5'),C_485) != k2_relat_1('#skF_5')
      | k1_relset_1(u1_struct_0(A_484),k2_relat_1('#skF_5'),C_485) != k2_struct_0(A_484)
      | ~ m1_subset_1(C_485,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_484),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_485,u1_struct_0(A_484),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(C_485)
      | ~ l1_pre_topc(A_484) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2448])).

tff(c_2472,plain,(
    ! [C_485] :
      ( ~ v4_pre_topc(k7_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),C_485,'#skF_2'('#skF_3','#skF_4',C_485)),'#skF_4')
      | ~ v4_pre_topc('#skF_2'('#skF_3','#skF_4',C_485),'#skF_3')
      | v3_tops_2(C_485,'#skF_3','#skF_4')
      | ~ v2_funct_1(C_485)
      | k2_relset_1(u1_struct_0('#skF_3'),k2_relat_1('#skF_5'),C_485) != k2_relat_1('#skF_5')
      | k1_relset_1(u1_struct_0('#skF_3'),k2_relat_1('#skF_5'),C_485) != k2_struct_0('#skF_3')
      | ~ m1_subset_1(C_485,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_485,u1_struct_0('#skF_3'),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(C_485)
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_2469])).

tff(c_15008,plain,(
    ! [C_1611] :
      ( ~ v4_pre_topc(k7_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),C_1611,'#skF_2'('#skF_3','#skF_4',C_1611)),'#skF_4')
      | ~ v4_pre_topc('#skF_2'('#skF_3','#skF_4',C_1611),'#skF_3')
      | v3_tops_2(C_1611,'#skF_3','#skF_4')
      | ~ v2_funct_1(C_1611)
      | k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),C_1611) != k2_relat_1('#skF_5')
      | k1_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),C_1611) != k1_relat_1('#skF_5')
      | ~ m1_subset_1(C_1611,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_1611,k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(C_1611) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_400,c_400,c_400,c_392,c_400,c_2472])).

tff(c_15028,plain,
    ( ~ v4_pre_topc(k9_relat_1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | ~ v4_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v3_tops_2('#skF_5','#skF_3','#skF_4')
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') != k2_relat_1('#skF_5')
    | k1_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') != k1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))))
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_528,c_15008])).

tff(c_15032,plain,(
    v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_398,c_395,c_394,c_396,c_70,c_9583,c_9582,c_15028])).

tff(c_15034,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_15032])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:22:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.46/5.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.46/5.96  
% 13.46/5.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.46/5.96  %$ v5_pre_topc > v3_tops_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v4_pre_topc > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_struct_0 > v2_pre_topc > v2_funct_1 > v1_relat_1 > v1_funct_1 > v1_compts_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 13.46/5.96  
% 13.46/5.96  %Foreground sorts:
% 13.46/5.96  
% 13.46/5.96  
% 13.46/5.96  %Background operators:
% 13.46/5.96  
% 13.46/5.96  
% 13.46/5.96  %Foreground operators:
% 13.46/5.96  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 13.46/5.96  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 13.46/5.96  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 13.46/5.96  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 13.46/5.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.46/5.96  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 13.46/5.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.46/5.96  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 13.46/5.96  tff(v3_tops_2, type, v3_tops_2: ($i * $i * $i) > $o).
% 13.46/5.96  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 13.46/5.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.46/5.96  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.46/5.96  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 13.46/5.96  tff('#skF_5', type, '#skF_5': $i).
% 13.46/5.96  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.46/5.96  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 13.46/5.96  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 13.46/5.96  tff('#skF_3', type, '#skF_3': $i).
% 13.46/5.96  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 13.46/5.96  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 13.46/5.96  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 13.46/5.96  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 13.46/5.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.46/5.96  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 13.46/5.96  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 13.46/5.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.46/5.96  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 13.46/5.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.46/5.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.46/5.96  tff('#skF_4', type, '#skF_4': $i).
% 13.46/5.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.46/5.96  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 13.46/5.96  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 13.46/5.96  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 13.46/5.96  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 13.46/5.96  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 13.46/5.96  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 13.46/5.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.46/5.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.46/5.96  
% 13.46/5.99  tff(f_212, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => ((((((v1_compts_1(A) & v8_pre_topc(B)) & (k1_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(A))) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v2_funct_1(C)) & v5_pre_topc(C, A, B)) => v3_tops_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_compts_1)).
% 13.46/5.99  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 13.46/5.99  tff(f_110, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 13.46/5.99  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 13.46/5.99  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 13.46/5.99  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 13.46/5.99  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 13.46/5.99  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 13.46/5.99  tff(f_85, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 13.46/5.99  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 13.46/5.99  tff(f_144, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((~v2_struct_0(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) <=> ((((k1_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(A)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v2_funct_1(C)) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(D, A) <=> v4_pre_topc(k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_tops_2)).
% 13.46/5.99  tff(f_65, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 13.46/5.99  tff(f_178, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => ((((v1_compts_1(A) & v8_pre_topc(B)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v5_pre_topc(C, A, B)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(D, A) => v4_pre_topc(k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_compts_1)).
% 13.46/5.99  tff(f_39, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 13.46/5.99  tff(f_53, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 13.46/5.99  tff(f_69, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 13.46/5.99  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(D, B) => v4_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_pre_topc)).
% 13.46/5.99  tff(c_66, plain, (~v3_tops_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_212])).
% 13.46/5.99  tff(c_84, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_212])).
% 13.46/5.99  tff(c_92, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 13.46/5.99  tff(c_42, plain, (![A_56]: (l1_struct_0(A_56) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_114])).
% 13.46/5.99  tff(c_96, plain, (![A_99]: (u1_struct_0(A_99)=k2_struct_0(A_99) | ~l1_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_110])).
% 13.46/5.99  tff(c_101, plain, (![A_100]: (u1_struct_0(A_100)=k2_struct_0(A_100) | ~l1_pre_topc(A_100))), inference(resolution, [status(thm)], [c_42, c_96])).
% 13.46/5.99  tff(c_109, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_92, c_101])).
% 13.46/5.99  tff(c_86, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_212])).
% 13.46/5.99  tff(c_108, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_86, c_101])).
% 13.46/5.99  tff(c_80, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_212])).
% 13.46/5.99  tff(c_121, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_108, c_80])).
% 13.46/5.99  tff(c_141, plain, (![C_105, A_106, B_107]: (v1_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.46/5.99  tff(c_149, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_121, c_141])).
% 13.46/5.99  tff(c_207, plain, (![A_129, B_130, C_131]: (k2_relset_1(A_129, B_130, C_131)=k2_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.46/5.99  tff(c_215, plain, (k2_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_121, c_207])).
% 13.46/5.99  tff(c_72, plain, (k2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')=k2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_212])).
% 13.46/5.99  tff(c_136, plain, (k2_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_108, c_72])).
% 13.46/5.99  tff(c_217, plain, (k2_struct_0('#skF_4')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_136])).
% 13.46/5.99  tff(c_167, plain, (![C_114, B_115, A_116]: (v5_relat_1(C_114, B_115) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_116, B_115))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.46/5.99  tff(c_175, plain, (v5_relat_1('#skF_5', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_121, c_167])).
% 13.46/5.99  tff(c_224, plain, (v5_relat_1('#skF_5', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_175])).
% 13.46/5.99  tff(c_24, plain, (![B_30]: (v2_funct_2(B_30, k2_relat_1(B_30)) | ~v5_relat_1(B_30, k2_relat_1(B_30)) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.46/5.99  tff(c_239, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_224, c_24])).
% 13.46/5.99  tff(c_246, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_239])).
% 13.46/5.99  tff(c_191, plain, (![B_125, A_126]: (k2_relat_1(B_125)=A_126 | ~v2_funct_2(B_125, A_126) | ~v5_relat_1(B_125, A_126) | ~v1_relat_1(B_125))), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.46/5.99  tff(c_194, plain, (k2_struct_0('#skF_4')=k2_relat_1('#skF_5') | ~v2_funct_2('#skF_5', k2_struct_0('#skF_4')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_175, c_191])).
% 13.46/5.99  tff(c_197, plain, (k2_struct_0('#skF_4')=k2_relat_1('#skF_5') | ~v2_funct_2('#skF_5', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_194])).
% 13.46/5.99  tff(c_198, plain, (~v2_funct_2('#skF_5', k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_197])).
% 13.46/5.99  tff(c_223, plain, (~v2_funct_2('#skF_5', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_198])).
% 13.46/5.99  tff(c_258, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_246, c_223])).
% 13.46/5.99  tff(c_259, plain, (k2_struct_0('#skF_4')=k2_relat_1('#skF_5')), inference(splitRight, [status(thm)], [c_197])).
% 13.46/5.99  tff(c_265, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_259, c_121])).
% 13.46/5.99  tff(c_341, plain, (![A_137, B_138, C_139]: (k1_relset_1(A_137, B_138, C_139)=k1_relat_1(C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.46/5.99  tff(c_349, plain, (k1_relset_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'), '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_265, c_341])).
% 13.46/5.99  tff(c_74, plain, (k1_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')=k2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 13.46/5.99  tff(c_131, plain, (k1_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_108, c_74])).
% 13.46/5.99  tff(c_263, plain, (k1_relset_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'), '#skF_5')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_259, c_131])).
% 13.46/5.99  tff(c_351, plain, (k2_struct_0('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_349, c_263])).
% 13.46/5.99  tff(c_151, plain, (![C_108, A_109, B_110]: (v4_relat_1(C_108, A_109) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.46/5.99  tff(c_159, plain, (v4_relat_1('#skF_5', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_121, c_151])).
% 13.46/5.99  tff(c_305, plain, (![B_135, A_136]: (k1_relat_1(B_135)=A_136 | ~v1_partfun1(B_135, A_136) | ~v4_relat_1(B_135, A_136) | ~v1_relat_1(B_135))), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.46/5.99  tff(c_308, plain, (k2_struct_0('#skF_3')=k1_relat_1('#skF_5') | ~v1_partfun1('#skF_5', k2_struct_0('#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_159, c_305])).
% 13.46/5.99  tff(c_311, plain, (k2_struct_0('#skF_3')=k1_relat_1('#skF_5') | ~v1_partfun1('#skF_5', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_308])).
% 13.46/5.99  tff(c_340, plain, (~v1_partfun1('#skF_5', k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_311])).
% 13.46/5.99  tff(c_357, plain, (~v1_partfun1('#skF_5', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_351, c_340])).
% 13.46/5.99  tff(c_362, plain, (v4_relat_1('#skF_5', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_351, c_159])).
% 13.46/5.99  tff(c_28, plain, (![B_32]: (v1_partfun1(B_32, k1_relat_1(B_32)) | ~v4_relat_1(B_32, k1_relat_1(B_32)) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.46/5.99  tff(c_373, plain, (v1_partfun1('#skF_5', k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_362, c_28])).
% 13.46/5.99  tff(c_380, plain, (v1_partfun1('#skF_5', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_373])).
% 13.46/5.99  tff(c_391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_357, c_380])).
% 13.46/5.99  tff(c_392, plain, (k2_struct_0('#skF_3')=k1_relat_1('#skF_5')), inference(splitRight, [status(thm)], [c_311])).
% 13.46/5.99  tff(c_82, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_212])).
% 13.46/5.99  tff(c_111, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_82])).
% 13.46/5.99  tff(c_120, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_111])).
% 13.46/5.99  tff(c_266, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_259, c_120])).
% 13.46/5.99  tff(c_398, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_392, c_266])).
% 13.46/5.99  tff(c_395, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_392, c_265])).
% 13.46/5.99  tff(c_394, plain, (k1_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_392, c_392, c_263])).
% 13.46/5.99  tff(c_262, plain, (k2_relset_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'), '#skF_5')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_259, c_259, c_136])).
% 13.46/5.99  tff(c_396, plain, (k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_392, c_262])).
% 13.46/5.99  tff(c_70, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_212])).
% 13.46/5.99  tff(c_122, plain, (![A_103, B_104]: (r1_tarski(A_103, B_104) | ~m1_subset_1(A_103, k1_zfmisc_1(B_104)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.46/5.99  tff(c_129, plain, (r1_tarski('#skF_5', k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_121, c_122])).
% 13.46/5.99  tff(c_264, plain, (r1_tarski('#skF_5', k2_zfmisc_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_259, c_129])).
% 13.46/5.99  tff(c_397, plain, (r1_tarski('#skF_5', k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_392, c_264])).
% 13.46/5.99  tff(c_400, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_392, c_109])).
% 13.46/5.99  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.46/5.99  tff(c_90, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_212])).
% 13.46/5.99  tff(c_267, plain, (u1_struct_0('#skF_4')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_259, c_108])).
% 13.46/5.99  tff(c_2004, plain, (![A_424, B_425, C_426]: (m1_subset_1('#skF_2'(A_424, B_425, C_426), k1_zfmisc_1(u1_struct_0(A_424))) | v3_tops_2(C_426, A_424, B_425) | ~v2_funct_1(C_426) | k2_relset_1(u1_struct_0(A_424), u1_struct_0(B_425), C_426)!=k2_struct_0(B_425) | k1_relset_1(u1_struct_0(A_424), u1_struct_0(B_425), C_426)!=k2_struct_0(A_424) | ~m1_subset_1(C_426, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_424), u1_struct_0(B_425)))) | ~v1_funct_2(C_426, u1_struct_0(A_424), u1_struct_0(B_425)) | ~v1_funct_1(C_426) | ~l1_pre_topc(B_425) | v2_struct_0(B_425) | ~l1_pre_topc(A_424))), inference(cnfTransformation, [status(thm)], [f_144])).
% 13.46/5.99  tff(c_2015, plain, (![A_424, C_426]: (m1_subset_1('#skF_2'(A_424, '#skF_4', C_426), k1_zfmisc_1(u1_struct_0(A_424))) | v3_tops_2(C_426, A_424, '#skF_4') | ~v2_funct_1(C_426) | k2_relset_1(u1_struct_0(A_424), u1_struct_0('#skF_4'), C_426)!=k2_struct_0('#skF_4') | k1_relset_1(u1_struct_0(A_424), u1_struct_0('#skF_4'), C_426)!=k2_struct_0(A_424) | ~m1_subset_1(C_426, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_424), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_426, u1_struct_0(A_424), u1_struct_0('#skF_4')) | ~v1_funct_1(C_426) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_424))), inference(superposition, [status(thm), theory('equality')], [c_267, c_2004])).
% 13.46/5.99  tff(c_2027, plain, (![A_424, C_426]: (m1_subset_1('#skF_2'(A_424, '#skF_4', C_426), k1_zfmisc_1(u1_struct_0(A_424))) | v3_tops_2(C_426, A_424, '#skF_4') | ~v2_funct_1(C_426) | k2_relset_1(u1_struct_0(A_424), k2_relat_1('#skF_5'), C_426)!=k2_relat_1('#skF_5') | k1_relset_1(u1_struct_0(A_424), k2_relat_1('#skF_5'), C_426)!=k2_struct_0(A_424) | ~m1_subset_1(C_426, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_424), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_426, u1_struct_0(A_424), k2_relat_1('#skF_5')) | ~v1_funct_1(C_426) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_424))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_267, c_267, c_259, c_267, c_2015])).
% 13.46/5.99  tff(c_2085, plain, (![A_432, C_433]: (m1_subset_1('#skF_2'(A_432, '#skF_4', C_433), k1_zfmisc_1(u1_struct_0(A_432))) | v3_tops_2(C_433, A_432, '#skF_4') | ~v2_funct_1(C_433) | k2_relset_1(u1_struct_0(A_432), k2_relat_1('#skF_5'), C_433)!=k2_relat_1('#skF_5') | k1_relset_1(u1_struct_0(A_432), k2_relat_1('#skF_5'), C_433)!=k2_struct_0(A_432) | ~m1_subset_1(C_433, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_432), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_433, u1_struct_0(A_432), k2_relat_1('#skF_5')) | ~v1_funct_1(C_433) | ~l1_pre_topc(A_432))), inference(negUnitSimplification, [status(thm)], [c_90, c_2027])).
% 13.46/5.99  tff(c_2772, plain, (![A_553, A_554]: (m1_subset_1('#skF_2'(A_553, '#skF_4', A_554), k1_zfmisc_1(u1_struct_0(A_553))) | v3_tops_2(A_554, A_553, '#skF_4') | ~v2_funct_1(A_554) | k2_relset_1(u1_struct_0(A_553), k2_relat_1('#skF_5'), A_554)!=k2_relat_1('#skF_5') | k1_relset_1(u1_struct_0(A_553), k2_relat_1('#skF_5'), A_554)!=k2_struct_0(A_553) | ~v1_funct_2(A_554, u1_struct_0(A_553), k2_relat_1('#skF_5')) | ~v1_funct_1(A_554) | ~l1_pre_topc(A_553) | ~r1_tarski(A_554, k2_zfmisc_1(u1_struct_0(A_553), k2_relat_1('#skF_5'))))), inference(resolution, [status(thm)], [c_4, c_2085])).
% 13.46/5.99  tff(c_2780, plain, (![A_554]: (m1_subset_1('#skF_2'('#skF_3', '#skF_4', A_554), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v3_tops_2(A_554, '#skF_3', '#skF_4') | ~v2_funct_1(A_554) | k2_relset_1(u1_struct_0('#skF_3'), k2_relat_1('#skF_5'), A_554)!=k2_relat_1('#skF_5') | k1_relset_1(u1_struct_0('#skF_3'), k2_relat_1('#skF_5'), A_554)!=k2_struct_0('#skF_3') | ~v1_funct_2(A_554, u1_struct_0('#skF_3'), k2_relat_1('#skF_5')) | ~v1_funct_1(A_554) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_554, k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_400, c_2772])).
% 13.46/5.99  tff(c_3969, plain, (![A_712]: (m1_subset_1('#skF_2'('#skF_3', '#skF_4', A_712), k1_zfmisc_1(k1_relat_1('#skF_5'))) | v3_tops_2(A_712, '#skF_3', '#skF_4') | ~v2_funct_1(A_712) | k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), A_712)!=k2_relat_1('#skF_5') | k1_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), A_712)!=k1_relat_1('#skF_5') | ~v1_funct_2(A_712, k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1(A_712) | ~r1_tarski(A_712, k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_400, c_400, c_392, c_400, c_400, c_2780])).
% 13.46/5.99  tff(c_3984, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k1_relat_1('#skF_5'))) | v3_tops_2('#skF_5', '#skF_3', '#skF_4') | ~v2_funct_1('#skF_5') | k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')!=k2_relat_1('#skF_5') | k1_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')!=k1_relat_1('#skF_5') | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_397, c_3969])).
% 13.46/5.99  tff(c_3990, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k1_relat_1('#skF_5'))) | v3_tops_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_398, c_394, c_396, c_70, c_3984])).
% 13.46/5.99  tff(c_3991, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k1_relat_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_66, c_3990])).
% 13.46/5.99  tff(c_68, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_212])).
% 13.46/5.99  tff(c_522, plain, (![A_164, B_165, C_166, D_167]: (k7_relset_1(A_164, B_165, C_166, D_167)=k9_relat_1(C_166, D_167) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.46/5.99  tff(c_528, plain, (![D_167]: (k7_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5', D_167)=k9_relat_1('#skF_5', D_167))), inference(resolution, [status(thm)], [c_395, c_522])).
% 13.46/5.99  tff(c_94, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 13.46/5.99  tff(c_78, plain, (v1_compts_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 13.46/5.99  tff(c_88, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_212])).
% 13.46/5.99  tff(c_76, plain, (v8_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_212])).
% 13.46/5.99  tff(c_2210, plain, (![A_445, B_446, C_447, D_448]: (v4_pre_topc(k7_relset_1(u1_struct_0(A_445), u1_struct_0(B_446), C_447, D_448), B_446) | ~v4_pre_topc(D_448, A_445) | ~m1_subset_1(D_448, k1_zfmisc_1(u1_struct_0(A_445))) | ~v5_pre_topc(C_447, A_445, B_446) | k2_relset_1(u1_struct_0(A_445), u1_struct_0(B_446), C_447)!=k2_struct_0(B_446) | ~v8_pre_topc(B_446) | ~v1_compts_1(A_445) | ~m1_subset_1(C_447, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_445), u1_struct_0(B_446)))) | ~v1_funct_2(C_447, u1_struct_0(A_445), u1_struct_0(B_446)) | ~v1_funct_1(C_447) | ~l1_pre_topc(B_446) | ~v2_pre_topc(B_446) | v2_struct_0(B_446) | ~l1_pre_topc(A_445) | ~v2_pre_topc(A_445))), inference(cnfTransformation, [status(thm)], [f_178])).
% 13.46/5.99  tff(c_2221, plain, (![A_445, C_447, D_448]: (v4_pre_topc(k7_relset_1(u1_struct_0(A_445), u1_struct_0('#skF_4'), C_447, D_448), '#skF_4') | ~v4_pre_topc(D_448, A_445) | ~m1_subset_1(D_448, k1_zfmisc_1(u1_struct_0(A_445))) | ~v5_pre_topc(C_447, A_445, '#skF_4') | k2_relset_1(u1_struct_0(A_445), u1_struct_0('#skF_4'), C_447)!=k2_struct_0('#skF_4') | ~v8_pre_topc('#skF_4') | ~v1_compts_1(A_445) | ~m1_subset_1(C_447, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_445), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_447, u1_struct_0(A_445), u1_struct_0('#skF_4')) | ~v1_funct_1(C_447) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_445) | ~v2_pre_topc(A_445))), inference(superposition, [status(thm), theory('equality')], [c_267, c_2210])).
% 13.46/5.99  tff(c_2233, plain, (![A_445, C_447, D_448]: (v4_pre_topc(k7_relset_1(u1_struct_0(A_445), k2_relat_1('#skF_5'), C_447, D_448), '#skF_4') | ~v4_pre_topc(D_448, A_445) | ~m1_subset_1(D_448, k1_zfmisc_1(u1_struct_0(A_445))) | ~v5_pre_topc(C_447, A_445, '#skF_4') | k2_relset_1(u1_struct_0(A_445), k2_relat_1('#skF_5'), C_447)!=k2_relat_1('#skF_5') | ~v1_compts_1(A_445) | ~m1_subset_1(C_447, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_445), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_447, u1_struct_0(A_445), k2_relat_1('#skF_5')) | ~v1_funct_1(C_447) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_445) | ~v2_pre_topc(A_445))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_267, c_76, c_259, c_267, c_267, c_2221])).
% 13.46/5.99  tff(c_2302, plain, (![A_455, C_456, D_457]: (v4_pre_topc(k7_relset_1(u1_struct_0(A_455), k2_relat_1('#skF_5'), C_456, D_457), '#skF_4') | ~v4_pre_topc(D_457, A_455) | ~m1_subset_1(D_457, k1_zfmisc_1(u1_struct_0(A_455))) | ~v5_pre_topc(C_456, A_455, '#skF_4') | k2_relset_1(u1_struct_0(A_455), k2_relat_1('#skF_5'), C_456)!=k2_relat_1('#skF_5') | ~v1_compts_1(A_455) | ~m1_subset_1(C_456, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_455), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_456, u1_struct_0(A_455), k2_relat_1('#skF_5')) | ~v1_funct_1(C_456) | ~l1_pre_topc(A_455) | ~v2_pre_topc(A_455))), inference(negUnitSimplification, [status(thm)], [c_90, c_2233])).
% 13.46/5.99  tff(c_2919, plain, (![A_578, A_579, D_580]: (v4_pre_topc(k7_relset_1(u1_struct_0(A_578), k2_relat_1('#skF_5'), A_579, D_580), '#skF_4') | ~v4_pre_topc(D_580, A_578) | ~m1_subset_1(D_580, k1_zfmisc_1(u1_struct_0(A_578))) | ~v5_pre_topc(A_579, A_578, '#skF_4') | k2_relset_1(u1_struct_0(A_578), k2_relat_1('#skF_5'), A_579)!=k2_relat_1('#skF_5') | ~v1_compts_1(A_578) | ~v1_funct_2(A_579, u1_struct_0(A_578), k2_relat_1('#skF_5')) | ~v1_funct_1(A_579) | ~l1_pre_topc(A_578) | ~v2_pre_topc(A_578) | ~r1_tarski(A_579, k2_zfmisc_1(u1_struct_0(A_578), k2_relat_1('#skF_5'))))), inference(resolution, [status(thm)], [c_4, c_2302])).
% 13.46/5.99  tff(c_2928, plain, (![A_579, D_580]: (v4_pre_topc(k7_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), A_579, D_580), '#skF_4') | ~v4_pre_topc(D_580, '#skF_3') | ~m1_subset_1(D_580, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v5_pre_topc(A_579, '#skF_3', '#skF_4') | k2_relset_1(u1_struct_0('#skF_3'), k2_relat_1('#skF_5'), A_579)!=k2_relat_1('#skF_5') | ~v1_compts_1('#skF_3') | ~v1_funct_2(A_579, u1_struct_0('#skF_3'), k2_relat_1('#skF_5')) | ~v1_funct_1(A_579) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~r1_tarski(A_579, k2_zfmisc_1(u1_struct_0('#skF_3'), k2_relat_1('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_400, c_2919])).
% 13.46/5.99  tff(c_3213, plain, (![A_648, D_649]: (v4_pre_topc(k7_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), A_648, D_649), '#skF_4') | ~v4_pre_topc(D_649, '#skF_3') | ~m1_subset_1(D_649, k1_zfmisc_1(k1_relat_1('#skF_5'))) | ~v5_pre_topc(A_648, '#skF_3', '#skF_4') | k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), A_648)!=k2_relat_1('#skF_5') | ~v1_funct_2(A_648, k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1(A_648) | ~r1_tarski(A_648, k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_400, c_94, c_92, c_400, c_78, c_400, c_400, c_2928])).
% 13.46/5.99  tff(c_3218, plain, (![D_167]: (v4_pre_topc(k9_relat_1('#skF_5', D_167), '#skF_4') | ~v4_pre_topc(D_167, '#skF_3') | ~m1_subset_1(D_167, k1_zfmisc_1(k1_relat_1('#skF_5'))) | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_4') | k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')!=k2_relat_1('#skF_5') | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~r1_tarski('#skF_5', k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_528, c_3213])).
% 13.46/5.99  tff(c_3221, plain, (![D_167]: (v4_pre_topc(k9_relat_1('#skF_5', D_167), '#skF_4') | ~v4_pre_topc(D_167, '#skF_3') | ~m1_subset_1(D_167, k1_zfmisc_1(k1_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_397, c_84, c_398, c_396, c_68, c_3218])).
% 13.46/5.99  tff(c_3998, plain, (v4_pre_topc(k9_relat_1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | ~v4_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_3991, c_3221])).
% 13.46/5.99  tff(c_4056, plain, (~v4_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_3998])).
% 13.46/5.99  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.46/5.99  tff(c_3999, plain, (r1_tarski('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_3991, c_2])).
% 13.46/5.99  tff(c_6, plain, (![B_4, A_3]: (k10_relat_1(B_4, k9_relat_1(B_4, A_3))=A_3 | ~v2_funct_1(B_4) | ~r1_tarski(A_3, k1_relat_1(B_4)) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.46/5.99  tff(c_4040, plain, (k10_relat_1('#skF_5', k9_relat_1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))='#skF_2'('#skF_3', '#skF_4', '#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_3999, c_6])).
% 13.46/5.99  tff(c_4043, plain, (k10_relat_1('#skF_5', k9_relat_1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))='#skF_2'('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_84, c_70, c_4040])).
% 13.46/5.99  tff(c_544, plain, (![A_173, B_174, C_175, D_176]: (m1_subset_1(k7_relset_1(A_173, B_174, C_175, D_176), k1_zfmisc_1(B_174)) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.46/5.99  tff(c_576, plain, (![D_167]: (m1_subset_1(k9_relat_1('#skF_5', D_167), k1_zfmisc_1(k2_relat_1('#skF_5'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5')))))), inference(superposition, [status(thm), theory('equality')], [c_528, c_544])).
% 13.46/5.99  tff(c_586, plain, (![D_167]: (m1_subset_1(k9_relat_1('#skF_5', D_167), k1_zfmisc_1(k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_395, c_576])).
% 13.46/5.99  tff(c_500, plain, (![A_155, B_156, C_157, D_158]: (k8_relset_1(A_155, B_156, C_157, D_158)=k10_relat_1(C_157, D_158) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 13.46/5.99  tff(c_506, plain, (![D_158]: (k8_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5', D_158)=k10_relat_1('#skF_5', D_158))), inference(resolution, [status(thm)], [c_395, c_500])).
% 13.46/5.99  tff(c_1506, plain, (![A_370, B_371, C_372, D_373]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_370), u1_struct_0(B_371), C_372, D_373), A_370) | ~v4_pre_topc(D_373, B_371) | ~m1_subset_1(D_373, k1_zfmisc_1(u1_struct_0(B_371))) | ~v5_pre_topc(C_372, A_370, B_371) | ~m1_subset_1(C_372, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_370), u1_struct_0(B_371)))) | ~v1_funct_2(C_372, u1_struct_0(A_370), u1_struct_0(B_371)) | ~v1_funct_1(C_372) | ~l1_pre_topc(B_371) | ~l1_pre_topc(A_370))), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.46/5.99  tff(c_2606, plain, (![A_521, B_522, A_523, D_524]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_521), u1_struct_0(B_522), A_523, D_524), A_521) | ~v4_pre_topc(D_524, B_522) | ~m1_subset_1(D_524, k1_zfmisc_1(u1_struct_0(B_522))) | ~v5_pre_topc(A_523, A_521, B_522) | ~v1_funct_2(A_523, u1_struct_0(A_521), u1_struct_0(B_522)) | ~v1_funct_1(A_523) | ~l1_pre_topc(B_522) | ~l1_pre_topc(A_521) | ~r1_tarski(A_523, k2_zfmisc_1(u1_struct_0(A_521), u1_struct_0(B_522))))), inference(resolution, [status(thm)], [c_4, c_1506])).
% 13.46/5.99  tff(c_2613, plain, (![B_522, A_523, D_524]: (v4_pre_topc(k8_relset_1(k1_relat_1('#skF_5'), u1_struct_0(B_522), A_523, D_524), '#skF_3') | ~v4_pre_topc(D_524, B_522) | ~m1_subset_1(D_524, k1_zfmisc_1(u1_struct_0(B_522))) | ~v5_pre_topc(A_523, '#skF_3', B_522) | ~v1_funct_2(A_523, u1_struct_0('#skF_3'), u1_struct_0(B_522)) | ~v1_funct_1(A_523) | ~l1_pre_topc(B_522) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_523, k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_522))))), inference(superposition, [status(thm), theory('equality')], [c_400, c_2606])).
% 13.46/5.99  tff(c_2632, plain, (![B_525, A_526, D_527]: (v4_pre_topc(k8_relset_1(k1_relat_1('#skF_5'), u1_struct_0(B_525), A_526, D_527), '#skF_3') | ~v4_pre_topc(D_527, B_525) | ~m1_subset_1(D_527, k1_zfmisc_1(u1_struct_0(B_525))) | ~v5_pre_topc(A_526, '#skF_3', B_525) | ~v1_funct_2(A_526, k1_relat_1('#skF_5'), u1_struct_0(B_525)) | ~v1_funct_1(A_526) | ~l1_pre_topc(B_525) | ~r1_tarski(A_526, k2_zfmisc_1(k1_relat_1('#skF_5'), u1_struct_0(B_525))))), inference(demodulation, [status(thm), theory('equality')], [c_400, c_92, c_400, c_2613])).
% 13.46/5.99  tff(c_2642, plain, (![A_526, D_527]: (v4_pre_topc(k8_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), A_526, D_527), '#skF_3') | ~v4_pre_topc(D_527, '#skF_4') | ~m1_subset_1(D_527, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v5_pre_topc(A_526, '#skF_3', '#skF_4') | ~v1_funct_2(A_526, k1_relat_1('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(A_526) | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_526, k2_zfmisc_1(k1_relat_1('#skF_5'), u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_267, c_2632])).
% 13.46/5.99  tff(c_2654, plain, (![A_530, D_531]: (v4_pre_topc(k8_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), A_530, D_531), '#skF_3') | ~v4_pre_topc(D_531, '#skF_4') | ~m1_subset_1(D_531, k1_zfmisc_1(k2_relat_1('#skF_5'))) | ~v5_pre_topc(A_530, '#skF_3', '#skF_4') | ~v1_funct_2(A_530, k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1(A_530) | ~r1_tarski(A_530, k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_267, c_86, c_267, c_267, c_2642])).
% 13.46/5.99  tff(c_2661, plain, (![D_158]: (v4_pre_topc(k10_relat_1('#skF_5', D_158), '#skF_3') | ~v4_pre_topc(D_158, '#skF_4') | ~m1_subset_1(D_158, k1_zfmisc_1(k2_relat_1('#skF_5'))) | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~r1_tarski('#skF_5', k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_506, c_2654])).
% 13.46/5.99  tff(c_2684, plain, (![D_535]: (v4_pre_topc(k10_relat_1('#skF_5', D_535), '#skF_3') | ~v4_pre_topc(D_535, '#skF_4') | ~m1_subset_1(D_535, k1_zfmisc_1(k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_397, c_84, c_398, c_68, c_2661])).
% 13.46/5.99  tff(c_2696, plain, (![D_167]: (v4_pre_topc(k10_relat_1('#skF_5', k9_relat_1('#skF_5', D_167)), '#skF_3') | ~v4_pre_topc(k9_relat_1('#skF_5', D_167), '#skF_4'))), inference(resolution, [status(thm)], [c_586, c_2684])).
% 13.46/5.99  tff(c_4050, plain, (v4_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_3') | ~v4_pre_topc(k9_relat_1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4043, c_2696])).
% 13.46/5.99  tff(c_4094, plain, (~v4_pre_topc(k9_relat_1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_4056, c_4050])).
% 13.46/5.99  tff(c_2505, plain, (![A_493, B_494, C_495]: (v4_pre_topc('#skF_2'(A_493, B_494, C_495), A_493) | v4_pre_topc(k7_relset_1(u1_struct_0(A_493), u1_struct_0(B_494), C_495, '#skF_2'(A_493, B_494, C_495)), B_494) | v3_tops_2(C_495, A_493, B_494) | ~v2_funct_1(C_495) | k2_relset_1(u1_struct_0(A_493), u1_struct_0(B_494), C_495)!=k2_struct_0(B_494) | k1_relset_1(u1_struct_0(A_493), u1_struct_0(B_494), C_495)!=k2_struct_0(A_493) | ~m1_subset_1(C_495, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_493), u1_struct_0(B_494)))) | ~v1_funct_2(C_495, u1_struct_0(A_493), u1_struct_0(B_494)) | ~v1_funct_1(C_495) | ~l1_pre_topc(B_494) | v2_struct_0(B_494) | ~l1_pre_topc(A_493))), inference(cnfTransformation, [status(thm)], [f_144])).
% 13.46/5.99  tff(c_2522, plain, (![A_493, C_495]: (v4_pre_topc('#skF_2'(A_493, '#skF_4', C_495), A_493) | v4_pre_topc(k7_relset_1(u1_struct_0(A_493), k2_relat_1('#skF_5'), C_495, '#skF_2'(A_493, '#skF_4', C_495)), '#skF_4') | v3_tops_2(C_495, A_493, '#skF_4') | ~v2_funct_1(C_495) | k2_relset_1(u1_struct_0(A_493), u1_struct_0('#skF_4'), C_495)!=k2_struct_0('#skF_4') | k1_relset_1(u1_struct_0(A_493), u1_struct_0('#skF_4'), C_495)!=k2_struct_0(A_493) | ~m1_subset_1(C_495, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_493), u1_struct_0('#skF_4')))) | ~v1_funct_2(C_495, u1_struct_0(A_493), u1_struct_0('#skF_4')) | ~v1_funct_1(C_495) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_493))), inference(superposition, [status(thm), theory('equality')], [c_267, c_2505])).
% 13.46/5.99  tff(c_2532, plain, (![A_493, C_495]: (v4_pre_topc('#skF_2'(A_493, '#skF_4', C_495), A_493) | v4_pre_topc(k7_relset_1(u1_struct_0(A_493), k2_relat_1('#skF_5'), C_495, '#skF_2'(A_493, '#skF_4', C_495)), '#skF_4') | v3_tops_2(C_495, A_493, '#skF_4') | ~v2_funct_1(C_495) | k2_relset_1(u1_struct_0(A_493), k2_relat_1('#skF_5'), C_495)!=k2_relat_1('#skF_5') | k1_relset_1(u1_struct_0(A_493), k2_relat_1('#skF_5'), C_495)!=k2_struct_0(A_493) | ~m1_subset_1(C_495, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_493), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_495, u1_struct_0(A_493), k2_relat_1('#skF_5')) | ~v1_funct_1(C_495) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_493))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_267, c_267, c_267, c_259, c_267, c_2522])).
% 13.46/5.99  tff(c_2551, plain, (![A_502, C_503]: (v4_pre_topc('#skF_2'(A_502, '#skF_4', C_503), A_502) | v4_pre_topc(k7_relset_1(u1_struct_0(A_502), k2_relat_1('#skF_5'), C_503, '#skF_2'(A_502, '#skF_4', C_503)), '#skF_4') | v3_tops_2(C_503, A_502, '#skF_4') | ~v2_funct_1(C_503) | k2_relset_1(u1_struct_0(A_502), k2_relat_1('#skF_5'), C_503)!=k2_relat_1('#skF_5') | k1_relset_1(u1_struct_0(A_502), k2_relat_1('#skF_5'), C_503)!=k2_struct_0(A_502) | ~m1_subset_1(C_503, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_502), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_503, u1_struct_0(A_502), k2_relat_1('#skF_5')) | ~v1_funct_1(C_503) | ~l1_pre_topc(A_502))), inference(negUnitSimplification, [status(thm)], [c_90, c_2532])).
% 13.46/5.99  tff(c_2559, plain, (![C_503]: (v4_pre_topc('#skF_2'('#skF_3', '#skF_4', C_503), '#skF_3') | v4_pre_topc(k7_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), C_503, '#skF_2'('#skF_3', '#skF_4', C_503)), '#skF_4') | v3_tops_2(C_503, '#skF_3', '#skF_4') | ~v2_funct_1(C_503) | k2_relset_1(u1_struct_0('#skF_3'), k2_relat_1('#skF_5'), C_503)!=k2_relat_1('#skF_5') | k1_relset_1(u1_struct_0('#skF_3'), k2_relat_1('#skF_5'), C_503)!=k2_struct_0('#skF_3') | ~m1_subset_1(C_503, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_503, u1_struct_0('#skF_3'), k2_relat_1('#skF_5')) | ~v1_funct_1(C_503) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_400, c_2551])).
% 13.46/5.99  tff(c_9558, plain, (![C_1169]: (v4_pre_topc('#skF_2'('#skF_3', '#skF_4', C_1169), '#skF_3') | v4_pre_topc(k7_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), C_1169, '#skF_2'('#skF_3', '#skF_4', C_1169)), '#skF_4') | v3_tops_2(C_1169, '#skF_3', '#skF_4') | ~v2_funct_1(C_1169) | k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), C_1169)!=k2_relat_1('#skF_5') | k1_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), C_1169)!=k1_relat_1('#skF_5') | ~m1_subset_1(C_1169, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_1169, k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1(C_1169))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_400, c_400, c_400, c_392, c_400, c_2559])).
% 13.46/5.99  tff(c_9575, plain, (v4_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_3') | v4_pre_topc(k9_relat_1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | v3_tops_2('#skF_5', '#skF_3', '#skF_4') | ~v2_funct_1('#skF_5') | k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')!=k2_relat_1('#skF_5') | k1_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')!=k1_relat_1('#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5')))) | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_528, c_9558])).
% 13.46/5.99  tff(c_9579, plain, (v4_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_3') | v4_pre_topc(k9_relat_1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | v3_tops_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_398, c_395, c_394, c_396, c_70, c_9575])).
% 13.46/5.99  tff(c_9581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_4094, c_4056, c_9579])).
% 13.46/5.99  tff(c_9583, plain, (v4_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_3998])).
% 13.46/5.99  tff(c_9582, plain, (v4_pre_topc(k9_relat_1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(splitRight, [status(thm)], [c_3998])).
% 13.46/5.99  tff(c_2428, plain, (![A_473, B_474, C_475]: (~v4_pre_topc(k7_relset_1(u1_struct_0(A_473), u1_struct_0(B_474), C_475, '#skF_2'(A_473, B_474, C_475)), B_474) | ~v4_pre_topc('#skF_2'(A_473, B_474, C_475), A_473) | v3_tops_2(C_475, A_473, B_474) | ~v2_funct_1(C_475) | k2_relset_1(u1_struct_0(A_473), u1_struct_0(B_474), C_475)!=k2_struct_0(B_474) | k1_relset_1(u1_struct_0(A_473), u1_struct_0(B_474), C_475)!=k2_struct_0(A_473) | ~m1_subset_1(C_475, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_473), u1_struct_0(B_474)))) | ~v1_funct_2(C_475, u1_struct_0(A_473), u1_struct_0(B_474)) | ~v1_funct_1(C_475) | ~l1_pre_topc(B_474) | v2_struct_0(B_474) | ~l1_pre_topc(A_473))), inference(cnfTransformation, [status(thm)], [f_144])).
% 13.46/5.99  tff(c_2440, plain, (![A_473, C_475]: (~v4_pre_topc(k7_relset_1(u1_struct_0(A_473), k2_relat_1('#skF_5'), C_475, '#skF_2'(A_473, '#skF_4', C_475)), '#skF_4') | ~v4_pre_topc('#skF_2'(A_473, '#skF_4', C_475), A_473) | v3_tops_2(C_475, A_473, '#skF_4') | ~v2_funct_1(C_475) | k2_relset_1(u1_struct_0(A_473), u1_struct_0('#skF_4'), C_475)!=k2_struct_0('#skF_4') | k1_relset_1(u1_struct_0(A_473), u1_struct_0('#skF_4'), C_475)!=k2_struct_0(A_473) | ~m1_subset_1(C_475, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_473), u1_struct_0('#skF_4')))) | ~v1_funct_2(C_475, u1_struct_0(A_473), u1_struct_0('#skF_4')) | ~v1_funct_1(C_475) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_473))), inference(superposition, [status(thm), theory('equality')], [c_267, c_2428])).
% 13.46/5.99  tff(c_2448, plain, (![A_473, C_475]: (~v4_pre_topc(k7_relset_1(u1_struct_0(A_473), k2_relat_1('#skF_5'), C_475, '#skF_2'(A_473, '#skF_4', C_475)), '#skF_4') | ~v4_pre_topc('#skF_2'(A_473, '#skF_4', C_475), A_473) | v3_tops_2(C_475, A_473, '#skF_4') | ~v2_funct_1(C_475) | k2_relset_1(u1_struct_0(A_473), k2_relat_1('#skF_5'), C_475)!=k2_relat_1('#skF_5') | k1_relset_1(u1_struct_0(A_473), k2_relat_1('#skF_5'), C_475)!=k2_struct_0(A_473) | ~m1_subset_1(C_475, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_473), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_475, u1_struct_0(A_473), k2_relat_1('#skF_5')) | ~v1_funct_1(C_475) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_473))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_267, c_267, c_267, c_259, c_267, c_2440])).
% 13.46/5.99  tff(c_2469, plain, (![A_484, C_485]: (~v4_pre_topc(k7_relset_1(u1_struct_0(A_484), k2_relat_1('#skF_5'), C_485, '#skF_2'(A_484, '#skF_4', C_485)), '#skF_4') | ~v4_pre_topc('#skF_2'(A_484, '#skF_4', C_485), A_484) | v3_tops_2(C_485, A_484, '#skF_4') | ~v2_funct_1(C_485) | k2_relset_1(u1_struct_0(A_484), k2_relat_1('#skF_5'), C_485)!=k2_relat_1('#skF_5') | k1_relset_1(u1_struct_0(A_484), k2_relat_1('#skF_5'), C_485)!=k2_struct_0(A_484) | ~m1_subset_1(C_485, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_484), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_485, u1_struct_0(A_484), k2_relat_1('#skF_5')) | ~v1_funct_1(C_485) | ~l1_pre_topc(A_484))), inference(negUnitSimplification, [status(thm)], [c_90, c_2448])).
% 13.46/5.99  tff(c_2472, plain, (![C_485]: (~v4_pre_topc(k7_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), C_485, '#skF_2'('#skF_3', '#skF_4', C_485)), '#skF_4') | ~v4_pre_topc('#skF_2'('#skF_3', '#skF_4', C_485), '#skF_3') | v3_tops_2(C_485, '#skF_3', '#skF_4') | ~v2_funct_1(C_485) | k2_relset_1(u1_struct_0('#skF_3'), k2_relat_1('#skF_5'), C_485)!=k2_relat_1('#skF_5') | k1_relset_1(u1_struct_0('#skF_3'), k2_relat_1('#skF_5'), C_485)!=k2_struct_0('#skF_3') | ~m1_subset_1(C_485, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_485, u1_struct_0('#skF_3'), k2_relat_1('#skF_5')) | ~v1_funct_1(C_485) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_400, c_2469])).
% 13.46/5.99  tff(c_15008, plain, (![C_1611]: (~v4_pre_topc(k7_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), C_1611, '#skF_2'('#skF_3', '#skF_4', C_1611)), '#skF_4') | ~v4_pre_topc('#skF_2'('#skF_3', '#skF_4', C_1611), '#skF_3') | v3_tops_2(C_1611, '#skF_3', '#skF_4') | ~v2_funct_1(C_1611) | k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), C_1611)!=k2_relat_1('#skF_5') | k1_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), C_1611)!=k1_relat_1('#skF_5') | ~m1_subset_1(C_1611, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_1611, k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1(C_1611))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_400, c_400, c_400, c_392, c_400, c_2472])).
% 13.46/5.99  tff(c_15028, plain, (~v4_pre_topc(k9_relat_1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | ~v4_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_3') | v3_tops_2('#skF_5', '#skF_3', '#skF_4') | ~v2_funct_1('#skF_5') | k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')!=k2_relat_1('#skF_5') | k1_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')!=k1_relat_1('#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5')))) | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_528, c_15008])).
% 13.46/5.99  tff(c_15032, plain, (v3_tops_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_398, c_395, c_394, c_396, c_70, c_9583, c_9582, c_15028])).
% 13.46/5.99  tff(c_15034, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_15032])).
% 13.46/5.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.46/5.99  
% 13.46/5.99  Inference rules
% 13.46/5.99  ----------------------
% 13.46/5.99  #Ref     : 0
% 13.46/5.99  #Sup     : 3278
% 13.46/5.99  #Fact    : 0
% 13.46/5.99  #Define  : 0
% 13.46/5.99  #Split   : 7
% 13.46/5.99  #Chain   : 0
% 13.46/5.99  #Close   : 0
% 13.46/5.99  
% 13.46/5.99  Ordering : KBO
% 13.46/5.99  
% 13.46/5.99  Simplification rules
% 13.46/5.99  ----------------------
% 13.46/5.99  #Subsume      : 306
% 13.46/5.99  #Demod        : 3862
% 13.46/5.99  #Tautology    : 248
% 13.46/5.99  #SimpNegUnit  : 84
% 13.46/5.99  #BackRed      : 33
% 13.46/5.99  
% 13.46/5.99  #Partial instantiations: 0
% 13.46/5.99  #Strategies tried      : 1
% 13.46/5.99  
% 13.46/5.99  Timing (in seconds)
% 13.46/5.99  ----------------------
% 13.46/5.99  Preprocessing        : 0.42
% 13.46/5.99  Parsing              : 0.21
% 13.46/5.99  CNF conversion       : 0.04
% 13.46/5.99  Main loop            : 4.74
% 13.46/5.99  Inferencing          : 1.59
% 13.46/5.99  Reduction            : 1.67
% 13.46/5.99  Demodulation         : 1.31
% 13.46/5.99  BG Simplification    : 0.23
% 13.46/5.99  Subsumption          : 0.95
% 13.46/5.99  Abstraction          : 0.36
% 13.46/5.99  MUC search           : 0.00
% 13.46/5.99  Cooper               : 0.00
% 13.46/5.99  Total                : 5.22
% 13.46/5.99  Index Insertion      : 0.00
% 13.46/5.99  Index Deletion       : 0.00
% 13.46/5.99  Index Matching       : 0.00
% 13.46/5.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
