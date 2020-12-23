%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:14 EST 2020

% Result     : Theorem 8.09s
% Output     : CNFRefutation 8.09s
% Verified   : 
% Statistics : Number of formulae       :  187 (1623 expanded)
%              Number of leaves         :   45 ( 631 expanded)
%              Depth                    :   21
%              Number of atoms          :  383 (5550 expanded)
%              Number of equality atoms :   81 (1074 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_funct_2 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_165,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,A)
          & v3_funct_2(C,A,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r1_tarski(B,A)
         => ( k7_relset_1(A,A,C,k8_relset_1(A,A,C,B)) = B
            & k8_relset_1(A,A,C,k7_relset_1(A,A,C,B)) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_150,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_140,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_124,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_60,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_2196,plain,(
    ! [B_157,A_158] :
      ( v1_relat_1(B_157)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(A_158))
      | ~ v1_relat_1(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2199,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_2196])).

tff(c_2202,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2199])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_64,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_3269,plain,(
    ! [C_237,A_238,B_239] :
      ( v2_funct_1(C_237)
      | ~ v3_funct_2(C_237,A_238,B_239)
      | ~ v1_funct_1(C_237)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_238,B_239))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3272,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_3269])).

tff(c_3275,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_3272])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_4626,plain,(
    ! [A_279,B_280] :
      ( k2_funct_2(A_279,B_280) = k2_funct_1(B_280)
      | ~ m1_subset_1(B_280,k1_zfmisc_1(k2_zfmisc_1(A_279,A_279)))
      | ~ v3_funct_2(B_280,A_279,A_279)
      | ~ v1_funct_2(B_280,A_279,A_279)
      | ~ v1_funct_1(B_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_4629,plain,
    ( k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_4626])).

tff(c_4632,plain,(
    k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_4629])).

tff(c_7007,plain,(
    ! [A_325,B_326] :
      ( m1_subset_1(k2_funct_2(A_325,B_326),k1_zfmisc_1(k2_zfmisc_1(A_325,A_325)))
      | ~ m1_subset_1(B_326,k1_zfmisc_1(k2_zfmisc_1(A_325,A_325)))
      | ~ v3_funct_2(B_326,A_325,A_325)
      | ~ v1_funct_2(B_326,A_325,A_325)
      | ~ v1_funct_1(B_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_7039,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4632,c_7007])).

tff(c_7054,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_7039])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_7083,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_7054,c_8])).

tff(c_7108,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_7083])).

tff(c_4135,plain,(
    ! [A_270,B_271] :
      ( v1_funct_1(k2_funct_2(A_270,B_271))
      | ~ m1_subset_1(B_271,k1_zfmisc_1(k2_zfmisc_1(A_270,A_270)))
      | ~ v3_funct_2(B_271,A_270,A_270)
      | ~ v1_funct_2(B_271,A_270,A_270)
      | ~ v1_funct_1(B_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_4138,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_4135])).

tff(c_4141,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_4138])).

tff(c_4633,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4632,c_4141])).

tff(c_6617,plain,(
    ! [A_316,B_317] :
      ( v3_funct_2(k2_funct_2(A_316,B_317),A_316,A_316)
      | ~ m1_subset_1(B_317,k1_zfmisc_1(k2_zfmisc_1(A_316,A_316)))
      | ~ v3_funct_2(B_317,A_316,A_316)
      | ~ v1_funct_2(B_317,A_316,A_316)
      | ~ v1_funct_1(B_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_6619,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_3'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_6617])).

tff(c_6622,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_4632,c_6619])).

tff(c_38,plain,(
    ! [C_36,B_35,A_34] :
      ( v2_funct_2(C_36,B_35)
      | ~ v3_funct_2(C_36,A_34,B_35)
      | ~ v1_funct_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_7067,plain,
    ( v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7054,c_38])).

tff(c_7098,plain,(
    v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4633,c_6622,c_7067])).

tff(c_30,plain,(
    ! [C_25,B_24,A_23] :
      ( v5_relat_1(C_25,B_24)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_7105,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_7054,c_30])).

tff(c_46,plain,(
    ! [B_38,A_37] :
      ( k2_relat_1(B_38) = A_37
      | ~ v2_funct_2(B_38,A_37)
      | ~ v5_relat_1(B_38,A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_7184,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7105,c_46])).

tff(c_7187,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7108,c_7184])).

tff(c_7652,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7098,c_7187])).

tff(c_2237,plain,(
    ! [C_165,B_166,A_167] :
      ( v5_relat_1(C_165,B_166)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_167,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2241,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_2237])).

tff(c_2256,plain,(
    ! [B_174,A_175] :
      ( k2_relat_1(B_174) = A_175
      | ~ v2_funct_2(B_174,A_175)
      | ~ v5_relat_1(B_174,A_175)
      | ~ v1_relat_1(B_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2259,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2241,c_2256])).

tff(c_2262,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2202,c_2259])).

tff(c_2263,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2262])).

tff(c_2435,plain,(
    ! [C_201,B_202,A_203] :
      ( v2_funct_2(C_201,B_202)
      | ~ v3_funct_2(C_201,A_203,B_202)
      | ~ v1_funct_1(C_201)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_203,B_202))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2438,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_2435])).

tff(c_2441,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_2438])).

tff(c_2443,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2263,c_2441])).

tff(c_2444,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2262])).

tff(c_22,plain,(
    ! [A_16] :
      ( k10_relat_1(A_16,k2_relat_1(A_16)) = k1_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2452,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2444,c_22])).

tff(c_2461,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2202,c_2452])).

tff(c_32,plain,(
    ! [C_25,A_23,B_24] :
      ( v4_relat_1(C_25,A_23)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_7104,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_7054,c_32])).

tff(c_2250,plain,(
    ! [C_170,A_171,B_172] :
      ( v4_relat_1(C_170,A_171)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2254,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_2250])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18,plain,(
    ! [A_12] :
      ( k9_relat_1(A_12,k1_relat_1(A_12)) = k2_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k9_relat_1(B_11,A_10),k2_relat_1(B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2455,plain,(
    ! [A_10] :
      ( r1_tarski(k9_relat_1('#skF_3',A_10),'#skF_1')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2444,c_16])).

tff(c_2470,plain,(
    ! [A_204] : r1_tarski(k9_relat_1('#skF_3',A_204),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2202,c_2455])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2480,plain,(
    ! [A_205] :
      ( k9_relat_1('#skF_3',A_205) = '#skF_1'
      | ~ r1_tarski('#skF_1',k9_relat_1('#skF_3',A_205)) ) ),
    inference(resolution,[status(thm)],[c_2470,c_2])).

tff(c_2484,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2480])).

tff(c_2486,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2202,c_6,c_2444,c_2484])).

tff(c_2514,plain,(
    ! [C_206,A_207,B_208] :
      ( r1_tarski(k9_relat_1(C_206,A_207),k9_relat_1(C_206,B_208))
      | ~ r1_tarski(A_207,B_208)
      | ~ v1_relat_1(C_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2519,plain,(
    ! [B_208] :
      ( r1_tarski('#skF_1',k9_relat_1('#skF_3',B_208))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_208)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2486,c_2514])).

tff(c_2534,plain,(
    ! [B_209] :
      ( r1_tarski('#skF_1',k9_relat_1('#skF_3',B_209))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2202,c_2519])).

tff(c_2538,plain,(
    ! [A_6] :
      ( r1_tarski('#skF_1',k9_relat_1('#skF_3',A_6))
      | ~ v4_relat_1('#skF_3',A_6)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_2534])).

tff(c_2574,plain,(
    ! [A_212] :
      ( r1_tarski('#skF_1',k9_relat_1('#skF_3',A_212))
      | ~ v4_relat_1('#skF_3',A_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2202,c_2538])).

tff(c_2477,plain,(
    ! [A_204] :
      ( k9_relat_1('#skF_3',A_204) = '#skF_1'
      | ~ r1_tarski('#skF_1',k9_relat_1('#skF_3',A_204)) ) ),
    inference(resolution,[status(thm)],[c_2470,c_2])).

tff(c_2594,plain,(
    ! [A_213] :
      ( k9_relat_1('#skF_3',A_213) = '#skF_1'
      | ~ v4_relat_1('#skF_3',A_213) ) ),
    inference(resolution,[status(thm)],[c_2574,c_2477])).

tff(c_2602,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2254,c_2594])).

tff(c_7667,plain,
    ( k10_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7652,c_22])).

tff(c_7682,plain,(
    k10_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7108,c_7667])).

tff(c_2820,plain,(
    ! [B_218,A_219] :
      ( k9_relat_1(B_218,k10_relat_1(B_218,A_219)) = A_219
      | ~ r1_tarski(A_219,k2_relat_1(B_218))
      | ~ v1_funct_1(B_218)
      | ~ v1_relat_1(B_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2835,plain,(
    ! [B_218] :
      ( k9_relat_1(B_218,k10_relat_1(B_218,k2_relat_1(B_218))) = k2_relat_1(B_218)
      | ~ v1_funct_1(B_218)
      | ~ v1_relat_1(B_218) ) ),
    inference(resolution,[status(thm)],[c_6,c_2820])).

tff(c_7659,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k10_relat_1(k2_funct_1('#skF_3'),'#skF_1')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7652,c_2835])).

tff(c_7676,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k10_relat_1(k2_funct_1('#skF_3'),'#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7108,c_4633,c_7652,c_7659])).

tff(c_7855,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7682,c_7676])).

tff(c_26,plain,(
    ! [B_20,A_19] :
      ( k9_relat_1(k2_funct_1(B_20),A_19) = k10_relat_1(B_20,A_19)
      | ~ v2_funct_1(B_20)
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_7873,plain,
    ( k10_relat_1('#skF_3',k1_relat_1(k2_funct_1('#skF_3'))) = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7855,c_26])).

tff(c_7904,plain,(
    k10_relat_1('#skF_3',k1_relat_1(k2_funct_1('#skF_3'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2202,c_68,c_3275,c_7873])).

tff(c_8592,plain,(
    ! [B_345,B_346] :
      ( k9_relat_1(B_345,k10_relat_1(B_345,k1_relat_1(B_346))) = k1_relat_1(B_346)
      | ~ v1_funct_1(B_345)
      | ~ v1_relat_1(B_345)
      | ~ v4_relat_1(B_346,k2_relat_1(B_345))
      | ~ v1_relat_1(B_346) ) ),
    inference(resolution,[status(thm)],[c_12,c_2820])).

tff(c_8746,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k9_relat_1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7904,c_8592])).

tff(c_8824,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7108,c_7104,c_2444,c_2202,c_68,c_2602,c_8746])).

tff(c_2548,plain,(
    ! [B_210,A_211] :
      ( k9_relat_1(k2_funct_1(B_210),A_211) = k10_relat_1(B_210,A_211)
      | ~ v2_funct_1(B_210)
      | ~ v1_funct_1(B_210)
      | ~ v1_relat_1(B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2561,plain,(
    ! [B_210] :
      ( k10_relat_1(B_210,k1_relat_1(k2_funct_1(B_210))) = k2_relat_1(k2_funct_1(B_210))
      | ~ v1_relat_1(k2_funct_1(B_210))
      | ~ v2_funct_1(B_210)
      | ~ v1_funct_1(B_210)
      | ~ v1_relat_1(B_210) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2548,c_18])).

tff(c_8840,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8824,c_2561])).

tff(c_8868,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2202,c_68,c_3275,c_7108,c_7652,c_2461,c_8840])).

tff(c_3718,plain,(
    ! [B_259,A_260] :
      ( k10_relat_1(B_259,k9_relat_1(B_259,A_260)) = A_260
      | ~ v2_funct_1(B_259)
      | ~ r1_tarski(A_260,k1_relat_1(B_259))
      | ~ v1_funct_1(B_259)
      | ~ v1_relat_1(B_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3726,plain,(
    ! [B_259] :
      ( k10_relat_1(B_259,k9_relat_1(B_259,k1_relat_1(B_259))) = k1_relat_1(B_259)
      | ~ v2_funct_1(B_259)
      | ~ v1_funct_1(B_259)
      | ~ v1_relat_1(B_259) ) ),
    inference(resolution,[status(thm)],[c_6,c_3718])).

tff(c_7670,plain,(
    ! [A_10] :
      ( r1_tarski(k9_relat_1(k2_funct_1('#skF_3'),A_10),'#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7652,c_16])).

tff(c_7686,plain,(
    ! [A_332] : r1_tarski(k9_relat_1(k2_funct_1('#skF_3'),A_332),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7108,c_7670])).

tff(c_7700,plain,(
    ! [A_19] :
      ( r1_tarski(k10_relat_1('#skF_3',A_19),'#skF_1')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_7686])).

tff(c_7715,plain,(
    ! [A_333] : r1_tarski(k10_relat_1('#skF_3',A_333),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2202,c_68,c_3275,c_7700])).

tff(c_7728,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3726,c_7715])).

tff(c_7741,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2202,c_68,c_3275,c_7728])).

tff(c_7846,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7741,c_2])).

tff(c_7854,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_7846])).

tff(c_8887,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8868,c_7854])).

tff(c_8900,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8887])).

tff(c_8901,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_7846])).

tff(c_28,plain,(
    ! [B_22,A_21] :
      ( k10_relat_1(B_22,k9_relat_1(B_22,A_21)) = A_21
      | ~ v2_funct_1(B_22)
      | ~ r1_tarski(A_21,k1_relat_1(B_22))
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_8922,plain,(
    ! [A_21] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_21)) = A_21
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_21,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8901,c_28])).

tff(c_10770,plain,(
    ! [A_370] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_370)) = A_370
      | ~ r1_tarski(A_370,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2202,c_68,c_3275,c_8922])).

tff(c_3447,plain,(
    ! [A_246,B_247,C_248,D_249] :
      ( k8_relset_1(A_246,B_247,C_248,D_249) = k10_relat_1(C_248,D_249)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_246,B_247))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3450,plain,(
    ! [D_249] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_249) = k10_relat_1('#skF_3',D_249) ),
    inference(resolution,[status(thm)],[c_62,c_3447])).

tff(c_3157,plain,(
    ! [A_231,B_232,C_233,D_234] :
      ( k7_relset_1(A_231,B_232,C_233,D_234) = k9_relat_1(C_233,D_234)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3160,plain,(
    ! [D_234] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_234) = k9_relat_1('#skF_3',D_234) ),
    inference(resolution,[status(thm)],[c_62,c_3157])).

tff(c_87,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_90,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_87])).

tff(c_93,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_90])).

tff(c_124,plain,(
    ! [C_57,B_58,A_59] :
      ( v5_relat_1(C_57,B_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_59,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_128,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_124])).

tff(c_143,plain,(
    ! [B_66,A_67] :
      ( k2_relat_1(B_66) = A_67
      | ~ v2_funct_2(B_66,A_67)
      | ~ v5_relat_1(B_66,A_67)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_146,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_128,c_143])).

tff(c_149,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_146])).

tff(c_150,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_149])).

tff(c_370,plain,(
    ! [C_99,B_100,A_101] :
      ( v2_funct_2(C_99,B_100)
      | ~ v3_funct_2(C_99,A_101,B_100)
      | ~ v1_funct_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_101,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_373,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_370])).

tff(c_376,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_373])).

tff(c_378,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_376])).

tff(c_379,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_2092,plain,(
    ! [B_154,A_155] :
      ( k9_relat_1(B_154,k10_relat_1(B_154,A_155)) = A_155
      | ~ r1_tarski(A_155,k2_relat_1(B_154))
      | ~ v1_funct_1(B_154)
      | ~ v1_relat_1(B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2094,plain,(
    ! [A_155] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_155)) = A_155
      | ~ r1_tarski(A_155,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_2092])).

tff(c_2108,plain,(
    ! [A_156] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_156)) = A_156
      | ~ r1_tarski(A_156,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_68,c_2094])).

tff(c_1133,plain,(
    ! [A_132,B_133,C_134,D_135] :
      ( k8_relset_1(A_132,B_133,C_134,D_135) = k10_relat_1(C_134,D_135)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1136,plain,(
    ! [D_135] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_135) = k10_relat_1('#skF_3',D_135) ),
    inference(resolution,[status(thm)],[c_62,c_1133])).

tff(c_755,plain,(
    ! [A_116,B_117,C_118,D_119] :
      ( k7_relset_1(A_116,B_117,C_118,D_119) = k9_relat_1(C_118,D_119)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_758,plain,(
    ! [D_119] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_119) = k9_relat_1('#skF_3',D_119) ),
    inference(resolution,[status(thm)],[c_62,c_755])).

tff(c_58,plain,
    ( k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2'
    | k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_86,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_759,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_758,c_86])).

tff(c_1137,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1136,c_759])).

tff(c_2134,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2108,c_1137])).

tff(c_2193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2134])).

tff(c_2194,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_3161,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3160,c_2194])).

tff(c_3459,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3450,c_3161])).

tff(c_10809,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10770,c_3459])).

tff(c_10907,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_10809])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:19:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.09/2.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.09/2.76  
% 8.09/2.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.09/2.76  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_funct_2 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 8.09/2.76  
% 8.09/2.76  %Foreground sorts:
% 8.09/2.76  
% 8.09/2.76  
% 8.09/2.76  %Background operators:
% 8.09/2.76  
% 8.09/2.76  
% 8.09/2.76  %Foreground operators:
% 8.09/2.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.09/2.76  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.09/2.76  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.09/2.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.09/2.76  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 8.09/2.76  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 8.09/2.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.09/2.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.09/2.76  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 8.09/2.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.09/2.76  tff('#skF_2', type, '#skF_2': $i).
% 8.09/2.76  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.09/2.76  tff('#skF_3', type, '#skF_3': $i).
% 8.09/2.76  tff('#skF_1', type, '#skF_1': $i).
% 8.09/2.76  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 8.09/2.76  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.09/2.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.09/2.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.09/2.76  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 8.09/2.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.09/2.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.09/2.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.09/2.76  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.09/2.76  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 8.09/2.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.09/2.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.09/2.76  
% 8.09/2.79  tff(f_165, negated_conjecture, ~(![A, B, C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_tarski(B, A) => ((k7_relset_1(A, A, C, k8_relset_1(A, A, C, B)) = B) & (k8_relset_1(A, A, C, k7_relset_1(A, A, C, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_funct_2)).
% 8.09/2.79  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.09/2.79  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.09/2.79  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 8.09/2.79  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.09/2.79  tff(f_150, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 8.09/2.79  tff(f_140, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 8.09/2.79  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.09/2.79  tff(f_124, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 8.09/2.79  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 8.09/2.79  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 8.09/2.79  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 8.09/2.79  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 8.09/2.79  tff(f_60, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 8.09/2.79  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 8.09/2.79  tff(f_80, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 8.09/2.79  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 8.09/2.79  tff(f_104, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 8.09/2.79  tff(f_100, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 8.09/2.79  tff(c_60, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.09/2.79  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.09/2.79  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.09/2.79  tff(c_2196, plain, (![B_157, A_158]: (v1_relat_1(B_157) | ~m1_subset_1(B_157, k1_zfmisc_1(A_158)) | ~v1_relat_1(A_158))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.09/2.79  tff(c_2199, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_2196])).
% 8.09/2.79  tff(c_2202, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2199])).
% 8.09/2.79  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.09/2.79  tff(c_64, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.09/2.79  tff(c_3269, plain, (![C_237, A_238, B_239]: (v2_funct_1(C_237) | ~v3_funct_2(C_237, A_238, B_239) | ~v1_funct_1(C_237) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_238, B_239))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.09/2.79  tff(c_3272, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_3269])).
% 8.09/2.79  tff(c_3275, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_3272])).
% 8.09/2.79  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.09/2.79  tff(c_66, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.09/2.79  tff(c_4626, plain, (![A_279, B_280]: (k2_funct_2(A_279, B_280)=k2_funct_1(B_280) | ~m1_subset_1(B_280, k1_zfmisc_1(k2_zfmisc_1(A_279, A_279))) | ~v3_funct_2(B_280, A_279, A_279) | ~v1_funct_2(B_280, A_279, A_279) | ~v1_funct_1(B_280))), inference(cnfTransformation, [status(thm)], [f_150])).
% 8.09/2.79  tff(c_4629, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_4626])).
% 8.09/2.79  tff(c_4632, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_4629])).
% 8.09/2.79  tff(c_7007, plain, (![A_325, B_326]: (m1_subset_1(k2_funct_2(A_325, B_326), k1_zfmisc_1(k2_zfmisc_1(A_325, A_325))) | ~m1_subset_1(B_326, k1_zfmisc_1(k2_zfmisc_1(A_325, A_325))) | ~v3_funct_2(B_326, A_325, A_325) | ~v1_funct_2(B_326, A_325, A_325) | ~v1_funct_1(B_326))), inference(cnfTransformation, [status(thm)], [f_140])).
% 8.09/2.79  tff(c_7039, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4632, c_7007])).
% 8.09/2.79  tff(c_7054, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_7039])).
% 8.09/2.79  tff(c_8, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.09/2.79  tff(c_7083, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_7054, c_8])).
% 8.09/2.79  tff(c_7108, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_7083])).
% 8.09/2.79  tff(c_4135, plain, (![A_270, B_271]: (v1_funct_1(k2_funct_2(A_270, B_271)) | ~m1_subset_1(B_271, k1_zfmisc_1(k2_zfmisc_1(A_270, A_270))) | ~v3_funct_2(B_271, A_270, A_270) | ~v1_funct_2(B_271, A_270, A_270) | ~v1_funct_1(B_271))), inference(cnfTransformation, [status(thm)], [f_140])).
% 8.09/2.79  tff(c_4138, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_4135])).
% 8.09/2.79  tff(c_4141, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_4138])).
% 8.09/2.79  tff(c_4633, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4632, c_4141])).
% 8.09/2.79  tff(c_6617, plain, (![A_316, B_317]: (v3_funct_2(k2_funct_2(A_316, B_317), A_316, A_316) | ~m1_subset_1(B_317, k1_zfmisc_1(k2_zfmisc_1(A_316, A_316))) | ~v3_funct_2(B_317, A_316, A_316) | ~v1_funct_2(B_317, A_316, A_316) | ~v1_funct_1(B_317))), inference(cnfTransformation, [status(thm)], [f_140])).
% 8.09/2.79  tff(c_6619, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_3'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_6617])).
% 8.09/2.79  tff(c_6622, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_4632, c_6619])).
% 8.09/2.79  tff(c_38, plain, (![C_36, B_35, A_34]: (v2_funct_2(C_36, B_35) | ~v3_funct_2(C_36, A_34, B_35) | ~v1_funct_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.09/2.79  tff(c_7067, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_7054, c_38])).
% 8.09/2.79  tff(c_7098, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4633, c_6622, c_7067])).
% 8.09/2.79  tff(c_30, plain, (![C_25, B_24, A_23]: (v5_relat_1(C_25, B_24) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.09/2.79  tff(c_7105, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_7054, c_30])).
% 8.09/2.79  tff(c_46, plain, (![B_38, A_37]: (k2_relat_1(B_38)=A_37 | ~v2_funct_2(B_38, A_37) | ~v5_relat_1(B_38, A_37) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.09/2.79  tff(c_7184, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_7105, c_46])).
% 8.09/2.79  tff(c_7187, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7108, c_7184])).
% 8.09/2.79  tff(c_7652, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7098, c_7187])).
% 8.09/2.79  tff(c_2237, plain, (![C_165, B_166, A_167]: (v5_relat_1(C_165, B_166) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_167, B_166))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.09/2.79  tff(c_2241, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_2237])).
% 8.09/2.79  tff(c_2256, plain, (![B_174, A_175]: (k2_relat_1(B_174)=A_175 | ~v2_funct_2(B_174, A_175) | ~v5_relat_1(B_174, A_175) | ~v1_relat_1(B_174))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.09/2.79  tff(c_2259, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2241, c_2256])).
% 8.09/2.79  tff(c_2262, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2202, c_2259])).
% 8.09/2.79  tff(c_2263, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_2262])).
% 8.09/2.79  tff(c_2435, plain, (![C_201, B_202, A_203]: (v2_funct_2(C_201, B_202) | ~v3_funct_2(C_201, A_203, B_202) | ~v1_funct_1(C_201) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_203, B_202))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.09/2.79  tff(c_2438, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_2435])).
% 8.09/2.79  tff(c_2441, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_2438])).
% 8.09/2.79  tff(c_2443, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2263, c_2441])).
% 8.09/2.79  tff(c_2444, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_2262])).
% 8.09/2.79  tff(c_22, plain, (![A_16]: (k10_relat_1(A_16, k2_relat_1(A_16))=k1_relat_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.09/2.79  tff(c_2452, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2444, c_22])).
% 8.09/2.79  tff(c_2461, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2202, c_2452])).
% 8.09/2.79  tff(c_32, plain, (![C_25, A_23, B_24]: (v4_relat_1(C_25, A_23) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.09/2.79  tff(c_7104, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_7054, c_32])).
% 8.09/2.79  tff(c_2250, plain, (![C_170, A_171, B_172]: (v4_relat_1(C_170, A_171) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.09/2.79  tff(c_2254, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_2250])).
% 8.09/2.79  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.09/2.79  tff(c_18, plain, (![A_12]: (k9_relat_1(A_12, k1_relat_1(A_12))=k2_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.09/2.79  tff(c_16, plain, (![B_11, A_10]: (r1_tarski(k9_relat_1(B_11, A_10), k2_relat_1(B_11)) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.09/2.79  tff(c_2455, plain, (![A_10]: (r1_tarski(k9_relat_1('#skF_3', A_10), '#skF_1') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2444, c_16])).
% 8.09/2.79  tff(c_2470, plain, (![A_204]: (r1_tarski(k9_relat_1('#skF_3', A_204), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2202, c_2455])).
% 8.09/2.79  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.09/2.79  tff(c_2480, plain, (![A_205]: (k9_relat_1('#skF_3', A_205)='#skF_1' | ~r1_tarski('#skF_1', k9_relat_1('#skF_3', A_205)))), inference(resolution, [status(thm)], [c_2470, c_2])).
% 8.09/2.79  tff(c_2484, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_1' | ~r1_tarski('#skF_1', k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_2480])).
% 8.09/2.79  tff(c_2486, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2202, c_6, c_2444, c_2484])).
% 8.09/2.79  tff(c_2514, plain, (![C_206, A_207, B_208]: (r1_tarski(k9_relat_1(C_206, A_207), k9_relat_1(C_206, B_208)) | ~r1_tarski(A_207, B_208) | ~v1_relat_1(C_206))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.09/2.79  tff(c_2519, plain, (![B_208]: (r1_tarski('#skF_1', k9_relat_1('#skF_3', B_208)) | ~r1_tarski(k1_relat_1('#skF_3'), B_208) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2486, c_2514])).
% 8.09/2.79  tff(c_2534, plain, (![B_209]: (r1_tarski('#skF_1', k9_relat_1('#skF_3', B_209)) | ~r1_tarski(k1_relat_1('#skF_3'), B_209))), inference(demodulation, [status(thm), theory('equality')], [c_2202, c_2519])).
% 8.09/2.79  tff(c_2538, plain, (![A_6]: (r1_tarski('#skF_1', k9_relat_1('#skF_3', A_6)) | ~v4_relat_1('#skF_3', A_6) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_12, c_2534])).
% 8.09/2.79  tff(c_2574, plain, (![A_212]: (r1_tarski('#skF_1', k9_relat_1('#skF_3', A_212)) | ~v4_relat_1('#skF_3', A_212))), inference(demodulation, [status(thm), theory('equality')], [c_2202, c_2538])).
% 8.09/2.79  tff(c_2477, plain, (![A_204]: (k9_relat_1('#skF_3', A_204)='#skF_1' | ~r1_tarski('#skF_1', k9_relat_1('#skF_3', A_204)))), inference(resolution, [status(thm)], [c_2470, c_2])).
% 8.09/2.79  tff(c_2594, plain, (![A_213]: (k9_relat_1('#skF_3', A_213)='#skF_1' | ~v4_relat_1('#skF_3', A_213))), inference(resolution, [status(thm)], [c_2574, c_2477])).
% 8.09/2.79  tff(c_2602, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_2254, c_2594])).
% 8.09/2.79  tff(c_7667, plain, (k10_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_7652, c_22])).
% 8.09/2.79  tff(c_7682, plain, (k10_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7108, c_7667])).
% 8.09/2.79  tff(c_2820, plain, (![B_218, A_219]: (k9_relat_1(B_218, k10_relat_1(B_218, A_219))=A_219 | ~r1_tarski(A_219, k2_relat_1(B_218)) | ~v1_funct_1(B_218) | ~v1_relat_1(B_218))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.09/2.79  tff(c_2835, plain, (![B_218]: (k9_relat_1(B_218, k10_relat_1(B_218, k2_relat_1(B_218)))=k2_relat_1(B_218) | ~v1_funct_1(B_218) | ~v1_relat_1(B_218))), inference(resolution, [status(thm)], [c_6, c_2820])).
% 8.09/2.79  tff(c_7659, plain, (k9_relat_1(k2_funct_1('#skF_3'), k10_relat_1(k2_funct_1('#skF_3'), '#skF_1'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_7652, c_2835])).
% 8.09/2.79  tff(c_7676, plain, (k9_relat_1(k2_funct_1('#skF_3'), k10_relat_1(k2_funct_1('#skF_3'), '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7108, c_4633, c_7652, c_7659])).
% 8.09/2.79  tff(c_7855, plain, (k9_relat_1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7682, c_7676])).
% 8.09/2.79  tff(c_26, plain, (![B_20, A_19]: (k9_relat_1(k2_funct_1(B_20), A_19)=k10_relat_1(B_20, A_19) | ~v2_funct_1(B_20) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.09/2.79  tff(c_7873, plain, (k10_relat_1('#skF_3', k1_relat_1(k2_funct_1('#skF_3')))='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7855, c_26])).
% 8.09/2.79  tff(c_7904, plain, (k10_relat_1('#skF_3', k1_relat_1(k2_funct_1('#skF_3')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2202, c_68, c_3275, c_7873])).
% 8.09/2.79  tff(c_8592, plain, (![B_345, B_346]: (k9_relat_1(B_345, k10_relat_1(B_345, k1_relat_1(B_346)))=k1_relat_1(B_346) | ~v1_funct_1(B_345) | ~v1_relat_1(B_345) | ~v4_relat_1(B_346, k2_relat_1(B_345)) | ~v1_relat_1(B_346))), inference(resolution, [status(thm)], [c_12, c_2820])).
% 8.09/2.79  tff(c_8746, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k9_relat_1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_7904, c_8592])).
% 8.09/2.79  tff(c_8824, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7108, c_7104, c_2444, c_2202, c_68, c_2602, c_8746])).
% 8.09/2.79  tff(c_2548, plain, (![B_210, A_211]: (k9_relat_1(k2_funct_1(B_210), A_211)=k10_relat_1(B_210, A_211) | ~v2_funct_1(B_210) | ~v1_funct_1(B_210) | ~v1_relat_1(B_210))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.09/2.79  tff(c_2561, plain, (![B_210]: (k10_relat_1(B_210, k1_relat_1(k2_funct_1(B_210)))=k2_relat_1(k2_funct_1(B_210)) | ~v1_relat_1(k2_funct_1(B_210)) | ~v2_funct_1(B_210) | ~v1_funct_1(B_210) | ~v1_relat_1(B_210))), inference(superposition, [status(thm), theory('equality')], [c_2548, c_18])).
% 8.09/2.79  tff(c_8840, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8824, c_2561])).
% 8.09/2.79  tff(c_8868, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2202, c_68, c_3275, c_7108, c_7652, c_2461, c_8840])).
% 8.09/2.79  tff(c_3718, plain, (![B_259, A_260]: (k10_relat_1(B_259, k9_relat_1(B_259, A_260))=A_260 | ~v2_funct_1(B_259) | ~r1_tarski(A_260, k1_relat_1(B_259)) | ~v1_funct_1(B_259) | ~v1_relat_1(B_259))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.09/2.79  tff(c_3726, plain, (![B_259]: (k10_relat_1(B_259, k9_relat_1(B_259, k1_relat_1(B_259)))=k1_relat_1(B_259) | ~v2_funct_1(B_259) | ~v1_funct_1(B_259) | ~v1_relat_1(B_259))), inference(resolution, [status(thm)], [c_6, c_3718])).
% 8.09/2.79  tff(c_7670, plain, (![A_10]: (r1_tarski(k9_relat_1(k2_funct_1('#skF_3'), A_10), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_7652, c_16])).
% 8.09/2.79  tff(c_7686, plain, (![A_332]: (r1_tarski(k9_relat_1(k2_funct_1('#skF_3'), A_332), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_7108, c_7670])).
% 8.09/2.79  tff(c_7700, plain, (![A_19]: (r1_tarski(k10_relat_1('#skF_3', A_19), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_7686])).
% 8.09/2.79  tff(c_7715, plain, (![A_333]: (r1_tarski(k10_relat_1('#skF_3', A_333), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2202, c_68, c_3275, c_7700])).
% 8.09/2.79  tff(c_7728, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3726, c_7715])).
% 8.09/2.79  tff(c_7741, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2202, c_68, c_3275, c_7728])).
% 8.09/2.79  tff(c_7846, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_7741, c_2])).
% 8.09/2.79  tff(c_7854, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_7846])).
% 8.09/2.79  tff(c_8887, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8868, c_7854])).
% 8.09/2.79  tff(c_8900, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_8887])).
% 8.09/2.79  tff(c_8901, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_7846])).
% 8.09/2.79  tff(c_28, plain, (![B_22, A_21]: (k10_relat_1(B_22, k9_relat_1(B_22, A_21))=A_21 | ~v2_funct_1(B_22) | ~r1_tarski(A_21, k1_relat_1(B_22)) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.09/2.79  tff(c_8922, plain, (![A_21]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_21))=A_21 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_21, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_8901, c_28])).
% 8.09/2.79  tff(c_10770, plain, (![A_370]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_370))=A_370 | ~r1_tarski(A_370, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2202, c_68, c_3275, c_8922])).
% 8.09/2.79  tff(c_3447, plain, (![A_246, B_247, C_248, D_249]: (k8_relset_1(A_246, B_247, C_248, D_249)=k10_relat_1(C_248, D_249) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_246, B_247))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.09/2.79  tff(c_3450, plain, (![D_249]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_249)=k10_relat_1('#skF_3', D_249))), inference(resolution, [status(thm)], [c_62, c_3447])).
% 8.09/2.79  tff(c_3157, plain, (![A_231, B_232, C_233, D_234]: (k7_relset_1(A_231, B_232, C_233, D_234)=k9_relat_1(C_233, D_234) | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(A_231, B_232))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.09/2.79  tff(c_3160, plain, (![D_234]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_234)=k9_relat_1('#skF_3', D_234))), inference(resolution, [status(thm)], [c_62, c_3157])).
% 8.09/2.79  tff(c_87, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.09/2.79  tff(c_90, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_87])).
% 8.09/2.79  tff(c_93, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_90])).
% 8.09/2.79  tff(c_124, plain, (![C_57, B_58, A_59]: (v5_relat_1(C_57, B_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_59, B_58))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.09/2.79  tff(c_128, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_124])).
% 8.09/2.79  tff(c_143, plain, (![B_66, A_67]: (k2_relat_1(B_66)=A_67 | ~v2_funct_2(B_66, A_67) | ~v5_relat_1(B_66, A_67) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.09/2.79  tff(c_146, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_128, c_143])).
% 8.09/2.79  tff(c_149, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_146])).
% 8.09/2.79  tff(c_150, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_149])).
% 8.09/2.79  tff(c_370, plain, (![C_99, B_100, A_101]: (v2_funct_2(C_99, B_100) | ~v3_funct_2(C_99, A_101, B_100) | ~v1_funct_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.09/2.79  tff(c_373, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_370])).
% 8.09/2.79  tff(c_376, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_373])).
% 8.09/2.79  tff(c_378, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150, c_376])).
% 8.09/2.79  tff(c_379, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_149])).
% 8.09/2.79  tff(c_2092, plain, (![B_154, A_155]: (k9_relat_1(B_154, k10_relat_1(B_154, A_155))=A_155 | ~r1_tarski(A_155, k2_relat_1(B_154)) | ~v1_funct_1(B_154) | ~v1_relat_1(B_154))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.09/2.79  tff(c_2094, plain, (![A_155]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_155))=A_155 | ~r1_tarski(A_155, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_379, c_2092])).
% 8.09/2.79  tff(c_2108, plain, (![A_156]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_156))=A_156 | ~r1_tarski(A_156, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_68, c_2094])).
% 8.09/2.79  tff(c_1133, plain, (![A_132, B_133, C_134, D_135]: (k8_relset_1(A_132, B_133, C_134, D_135)=k10_relat_1(C_134, D_135) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.09/2.79  tff(c_1136, plain, (![D_135]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_135)=k10_relat_1('#skF_3', D_135))), inference(resolution, [status(thm)], [c_62, c_1133])).
% 8.09/2.79  tff(c_755, plain, (![A_116, B_117, C_118, D_119]: (k7_relset_1(A_116, B_117, C_118, D_119)=k9_relat_1(C_118, D_119) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.09/2.79  tff(c_758, plain, (![D_119]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_119)=k9_relat_1('#skF_3', D_119))), inference(resolution, [status(thm)], [c_62, c_755])).
% 8.09/2.79  tff(c_58, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2' | k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.09/2.79  tff(c_86, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_58])).
% 8.09/2.79  tff(c_759, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_758, c_86])).
% 8.09/2.79  tff(c_1137, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1136, c_759])).
% 8.09/2.79  tff(c_2134, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2108, c_1137])).
% 8.09/2.79  tff(c_2193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_2134])).
% 8.09/2.79  tff(c_2194, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitRight, [status(thm)], [c_58])).
% 8.09/2.79  tff(c_3161, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3160, c_2194])).
% 8.09/2.79  tff(c_3459, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3450, c_3161])).
% 8.09/2.79  tff(c_10809, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10770, c_3459])).
% 8.09/2.79  tff(c_10907, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_10809])).
% 8.09/2.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.09/2.79  
% 8.09/2.79  Inference rules
% 8.09/2.79  ----------------------
% 8.09/2.79  #Ref     : 0
% 8.09/2.79  #Sup     : 2352
% 8.09/2.79  #Fact    : 0
% 8.09/2.79  #Define  : 0
% 8.09/2.79  #Split   : 11
% 8.09/2.79  #Chain   : 0
% 8.09/2.79  #Close   : 0
% 8.09/2.79  
% 8.09/2.79  Ordering : KBO
% 8.09/2.79  
% 8.09/2.79  Simplification rules
% 8.09/2.79  ----------------------
% 8.09/2.79  #Subsume      : 523
% 8.09/2.79  #Demod        : 3858
% 8.09/2.79  #Tautology    : 1066
% 8.09/2.79  #SimpNegUnit  : 37
% 8.09/2.79  #BackRed      : 80
% 8.09/2.79  
% 8.09/2.79  #Partial instantiations: 0
% 8.09/2.79  #Strategies tried      : 1
% 8.09/2.79  
% 8.09/2.79  Timing (in seconds)
% 8.09/2.79  ----------------------
% 8.09/2.79  Preprocessing        : 0.38
% 8.09/2.79  Parsing              : 0.21
% 8.09/2.79  CNF conversion       : 0.02
% 8.09/2.79  Main loop            : 1.56
% 8.09/2.79  Inferencing          : 0.47
% 8.09/2.79  Reduction            : 0.61
% 8.09/2.79  Demodulation         : 0.46
% 8.09/2.79  BG Simplification    : 0.05
% 8.09/2.79  Subsumption          : 0.33
% 8.09/2.79  Abstraction          : 0.07
% 8.09/2.79  MUC search           : 0.00
% 8.09/2.79  Cooper               : 0.00
% 8.09/2.79  Total                : 2.00
% 8.09/2.79  Index Insertion      : 0.00
% 8.09/2.79  Index Deletion       : 0.00
% 8.09/2.79  Index Matching       : 0.00
% 8.09/2.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
