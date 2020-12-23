%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:50 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 384 expanded)
%              Number of leaves         :   38 ( 147 expanded)
%              Depth                    :   11
%              Number of atoms          :  211 (1000 expanded)
%              Number of equality atoms :   51 ( 152 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_131,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_6,plain,(
    ! [A_5,B_6] : v1_relat_1(k2_zfmisc_1(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_115,plain,(
    ! [B_37,A_38] :
      ( v1_relat_1(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_118,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_115])).

tff(c_121,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_118])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_46,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_44,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_266,plain,(
    ! [A_53,B_54,C_55] :
      ( k2_relset_1(A_53,B_54,C_55) = k2_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_269,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_266])).

tff(c_271,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_269])).

tff(c_10,plain,(
    ! [A_9] :
      ( k10_relat_1(A_9,k2_relat_1(A_9)) = k1_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_278,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_10])).

tff(c_282,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_278])).

tff(c_136,plain,(
    ! [C_42,A_43,B_44] :
      ( v4_relat_1(C_42,A_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_140,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_136])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( k7_relat_1(B_11,A_10) = B_11
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_148,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_140,c_12])).

tff(c_151,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_148])).

tff(c_156,plain,(
    ! [B_48,A_49] :
      ( k2_relat_1(k7_relat_1(B_48,A_49)) = k9_relat_1(B_48,A_49)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_168,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_156])).

tff(c_172,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_168])).

tff(c_274,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_172])).

tff(c_310,plain,(
    ! [B_56,A_57] :
      ( r1_tarski(k10_relat_1(B_56,k9_relat_1(B_56,A_57)),A_57)
      | ~ v2_funct_1(B_56)
      | ~ v1_funct_1(B_56)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_313,plain,
    ( r1_tarski(k10_relat_1('#skF_3','#skF_2'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_310])).

tff(c_315,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_52,c_46,c_282,c_313])).

tff(c_177,plain,(
    ! [A_50] :
      ( k4_relat_1(A_50) = k2_funct_1(A_50)
      | ~ v2_funct_1(A_50)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_180,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_177])).

tff(c_183,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_52,c_180])).

tff(c_4,plain,(
    ! [A_4] :
      ( v1_relat_1(k4_relat_1(A_4))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_193,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_4])).

tff(c_201,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_193])).

tff(c_20,plain,(
    ! [A_14] :
      ( v1_funct_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_42,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_61,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_64,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_61])).

tff(c_67,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_64])).

tff(c_86,plain,(
    ! [B_33,A_34] :
      ( v1_relat_1(B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_34))
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_89,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_86])).

tff(c_92,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_89])).

tff(c_94,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_92])).

tff(c_96,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_14,plain,(
    ! [A_12] :
      ( k2_relat_1(k4_relat_1(A_12)) = k1_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_187,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_14])).

tff(c_197,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_187])).

tff(c_16,plain,(
    ! [A_12] :
      ( k1_relat_1(k4_relat_1(A_12)) = k2_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_190,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_16])).

tff(c_199,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_190])).

tff(c_273,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_199])).

tff(c_329,plain,(
    ! [B_61,A_62] :
      ( m1_subset_1(B_61,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_61),A_62)))
      | ~ r1_tarski(k2_relat_1(B_61),A_62)
      | ~ v1_funct_1(B_61)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_344,plain,(
    ! [A_62] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_62)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_62)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_329])).

tff(c_381,plain,(
    ! [A_67] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_67)))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_96,c_197,c_344])).

tff(c_95,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_122,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_393,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_381,c_122])).

tff(c_404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_393])).

tff(c_406,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_409,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_406,c_2])).

tff(c_412,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_409])).

tff(c_494,plain,(
    ! [A_79] :
      ( k4_relat_1(A_79) = k2_funct_1(A_79)
      | ~ v2_funct_1(A_79)
      | ~ v1_funct_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_497,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_494])).

tff(c_500,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_52,c_497])).

tff(c_504,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_500,c_14])).

tff(c_514,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_504])).

tff(c_588,plain,(
    ! [A_82,B_83,C_84] :
      ( k2_relset_1(A_82,B_83,C_84) = k2_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_594,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_588])).

tff(c_598,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_594])).

tff(c_507,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_500,c_16])).

tff(c_516,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_507])).

tff(c_600,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_598,c_516])).

tff(c_637,plain,(
    ! [B_85,A_86] :
      ( v1_funct_2(B_85,k1_relat_1(B_85),A_86)
      | ~ r1_tarski(k2_relat_1(B_85),A_86)
      | ~ v1_funct_1(B_85)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_640,plain,(
    ! [A_86] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_86)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_86)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_600,c_637])).

tff(c_653,plain,(
    ! [A_87] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_87)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_96,c_514,c_640])).

tff(c_405,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_657,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_653,c_405])).

tff(c_605,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_598,c_10])).

tff(c_609,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_605])).

tff(c_435,plain,(
    ! [C_74,A_75,B_76] :
      ( v4_relat_1(C_74,A_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_443,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_435])).

tff(c_446,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_443,c_12])).

tff(c_449,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_446])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( k2_relat_1(k7_relat_1(B_8,A_7)) = k9_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_471,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_449,c_8])).

tff(c_475,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_471])).

tff(c_601,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_598,c_475])).

tff(c_658,plain,(
    ! [B_88,A_89] :
      ( r1_tarski(k10_relat_1(B_88,k9_relat_1(B_88,A_89)),A_89)
      | ~ v2_funct_1(B_88)
      | ~ v1_funct_1(B_88)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_661,plain,
    ( r1_tarski(k10_relat_1('#skF_3','#skF_2'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_601,c_658])).

tff(c_666,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_52,c_46,c_609,c_661])).

tff(c_668,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_657,c_666])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:09:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.38  
% 2.62/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.38  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.62/1.38  
% 2.62/1.38  %Foreground sorts:
% 2.62/1.38  
% 2.62/1.38  
% 2.62/1.38  %Background operators:
% 2.62/1.38  
% 2.62/1.38  
% 2.62/1.38  %Foreground operators:
% 2.62/1.38  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.62/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.62/1.38  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.62/1.38  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.62/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.62/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.62/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.62/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.38  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.62/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.62/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.62/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.38  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.62/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.62/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.62/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.62/1.38  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.62/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.38  
% 2.91/1.40  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.91/1.40  tff(f_131, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 2.91/1.40  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.91/1.40  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.91/1.40  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.91/1.40  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.91/1.40  tff(f_52, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.91/1.40  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.91/1.40  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 2.91/1.40  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 2.91/1.40  tff(f_36, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.91/1.40  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.91/1.40  tff(f_58, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 2.91/1.40  tff(f_114, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 2.91/1.40  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k2_zfmisc_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.91/1.40  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.91/1.40  tff(c_115, plain, (![B_37, A_38]: (v1_relat_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.91/1.40  tff(c_118, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_115])).
% 2.91/1.40  tff(c_121, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_118])).
% 2.91/1.40  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.91/1.40  tff(c_46, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.91/1.40  tff(c_44, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.91/1.40  tff(c_266, plain, (![A_53, B_54, C_55]: (k2_relset_1(A_53, B_54, C_55)=k2_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.91/1.40  tff(c_269, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_266])).
% 2.91/1.40  tff(c_271, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_269])).
% 2.91/1.40  tff(c_10, plain, (![A_9]: (k10_relat_1(A_9, k2_relat_1(A_9))=k1_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.91/1.40  tff(c_278, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_271, c_10])).
% 2.91/1.40  tff(c_282, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_278])).
% 2.91/1.40  tff(c_136, plain, (![C_42, A_43, B_44]: (v4_relat_1(C_42, A_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.91/1.40  tff(c_140, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_136])).
% 2.91/1.40  tff(c_12, plain, (![B_11, A_10]: (k7_relat_1(B_11, A_10)=B_11 | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.91/1.40  tff(c_148, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_140, c_12])).
% 2.91/1.40  tff(c_151, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_121, c_148])).
% 2.91/1.40  tff(c_156, plain, (![B_48, A_49]: (k2_relat_1(k7_relat_1(B_48, A_49))=k9_relat_1(B_48, A_49) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.91/1.40  tff(c_168, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_151, c_156])).
% 2.91/1.40  tff(c_172, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_168])).
% 2.91/1.40  tff(c_274, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_271, c_172])).
% 2.91/1.40  tff(c_310, plain, (![B_56, A_57]: (r1_tarski(k10_relat_1(B_56, k9_relat_1(B_56, A_57)), A_57) | ~v2_funct_1(B_56) | ~v1_funct_1(B_56) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.91/1.40  tff(c_313, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_2'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_274, c_310])).
% 2.91/1.40  tff(c_315, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_52, c_46, c_282, c_313])).
% 2.91/1.40  tff(c_177, plain, (![A_50]: (k4_relat_1(A_50)=k2_funct_1(A_50) | ~v2_funct_1(A_50) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.91/1.40  tff(c_180, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_177])).
% 2.91/1.40  tff(c_183, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_52, c_180])).
% 2.91/1.40  tff(c_4, plain, (![A_4]: (v1_relat_1(k4_relat_1(A_4)) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.91/1.40  tff(c_193, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_183, c_4])).
% 2.91/1.40  tff(c_201, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_193])).
% 2.91/1.40  tff(c_20, plain, (![A_14]: (v1_funct_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.91/1.40  tff(c_42, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.91/1.40  tff(c_61, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_42])).
% 2.91/1.40  tff(c_64, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_61])).
% 2.91/1.40  tff(c_67, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_64])).
% 2.91/1.40  tff(c_86, plain, (![B_33, A_34]: (v1_relat_1(B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_34)) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.91/1.40  tff(c_89, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_86])).
% 2.91/1.40  tff(c_92, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_89])).
% 2.91/1.40  tff(c_94, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_92])).
% 2.91/1.40  tff(c_96, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_42])).
% 2.91/1.40  tff(c_14, plain, (![A_12]: (k2_relat_1(k4_relat_1(A_12))=k1_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.91/1.40  tff(c_187, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_183, c_14])).
% 2.91/1.40  tff(c_197, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_187])).
% 2.91/1.40  tff(c_16, plain, (![A_12]: (k1_relat_1(k4_relat_1(A_12))=k2_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.91/1.40  tff(c_190, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_183, c_16])).
% 2.91/1.40  tff(c_199, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_190])).
% 2.91/1.40  tff(c_273, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_271, c_199])).
% 2.91/1.40  tff(c_329, plain, (![B_61, A_62]: (m1_subset_1(B_61, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_61), A_62))) | ~r1_tarski(k2_relat_1(B_61), A_62) | ~v1_funct_1(B_61) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.91/1.40  tff(c_344, plain, (![A_62]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_62))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_62) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_273, c_329])).
% 2.91/1.40  tff(c_381, plain, (![A_67]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_67))) | ~r1_tarski(k1_relat_1('#skF_3'), A_67))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_96, c_197, c_344])).
% 2.91/1.40  tff(c_95, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_42])).
% 2.91/1.40  tff(c_122, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_95])).
% 2.91/1.40  tff(c_393, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_381, c_122])).
% 2.91/1.40  tff(c_404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_315, c_393])).
% 2.91/1.40  tff(c_406, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_95])).
% 2.91/1.40  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.91/1.40  tff(c_409, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_406, c_2])).
% 2.91/1.40  tff(c_412, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_409])).
% 2.91/1.40  tff(c_494, plain, (![A_79]: (k4_relat_1(A_79)=k2_funct_1(A_79) | ~v2_funct_1(A_79) | ~v1_funct_1(A_79) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.91/1.40  tff(c_497, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_494])).
% 2.91/1.40  tff(c_500, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_52, c_497])).
% 2.91/1.40  tff(c_504, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_500, c_14])).
% 2.91/1.40  tff(c_514, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_504])).
% 2.91/1.40  tff(c_588, plain, (![A_82, B_83, C_84]: (k2_relset_1(A_82, B_83, C_84)=k2_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.91/1.40  tff(c_594, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_588])).
% 2.91/1.40  tff(c_598, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_594])).
% 2.91/1.40  tff(c_507, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_500, c_16])).
% 2.91/1.40  tff(c_516, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_507])).
% 2.91/1.40  tff(c_600, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_598, c_516])).
% 2.91/1.40  tff(c_637, plain, (![B_85, A_86]: (v1_funct_2(B_85, k1_relat_1(B_85), A_86) | ~r1_tarski(k2_relat_1(B_85), A_86) | ~v1_funct_1(B_85) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.91/1.40  tff(c_640, plain, (![A_86]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_86) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_86) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_600, c_637])).
% 2.91/1.40  tff(c_653, plain, (![A_87]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_87) | ~r1_tarski(k1_relat_1('#skF_3'), A_87))), inference(demodulation, [status(thm), theory('equality')], [c_412, c_96, c_514, c_640])).
% 2.91/1.40  tff(c_405, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_95])).
% 2.91/1.40  tff(c_657, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_653, c_405])).
% 2.91/1.40  tff(c_605, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_598, c_10])).
% 2.91/1.40  tff(c_609, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_605])).
% 2.91/1.40  tff(c_435, plain, (![C_74, A_75, B_76]: (v4_relat_1(C_74, A_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.91/1.40  tff(c_443, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_435])).
% 2.91/1.40  tff(c_446, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_443, c_12])).
% 2.91/1.40  tff(c_449, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_121, c_446])).
% 2.91/1.40  tff(c_8, plain, (![B_8, A_7]: (k2_relat_1(k7_relat_1(B_8, A_7))=k9_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.91/1.40  tff(c_471, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_449, c_8])).
% 2.91/1.40  tff(c_475, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_471])).
% 2.91/1.40  tff(c_601, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_598, c_475])).
% 2.91/1.40  tff(c_658, plain, (![B_88, A_89]: (r1_tarski(k10_relat_1(B_88, k9_relat_1(B_88, A_89)), A_89) | ~v2_funct_1(B_88) | ~v1_funct_1(B_88) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.91/1.40  tff(c_661, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_2'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_601, c_658])).
% 2.91/1.40  tff(c_666, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_52, c_46, c_609, c_661])).
% 2.91/1.40  tff(c_668, plain, $false, inference(negUnitSimplification, [status(thm)], [c_657, c_666])).
% 2.91/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.40  
% 2.91/1.40  Inference rules
% 2.91/1.40  ----------------------
% 2.91/1.40  #Ref     : 0
% 2.91/1.40  #Sup     : 154
% 2.91/1.40  #Fact    : 0
% 2.91/1.40  #Define  : 0
% 2.91/1.40  #Split   : 2
% 2.91/1.40  #Chain   : 0
% 2.91/1.40  #Close   : 0
% 2.91/1.40  
% 2.91/1.40  Ordering : KBO
% 2.91/1.40  
% 2.91/1.40  Simplification rules
% 2.91/1.40  ----------------------
% 2.91/1.40  #Subsume      : 1
% 2.91/1.40  #Demod        : 101
% 2.91/1.40  #Tautology    : 93
% 2.91/1.40  #SimpNegUnit  : 2
% 2.91/1.40  #BackRed      : 7
% 2.91/1.40  
% 2.91/1.40  #Partial instantiations: 0
% 2.91/1.40  #Strategies tried      : 1
% 2.91/1.40  
% 2.91/1.40  Timing (in seconds)
% 2.91/1.40  ----------------------
% 2.91/1.40  Preprocessing        : 0.31
% 2.91/1.40  Parsing              : 0.17
% 2.91/1.40  CNF conversion       : 0.02
% 2.91/1.41  Main loop            : 0.29
% 2.91/1.41  Inferencing          : 0.11
% 2.91/1.41  Reduction            : 0.10
% 2.91/1.41  Demodulation         : 0.07
% 2.91/1.41  BG Simplification    : 0.02
% 2.91/1.41  Subsumption          : 0.04
% 2.91/1.41  Abstraction          : 0.02
% 2.91/1.41  MUC search           : 0.00
% 2.91/1.41  Cooper               : 0.00
% 2.91/1.41  Total                : 0.65
% 2.91/1.41  Index Insertion      : 0.00
% 2.91/1.41  Index Deletion       : 0.00
% 2.91/1.41  Index Matching       : 0.00
% 2.91/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
