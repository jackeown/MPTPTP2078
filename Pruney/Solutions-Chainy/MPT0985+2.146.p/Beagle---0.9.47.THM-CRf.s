%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:50 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 507 expanded)
%              Number of leaves         :   29 ( 192 expanded)
%              Depth                    :   15
%              Number of atoms          :  265 (1629 expanded)
%              Number of equality atoms :   14 ( 161 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_52,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_48,plain,(
    ! [B_20,A_21] :
      ( v1_relat_1(B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_21))
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_51,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_48])).

tff(c_54,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_51])).

tff(c_55,plain,(
    ! [C_22,A_23,B_24] :
      ( v4_relat_1(C_22,A_23)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_59,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_55])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_36,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_16,plain,(
    ! [A_9] :
      ( k2_relat_1(k2_funct_1(A_9)) = k1_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    ! [A_8] :
      ( v1_relat_1(k2_funct_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_69,plain,(
    ! [A_32] :
      ( v1_funct_1(k2_funct_1(A_32))
      | ~ v2_funct_1(A_32)
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_60,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_72,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_69,c_60])).

tff(c_76,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_42,c_36,c_72])).

tff(c_78,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_34,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_118,plain,(
    ! [A_45,B_46,C_47] :
      ( k2_relset_1(A_45,B_46,C_47) = k2_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_121,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_118])).

tff(c_123,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_121])).

tff(c_132,plain,(
    ! [B_50,A_51] :
      ( m1_subset_1(B_50,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_50),A_51)))
      | ~ r1_tarski(k2_relat_1(B_50),A_51)
      | ~ v1_funct_1(B_50)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_22,plain,(
    ! [C_12,A_10,B_11] :
      ( v4_relat_1(C_12,A_10)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_164,plain,(
    ! [B_55,A_56] :
      ( v4_relat_1(B_55,k1_relat_1(B_55))
      | ~ r1_tarski(k2_relat_1(B_55),A_56)
      | ~ v1_funct_1(B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(resolution,[status(thm)],[c_132,c_22])).

tff(c_166,plain,(
    ! [A_56] :
      ( v4_relat_1('#skF_3',k1_relat_1('#skF_3'))
      | ~ r1_tarski('#skF_2',A_56)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_164])).

tff(c_170,plain,(
    ! [A_56] :
      ( v4_relat_1('#skF_3',k1_relat_1('#skF_3'))
      | ~ r1_tarski('#skF_2',A_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_42,c_166])).

tff(c_171,plain,(
    ! [A_56] : ~ r1_tarski('#skF_2',A_56) ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_18,plain,(
    ! [A_9] :
      ( k1_relat_1(k2_funct_1(A_9)) = k2_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_128,plain,(
    ! [B_48,A_49] :
      ( v1_funct_2(B_48,k1_relat_1(B_48),A_49)
      | ~ r1_tarski(k2_relat_1(B_48),A_49)
      | ~ v1_funct_1(B_48)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_193,plain,(
    ! [A_68,A_69] :
      ( v1_funct_2(k2_funct_1(A_68),k2_relat_1(A_68),A_69)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_68)),A_69)
      | ~ v1_funct_1(k2_funct_1(A_68))
      | ~ v1_relat_1(k2_funct_1(A_68))
      | ~ v2_funct_1(A_68)
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_128])).

tff(c_196,plain,(
    ! [A_69] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_69)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_69)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_193])).

tff(c_201,plain,(
    ! [A_69] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_69)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_69)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_42,c_36,c_78,c_196])).

tff(c_202,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_205,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_202])).

tff(c_209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_42,c_36,c_205])).

tff(c_211,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_187,plain,(
    ! [A_66,A_67] :
      ( v4_relat_1(k2_funct_1(A_66),k1_relat_1(k2_funct_1(A_66)))
      | ~ r1_tarski(k1_relat_1(A_66),A_67)
      | ~ v1_funct_1(k2_funct_1(A_66))
      | ~ v1_relat_1(k2_funct_1(A_66))
      | ~ v2_funct_1(A_66)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_164])).

tff(c_219,plain,(
    ! [B_72,A_73] :
      ( v4_relat_1(k2_funct_1(B_72),k1_relat_1(k2_funct_1(B_72)))
      | ~ v1_funct_1(k2_funct_1(B_72))
      | ~ v1_relat_1(k2_funct_1(B_72))
      | ~ v2_funct_1(B_72)
      | ~ v1_funct_1(B_72)
      | ~ v4_relat_1(B_72,A_73)
      | ~ v1_relat_1(B_72) ) ),
    inference(resolution,[status(thm)],[c_6,c_187])).

tff(c_223,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_59,c_219])).

tff(c_227,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_42,c_36,c_211,c_78,c_223])).

tff(c_93,plain,(
    ! [A_43] :
      ( k1_relat_1(k2_funct_1(A_43)) = k2_relat_1(A_43)
      | ~ v2_funct_1(A_43)
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_99,plain,(
    ! [A_43,A_4] :
      ( r1_tarski(k2_relat_1(A_43),A_4)
      | ~ v4_relat_1(k2_funct_1(A_43),A_4)
      | ~ v1_relat_1(k2_funct_1(A_43))
      | ~ v2_funct_1(A_43)
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_6])).

tff(c_232,plain,
    ( r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_227,c_99])).

tff(c_241,plain,(
    r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_42,c_36,c_211,c_123,c_232])).

tff(c_243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_241])).

tff(c_244,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_268,plain,(
    ! [A_83,A_84] :
      ( v4_relat_1(k2_funct_1(A_83),k1_relat_1(k2_funct_1(A_83)))
      | ~ r1_tarski(k1_relat_1(A_83),A_84)
      | ~ v1_funct_1(k2_funct_1(A_83))
      | ~ v1_relat_1(k2_funct_1(A_83))
      | ~ v2_funct_1(A_83)
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_164])).

tff(c_274,plain,(
    ! [B_85,A_86] :
      ( v4_relat_1(k2_funct_1(B_85),k1_relat_1(k2_funct_1(B_85)))
      | ~ v1_funct_1(k2_funct_1(B_85))
      | ~ v1_relat_1(k2_funct_1(B_85))
      | ~ v2_funct_1(B_85)
      | ~ v1_funct_1(B_85)
      | ~ v4_relat_1(B_85,A_86)
      | ~ v1_relat_1(B_85) ) ),
    inference(resolution,[status(thm)],[c_6,c_268])).

tff(c_278,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_244,c_274])).

tff(c_284,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_42,c_36,c_78,c_278])).

tff(c_288,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_284])).

tff(c_291,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_288])).

tff(c_295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_42,c_36,c_291])).

tff(c_297,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_284])).

tff(c_358,plain,(
    ! [A_91,A_92] :
      ( m1_subset_1(k2_funct_1(A_91),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_91),A_92)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_91)),A_92)
      | ~ v1_funct_1(k2_funct_1(A_91))
      | ~ v1_relat_1(k2_funct_1(A_91))
      | ~ v2_funct_1(A_91)
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_132])).

tff(c_373,plain,(
    ! [A_92] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_92)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_92)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_358])).

tff(c_385,plain,(
    ! [A_93] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_93)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_42,c_36,c_297,c_78,c_373])).

tff(c_77,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_117,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_402,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_385,c_117])).

tff(c_411,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_402])).

tff(c_413,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_42,c_36,c_411])).

tff(c_416,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_413])).

tff(c_420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_59,c_416])).

tff(c_422,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_431,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_422,c_2])).

tff(c_436,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_431])).

tff(c_437,plain,(
    ! [A_94,B_95,C_96] :
      ( k2_relset_1(A_94,B_95,C_96) = k2_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_443,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_437])).

tff(c_446,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_443])).

tff(c_447,plain,(
    ! [B_97,A_98] :
      ( v1_funct_2(B_97,k1_relat_1(B_97),A_98)
      | ~ r1_tarski(k2_relat_1(B_97),A_98)
      | ~ v1_funct_1(B_97)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_571,plain,(
    ! [A_124,A_125] :
      ( v1_funct_2(k2_funct_1(A_124),k2_relat_1(A_124),A_125)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_124)),A_125)
      | ~ v1_funct_1(k2_funct_1(A_124))
      | ~ v1_relat_1(k2_funct_1(A_124))
      | ~ v2_funct_1(A_124)
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_447])).

tff(c_574,plain,(
    ! [A_125] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_125)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_125)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_571])).

tff(c_602,plain,(
    ! [A_126] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_126)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_42,c_36,c_436,c_78,c_574])).

tff(c_605,plain,(
    ! [A_126] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_126)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_126)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_602])).

tff(c_608,plain,(
    ! [A_127] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_127)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_42,c_36,c_605])).

tff(c_421,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_612,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_608,c_421])).

tff(c_615,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_612])).

tff(c_619,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_59,c_615])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:21:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.49  
% 2.80/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.49  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.80/1.49  
% 2.80/1.49  %Foreground sorts:
% 2.80/1.49  
% 2.80/1.49  
% 2.80/1.49  %Background operators:
% 2.80/1.49  
% 2.80/1.49  
% 2.80/1.49  %Foreground operators:
% 2.80/1.49  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.80/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.80/1.49  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.80/1.49  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.80/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.80/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.80/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.80/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.80/1.49  tff('#skF_1', type, '#skF_1': $i).
% 2.80/1.49  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.80/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.80/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.80/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.80/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.49  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.80/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.80/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.80/1.49  
% 3.18/1.51  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.18/1.51  tff(f_101, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 3.18/1.51  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.18/1.51  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.18/1.51  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.18/1.51  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.18/1.51  tff(f_52, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 3.18/1.51  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.18/1.51  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 3.18/1.51  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.18/1.51  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.18/1.51  tff(c_48, plain, (![B_20, A_21]: (v1_relat_1(B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(A_21)) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.18/1.51  tff(c_51, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_48])).
% 3.18/1.51  tff(c_54, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_51])).
% 3.18/1.51  tff(c_55, plain, (![C_22, A_23, B_24]: (v4_relat_1(C_22, A_23) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.18/1.51  tff(c_59, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_55])).
% 3.18/1.51  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.18/1.51  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.18/1.51  tff(c_36, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.18/1.51  tff(c_16, plain, (![A_9]: (k2_relat_1(k2_funct_1(A_9))=k1_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.18/1.51  tff(c_14, plain, (![A_8]: (v1_relat_1(k2_funct_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.18/1.51  tff(c_69, plain, (![A_32]: (v1_funct_1(k2_funct_1(A_32)) | ~v2_funct_1(A_32) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.18/1.51  tff(c_32, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.18/1.51  tff(c_60, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_32])).
% 3.18/1.51  tff(c_72, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_69, c_60])).
% 3.18/1.51  tff(c_76, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_42, c_36, c_72])).
% 3.18/1.51  tff(c_78, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_32])).
% 3.18/1.51  tff(c_34, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.18/1.51  tff(c_118, plain, (![A_45, B_46, C_47]: (k2_relset_1(A_45, B_46, C_47)=k2_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.18/1.51  tff(c_121, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_118])).
% 3.18/1.51  tff(c_123, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_121])).
% 3.18/1.51  tff(c_132, plain, (![B_50, A_51]: (m1_subset_1(B_50, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_50), A_51))) | ~r1_tarski(k2_relat_1(B_50), A_51) | ~v1_funct_1(B_50) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.18/1.51  tff(c_22, plain, (![C_12, A_10, B_11]: (v4_relat_1(C_12, A_10) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.18/1.51  tff(c_164, plain, (![B_55, A_56]: (v4_relat_1(B_55, k1_relat_1(B_55)) | ~r1_tarski(k2_relat_1(B_55), A_56) | ~v1_funct_1(B_55) | ~v1_relat_1(B_55))), inference(resolution, [status(thm)], [c_132, c_22])).
% 3.18/1.51  tff(c_166, plain, (![A_56]: (v4_relat_1('#skF_3', k1_relat_1('#skF_3')) | ~r1_tarski('#skF_2', A_56) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_123, c_164])).
% 3.18/1.51  tff(c_170, plain, (![A_56]: (v4_relat_1('#skF_3', k1_relat_1('#skF_3')) | ~r1_tarski('#skF_2', A_56))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_42, c_166])).
% 3.18/1.51  tff(c_171, plain, (![A_56]: (~r1_tarski('#skF_2', A_56))), inference(splitLeft, [status(thm)], [c_170])).
% 3.18/1.51  tff(c_18, plain, (![A_9]: (k1_relat_1(k2_funct_1(A_9))=k2_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.18/1.51  tff(c_128, plain, (![B_48, A_49]: (v1_funct_2(B_48, k1_relat_1(B_48), A_49) | ~r1_tarski(k2_relat_1(B_48), A_49) | ~v1_funct_1(B_48) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.18/1.51  tff(c_193, plain, (![A_68, A_69]: (v1_funct_2(k2_funct_1(A_68), k2_relat_1(A_68), A_69) | ~r1_tarski(k2_relat_1(k2_funct_1(A_68)), A_69) | ~v1_funct_1(k2_funct_1(A_68)) | ~v1_relat_1(k2_funct_1(A_68)) | ~v2_funct_1(A_68) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(superposition, [status(thm), theory('equality')], [c_18, c_128])).
% 3.18/1.51  tff(c_196, plain, (![A_69]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_69) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_69) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_123, c_193])).
% 3.18/1.51  tff(c_201, plain, (![A_69]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_69) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_69) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_42, c_36, c_78, c_196])).
% 3.18/1.51  tff(c_202, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_201])).
% 3.18/1.51  tff(c_205, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_202])).
% 3.18/1.51  tff(c_209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_42, c_36, c_205])).
% 3.18/1.51  tff(c_211, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_201])).
% 3.18/1.51  tff(c_187, plain, (![A_66, A_67]: (v4_relat_1(k2_funct_1(A_66), k1_relat_1(k2_funct_1(A_66))) | ~r1_tarski(k1_relat_1(A_66), A_67) | ~v1_funct_1(k2_funct_1(A_66)) | ~v1_relat_1(k2_funct_1(A_66)) | ~v2_funct_1(A_66) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(superposition, [status(thm), theory('equality')], [c_16, c_164])).
% 3.18/1.51  tff(c_219, plain, (![B_72, A_73]: (v4_relat_1(k2_funct_1(B_72), k1_relat_1(k2_funct_1(B_72))) | ~v1_funct_1(k2_funct_1(B_72)) | ~v1_relat_1(k2_funct_1(B_72)) | ~v2_funct_1(B_72) | ~v1_funct_1(B_72) | ~v4_relat_1(B_72, A_73) | ~v1_relat_1(B_72))), inference(resolution, [status(thm)], [c_6, c_187])).
% 3.18/1.51  tff(c_223, plain, (v4_relat_1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_59, c_219])).
% 3.18/1.51  tff(c_227, plain, (v4_relat_1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_42, c_36, c_211, c_78, c_223])).
% 3.18/1.51  tff(c_93, plain, (![A_43]: (k1_relat_1(k2_funct_1(A_43))=k2_relat_1(A_43) | ~v2_funct_1(A_43) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.18/1.51  tff(c_99, plain, (![A_43, A_4]: (r1_tarski(k2_relat_1(A_43), A_4) | ~v4_relat_1(k2_funct_1(A_43), A_4) | ~v1_relat_1(k2_funct_1(A_43)) | ~v2_funct_1(A_43) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(superposition, [status(thm), theory('equality')], [c_93, c_6])).
% 3.18/1.51  tff(c_232, plain, (r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_227, c_99])).
% 3.18/1.51  tff(c_241, plain, (r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_42, c_36, c_211, c_123, c_232])).
% 3.18/1.51  tff(c_243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_171, c_241])).
% 3.18/1.51  tff(c_244, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_170])).
% 3.18/1.51  tff(c_268, plain, (![A_83, A_84]: (v4_relat_1(k2_funct_1(A_83), k1_relat_1(k2_funct_1(A_83))) | ~r1_tarski(k1_relat_1(A_83), A_84) | ~v1_funct_1(k2_funct_1(A_83)) | ~v1_relat_1(k2_funct_1(A_83)) | ~v2_funct_1(A_83) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(superposition, [status(thm), theory('equality')], [c_16, c_164])).
% 3.18/1.51  tff(c_274, plain, (![B_85, A_86]: (v4_relat_1(k2_funct_1(B_85), k1_relat_1(k2_funct_1(B_85))) | ~v1_funct_1(k2_funct_1(B_85)) | ~v1_relat_1(k2_funct_1(B_85)) | ~v2_funct_1(B_85) | ~v1_funct_1(B_85) | ~v4_relat_1(B_85, A_86) | ~v1_relat_1(B_85))), inference(resolution, [status(thm)], [c_6, c_268])).
% 3.18/1.51  tff(c_278, plain, (v4_relat_1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_244, c_274])).
% 3.18/1.51  tff(c_284, plain, (v4_relat_1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_42, c_36, c_78, c_278])).
% 3.18/1.51  tff(c_288, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_284])).
% 3.18/1.51  tff(c_291, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_288])).
% 3.18/1.51  tff(c_295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_42, c_36, c_291])).
% 3.18/1.51  tff(c_297, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_284])).
% 3.18/1.51  tff(c_358, plain, (![A_91, A_92]: (m1_subset_1(k2_funct_1(A_91), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_91), A_92))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_91)), A_92) | ~v1_funct_1(k2_funct_1(A_91)) | ~v1_relat_1(k2_funct_1(A_91)) | ~v2_funct_1(A_91) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(superposition, [status(thm), theory('equality')], [c_18, c_132])).
% 3.18/1.51  tff(c_373, plain, (![A_92]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_92))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_92) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_123, c_358])).
% 3.18/1.51  tff(c_385, plain, (![A_93]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_93))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_93))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_42, c_36, c_297, c_78, c_373])).
% 3.18/1.51  tff(c_77, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_32])).
% 3.18/1.51  tff(c_117, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_77])).
% 3.18/1.51  tff(c_402, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(resolution, [status(thm)], [c_385, c_117])).
% 3.18/1.51  tff(c_411, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_402])).
% 3.18/1.51  tff(c_413, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_42, c_36, c_411])).
% 3.18/1.51  tff(c_416, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_413])).
% 3.18/1.51  tff(c_420, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_59, c_416])).
% 3.18/1.51  tff(c_422, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_77])).
% 3.18/1.51  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.18/1.51  tff(c_431, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_422, c_2])).
% 3.18/1.51  tff(c_436, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_431])).
% 3.18/1.51  tff(c_437, plain, (![A_94, B_95, C_96]: (k2_relset_1(A_94, B_95, C_96)=k2_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.18/1.51  tff(c_443, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_437])).
% 3.18/1.51  tff(c_446, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_443])).
% 3.18/1.51  tff(c_447, plain, (![B_97, A_98]: (v1_funct_2(B_97, k1_relat_1(B_97), A_98) | ~r1_tarski(k2_relat_1(B_97), A_98) | ~v1_funct_1(B_97) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.18/1.51  tff(c_571, plain, (![A_124, A_125]: (v1_funct_2(k2_funct_1(A_124), k2_relat_1(A_124), A_125) | ~r1_tarski(k2_relat_1(k2_funct_1(A_124)), A_125) | ~v1_funct_1(k2_funct_1(A_124)) | ~v1_relat_1(k2_funct_1(A_124)) | ~v2_funct_1(A_124) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124))), inference(superposition, [status(thm), theory('equality')], [c_18, c_447])).
% 3.18/1.51  tff(c_574, plain, (![A_125]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_125) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_125) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_446, c_571])).
% 3.18/1.51  tff(c_602, plain, (![A_126]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_126) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_126))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_42, c_36, c_436, c_78, c_574])).
% 3.18/1.51  tff(c_605, plain, (![A_126]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_126) | ~r1_tarski(k1_relat_1('#skF_3'), A_126) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_602])).
% 3.18/1.51  tff(c_608, plain, (![A_127]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_127) | ~r1_tarski(k1_relat_1('#skF_3'), A_127))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_42, c_36, c_605])).
% 3.18/1.51  tff(c_421, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_77])).
% 3.18/1.51  tff(c_612, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_608, c_421])).
% 3.18/1.51  tff(c_615, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_612])).
% 3.18/1.51  tff(c_619, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_59, c_615])).
% 3.18/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.51  
% 3.18/1.51  Inference rules
% 3.18/1.51  ----------------------
% 3.18/1.51  #Ref     : 0
% 3.18/1.51  #Sup     : 118
% 3.18/1.51  #Fact    : 0
% 3.18/1.51  #Define  : 0
% 3.18/1.51  #Split   : 7
% 3.18/1.51  #Chain   : 0
% 3.18/1.51  #Close   : 0
% 3.18/1.51  
% 3.18/1.51  Ordering : KBO
% 3.18/1.51  
% 3.18/1.51  Simplification rules
% 3.18/1.51  ----------------------
% 3.18/1.51  #Subsume      : 6
% 3.18/1.51  #Demod        : 162
% 3.18/1.51  #Tautology    : 30
% 3.18/1.51  #SimpNegUnit  : 2
% 3.18/1.51  #BackRed      : 0
% 3.18/1.51  
% 3.18/1.51  #Partial instantiations: 0
% 3.18/1.51  #Strategies tried      : 1
% 3.18/1.51  
% 3.18/1.51  Timing (in seconds)
% 3.18/1.51  ----------------------
% 3.18/1.52  Preprocessing        : 0.33
% 3.18/1.52  Parsing              : 0.18
% 3.18/1.52  CNF conversion       : 0.02
% 3.18/1.52  Main loop            : 0.34
% 3.18/1.52  Inferencing          : 0.14
% 3.18/1.52  Reduction            : 0.10
% 3.18/1.52  Demodulation         : 0.07
% 3.18/1.52  BG Simplification    : 0.02
% 3.18/1.52  Subsumption          : 0.06
% 3.18/1.52  Abstraction          : 0.02
% 3.18/1.52  MUC search           : 0.00
% 3.18/1.52  Cooper               : 0.00
% 3.18/1.52  Total                : 0.71
% 3.18/1.52  Index Insertion      : 0.00
% 3.18/1.52  Index Deletion       : 0.00
% 3.18/1.52  Index Matching       : 0.00
% 3.18/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
