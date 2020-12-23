%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0985+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:11 EST 2020

% Result     : Theorem 4.45s
% Output     : CNFRefutation 4.45s
% Verified   : 
% Statistics : Number of formulae       :  190 (1603 expanded)
%              Number of leaves         :   39 ( 512 expanded)
%              Depth                    :   20
%              Number of atoms          :  289 (3948 expanded)
%              Number of equality atoms :   68 ( 681 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
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

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_115,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_70,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_119,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_73,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_205,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_xboole_0(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_218,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_205])).

tff(c_220,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_177,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_190,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_177])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_54,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_52,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1082,plain,(
    ! [A_137,B_138,C_139] :
      ( k2_relset_1(A_137,B_138,C_139) = k2_relat_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1095,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_1082])).

tff(c_1105,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1095])).

tff(c_46,plain,(
    ! [A_33] :
      ( k1_relat_1(k2_funct_1(A_33)) = k2_relat_1(A_33)
      | ~ v2_funct_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_554,plain,(
    ! [A_106,B_107,C_108] :
      ( m1_subset_1(k2_relset_1(A_106,B_107,C_108),k1_zfmisc_1(B_107))
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_585,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_554])).

tff(c_592,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_585])).

tff(c_40,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_596,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_592,c_40])).

tff(c_414,plain,(
    ! [A_87,B_88,C_89] :
      ( k2_relset_1(A_87,B_88,C_89) = k2_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_424,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_414])).

tff(c_433,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_424])).

tff(c_344,plain,(
    ! [A_79,B_80,C_81] :
      ( k1_relset_1(A_79,B_80,C_81) = k1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_361,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_344])).

tff(c_669,plain,(
    ! [A_112,B_113,C_114] :
      ( m1_subset_1(k1_relset_1(A_112,B_113,C_114),k1_zfmisc_1(A_112))
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_697,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_669])).

tff(c_708,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_697])).

tff(c_712,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_708,c_40])).

tff(c_44,plain,(
    ! [A_33] :
      ( k2_relat_1(k2_funct_1(A_33)) = k1_relat_1(A_33)
      | ~ v2_funct_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_22,plain,(
    ! [A_14] :
      ( v1_relat_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_937,plain,(
    ! [C_128,A_129,B_130] :
      ( m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130)))
      | ~ r1_tarski(k2_relat_1(C_128),B_130)
      | ~ r1_tarski(k1_relat_1(C_128),A_129)
      | ~ v1_relat_1(C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_148,plain,(
    ! [A_46] :
      ( v1_funct_1(k2_funct_1(A_46))
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_50,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_147,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_151,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_148,c_147])).

tff(c_154,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_151])).

tff(c_156,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_163,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_156])).

tff(c_172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_163])).

tff(c_173,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_367,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_972,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_4')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_4')),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_937,c_367])).

tff(c_990,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_972])).

tff(c_993,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_990])).

tff(c_997,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_60,c_993])).

tff(c_998,plain,
    ( ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_4')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_4')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_972])).

tff(c_1044,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_4')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_998])).

tff(c_1047,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1044])).

tff(c_1050,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_60,c_54,c_712,c_1047])).

tff(c_1051,plain,(
    ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_4')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_998])).

tff(c_1060,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1051])).

tff(c_1063,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_60,c_54,c_596,c_433,c_1060])).

tff(c_1064,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_1065,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_34,plain,(
    ! [A_22,B_23,C_24] :
      ( k1_relset_1(A_22,B_23,C_24) = k1_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1078,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1065,c_34])).

tff(c_1752,plain,(
    ! [B_182,C_183,A_184] :
      ( k1_xboole_0 = B_182
      | v1_funct_2(C_183,A_184,B_182)
      | k1_relset_1(A_184,B_182,C_183) != A_184
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_184,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1770,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_1065,c_1752])).

tff(c_1788,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1078,c_1770])).

tff(c_1789,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1064,c_1788])).

tff(c_1795,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1789])).

tff(c_1798,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1795])).

tff(c_1801,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_60,c_54,c_1105,c_1798])).

tff(c_1802,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1789])).

tff(c_26,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_62,plain,(
    ! [A_36] :
      ( k1_xboole_0 = A_36
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_66,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_62])).

tff(c_67,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_26])).

tff(c_1822,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1802,c_67])).

tff(c_1826,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_1822])).

tff(c_1827,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_48,plain,(
    ! [A_34] :
      ( k1_xboole_0 = A_34
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2907,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1827,c_48])).

tff(c_1828,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_2915,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1828,c_48])).

tff(c_2927,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2907,c_2915])).

tff(c_2932,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2927,c_52])).

tff(c_81,plain,(
    ! [A_37] :
      ( v1_xboole_0(k2_relat_1(A_37))
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_85,plain,(
    ! [A_37] :
      ( k2_relat_1(A_37) = k1_xboole_0
      | ~ v1_xboole_0(A_37) ) ),
    inference(resolution,[status(thm)],[c_81,c_48])).

tff(c_2906,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1827,c_85])).

tff(c_2943,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2907,c_2906])).

tff(c_2931,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2927,c_56])).

tff(c_3166,plain,(
    ! [A_290,B_291,C_292] :
      ( k2_relset_1(A_290,B_291,C_292) = k2_relat_1(C_292)
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(A_290,B_291))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3172,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2931,c_3166])).

tff(c_3187,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2932,c_2943,c_3172])).

tff(c_28,plain,(
    ! [A_18] : m1_subset_1('#skF_1'(A_18),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1975,plain,(
    ! [A_189,B_190] :
      ( v1_xboole_0('#skF_1'(k1_zfmisc_1(k2_zfmisc_1(A_189,B_190))))
      | ~ v1_xboole_0(A_189) ) ),
    inference(resolution,[status(thm)],[c_28,c_205])).

tff(c_1837,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1827,c_48])).

tff(c_1851,plain,(
    ! [A_34] :
      ( A_34 = '#skF_4'
      | ~ v1_xboole_0(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1837,c_48])).

tff(c_1984,plain,(
    ! [A_191,B_192] :
      ( '#skF_1'(k1_zfmisc_1(k2_zfmisc_1(A_191,B_192))) = '#skF_4'
      | ~ v1_xboole_0(A_191) ) ),
    inference(resolution,[status(thm)],[c_1975,c_1851])).

tff(c_1998,plain,(
    ! [A_191,B_192] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_191,B_192)))
      | ~ v1_xboole_0(A_191) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1984,c_28])).

tff(c_1845,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1828,c_48])).

tff(c_1857,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1837,c_1845])).

tff(c_1844,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1828,c_85])).

tff(c_1877,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1857,c_1837,c_1844])).

tff(c_2100,plain,(
    ! [A_206,B_207,C_208] :
      ( k2_relset_1(A_206,B_207,C_208) = k2_relat_1(C_208)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_206,B_207))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2103,plain,(
    ! [A_191,B_192] :
      ( k2_relset_1(A_191,B_192,'#skF_4') = k2_relat_1('#skF_4')
      | ~ v1_xboole_0(A_191) ) ),
    inference(resolution,[status(thm)],[c_1998,c_2100])).

tff(c_2232,plain,(
    ! [A_213,B_214] :
      ( k2_relset_1(A_213,B_214,'#skF_4') = '#skF_4'
      | ~ v1_xboole_0(A_213) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1877,c_2103])).

tff(c_2243,plain,(
    ! [B_215] : k2_relset_1('#skF_4',B_215,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1827,c_2232])).

tff(c_24,plain,(
    ! [A_15,B_16,C_17] :
      ( m1_subset_1(k2_relset_1(A_15,B_16,C_17),k1_zfmisc_1(B_16))
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2309,plain,(
    ! [B_222] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(B_222))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_222))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2243,c_24])).

tff(c_2316,plain,(
    ! [B_192] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(B_192))
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1998,c_2309])).

tff(c_2333,plain,(
    ! [B_223] : m1_subset_1('#skF_4',k1_zfmisc_1(B_223)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1827,c_2316])).

tff(c_2360,plain,(
    ! [B_223] : r1_tarski('#skF_4',B_223) ),
    inference(resolution,[status(thm)],[c_2333,c_40])).

tff(c_2324,plain,(
    ! [B_192] : m1_subset_1('#skF_4',k1_zfmisc_1(B_192)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1827,c_2316])).

tff(c_2394,plain,(
    ! [A_228,B_229] : k1_relset_1(A_228,B_229,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2333,c_34])).

tff(c_18,plain,(
    ! [A_11,B_12,C_13] :
      ( m1_subset_1(k1_relset_1(A_11,B_12,C_13),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2399,plain,(
    ! [A_228,B_229] :
      ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(A_228))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_228,B_229))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2394,c_18])).

tff(c_2435,plain,(
    ! [A_232] : m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(A_232)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2324,c_2399])).

tff(c_4,plain,(
    ! [C_7,A_4,B_5] :
      ( v1_xboole_0(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5)))
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2462,plain,(
    ! [A_4] :
      ( v1_xboole_0(k1_relat_1('#skF_4'))
      | ~ v1_xboole_0(A_4) ) ),
    inference(resolution,[status(thm)],[c_2435,c_4])).

tff(c_2480,plain,(
    ! [A_4] : ~ v1_xboole_0(A_4) ),
    inference(splitLeft,[status(thm)],[c_2462])).

tff(c_2487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2480,c_1827])).

tff(c_2488,plain,(
    v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2462])).

tff(c_2499,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2488,c_1851])).

tff(c_2625,plain,(
    ! [C_247,A_248,B_249] :
      ( m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249)))
      | ~ r1_tarski(k2_relat_1(C_247),B_249)
      | ~ r1_tarski(k1_relat_1(C_247),A_248)
      | ~ v1_relat_1(C_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1861,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1857,c_52])).

tff(c_1860,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1857,c_56])).

tff(c_2106,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1860,c_2100])).

tff(c_2118,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1861,c_1877,c_2106])).

tff(c_1829,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_1872,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1857,c_1829])).

tff(c_2127,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2118,c_1872])).

tff(c_2659,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2625,c_2127])).

tff(c_2836,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2659])).

tff(c_2839,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_2836])).

tff(c_2843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_60,c_2839])).

tff(c_2844,plain,
    ( ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_4')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_2659])).

tff(c_2846,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_4')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2844])).

tff(c_2849,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_2846])).

tff(c_2852,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_60,c_54,c_2360,c_2499,c_2849])).

tff(c_2853,plain,(
    ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_4')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_2844])).

tff(c_2894,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2853])).

tff(c_2897,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_60,c_54,c_2360,c_1877,c_2894])).

tff(c_2899,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_2954,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2927,c_2899])).

tff(c_2964,plain,
    ( v1_xboole_0(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2954,c_4])).

tff(c_3009,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2964])).

tff(c_3193,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3187,c_3009])).

tff(c_3201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1827,c_3193])).

tff(c_3203,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2964])).

tff(c_2921,plain,(
    ! [A_34] :
      ( A_34 = '#skF_4'
      | ~ v1_xboole_0(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2907,c_48])).

tff(c_3211,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3203,c_2921])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2933,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2927,c_58])).

tff(c_3216,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3211,c_2933])).

tff(c_3202,plain,(
    v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2964])).

tff(c_3230,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3202,c_2921])).

tff(c_2898,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_2928,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2927,c_2898])).

tff(c_3213,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3211,c_2928])).

tff(c_3302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3216,c_3230,c_3213])).

%------------------------------------------------------------------------------
