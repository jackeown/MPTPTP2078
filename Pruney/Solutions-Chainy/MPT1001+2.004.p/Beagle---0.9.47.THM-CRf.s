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
% DateTime   : Thu Dec  3 10:13:55 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 141 expanded)
%              Number of leaves         :   37 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  132 ( 285 expanded)
%              Number of equality atoms :   40 (  93 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & k8_relset_1(A,B,C,k1_tarski(D)) = k1_xboole_0 )
        <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( ! [C] :
            ~ ( r2_hidden(C,A)
              & k10_relat_1(B,k1_tarski(C)) = k1_xboole_0 )
       => r1_tarski(A,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_funct_1)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_46,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_329,plain,(
    ! [A_99,B_100,C_101] :
      ( k2_relset_1(A_99,B_100,C_101) = k2_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_338,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_329])).

tff(c_48,plain,
    ( k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_71,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_339,plain,(
    k2_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_71])).

tff(c_412,plain,(
    ! [A_117,B_118,C_119] :
      ( m1_subset_1(k2_relset_1(A_117,B_118,C_119),k1_zfmisc_1(B_118))
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_429,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_412])).

tff(c_434,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_429])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_438,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_434,c_18])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_452,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_438,c_4])).

tff(c_455,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_339,c_452])).

tff(c_96,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_105,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_96])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_1'(A_14,B_15),A_14)
      | r1_tarski(A_14,k2_relat_1(B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    ! [B_15,A_14] :
      ( k10_relat_1(B_15,k1_tarski('#skF_1'(A_14,B_15))) = k1_xboole_0
      | r1_tarski(A_14,k2_relat_1(B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_439,plain,(
    ! [A_120,B_121,C_122,D_123] :
      ( k8_relset_1(A_120,B_121,C_122,D_123) = k10_relat_1(C_122,D_123)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_450,plain,(
    ! [D_123] : k8_relset_1('#skF_2','#skF_3','#skF_4',D_123) = k10_relat_1('#skF_4',D_123) ),
    inference(resolution,[status(thm)],[c_38,c_439])).

tff(c_54,plain,(
    ! [D_32] :
      ( k8_relset_1('#skF_2','#skF_3','#skF_4',k1_tarski(D_32)) != k1_xboole_0
      | ~ r2_hidden(D_32,'#skF_3')
      | k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_391,plain,(
    ! [D_32] :
      ( k8_relset_1('#skF_2','#skF_3','#skF_4',k1_tarski(D_32)) != k1_xboole_0
      | ~ r2_hidden(D_32,'#skF_3')
      | k2_relat_1('#skF_4') = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_54])).

tff(c_392,plain,(
    ! [D_32] :
      ( k8_relset_1('#skF_2','#skF_3','#skF_4',k1_tarski(D_32)) != k1_xboole_0
      | ~ r2_hidden(D_32,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_339,c_391])).

tff(c_468,plain,(
    ! [D_125] :
      ( k10_relat_1('#skF_4',k1_tarski(D_125)) != k1_xboole_0
      | ~ r2_hidden(D_125,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_392])).

tff(c_472,plain,(
    ! [A_14] :
      ( ~ r2_hidden('#skF_1'(A_14,'#skF_4'),'#skF_3')
      | r1_tarski(A_14,k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_468])).

tff(c_476,plain,(
    ! [A_126] :
      ( ~ r2_hidden('#skF_1'(A_126,'#skF_4'),'#skF_3')
      | r1_tarski(A_126,k2_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_472])).

tff(c_480,plain,
    ( r1_tarski('#skF_3',k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_476])).

tff(c_483,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_480])).

tff(c_485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_455,c_483])).

tff(c_486,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_780,plain,(
    ! [A_177,B_178,C_179,D_180] :
      ( k8_relset_1(A_177,B_178,C_179,D_180) = k10_relat_1(C_179,D_180)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_792,plain,(
    ! [D_181] : k8_relset_1('#skF_2','#skF_3','#skF_4',D_181) = k10_relat_1('#skF_4',D_181) ),
    inference(resolution,[status(thm)],[c_38,c_780])).

tff(c_487,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_44,plain,
    ( k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | k8_relset_1('#skF_2','#skF_3','#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_516,plain,(
    k8_relset_1('#skF_2','#skF_3','#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_44])).

tff(c_798,plain,(
    k10_relat_1('#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_792,c_516])).

tff(c_12,plain,(
    ! [A_7] : ~ v1_xboole_0(k1_tarski(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k1_tarski(A_8),B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_521,plain,(
    ! [C_133,A_134,B_135] :
      ( v1_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_530,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_521])).

tff(c_598,plain,(
    ! [A_156,B_157,C_158] :
      ( k2_relset_1(A_156,B_157,C_158) = k2_relat_1(C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_605,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_598])).

tff(c_608,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_605])).

tff(c_549,plain,(
    ! [B_143,A_144] :
      ( r1_xboole_0(k2_relat_1(B_143),A_144)
      | k10_relat_1(B_143,A_144) != k1_xboole_0
      | ~ v1_relat_1(B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_556,plain,(
    ! [A_144,B_143] :
      ( r1_xboole_0(A_144,k2_relat_1(B_143))
      | k10_relat_1(B_143,A_144) != k1_xboole_0
      | ~ v1_relat_1(B_143) ) ),
    inference(resolution,[status(thm)],[c_549,c_2])).

tff(c_621,plain,(
    ! [A_144] :
      ( r1_xboole_0(A_144,'#skF_3')
      | k10_relat_1('#skF_4',A_144) != k1_xboole_0
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_608,c_556])).

tff(c_637,plain,(
    ! [A_161] :
      ( r1_xboole_0(A_161,'#skF_3')
      | k10_relat_1('#skF_4',A_161) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_530,c_621])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( ~ r1_xboole_0(B_6,A_5)
      | ~ r1_tarski(B_6,A_5)
      | v1_xboole_0(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_674,plain,(
    ! [A_164] :
      ( ~ r1_tarski(A_164,'#skF_3')
      | v1_xboole_0(A_164)
      | k10_relat_1('#skF_4',A_164) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_637,c_10])).

tff(c_678,plain,(
    ! [A_8] :
      ( v1_xboole_0(k1_tarski(A_8))
      | k10_relat_1('#skF_4',k1_tarski(A_8)) != k1_xboole_0
      | ~ r2_hidden(A_8,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_674])).

tff(c_685,plain,(
    ! [A_8] :
      ( k10_relat_1('#skF_4',k1_tarski(A_8)) != k1_xboole_0
      | ~ r2_hidden(A_8,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_678])).

tff(c_810,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_798,c_685])).

tff(c_816,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_810])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:04:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.43  
% 2.79/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.44  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.79/1.44  
% 2.79/1.44  %Foreground sorts:
% 2.79/1.44  
% 2.79/1.44  
% 2.79/1.44  %Background operators:
% 2.79/1.44  
% 2.79/1.44  
% 2.79/1.44  %Foreground operators:
% 2.79/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.79/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.79/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.79/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.79/1.44  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.79/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.79/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.79/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.79/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.79/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.79/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.79/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.44  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.79/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.79/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.79/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.79/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.79/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.79/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.44  
% 2.79/1.45  tff(f_101, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (k8_relset_1(A, B, C, k1_tarski(D)) = k1_xboole_0))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_funct_2)).
% 2.79/1.45  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.79/1.45  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.79/1.45  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.79/1.45  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.79/1.45  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.79/1.45  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => ((![C]: ~(r2_hidden(C, A) & (k10_relat_1(B, k1_tarski(C)) = k1_xboole_0))) => r1_tarski(A, k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_funct_1)).
% 2.79/1.45  tff(f_86, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.79/1.45  tff(f_46, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.79/1.45  tff(f_50, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.79/1.45  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 2.79/1.45  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.79/1.45  tff(f_43, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.79/1.45  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.79/1.45  tff(c_329, plain, (![A_99, B_100, C_101]: (k2_relset_1(A_99, B_100, C_101)=k2_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.79/1.45  tff(c_338, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_329])).
% 2.79/1.45  tff(c_48, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.79/1.45  tff(c_71, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_48])).
% 2.79/1.45  tff(c_339, plain, (k2_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_338, c_71])).
% 2.79/1.45  tff(c_412, plain, (![A_117, B_118, C_119]: (m1_subset_1(k2_relset_1(A_117, B_118, C_119), k1_zfmisc_1(B_118)) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.79/1.45  tff(c_429, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_338, c_412])).
% 2.79/1.45  tff(c_434, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_429])).
% 2.79/1.45  tff(c_18, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.79/1.45  tff(c_438, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_434, c_18])).
% 2.79/1.45  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.79/1.45  tff(c_452, plain, (k2_relat_1('#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_438, c_4])).
% 2.79/1.45  tff(c_455, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_339, c_452])).
% 2.79/1.45  tff(c_96, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.79/1.45  tff(c_105, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_96])).
% 2.79/1.45  tff(c_28, plain, (![A_14, B_15]: (r2_hidden('#skF_1'(A_14, B_15), A_14) | r1_tarski(A_14, k2_relat_1(B_15)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.79/1.45  tff(c_26, plain, (![B_15, A_14]: (k10_relat_1(B_15, k1_tarski('#skF_1'(A_14, B_15)))=k1_xboole_0 | r1_tarski(A_14, k2_relat_1(B_15)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.79/1.45  tff(c_439, plain, (![A_120, B_121, C_122, D_123]: (k8_relset_1(A_120, B_121, C_122, D_123)=k10_relat_1(C_122, D_123) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.79/1.45  tff(c_450, plain, (![D_123]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', D_123)=k10_relat_1('#skF_4', D_123))), inference(resolution, [status(thm)], [c_38, c_439])).
% 2.79/1.45  tff(c_54, plain, (![D_32]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', k1_tarski(D_32))!=k1_xboole_0 | ~r2_hidden(D_32, '#skF_3') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.79/1.45  tff(c_391, plain, (![D_32]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', k1_tarski(D_32))!=k1_xboole_0 | ~r2_hidden(D_32, '#skF_3') | k2_relat_1('#skF_4')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_338, c_54])).
% 2.79/1.45  tff(c_392, plain, (![D_32]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', k1_tarski(D_32))!=k1_xboole_0 | ~r2_hidden(D_32, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_339, c_391])).
% 2.79/1.45  tff(c_468, plain, (![D_125]: (k10_relat_1('#skF_4', k1_tarski(D_125))!=k1_xboole_0 | ~r2_hidden(D_125, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_450, c_392])).
% 2.79/1.45  tff(c_472, plain, (![A_14]: (~r2_hidden('#skF_1'(A_14, '#skF_4'), '#skF_3') | r1_tarski(A_14, k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_468])).
% 2.79/1.45  tff(c_476, plain, (![A_126]: (~r2_hidden('#skF_1'(A_126, '#skF_4'), '#skF_3') | r1_tarski(A_126, k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_472])).
% 2.79/1.45  tff(c_480, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_476])).
% 2.79/1.45  tff(c_483, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_480])).
% 2.79/1.45  tff(c_485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_455, c_483])).
% 2.79/1.45  tff(c_486, plain, (r2_hidden('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 2.79/1.45  tff(c_780, plain, (![A_177, B_178, C_179, D_180]: (k8_relset_1(A_177, B_178, C_179, D_180)=k10_relat_1(C_179, D_180) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.79/1.45  tff(c_792, plain, (![D_181]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', D_181)=k10_relat_1('#skF_4', D_181))), inference(resolution, [status(thm)], [c_38, c_780])).
% 2.79/1.45  tff(c_487, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_48])).
% 2.79/1.45  tff(c_44, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | k8_relset_1('#skF_2', '#skF_3', '#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.79/1.45  tff(c_516, plain, (k8_relset_1('#skF_2', '#skF_3', '#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_487, c_44])).
% 2.79/1.45  tff(c_798, plain, (k10_relat_1('#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_792, c_516])).
% 2.79/1.45  tff(c_12, plain, (![A_7]: (~v1_xboole_0(k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.79/1.45  tff(c_16, plain, (![A_8, B_9]: (r1_tarski(k1_tarski(A_8), B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.79/1.45  tff(c_521, plain, (![C_133, A_134, B_135]: (v1_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.79/1.45  tff(c_530, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_521])).
% 2.79/1.45  tff(c_598, plain, (![A_156, B_157, C_158]: (k2_relset_1(A_156, B_157, C_158)=k2_relat_1(C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.79/1.45  tff(c_605, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_598])).
% 2.79/1.45  tff(c_608, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_487, c_605])).
% 2.79/1.45  tff(c_549, plain, (![B_143, A_144]: (r1_xboole_0(k2_relat_1(B_143), A_144) | k10_relat_1(B_143, A_144)!=k1_xboole_0 | ~v1_relat_1(B_143))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.79/1.45  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.79/1.45  tff(c_556, plain, (![A_144, B_143]: (r1_xboole_0(A_144, k2_relat_1(B_143)) | k10_relat_1(B_143, A_144)!=k1_xboole_0 | ~v1_relat_1(B_143))), inference(resolution, [status(thm)], [c_549, c_2])).
% 2.79/1.45  tff(c_621, plain, (![A_144]: (r1_xboole_0(A_144, '#skF_3') | k10_relat_1('#skF_4', A_144)!=k1_xboole_0 | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_608, c_556])).
% 2.79/1.45  tff(c_637, plain, (![A_161]: (r1_xboole_0(A_161, '#skF_3') | k10_relat_1('#skF_4', A_161)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_530, c_621])).
% 2.79/1.45  tff(c_10, plain, (![B_6, A_5]: (~r1_xboole_0(B_6, A_5) | ~r1_tarski(B_6, A_5) | v1_xboole_0(B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.79/1.45  tff(c_674, plain, (![A_164]: (~r1_tarski(A_164, '#skF_3') | v1_xboole_0(A_164) | k10_relat_1('#skF_4', A_164)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_637, c_10])).
% 2.79/1.45  tff(c_678, plain, (![A_8]: (v1_xboole_0(k1_tarski(A_8)) | k10_relat_1('#skF_4', k1_tarski(A_8))!=k1_xboole_0 | ~r2_hidden(A_8, '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_674])).
% 2.79/1.45  tff(c_685, plain, (![A_8]: (k10_relat_1('#skF_4', k1_tarski(A_8))!=k1_xboole_0 | ~r2_hidden(A_8, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_12, c_678])).
% 2.79/1.45  tff(c_810, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_798, c_685])).
% 2.79/1.45  tff(c_816, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_486, c_810])).
% 2.79/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.45  
% 2.79/1.45  Inference rules
% 2.79/1.45  ----------------------
% 2.79/1.45  #Ref     : 0
% 2.79/1.45  #Sup     : 150
% 2.79/1.45  #Fact    : 0
% 2.79/1.45  #Define  : 0
% 2.79/1.45  #Split   : 7
% 2.79/1.45  #Chain   : 0
% 2.79/1.45  #Close   : 0
% 2.79/1.45  
% 2.79/1.45  Ordering : KBO
% 2.79/1.45  
% 2.79/1.45  Simplification rules
% 2.79/1.45  ----------------------
% 2.79/1.45  #Subsume      : 10
% 2.79/1.45  #Demod        : 47
% 2.79/1.46  #Tautology    : 56
% 2.79/1.46  #SimpNegUnit  : 10
% 2.79/1.46  #BackRed      : 4
% 2.79/1.46  
% 2.79/1.46  #Partial instantiations: 0
% 2.79/1.46  #Strategies tried      : 1
% 2.79/1.46  
% 2.79/1.46  Timing (in seconds)
% 2.79/1.46  ----------------------
% 3.07/1.46  Preprocessing        : 0.32
% 3.07/1.46  Parsing              : 0.17
% 3.07/1.46  CNF conversion       : 0.02
% 3.07/1.46  Main loop            : 0.35
% 3.07/1.46  Inferencing          : 0.14
% 3.07/1.46  Reduction            : 0.10
% 3.07/1.46  Demodulation         : 0.07
% 3.07/1.46  BG Simplification    : 0.02
% 3.07/1.46  Subsumption          : 0.06
% 3.07/1.46  Abstraction          : 0.02
% 3.07/1.46  MUC search           : 0.00
% 3.07/1.46  Cooper               : 0.00
% 3.07/1.46  Total                : 0.70
% 3.07/1.46  Index Insertion      : 0.00
% 3.07/1.46  Index Deletion       : 0.00
% 3.07/1.46  Index Matching       : 0.00
% 3.07/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
