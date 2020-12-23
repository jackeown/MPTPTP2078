%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:58 EST 2020

% Result     : Theorem 4.87s
% Output     : CNFRefutation 4.87s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 708 expanded)
%              Number of leaves         :   44 ( 260 expanded)
%              Depth                    :   14
%              Number of atoms          :  145 (1635 expanded)
%              Number of equality atoms :   37 ( 363 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_136,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_40,plain,(
    ! [A_24,B_25] : v1_relat_1(k2_zfmisc_1(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_72,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_175,plain,(
    ! [B_69,A_70] :
      ( v1_relat_1(B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_70))
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_178,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_72,c_175])).

tff(c_187,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_178])).

tff(c_42,plain,(
    ! [B_27,A_26] :
      ( r1_tarski(k9_relat_1(B_27,A_26),k2_relat_1(B_27))
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_130,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(A_61,B_62)
      | ~ m1_subset_1(A_61,k1_zfmisc_1(B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_138,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(resolution,[status(thm)],[c_26,c_130])).

tff(c_76,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_24,plain,(
    ! [B_12] : k2_zfmisc_1(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_485,plain,(
    ! [B_118,A_119] :
      ( k1_tarski(k1_funct_1(B_118,A_119)) = k2_relat_1(B_118)
      | k1_tarski(A_119) != k1_relat_1(B_118)
      | ~ v1_funct_1(B_118)
      | ~ v1_relat_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_68,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_5','#skF_4'),k1_tarski(k1_funct_1('#skF_5','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_494,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_5','#skF_4'),k2_relat_1('#skF_5'))
    | k1_tarski('#skF_2') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_68])).

tff(c_500,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_5','#skF_4'),k2_relat_1('#skF_5'))
    | k1_tarski('#skF_2') != k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_76,c_494])).

tff(c_505,plain,(
    k1_tarski('#skF_2') != k1_relat_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_500])).

tff(c_222,plain,(
    ! [C_75,A_76,B_77] :
      ( v4_relat_1(C_75,A_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_240,plain,(
    v4_relat_1('#skF_5',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_222])).

tff(c_38,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k1_relat_1(B_23),A_22)
      | ~ v4_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_386,plain,(
    ! [B_98,A_99] :
      ( k1_tarski(B_98) = A_99
      | k1_xboole_0 = A_99
      | ~ r1_tarski(A_99,k1_tarski(B_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1566,plain,(
    ! [B_225,B_226] :
      ( k1_tarski(B_225) = k1_relat_1(B_226)
      | k1_relat_1(B_226) = k1_xboole_0
      | ~ v4_relat_1(B_226,k1_tarski(B_225))
      | ~ v1_relat_1(B_226) ) ),
    inference(resolution,[status(thm)],[c_38,c_386])).

tff(c_1596,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_5')
    | k1_relat_1('#skF_5') = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_240,c_1566])).

tff(c_1611,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_5')
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_1596])).

tff(c_1612,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_505,c_1611])).

tff(c_58,plain,(
    ! [C_45,B_44] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_45),B_44,C_45),k1_relat_1(C_45))
      | m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_45),B_44)))
      | ~ v1_funct_1(C_45)
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1647,plain,(
    ! [B_44] :
      ( r2_hidden('#skF_1'(k1_relat_1('#skF_5'),B_44,'#skF_5'),k1_xboole_0)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_44)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1612,c_58])).

tff(c_1690,plain,(
    ! [B_44] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_44,'#skF_5'),k1_xboole_0)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_76,c_24,c_1612,c_1612,c_1647])).

tff(c_1773,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_1690])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1799,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1773,c_28])).

tff(c_146,plain,(
    ! [B_66,A_67] :
      ( B_66 = A_67
      | ~ r1_tarski(B_66,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_157,plain,(
    ! [A_13] :
      ( k1_xboole_0 = A_13
      | ~ r1_tarski(A_13,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_138,c_146])).

tff(c_1826,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1799,c_157])).

tff(c_1864,plain,(
    ! [A_13] : r1_tarski('#skF_5',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1826,c_138])).

tff(c_539,plain,(
    ! [A_130,B_131,C_132,D_133] :
      ( k7_relset_1(A_130,B_131,C_132,D_133) = k9_relat_1(C_132,D_133)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_554,plain,(
    ! [A_130,B_131,D_133] : k7_relset_1(A_130,B_131,k1_xboole_0,D_133) = k9_relat_1(k1_xboole_0,D_133) ),
    inference(resolution,[status(thm)],[c_26,c_539])).

tff(c_579,plain,(
    ! [A_138,B_139,C_140,D_141] :
      ( m1_subset_1(k7_relset_1(A_138,B_139,C_140,D_141),k1_zfmisc_1(B_139))
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_610,plain,(
    ! [D_133,B_131,A_130] :
      ( m1_subset_1(k9_relat_1(k1_xboole_0,D_133),k1_zfmisc_1(B_131))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_554,c_579])).

tff(c_645,plain,(
    ! [D_144,B_145] : m1_subset_1(k9_relat_1(k1_xboole_0,D_144),k1_zfmisc_1(B_145)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_610])).

tff(c_709,plain,(
    ! [D_152,B_153] : r1_tarski(k9_relat_1(k1_xboole_0,D_152),B_153) ),
    inference(resolution,[status(thm)],[c_645,c_28])).

tff(c_742,plain,(
    ! [D_152] : k9_relat_1(k1_xboole_0,D_152) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_709,c_157])).

tff(c_1850,plain,(
    ! [D_152] : k9_relat_1('#skF_5',D_152) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1826,c_1826,c_742])).

tff(c_552,plain,(
    ! [D_133] : k7_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_5',D_133) = k9_relat_1('#skF_5',D_133) ),
    inference(resolution,[status(thm)],[c_72,c_539])).

tff(c_564,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5','#skF_4'),k1_tarski(k1_funct_1('#skF_5','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_68])).

tff(c_2047,plain,(
    ~ r1_tarski('#skF_5',k1_tarski(k1_funct_1('#skF_5','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1850,c_564])).

tff(c_2054,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1864,c_2047])).

tff(c_2067,plain,(
    ! [B_242] : r2_hidden('#skF_1'(k1_xboole_0,B_242,'#skF_5'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1690])).

tff(c_46,plain,(
    ! [B_31,A_30] :
      ( ~ r1_tarski(B_31,A_30)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2074,plain,(
    ! [B_242] : ~ r1_tarski(k1_xboole_0,'#skF_1'(k1_xboole_0,B_242,'#skF_5')) ),
    inference(resolution,[status(thm)],[c_2067,c_46])).

tff(c_2082,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_2074])).

tff(c_2084,plain,(
    k1_tarski('#skF_2') = k1_relat_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_500])).

tff(c_2090,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2084,c_72])).

tff(c_2249,plain,(
    ! [A_254,B_255,C_256,D_257] :
      ( k7_relset_1(A_254,B_255,C_256,D_257) = k9_relat_1(C_256,D_257)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_254,B_255))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2266,plain,(
    ! [D_257] : k7_relset_1(k1_relat_1('#skF_5'),'#skF_3','#skF_5',D_257) = k9_relat_1('#skF_5',D_257) ),
    inference(resolution,[status(thm)],[c_2090,c_2249])).

tff(c_2083,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_5','#skF_4'),k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_500])).

tff(c_2143,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_5'),'#skF_3','#skF_5','#skF_4'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2084,c_2083])).

tff(c_2319,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5','#skF_4'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2266,c_2143])).

tff(c_2421,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_2319])).

tff(c_2425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_2421])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:38:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.87/2.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/2.26  
% 4.87/2.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/2.26  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 4.87/2.26  
% 4.87/2.26  %Foreground sorts:
% 4.87/2.26  
% 4.87/2.26  
% 4.87/2.26  %Background operators:
% 4.87/2.26  
% 4.87/2.26  
% 4.87/2.26  %Foreground operators:
% 4.87/2.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.87/2.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.87/2.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.87/2.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.87/2.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.87/2.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.87/2.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.87/2.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.87/2.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.87/2.26  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.87/2.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.87/2.26  tff('#skF_5', type, '#skF_5': $i).
% 4.87/2.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.87/2.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.87/2.26  tff('#skF_2', type, '#skF_2': $i).
% 4.87/2.26  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.87/2.26  tff('#skF_3', type, '#skF_3': $i).
% 4.87/2.26  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.87/2.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.87/2.26  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.87/2.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.87/2.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.87/2.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.87/2.26  tff('#skF_4', type, '#skF_4': $i).
% 4.87/2.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.87/2.26  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.87/2.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.87/2.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.87/2.26  
% 4.87/2.27  tff(f_76, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.87/2.27  tff(f_136, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 4.87/2.27  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.87/2.27  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 4.87/2.27  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.87/2.27  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.87/2.27  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.87/2.27  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 4.87/2.27  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.87/2.27  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.87/2.27  tff(f_43, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.87/2.27  tff(f_124, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_funct_2)).
% 4.87/2.27  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.87/2.27  tff(f_107, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.87/2.27  tff(f_103, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 4.87/2.27  tff(f_93, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.87/2.27  tff(c_40, plain, (![A_24, B_25]: (v1_relat_1(k2_zfmisc_1(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.87/2.27  tff(c_72, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.87/2.27  tff(c_175, plain, (![B_69, A_70]: (v1_relat_1(B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_70)) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.87/2.27  tff(c_178, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))), inference(resolution, [status(thm)], [c_72, c_175])).
% 4.87/2.27  tff(c_187, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_178])).
% 4.87/2.27  tff(c_42, plain, (![B_27, A_26]: (r1_tarski(k9_relat_1(B_27, A_26), k2_relat_1(B_27)) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.87/2.27  tff(c_26, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.87/2.27  tff(c_130, plain, (![A_61, B_62]: (r1_tarski(A_61, B_62) | ~m1_subset_1(A_61, k1_zfmisc_1(B_62)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.87/2.27  tff(c_138, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(resolution, [status(thm)], [c_26, c_130])).
% 4.87/2.27  tff(c_76, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.87/2.27  tff(c_24, plain, (![B_12]: (k2_zfmisc_1(k1_xboole_0, B_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.87/2.27  tff(c_485, plain, (![B_118, A_119]: (k1_tarski(k1_funct_1(B_118, A_119))=k2_relat_1(B_118) | k1_tarski(A_119)!=k1_relat_1(B_118) | ~v1_funct_1(B_118) | ~v1_relat_1(B_118))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.87/2.27  tff(c_68, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_5', '#skF_4'), k1_tarski(k1_funct_1('#skF_5', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.87/2.27  tff(c_494, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_5', '#skF_4'), k2_relat_1('#skF_5')) | k1_tarski('#skF_2')!=k1_relat_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_485, c_68])).
% 4.87/2.27  tff(c_500, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_5', '#skF_4'), k2_relat_1('#skF_5')) | k1_tarski('#skF_2')!=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_187, c_76, c_494])).
% 4.87/2.27  tff(c_505, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_5')), inference(splitLeft, [status(thm)], [c_500])).
% 4.87/2.27  tff(c_222, plain, (![C_75, A_76, B_77]: (v4_relat_1(C_75, A_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.87/2.27  tff(c_240, plain, (v4_relat_1('#skF_5', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_72, c_222])).
% 4.87/2.27  tff(c_38, plain, (![B_23, A_22]: (r1_tarski(k1_relat_1(B_23), A_22) | ~v4_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.87/2.27  tff(c_386, plain, (![B_98, A_99]: (k1_tarski(B_98)=A_99 | k1_xboole_0=A_99 | ~r1_tarski(A_99, k1_tarski(B_98)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.87/2.27  tff(c_1566, plain, (![B_225, B_226]: (k1_tarski(B_225)=k1_relat_1(B_226) | k1_relat_1(B_226)=k1_xboole_0 | ~v4_relat_1(B_226, k1_tarski(B_225)) | ~v1_relat_1(B_226))), inference(resolution, [status(thm)], [c_38, c_386])).
% 4.87/2.27  tff(c_1596, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_5') | k1_relat_1('#skF_5')=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_240, c_1566])).
% 4.87/2.27  tff(c_1611, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_5') | k1_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_187, c_1596])).
% 4.87/2.27  tff(c_1612, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_505, c_1611])).
% 4.87/2.27  tff(c_58, plain, (![C_45, B_44]: (r2_hidden('#skF_1'(k1_relat_1(C_45), B_44, C_45), k1_relat_1(C_45)) | m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_45), B_44))) | ~v1_funct_1(C_45) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.87/2.27  tff(c_1647, plain, (![B_44]: (r2_hidden('#skF_1'(k1_relat_1('#skF_5'), B_44, '#skF_5'), k1_xboole_0) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_44))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1612, c_58])).
% 4.87/2.27  tff(c_1690, plain, (![B_44]: (r2_hidden('#skF_1'(k1_xboole_0, B_44, '#skF_5'), k1_xboole_0) | m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_76, c_24, c_1612, c_1612, c_1647])).
% 4.87/2.27  tff(c_1773, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_1690])).
% 4.87/2.27  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.87/2.27  tff(c_1799, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_1773, c_28])).
% 4.87/2.27  tff(c_146, plain, (![B_66, A_67]: (B_66=A_67 | ~r1_tarski(B_66, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.87/2.27  tff(c_157, plain, (![A_13]: (k1_xboole_0=A_13 | ~r1_tarski(A_13, k1_xboole_0))), inference(resolution, [status(thm)], [c_138, c_146])).
% 4.87/2.27  tff(c_1826, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1799, c_157])).
% 4.87/2.27  tff(c_1864, plain, (![A_13]: (r1_tarski('#skF_5', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_1826, c_138])).
% 4.87/2.27  tff(c_539, plain, (![A_130, B_131, C_132, D_133]: (k7_relset_1(A_130, B_131, C_132, D_133)=k9_relat_1(C_132, D_133) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.87/2.27  tff(c_554, plain, (![A_130, B_131, D_133]: (k7_relset_1(A_130, B_131, k1_xboole_0, D_133)=k9_relat_1(k1_xboole_0, D_133))), inference(resolution, [status(thm)], [c_26, c_539])).
% 4.87/2.27  tff(c_579, plain, (![A_138, B_139, C_140, D_141]: (m1_subset_1(k7_relset_1(A_138, B_139, C_140, D_141), k1_zfmisc_1(B_139)) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.87/2.27  tff(c_610, plain, (![D_133, B_131, A_130]: (m1_subset_1(k9_relat_1(k1_xboole_0, D_133), k1_zfmisc_1(B_131)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(superposition, [status(thm), theory('equality')], [c_554, c_579])).
% 4.87/2.27  tff(c_645, plain, (![D_144, B_145]: (m1_subset_1(k9_relat_1(k1_xboole_0, D_144), k1_zfmisc_1(B_145)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_610])).
% 4.87/2.27  tff(c_709, plain, (![D_152, B_153]: (r1_tarski(k9_relat_1(k1_xboole_0, D_152), B_153))), inference(resolution, [status(thm)], [c_645, c_28])).
% 4.87/2.27  tff(c_742, plain, (![D_152]: (k9_relat_1(k1_xboole_0, D_152)=k1_xboole_0)), inference(resolution, [status(thm)], [c_709, c_157])).
% 4.87/2.27  tff(c_1850, plain, (![D_152]: (k9_relat_1('#skF_5', D_152)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1826, c_1826, c_742])).
% 4.87/2.27  tff(c_552, plain, (![D_133]: (k7_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_5', D_133)=k9_relat_1('#skF_5', D_133))), inference(resolution, [status(thm)], [c_72, c_539])).
% 4.87/2.27  tff(c_564, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_4'), k1_tarski(k1_funct_1('#skF_5', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_552, c_68])).
% 4.87/2.27  tff(c_2047, plain, (~r1_tarski('#skF_5', k1_tarski(k1_funct_1('#skF_5', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1850, c_564])).
% 4.87/2.27  tff(c_2054, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1864, c_2047])).
% 4.87/2.27  tff(c_2067, plain, (![B_242]: (r2_hidden('#skF_1'(k1_xboole_0, B_242, '#skF_5'), k1_xboole_0))), inference(splitRight, [status(thm)], [c_1690])).
% 4.87/2.27  tff(c_46, plain, (![B_31, A_30]: (~r1_tarski(B_31, A_30) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.87/2.27  tff(c_2074, plain, (![B_242]: (~r1_tarski(k1_xboole_0, '#skF_1'(k1_xboole_0, B_242, '#skF_5')))), inference(resolution, [status(thm)], [c_2067, c_46])).
% 4.87/2.27  tff(c_2082, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138, c_2074])).
% 4.87/2.27  tff(c_2084, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_5')), inference(splitRight, [status(thm)], [c_500])).
% 4.87/2.27  tff(c_2090, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2084, c_72])).
% 4.87/2.27  tff(c_2249, plain, (![A_254, B_255, C_256, D_257]: (k7_relset_1(A_254, B_255, C_256, D_257)=k9_relat_1(C_256, D_257) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_254, B_255))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.87/2.27  tff(c_2266, plain, (![D_257]: (k7_relset_1(k1_relat_1('#skF_5'), '#skF_3', '#skF_5', D_257)=k9_relat_1('#skF_5', D_257))), inference(resolution, [status(thm)], [c_2090, c_2249])).
% 4.87/2.27  tff(c_2083, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_5', '#skF_4'), k2_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_500])).
% 4.87/2.27  tff(c_2143, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_5'), '#skF_3', '#skF_5', '#skF_4'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2084, c_2083])).
% 4.87/2.27  tff(c_2319, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_4'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2266, c_2143])).
% 4.87/2.27  tff(c_2421, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_2319])).
% 4.87/2.27  tff(c_2425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_187, c_2421])).
% 4.87/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/2.27  
% 4.87/2.27  Inference rules
% 4.87/2.27  ----------------------
% 4.87/2.27  #Ref     : 0
% 4.87/2.27  #Sup     : 461
% 4.87/2.27  #Fact    : 0
% 4.87/2.27  #Define  : 0
% 4.87/2.27  #Split   : 9
% 4.87/2.27  #Chain   : 0
% 4.87/2.27  #Close   : 0
% 4.87/2.27  
% 4.87/2.27  Ordering : KBO
% 4.87/2.27  
% 4.87/2.27  Simplification rules
% 4.87/2.27  ----------------------
% 4.87/2.27  #Subsume      : 60
% 4.87/2.27  #Demod        : 662
% 4.87/2.27  #Tautology    : 241
% 4.87/2.27  #SimpNegUnit  : 19
% 4.87/2.27  #BackRed      : 113
% 4.87/2.27  
% 4.87/2.27  #Partial instantiations: 0
% 4.87/2.27  #Strategies tried      : 1
% 4.87/2.27  
% 4.87/2.27  Timing (in seconds)
% 4.87/2.27  ----------------------
% 4.87/2.28  Preprocessing        : 0.55
% 4.87/2.28  Parsing              : 0.28
% 4.87/2.28  CNF conversion       : 0.04
% 4.87/2.28  Main loop            : 0.81
% 4.87/2.28  Inferencing          : 0.28
% 4.87/2.28  Reduction            : 0.29
% 4.87/2.28  Demodulation         : 0.21
% 4.87/2.28  BG Simplification    : 0.04
% 4.87/2.28  Subsumption          : 0.14
% 4.87/2.28  Abstraction          : 0.03
% 4.87/2.28  MUC search           : 0.00
% 4.87/2.28  Cooper               : 0.00
% 4.87/2.28  Total                : 1.40
% 4.87/2.28  Index Insertion      : 0.00
% 4.87/2.28  Index Deletion       : 0.00
% 4.87/2.28  Index Matching       : 0.00
% 4.87/2.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
