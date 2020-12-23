%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:20 EST 2020

% Result     : Theorem 5.15s
% Output     : CNFRefutation 5.51s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 419 expanded)
%              Number of leaves         :   40 ( 159 expanded)
%              Depth                    :   16
%              Number of atoms          :  216 (1135 expanded)
%              Number of equality atoms :   50 ( 206 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_8 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_96,axiom,(
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

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(c_50,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_83,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_87,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_83])).

tff(c_118,plain,(
    ! [C_60,B_61,A_62] :
      ( v5_relat_1(C_60,B_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_62,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_122,plain,(
    v5_relat_1('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_118])).

tff(c_24,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v5_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_635,plain,(
    ! [A_144,B_145,C_146] :
      ( k2_relset_1(A_144,B_145,C_146) = k2_relat_1(C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_639,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_635])).

tff(c_640,plain,(
    k2_relat_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_639,c_50])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [C_65,B_66,A_67] :
      ( r2_hidden(C_65,B_66)
      | ~ r2_hidden(C_65,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_138,plain,(
    ! [A_68,B_69] :
      ( r2_hidden('#skF_1'(A_68),B_69)
      | ~ r1_tarski(A_68,B_69)
      | v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_4,c_128])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_146,plain,(
    ! [B_70,A_71] :
      ( ~ v1_xboole_0(B_70)
      | ~ r1_tarski(A_71,B_70)
      | v1_xboole_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_138,c_2])).

tff(c_565,plain,(
    ! [A_124,B_125] :
      ( ~ v1_xboole_0(A_124)
      | v1_xboole_0(k2_relat_1(B_125))
      | ~ v5_relat_1(B_125,A_124)
      | ~ v1_relat_1(B_125) ) ),
    inference(resolution,[status(thm)],[c_24,c_146])).

tff(c_567,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0(k2_relat_1('#skF_7'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_122,c_565])).

tff(c_572,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0(k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_567])).

tff(c_575,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_572])).

tff(c_88,plain,(
    ! [A_47,B_48] :
      ( r2_hidden('#skF_2'(A_47,B_48),A_47)
      | r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_96,plain,(
    ! [A_47] : r1_tarski(A_47,A_47) ),
    inference(resolution,[status(thm)],[c_88,c_8])).

tff(c_54,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_626,plain,(
    ! [A_141,B_142,C_143] :
      ( k1_relset_1(A_141,B_142,C_143) = k1_relat_1(C_143)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_630,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_626])).

tff(c_1074,plain,(
    ! [B_214,A_215,C_216] :
      ( k1_xboole_0 = B_214
      | k1_relset_1(A_215,B_214,C_216) = A_215
      | ~ v1_funct_2(C_216,A_215,B_214)
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(A_215,B_214))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1077,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_1074])).

tff(c_1080,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_630,c_1077])).

tff(c_1081,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1080])).

tff(c_60,plain,(
    ! [D_35] :
      ( r2_hidden('#skF_8'(D_35),'#skF_5')
      | ~ r2_hidden(D_35,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_136,plain,(
    ! [D_35,B_66] :
      ( r2_hidden('#skF_8'(D_35),B_66)
      | ~ r1_tarski('#skF_5',B_66)
      | ~ r2_hidden(D_35,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_60,c_128])).

tff(c_56,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_58,plain,(
    ! [D_35] :
      ( k1_funct_1('#skF_7','#skF_8'(D_35)) = D_35
      | ~ r2_hidden(D_35,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_743,plain,(
    ! [B_171,A_172] :
      ( r2_hidden(k1_funct_1(B_171,A_172),k2_relat_1(B_171))
      | ~ r2_hidden(A_172,k1_relat_1(B_171))
      | ~ v1_funct_1(B_171)
      | ~ v1_relat_1(B_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_751,plain,(
    ! [D_35] :
      ( r2_hidden(D_35,k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_8'(D_35),k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(D_35,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_743])).

tff(c_827,plain,(
    ! [D_178] :
      ( r2_hidden(D_178,k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_8'(D_178),k1_relat_1('#skF_7'))
      | ~ r2_hidden(D_178,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_56,c_751])).

tff(c_832,plain,(
    ! [D_35] :
      ( r2_hidden(D_35,k2_relat_1('#skF_7'))
      | ~ r1_tarski('#skF_5',k1_relat_1('#skF_7'))
      | ~ r2_hidden(D_35,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_136,c_827])).

tff(c_833,plain,(
    ~ r1_tarski('#skF_5',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_832])).

tff(c_1082,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_833])).

tff(c_1087,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_1082])).

tff(c_1088,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1080])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1097,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1088,c_12])).

tff(c_1099,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_575,c_1097])).

tff(c_1177,plain,(
    ! [D_220] :
      ( r2_hidden(D_220,k2_relat_1('#skF_7'))
      | ~ r2_hidden(D_220,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_832])).

tff(c_1225,plain,(
    ! [A_223] :
      ( r1_tarski(A_223,k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_2'(A_223,k2_relat_1('#skF_7')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1177,c_8])).

tff(c_1235,plain,(
    r1_tarski('#skF_6',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_10,c_1225])).

tff(c_663,plain,(
    ! [A_154,B_155] :
      ( r2_hidden('#skF_3'(A_154,B_155),B_155)
      | r2_hidden('#skF_4'(A_154,B_155),A_154)
      | B_155 = A_154 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1802,plain,(
    ! [A_277,B_278,B_279] :
      ( r2_hidden('#skF_3'(A_277,B_278),B_279)
      | ~ r1_tarski(B_278,B_279)
      | r2_hidden('#skF_4'(A_277,B_278),A_277)
      | B_278 = A_277 ) ),
    inference(resolution,[status(thm)],[c_663,c_6])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( ~ r2_hidden('#skF_3'(A_10,B_11),A_10)
      | r2_hidden('#skF_4'(A_10,B_11),A_10)
      | B_11 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1848,plain,(
    ! [B_280,B_281] :
      ( ~ r1_tarski(B_280,B_281)
      | r2_hidden('#skF_4'(B_281,B_280),B_281)
      | B_281 = B_280 ) ),
    inference(resolution,[status(thm)],[c_1802,c_18])).

tff(c_1871,plain,(
    ! [B_281,B_280,B_6] :
      ( r2_hidden('#skF_4'(B_281,B_280),B_6)
      | ~ r1_tarski(B_281,B_6)
      | ~ r1_tarski(B_280,B_281)
      | B_281 = B_280 ) ),
    inference(resolution,[status(thm)],[c_1848,c_6])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_3'(A_10,B_11),B_11)
      | ~ r2_hidden('#skF_4'(A_10,B_11),B_11)
      | B_11 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2083,plain,(
    ! [B_300,B_301,B_302] :
      ( r2_hidden('#skF_4'(B_300,B_301),B_302)
      | ~ r1_tarski(B_300,B_302)
      | ~ r1_tarski(B_301,B_300)
      | B_301 = B_300 ) ),
    inference(resolution,[status(thm)],[c_1848,c_6])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( ~ r2_hidden('#skF_3'(A_10,B_11),A_10)
      | ~ r2_hidden('#skF_4'(A_10,B_11),B_11)
      | B_11 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1194,plain,(
    ! [B_11] :
      ( ~ r2_hidden('#skF_4'(k2_relat_1('#skF_7'),B_11),B_11)
      | k2_relat_1('#skF_7') = B_11
      | ~ r2_hidden('#skF_3'(k2_relat_1('#skF_7'),B_11),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1177,c_14])).

tff(c_2855,plain,(
    ! [B_366] :
      ( ~ r2_hidden('#skF_3'(k2_relat_1('#skF_7'),B_366),'#skF_6')
      | ~ r1_tarski(k2_relat_1('#skF_7'),B_366)
      | ~ r1_tarski(B_366,k2_relat_1('#skF_7'))
      | k2_relat_1('#skF_7') = B_366 ) ),
    inference(resolution,[status(thm)],[c_2083,c_1194])).

tff(c_2883,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6')
    | ~ r1_tarski('#skF_6',k2_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_4'(k2_relat_1('#skF_7'),'#skF_6'),'#skF_6')
    | k2_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_16,c_2855])).

tff(c_2903,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_4'(k2_relat_1('#skF_7'),'#skF_6'),'#skF_6')
    | k2_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1235,c_2883])).

tff(c_2904,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_4'(k2_relat_1('#skF_7'),'#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_640,c_2903])).

tff(c_2905,plain,(
    ~ r2_hidden('#skF_4'(k2_relat_1('#skF_7'),'#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2904])).

tff(c_2908,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6')
    | ~ r1_tarski('#skF_6',k2_relat_1('#skF_7'))
    | k2_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1871,c_2905])).

tff(c_2915,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6')
    | k2_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1235,c_2908])).

tff(c_2916,plain,(
    ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_640,c_2915])).

tff(c_2921,plain,
    ( ~ v5_relat_1('#skF_7','#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_2916])).

tff(c_2928,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_122,c_2921])).

tff(c_2929,plain,(
    ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_2904])).

tff(c_2933,plain,
    ( ~ v5_relat_1('#skF_7','#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_2929])).

tff(c_2940,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_122,c_2933])).

tff(c_2942,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_572])).

tff(c_3027,plain,(
    ! [A_383,B_384] :
      ( r2_hidden('#skF_3'(A_383,B_384),B_384)
      | r2_hidden('#skF_4'(A_383,B_384),A_383)
      | B_384 = A_383 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3047,plain,(
    ! [B_385,A_386] :
      ( ~ v1_xboole_0(B_385)
      | r2_hidden('#skF_4'(A_386,B_385),A_386)
      | B_385 = A_386 ) ),
    inference(resolution,[status(thm)],[c_3027,c_2])).

tff(c_3055,plain,(
    ! [A_387,B_388] :
      ( ~ v1_xboole_0(A_387)
      | ~ v1_xboole_0(B_388)
      | B_388 = A_387 ) ),
    inference(resolution,[status(thm)],[c_3047,c_2])).

tff(c_3065,plain,(
    ! [B_389] :
      ( ~ v1_xboole_0(B_389)
      | k1_xboole_0 = B_389 ) ),
    inference(resolution,[status(thm)],[c_12,c_3055])).

tff(c_3076,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2942,c_3065])).

tff(c_2941,plain,(
    v1_xboole_0(k2_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_572])).

tff(c_3075,plain,(
    k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2941,c_3065])).

tff(c_3088,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3076,c_3075])).

tff(c_3175,plain,(
    ! [A_399,B_400,C_401] :
      ( k2_relset_1(A_399,B_400,C_401) = k2_relat_1(C_401)
      | ~ m1_subset_1(C_401,k1_zfmisc_1(k2_zfmisc_1(A_399,B_400))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3178,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_3175])).

tff(c_3180,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3088,c_3178])).

tff(c_3182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_3180])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.15/1.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.15/1.98  
% 5.15/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.15/1.98  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_8 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 5.15/1.98  
% 5.15/1.98  %Foreground sorts:
% 5.15/1.98  
% 5.15/1.98  
% 5.15/1.98  %Background operators:
% 5.15/1.98  
% 5.15/1.98  
% 5.15/1.98  %Foreground operators:
% 5.15/1.98  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.15/1.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.15/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.15/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.15/1.98  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.15/1.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.15/1.98  tff('#skF_8', type, '#skF_8': $i > $i).
% 5.15/1.98  tff('#skF_7', type, '#skF_7': $i).
% 5.15/1.98  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.15/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.15/1.98  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.15/1.98  tff('#skF_5', type, '#skF_5': $i).
% 5.15/1.98  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.15/1.98  tff('#skF_6', type, '#skF_6': $i).
% 5.15/1.98  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.15/1.98  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.15/1.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.15/1.98  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.15/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.15/1.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.15/1.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.15/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.15/1.98  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.15/1.98  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.15/1.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.15/1.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.15/1.98  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.15/1.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.15/1.98  
% 5.51/2.00  tff(f_115, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 5.51/2.00  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.51/2.00  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.51/2.00  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 5.51/2.00  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.51/2.00  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.51/2.00  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.51/2.00  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.51/2.00  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.51/2.00  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 5.51/2.00  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.51/2.00  tff(f_46, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 5.51/2.00  tff(c_50, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.51/2.00  tff(c_52, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.51/2.00  tff(c_83, plain, (![C_44, A_45, B_46]: (v1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.51/2.00  tff(c_87, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_52, c_83])).
% 5.51/2.00  tff(c_118, plain, (![C_60, B_61, A_62]: (v5_relat_1(C_60, B_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_62, B_61))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.51/2.00  tff(c_122, plain, (v5_relat_1('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_52, c_118])).
% 5.51/2.00  tff(c_24, plain, (![B_14, A_13]: (r1_tarski(k2_relat_1(B_14), A_13) | ~v5_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.51/2.00  tff(c_635, plain, (![A_144, B_145, C_146]: (k2_relset_1(A_144, B_145, C_146)=k2_relat_1(C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.51/2.00  tff(c_639, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_52, c_635])).
% 5.51/2.00  tff(c_640, plain, (k2_relat_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_639, c_50])).
% 5.51/2.00  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.51/2.00  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.51/2.00  tff(c_128, plain, (![C_65, B_66, A_67]: (r2_hidden(C_65, B_66) | ~r2_hidden(C_65, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.51/2.00  tff(c_138, plain, (![A_68, B_69]: (r2_hidden('#skF_1'(A_68), B_69) | ~r1_tarski(A_68, B_69) | v1_xboole_0(A_68))), inference(resolution, [status(thm)], [c_4, c_128])).
% 5.51/2.00  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.51/2.00  tff(c_146, plain, (![B_70, A_71]: (~v1_xboole_0(B_70) | ~r1_tarski(A_71, B_70) | v1_xboole_0(A_71))), inference(resolution, [status(thm)], [c_138, c_2])).
% 5.51/2.00  tff(c_565, plain, (![A_124, B_125]: (~v1_xboole_0(A_124) | v1_xboole_0(k2_relat_1(B_125)) | ~v5_relat_1(B_125, A_124) | ~v1_relat_1(B_125))), inference(resolution, [status(thm)], [c_24, c_146])).
% 5.51/2.00  tff(c_567, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0(k2_relat_1('#skF_7')) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_122, c_565])).
% 5.51/2.00  tff(c_572, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0(k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_567])).
% 5.51/2.00  tff(c_575, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_572])).
% 5.51/2.00  tff(c_88, plain, (![A_47, B_48]: (r2_hidden('#skF_2'(A_47, B_48), A_47) | r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.51/2.00  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.51/2.00  tff(c_96, plain, (![A_47]: (r1_tarski(A_47, A_47))), inference(resolution, [status(thm)], [c_88, c_8])).
% 5.51/2.00  tff(c_54, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.51/2.00  tff(c_626, plain, (![A_141, B_142, C_143]: (k1_relset_1(A_141, B_142, C_143)=k1_relat_1(C_143) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.51/2.00  tff(c_630, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_52, c_626])).
% 5.51/2.00  tff(c_1074, plain, (![B_214, A_215, C_216]: (k1_xboole_0=B_214 | k1_relset_1(A_215, B_214, C_216)=A_215 | ~v1_funct_2(C_216, A_215, B_214) | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(A_215, B_214))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.51/2.00  tff(c_1077, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_52, c_1074])).
% 5.51/2.00  tff(c_1080, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_630, c_1077])).
% 5.51/2.00  tff(c_1081, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitLeft, [status(thm)], [c_1080])).
% 5.51/2.00  tff(c_60, plain, (![D_35]: (r2_hidden('#skF_8'(D_35), '#skF_5') | ~r2_hidden(D_35, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.51/2.00  tff(c_136, plain, (![D_35, B_66]: (r2_hidden('#skF_8'(D_35), B_66) | ~r1_tarski('#skF_5', B_66) | ~r2_hidden(D_35, '#skF_6'))), inference(resolution, [status(thm)], [c_60, c_128])).
% 5.51/2.00  tff(c_56, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.51/2.00  tff(c_58, plain, (![D_35]: (k1_funct_1('#skF_7', '#skF_8'(D_35))=D_35 | ~r2_hidden(D_35, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.51/2.00  tff(c_743, plain, (![B_171, A_172]: (r2_hidden(k1_funct_1(B_171, A_172), k2_relat_1(B_171)) | ~r2_hidden(A_172, k1_relat_1(B_171)) | ~v1_funct_1(B_171) | ~v1_relat_1(B_171))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.51/2.00  tff(c_751, plain, (![D_35]: (r2_hidden(D_35, k2_relat_1('#skF_7')) | ~r2_hidden('#skF_8'(D_35), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(D_35, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_743])).
% 5.51/2.00  tff(c_827, plain, (![D_178]: (r2_hidden(D_178, k2_relat_1('#skF_7')) | ~r2_hidden('#skF_8'(D_178), k1_relat_1('#skF_7')) | ~r2_hidden(D_178, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_56, c_751])).
% 5.51/2.00  tff(c_832, plain, (![D_35]: (r2_hidden(D_35, k2_relat_1('#skF_7')) | ~r1_tarski('#skF_5', k1_relat_1('#skF_7')) | ~r2_hidden(D_35, '#skF_6'))), inference(resolution, [status(thm)], [c_136, c_827])).
% 5.51/2.00  tff(c_833, plain, (~r1_tarski('#skF_5', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_832])).
% 5.51/2.00  tff(c_1082, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1081, c_833])).
% 5.51/2.00  tff(c_1087, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_1082])).
% 5.51/2.00  tff(c_1088, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_1080])).
% 5.51/2.00  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.51/2.00  tff(c_1097, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1088, c_12])).
% 5.51/2.00  tff(c_1099, plain, $false, inference(negUnitSimplification, [status(thm)], [c_575, c_1097])).
% 5.51/2.00  tff(c_1177, plain, (![D_220]: (r2_hidden(D_220, k2_relat_1('#skF_7')) | ~r2_hidden(D_220, '#skF_6'))), inference(splitRight, [status(thm)], [c_832])).
% 5.51/2.00  tff(c_1225, plain, (![A_223]: (r1_tarski(A_223, k2_relat_1('#skF_7')) | ~r2_hidden('#skF_2'(A_223, k2_relat_1('#skF_7')), '#skF_6'))), inference(resolution, [status(thm)], [c_1177, c_8])).
% 5.51/2.00  tff(c_1235, plain, (r1_tarski('#skF_6', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_10, c_1225])).
% 5.51/2.00  tff(c_663, plain, (![A_154, B_155]: (r2_hidden('#skF_3'(A_154, B_155), B_155) | r2_hidden('#skF_4'(A_154, B_155), A_154) | B_155=A_154)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.51/2.00  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.51/2.00  tff(c_1802, plain, (![A_277, B_278, B_279]: (r2_hidden('#skF_3'(A_277, B_278), B_279) | ~r1_tarski(B_278, B_279) | r2_hidden('#skF_4'(A_277, B_278), A_277) | B_278=A_277)), inference(resolution, [status(thm)], [c_663, c_6])).
% 5.51/2.00  tff(c_18, plain, (![A_10, B_11]: (~r2_hidden('#skF_3'(A_10, B_11), A_10) | r2_hidden('#skF_4'(A_10, B_11), A_10) | B_11=A_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.51/2.00  tff(c_1848, plain, (![B_280, B_281]: (~r1_tarski(B_280, B_281) | r2_hidden('#skF_4'(B_281, B_280), B_281) | B_281=B_280)), inference(resolution, [status(thm)], [c_1802, c_18])).
% 5.51/2.00  tff(c_1871, plain, (![B_281, B_280, B_6]: (r2_hidden('#skF_4'(B_281, B_280), B_6) | ~r1_tarski(B_281, B_6) | ~r1_tarski(B_280, B_281) | B_281=B_280)), inference(resolution, [status(thm)], [c_1848, c_6])).
% 5.51/2.00  tff(c_16, plain, (![A_10, B_11]: (r2_hidden('#skF_3'(A_10, B_11), B_11) | ~r2_hidden('#skF_4'(A_10, B_11), B_11) | B_11=A_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.51/2.00  tff(c_2083, plain, (![B_300, B_301, B_302]: (r2_hidden('#skF_4'(B_300, B_301), B_302) | ~r1_tarski(B_300, B_302) | ~r1_tarski(B_301, B_300) | B_301=B_300)), inference(resolution, [status(thm)], [c_1848, c_6])).
% 5.51/2.00  tff(c_14, plain, (![A_10, B_11]: (~r2_hidden('#skF_3'(A_10, B_11), A_10) | ~r2_hidden('#skF_4'(A_10, B_11), B_11) | B_11=A_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.51/2.00  tff(c_1194, plain, (![B_11]: (~r2_hidden('#skF_4'(k2_relat_1('#skF_7'), B_11), B_11) | k2_relat_1('#skF_7')=B_11 | ~r2_hidden('#skF_3'(k2_relat_1('#skF_7'), B_11), '#skF_6'))), inference(resolution, [status(thm)], [c_1177, c_14])).
% 5.51/2.00  tff(c_2855, plain, (![B_366]: (~r2_hidden('#skF_3'(k2_relat_1('#skF_7'), B_366), '#skF_6') | ~r1_tarski(k2_relat_1('#skF_7'), B_366) | ~r1_tarski(B_366, k2_relat_1('#skF_7')) | k2_relat_1('#skF_7')=B_366)), inference(resolution, [status(thm)], [c_2083, c_1194])).
% 5.51/2.00  tff(c_2883, plain, (~r1_tarski(k2_relat_1('#skF_7'), '#skF_6') | ~r1_tarski('#skF_6', k2_relat_1('#skF_7')) | ~r2_hidden('#skF_4'(k2_relat_1('#skF_7'), '#skF_6'), '#skF_6') | k2_relat_1('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_16, c_2855])).
% 5.51/2.00  tff(c_2903, plain, (~r1_tarski(k2_relat_1('#skF_7'), '#skF_6') | ~r2_hidden('#skF_4'(k2_relat_1('#skF_7'), '#skF_6'), '#skF_6') | k2_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1235, c_2883])).
% 5.51/2.00  tff(c_2904, plain, (~r1_tarski(k2_relat_1('#skF_7'), '#skF_6') | ~r2_hidden('#skF_4'(k2_relat_1('#skF_7'), '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_640, c_2903])).
% 5.51/2.00  tff(c_2905, plain, (~r2_hidden('#skF_4'(k2_relat_1('#skF_7'), '#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_2904])).
% 5.51/2.00  tff(c_2908, plain, (~r1_tarski(k2_relat_1('#skF_7'), '#skF_6') | ~r1_tarski('#skF_6', k2_relat_1('#skF_7')) | k2_relat_1('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_1871, c_2905])).
% 5.51/2.00  tff(c_2915, plain, (~r1_tarski(k2_relat_1('#skF_7'), '#skF_6') | k2_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1235, c_2908])).
% 5.51/2.00  tff(c_2916, plain, (~r1_tarski(k2_relat_1('#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_640, c_2915])).
% 5.51/2.00  tff(c_2921, plain, (~v5_relat_1('#skF_7', '#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_24, c_2916])).
% 5.51/2.00  tff(c_2928, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_122, c_2921])).
% 5.51/2.00  tff(c_2929, plain, (~r1_tarski(k2_relat_1('#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_2904])).
% 5.51/2.00  tff(c_2933, plain, (~v5_relat_1('#skF_7', '#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_24, c_2929])).
% 5.51/2.00  tff(c_2940, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_122, c_2933])).
% 5.51/2.00  tff(c_2942, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_572])).
% 5.51/2.00  tff(c_3027, plain, (![A_383, B_384]: (r2_hidden('#skF_3'(A_383, B_384), B_384) | r2_hidden('#skF_4'(A_383, B_384), A_383) | B_384=A_383)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.51/2.00  tff(c_3047, plain, (![B_385, A_386]: (~v1_xboole_0(B_385) | r2_hidden('#skF_4'(A_386, B_385), A_386) | B_385=A_386)), inference(resolution, [status(thm)], [c_3027, c_2])).
% 5.51/2.00  tff(c_3055, plain, (![A_387, B_388]: (~v1_xboole_0(A_387) | ~v1_xboole_0(B_388) | B_388=A_387)), inference(resolution, [status(thm)], [c_3047, c_2])).
% 5.51/2.00  tff(c_3065, plain, (![B_389]: (~v1_xboole_0(B_389) | k1_xboole_0=B_389)), inference(resolution, [status(thm)], [c_12, c_3055])).
% 5.51/2.00  tff(c_3076, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_2942, c_3065])).
% 5.51/2.00  tff(c_2941, plain, (v1_xboole_0(k2_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_572])).
% 5.51/2.00  tff(c_3075, plain, (k2_relat_1('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_2941, c_3065])).
% 5.51/2.00  tff(c_3088, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3076, c_3075])).
% 5.51/2.00  tff(c_3175, plain, (![A_399, B_400, C_401]: (k2_relset_1(A_399, B_400, C_401)=k2_relat_1(C_401) | ~m1_subset_1(C_401, k1_zfmisc_1(k2_zfmisc_1(A_399, B_400))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.51/2.00  tff(c_3178, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_52, c_3175])).
% 5.51/2.00  tff(c_3180, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3088, c_3178])).
% 5.51/2.00  tff(c_3182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_3180])).
% 5.51/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.51/2.00  
% 5.51/2.00  Inference rules
% 5.51/2.00  ----------------------
% 5.51/2.00  #Ref     : 0
% 5.51/2.00  #Sup     : 669
% 5.51/2.00  #Fact    : 0
% 5.51/2.00  #Define  : 0
% 5.51/2.00  #Split   : 15
% 5.51/2.00  #Chain   : 0
% 5.51/2.00  #Close   : 0
% 5.51/2.00  
% 5.51/2.00  Ordering : KBO
% 5.51/2.00  
% 5.51/2.00  Simplification rules
% 5.51/2.00  ----------------------
% 5.51/2.00  #Subsume      : 295
% 5.51/2.00  #Demod        : 234
% 5.51/2.00  #Tautology    : 111
% 5.51/2.00  #SimpNegUnit  : 26
% 5.51/2.00  #BackRed      : 27
% 5.51/2.00  
% 5.51/2.00  #Partial instantiations: 0
% 5.51/2.00  #Strategies tried      : 1
% 5.51/2.00  
% 5.51/2.00  Timing (in seconds)
% 5.51/2.00  ----------------------
% 5.51/2.01  Preprocessing        : 0.32
% 5.51/2.01  Parsing              : 0.16
% 5.51/2.01  CNF conversion       : 0.02
% 5.51/2.01  Main loop            : 0.90
% 5.51/2.01  Inferencing          : 0.32
% 5.51/2.01  Reduction            : 0.25
% 5.51/2.01  Demodulation         : 0.16
% 5.51/2.01  BG Simplification    : 0.03
% 5.51/2.01  Subsumption          : 0.24
% 5.51/2.01  Abstraction          : 0.04
% 5.51/2.01  MUC search           : 0.00
% 5.51/2.01  Cooper               : 0.00
% 5.51/2.01  Total                : 1.27
% 5.51/2.01  Index Insertion      : 0.00
% 5.51/2.01  Index Deletion       : 0.00
% 5.51/2.01  Index Matching       : 0.00
% 5.51/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
