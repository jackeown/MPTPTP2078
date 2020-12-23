%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:22 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 540 expanded)
%              Number of leaves         :   21 ( 173 expanded)
%              Depth                    :   16
%              Number of atoms          :  190 (1533 expanded)
%              Number of equality atoms :   40 ( 112 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ~ ( B != k1_xboole_0
            & ! [C] :
                ( m1_subset_1(C,A)
               => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( m1_subset_1(B_14,A_13)
      | ~ v1_xboole_0(B_14)
      | ~ v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_52,plain,(
    ! [B_32,A_33] :
      ( r2_hidden(B_32,A_33)
      | ~ m1_subset_1(B_32,A_33)
      | v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_28,plain,(
    ! [C_20] :
      ( ~ r2_hidden(C_20,'#skF_4')
      | ~ m1_subset_1(C_20,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_60,plain,(
    ! [B_32] :
      ( ~ m1_subset_1(B_32,'#skF_3')
      | ~ m1_subset_1(B_32,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_52,c_28])).

tff(c_136,plain,(
    ! [B_50] :
      ( ~ m1_subset_1(B_50,'#skF_3')
      | ~ m1_subset_1(B_50,'#skF_4') ) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_141,plain,(
    ! [B_14] :
      ( ~ m1_subset_1(B_14,'#skF_4')
      | ~ v1_xboole_0(B_14)
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_136])).

tff(c_142,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_73,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_1'(A_38,B_39),A_38)
      | r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( m1_subset_1(B_14,A_13)
      | ~ r2_hidden(B_14,A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_193,plain,(
    ! [A_65,B_66] :
      ( m1_subset_1('#skF_1'(A_65,B_66),A_65)
      | v1_xboole_0(A_65)
      | r1_tarski(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_73,c_18])).

tff(c_135,plain,(
    ! [B_32] :
      ( ~ m1_subset_1(B_32,'#skF_3')
      | ~ m1_subset_1(B_32,'#skF_4') ) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_201,plain,(
    ! [B_66] :
      ( ~ m1_subset_1('#skF_1'('#skF_3',B_66),'#skF_4')
      | v1_xboole_0('#skF_3')
      | r1_tarski('#skF_3',B_66) ) ),
    inference(resolution,[status(thm)],[c_193,c_135])).

tff(c_211,plain,(
    ! [B_67] :
      ( ~ m1_subset_1('#skF_1'('#skF_3',B_67),'#skF_4')
      | r1_tarski('#skF_3',B_67) ) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_201])).

tff(c_215,plain,(
    ! [B_67] :
      ( r1_tarski('#skF_3',B_67)
      | ~ v1_xboole_0('#skF_1'('#skF_3',B_67))
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_211])).

tff(c_251,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( r2_hidden(B_14,A_13)
      | ~ m1_subset_1(B_14,A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_169,plain,(
    ! [C_58,A_59,B_60] :
      ( r2_hidden(C_58,A_59)
      | ~ r2_hidden(C_58,B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_320,plain,(
    ! [B_85,A_86,A_87] :
      ( r2_hidden(B_85,A_86)
      | ~ m1_subset_1(A_87,k1_zfmisc_1(A_86))
      | ~ m1_subset_1(B_85,A_87)
      | v1_xboole_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_20,c_169])).

tff(c_328,plain,(
    ! [B_85] :
      ( r2_hidden(B_85,'#skF_3')
      | ~ m1_subset_1(B_85,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_320])).

tff(c_334,plain,(
    ! [B_88] :
      ( r2_hidden(B_88,'#skF_3')
      | ~ m1_subset_1(B_88,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_251,c_328])).

tff(c_345,plain,(
    ! [B_88] :
      ( m1_subset_1(B_88,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_88,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_334,c_18])).

tff(c_356,plain,(
    ! [B_89] :
      ( m1_subset_1(B_89,'#skF_3')
      | ~ m1_subset_1(B_89,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_345])).

tff(c_381,plain,(
    ! [B_89] : ~ m1_subset_1(B_89,'#skF_4') ),
    inference(resolution,[status(thm)],[c_356,c_135])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_144,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_2'(A_53,B_54),A_53)
      | k1_xboole_0 = A_53
      | k1_tarski(B_54) = A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_440,plain,(
    ! [A_96,B_97] :
      ( m1_subset_1('#skF_2'(A_96,B_97),A_96)
      | v1_xboole_0(A_96)
      | k1_xboole_0 = A_96
      | k1_tarski(B_97) = A_96 ) ),
    inference(resolution,[status(thm)],[c_144,c_18])).

tff(c_448,plain,(
    ! [B_97] :
      ( v1_xboole_0('#skF_4')
      | k1_xboole_0 = '#skF_4'
      | k1_tarski(B_97) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_440,c_381])).

tff(c_461,plain,(
    ! [B_97] : k1_tarski(B_97) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_251,c_448])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_92,plain,(
    ! [A_40] : r1_tarski(A_40,A_40) ),
    inference(resolution,[status(thm)],[c_73,c_4])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | ~ r1_tarski(k1_tarski(A_11),B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_105,plain,(
    ! [A_44] : r2_hidden(A_44,k1_tarski(A_44)) ),
    inference(resolution,[status(thm)],[c_92,c_14])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( ~ v1_xboole_0(B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_116,plain,(
    ! [A_44] : ~ v1_xboole_0(k1_tarski(A_44)) ),
    inference(resolution,[status(thm)],[c_105,c_8])).

tff(c_115,plain,(
    ! [A_44] :
      ( m1_subset_1(A_44,k1_tarski(A_44))
      | v1_xboole_0(k1_tarski(A_44)) ) ),
    inference(resolution,[status(thm)],[c_105,c_18])).

tff(c_129,plain,(
    ! [A_44] : m1_subset_1(A_44,k1_tarski(A_44)) ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_115])).

tff(c_474,plain,(
    ! [A_44] : m1_subset_1(A_44,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_129])).

tff(c_480,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_474])).

tff(c_482,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_162,plain,(
    ! [A_53,B_54] :
      ( ~ v1_xboole_0(A_53)
      | k1_xboole_0 = A_53
      | k1_tarski(B_54) = A_53 ) ),
    inference(resolution,[status(thm)],[c_144,c_8])).

tff(c_484,plain,(
    ! [B_54] :
      ( k1_xboole_0 = '#skF_4'
      | k1_tarski(B_54) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_482,c_162])).

tff(c_487,plain,(
    ! [B_54] : k1_tarski(B_54) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_484])).

tff(c_494,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_116])).

tff(c_500,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_494])).

tff(c_502,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_509,plain,(
    ! [B_98] :
      ( ~ m1_subset_1(B_98,'#skF_4')
      | ~ v1_xboole_0(B_98) ) ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_514,plain,(
    ! [B_14] :
      ( ~ v1_xboole_0(B_14)
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_509])).

tff(c_516,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_514])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_555,plain,(
    ! [C_108,A_109,B_110] :
      ( r2_hidden(C_108,A_109)
      | ~ r2_hidden(C_108,B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_704,plain,(
    ! [A_139,B_140,A_141] :
      ( r2_hidden('#skF_1'(A_139,B_140),A_141)
      | ~ m1_subset_1(A_139,k1_zfmisc_1(A_141))
      | r1_tarski(A_139,B_140) ) ),
    inference(resolution,[status(thm)],[c_6,c_555])).

tff(c_729,plain,(
    ! [A_142,A_143] :
      ( ~ m1_subset_1(A_142,k1_zfmisc_1(A_143))
      | r1_tarski(A_142,A_143) ) ),
    inference(resolution,[status(thm)],[c_704,c_4])).

tff(c_743,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_729])).

tff(c_98,plain,(
    ! [C_41,B_42,A_43] :
      ( r2_hidden(C_41,B_42)
      | ~ r2_hidden(C_41,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_104,plain,(
    ! [B_14,B_42,A_13] :
      ( r2_hidden(B_14,B_42)
      | ~ r1_tarski(A_13,B_42)
      | ~ m1_subset_1(B_14,A_13)
      | v1_xboole_0(A_13) ) ),
    inference(resolution,[status(thm)],[c_20,c_98])).

tff(c_745,plain,(
    ! [B_14] :
      ( r2_hidden(B_14,'#skF_3')
      | ~ m1_subset_1(B_14,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_743,c_104])).

tff(c_767,plain,(
    ! [B_145] :
      ( r2_hidden(B_145,'#skF_3')
      | ~ m1_subset_1(B_145,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_516,c_745])).

tff(c_781,plain,(
    ! [B_145] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_145,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_767,c_8])).

tff(c_789,plain,(
    ! [B_145] : ~ m1_subset_1(B_145,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_781])).

tff(c_518,plain,(
    ! [A_102,B_103] :
      ( r2_hidden('#skF_2'(A_102,B_103),A_102)
      | k1_xboole_0 = A_102
      | k1_tarski(B_103) = A_102 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_537,plain,(
    ! [A_104,B_105] :
      ( ~ v1_xboole_0(A_104)
      | k1_xboole_0 = A_104
      | k1_tarski(B_105) = A_104 ) ),
    inference(resolution,[status(thm)],[c_518,c_8])).

tff(c_540,plain,(
    ! [B_105] :
      ( k1_xboole_0 = '#skF_3'
      | k1_tarski(B_105) = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_502,c_537])).

tff(c_541,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_540])).

tff(c_545,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_30])).

tff(c_532,plain,(
    ! [A_102,B_103] :
      ( m1_subset_1('#skF_2'(A_102,B_103),A_102)
      | v1_xboole_0(A_102)
      | k1_xboole_0 = A_102
      | k1_tarski(B_103) = A_102 ) ),
    inference(resolution,[status(thm)],[c_518,c_18])).

tff(c_804,plain,(
    ! [A_147,B_148] :
      ( m1_subset_1('#skF_2'(A_147,B_148),A_147)
      | v1_xboole_0(A_147)
      | A_147 = '#skF_3'
      | k1_tarski(B_148) = A_147 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_532])).

tff(c_808,plain,(
    ! [B_148] :
      ( v1_xboole_0('#skF_4')
      | '#skF_3' = '#skF_4'
      | k1_tarski(B_148) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_804,c_789])).

tff(c_821,plain,(
    ! [B_148] : k1_tarski(B_148) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_545,c_516,c_808])).

tff(c_835,plain,(
    ! [A_44] : m1_subset_1(A_44,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_129])).

tff(c_841,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_789,c_835])).

tff(c_842,plain,(
    ! [B_105] : k1_tarski(B_105) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_540])).

tff(c_848,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_842,c_116])).

tff(c_854,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_848])).

tff(c_855,plain,(
    ! [B_14] : ~ v1_xboole_0(B_14) ),
    inference(splitRight,[status(thm)],[c_514])).

tff(c_862,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_855,c_502])).

tff(c_863,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_881,plain,(
    ! [A_157,B_158] :
      ( r2_hidden('#skF_2'(A_157,B_158),A_157)
      | k1_xboole_0 = A_157
      | k1_tarski(B_158) = A_157 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_903,plain,(
    ! [A_159,B_160] :
      ( ~ v1_xboole_0(A_159)
      | k1_xboole_0 = A_159
      | k1_tarski(B_160) = A_159 ) ),
    inference(resolution,[status(thm)],[c_881,c_8])).

tff(c_905,plain,(
    ! [B_160] :
      ( k1_xboole_0 = '#skF_4'
      | k1_tarski(B_160) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_863,c_903])).

tff(c_908,plain,(
    ! [B_160] : k1_tarski(B_160) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_905])).

tff(c_914,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_908,c_116])).

tff(c_920,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_863,c_914])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:29:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.42  
% 2.81/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.42  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.81/1.42  
% 2.81/1.42  %Foreground sorts:
% 2.81/1.42  
% 2.81/1.42  
% 2.81/1.42  %Background operators:
% 2.81/1.42  
% 2.81/1.42  
% 2.81/1.42  %Foreground operators:
% 2.81/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.81/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.81/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.81/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.81/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.81/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.81/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.81/1.42  
% 2.81/1.44  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.81/1.44  tff(f_88, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 2.81/1.44  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.81/1.44  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.81/1.44  tff(f_51, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 2.81/1.44  tff(f_55, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 2.81/1.44  tff(f_37, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 2.81/1.44  tff(c_22, plain, (![B_14, A_13]: (m1_subset_1(B_14, A_13) | ~v1_xboole_0(B_14) | ~v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.81/1.44  tff(c_52, plain, (![B_32, A_33]: (r2_hidden(B_32, A_33) | ~m1_subset_1(B_32, A_33) | v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.81/1.44  tff(c_28, plain, (![C_20]: (~r2_hidden(C_20, '#skF_4') | ~m1_subset_1(C_20, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.81/1.44  tff(c_60, plain, (![B_32]: (~m1_subset_1(B_32, '#skF_3') | ~m1_subset_1(B_32, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_52, c_28])).
% 2.81/1.44  tff(c_136, plain, (![B_50]: (~m1_subset_1(B_50, '#skF_3') | ~m1_subset_1(B_50, '#skF_4'))), inference(splitLeft, [status(thm)], [c_60])).
% 2.81/1.44  tff(c_141, plain, (![B_14]: (~m1_subset_1(B_14, '#skF_4') | ~v1_xboole_0(B_14) | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_136])).
% 2.81/1.44  tff(c_142, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_141])).
% 2.81/1.44  tff(c_73, plain, (![A_38, B_39]: (r2_hidden('#skF_1'(A_38, B_39), A_38) | r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.81/1.44  tff(c_18, plain, (![B_14, A_13]: (m1_subset_1(B_14, A_13) | ~r2_hidden(B_14, A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.81/1.44  tff(c_193, plain, (![A_65, B_66]: (m1_subset_1('#skF_1'(A_65, B_66), A_65) | v1_xboole_0(A_65) | r1_tarski(A_65, B_66))), inference(resolution, [status(thm)], [c_73, c_18])).
% 2.81/1.44  tff(c_135, plain, (![B_32]: (~m1_subset_1(B_32, '#skF_3') | ~m1_subset_1(B_32, '#skF_4'))), inference(splitLeft, [status(thm)], [c_60])).
% 2.81/1.44  tff(c_201, plain, (![B_66]: (~m1_subset_1('#skF_1'('#skF_3', B_66), '#skF_4') | v1_xboole_0('#skF_3') | r1_tarski('#skF_3', B_66))), inference(resolution, [status(thm)], [c_193, c_135])).
% 2.81/1.44  tff(c_211, plain, (![B_67]: (~m1_subset_1('#skF_1'('#skF_3', B_67), '#skF_4') | r1_tarski('#skF_3', B_67))), inference(negUnitSimplification, [status(thm)], [c_142, c_201])).
% 2.81/1.44  tff(c_215, plain, (![B_67]: (r1_tarski('#skF_3', B_67) | ~v1_xboole_0('#skF_1'('#skF_3', B_67)) | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_211])).
% 2.81/1.44  tff(c_251, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_215])).
% 2.81/1.44  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.81/1.44  tff(c_20, plain, (![B_14, A_13]: (r2_hidden(B_14, A_13) | ~m1_subset_1(B_14, A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.81/1.44  tff(c_169, plain, (![C_58, A_59, B_60]: (r2_hidden(C_58, A_59) | ~r2_hidden(C_58, B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.81/1.44  tff(c_320, plain, (![B_85, A_86, A_87]: (r2_hidden(B_85, A_86) | ~m1_subset_1(A_87, k1_zfmisc_1(A_86)) | ~m1_subset_1(B_85, A_87) | v1_xboole_0(A_87))), inference(resolution, [status(thm)], [c_20, c_169])).
% 2.81/1.44  tff(c_328, plain, (![B_85]: (r2_hidden(B_85, '#skF_3') | ~m1_subset_1(B_85, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_320])).
% 2.81/1.44  tff(c_334, plain, (![B_88]: (r2_hidden(B_88, '#skF_3') | ~m1_subset_1(B_88, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_251, c_328])).
% 2.81/1.44  tff(c_345, plain, (![B_88]: (m1_subset_1(B_88, '#skF_3') | v1_xboole_0('#skF_3') | ~m1_subset_1(B_88, '#skF_4'))), inference(resolution, [status(thm)], [c_334, c_18])).
% 2.81/1.44  tff(c_356, plain, (![B_89]: (m1_subset_1(B_89, '#skF_3') | ~m1_subset_1(B_89, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_142, c_345])).
% 2.81/1.44  tff(c_381, plain, (![B_89]: (~m1_subset_1(B_89, '#skF_4'))), inference(resolution, [status(thm)], [c_356, c_135])).
% 2.81/1.44  tff(c_30, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.81/1.44  tff(c_144, plain, (![A_53, B_54]: (r2_hidden('#skF_2'(A_53, B_54), A_53) | k1_xboole_0=A_53 | k1_tarski(B_54)=A_53)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.81/1.44  tff(c_440, plain, (![A_96, B_97]: (m1_subset_1('#skF_2'(A_96, B_97), A_96) | v1_xboole_0(A_96) | k1_xboole_0=A_96 | k1_tarski(B_97)=A_96)), inference(resolution, [status(thm)], [c_144, c_18])).
% 2.81/1.44  tff(c_448, plain, (![B_97]: (v1_xboole_0('#skF_4') | k1_xboole_0='#skF_4' | k1_tarski(B_97)='#skF_4')), inference(resolution, [status(thm)], [c_440, c_381])).
% 2.81/1.44  tff(c_461, plain, (![B_97]: (k1_tarski(B_97)='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_30, c_251, c_448])).
% 2.81/1.44  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.81/1.44  tff(c_92, plain, (![A_40]: (r1_tarski(A_40, A_40))), inference(resolution, [status(thm)], [c_73, c_4])).
% 2.81/1.44  tff(c_14, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | ~r1_tarski(k1_tarski(A_11), B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.81/1.44  tff(c_105, plain, (![A_44]: (r2_hidden(A_44, k1_tarski(A_44)))), inference(resolution, [status(thm)], [c_92, c_14])).
% 2.81/1.44  tff(c_8, plain, (![B_7, A_6]: (~v1_xboole_0(B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.81/1.44  tff(c_116, plain, (![A_44]: (~v1_xboole_0(k1_tarski(A_44)))), inference(resolution, [status(thm)], [c_105, c_8])).
% 2.81/1.44  tff(c_115, plain, (![A_44]: (m1_subset_1(A_44, k1_tarski(A_44)) | v1_xboole_0(k1_tarski(A_44)))), inference(resolution, [status(thm)], [c_105, c_18])).
% 2.81/1.44  tff(c_129, plain, (![A_44]: (m1_subset_1(A_44, k1_tarski(A_44)))), inference(negUnitSimplification, [status(thm)], [c_116, c_115])).
% 2.81/1.44  tff(c_474, plain, (![A_44]: (m1_subset_1(A_44, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_461, c_129])).
% 2.81/1.44  tff(c_480, plain, $false, inference(negUnitSimplification, [status(thm)], [c_381, c_474])).
% 2.81/1.44  tff(c_482, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_215])).
% 2.81/1.44  tff(c_162, plain, (![A_53, B_54]: (~v1_xboole_0(A_53) | k1_xboole_0=A_53 | k1_tarski(B_54)=A_53)), inference(resolution, [status(thm)], [c_144, c_8])).
% 2.81/1.44  tff(c_484, plain, (![B_54]: (k1_xboole_0='#skF_4' | k1_tarski(B_54)='#skF_4')), inference(resolution, [status(thm)], [c_482, c_162])).
% 2.81/1.44  tff(c_487, plain, (![B_54]: (k1_tarski(B_54)='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_30, c_484])).
% 2.81/1.44  tff(c_494, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_487, c_116])).
% 2.81/1.44  tff(c_500, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_482, c_494])).
% 2.81/1.44  tff(c_502, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_141])).
% 2.81/1.44  tff(c_509, plain, (![B_98]: (~m1_subset_1(B_98, '#skF_4') | ~v1_xboole_0(B_98))), inference(splitRight, [status(thm)], [c_141])).
% 2.81/1.44  tff(c_514, plain, (![B_14]: (~v1_xboole_0(B_14) | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_509])).
% 2.81/1.44  tff(c_516, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_514])).
% 2.81/1.44  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.81/1.44  tff(c_555, plain, (![C_108, A_109, B_110]: (r2_hidden(C_108, A_109) | ~r2_hidden(C_108, B_110) | ~m1_subset_1(B_110, k1_zfmisc_1(A_109)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.81/1.44  tff(c_704, plain, (![A_139, B_140, A_141]: (r2_hidden('#skF_1'(A_139, B_140), A_141) | ~m1_subset_1(A_139, k1_zfmisc_1(A_141)) | r1_tarski(A_139, B_140))), inference(resolution, [status(thm)], [c_6, c_555])).
% 2.81/1.44  tff(c_729, plain, (![A_142, A_143]: (~m1_subset_1(A_142, k1_zfmisc_1(A_143)) | r1_tarski(A_142, A_143))), inference(resolution, [status(thm)], [c_704, c_4])).
% 2.81/1.44  tff(c_743, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_729])).
% 2.81/1.44  tff(c_98, plain, (![C_41, B_42, A_43]: (r2_hidden(C_41, B_42) | ~r2_hidden(C_41, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.81/1.44  tff(c_104, plain, (![B_14, B_42, A_13]: (r2_hidden(B_14, B_42) | ~r1_tarski(A_13, B_42) | ~m1_subset_1(B_14, A_13) | v1_xboole_0(A_13))), inference(resolution, [status(thm)], [c_20, c_98])).
% 2.81/1.44  tff(c_745, plain, (![B_14]: (r2_hidden(B_14, '#skF_3') | ~m1_subset_1(B_14, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_743, c_104])).
% 2.81/1.44  tff(c_767, plain, (![B_145]: (r2_hidden(B_145, '#skF_3') | ~m1_subset_1(B_145, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_516, c_745])).
% 2.81/1.44  tff(c_781, plain, (![B_145]: (~v1_xboole_0('#skF_3') | ~m1_subset_1(B_145, '#skF_4'))), inference(resolution, [status(thm)], [c_767, c_8])).
% 2.81/1.44  tff(c_789, plain, (![B_145]: (~m1_subset_1(B_145, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_502, c_781])).
% 2.81/1.44  tff(c_518, plain, (![A_102, B_103]: (r2_hidden('#skF_2'(A_102, B_103), A_102) | k1_xboole_0=A_102 | k1_tarski(B_103)=A_102)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.81/1.44  tff(c_537, plain, (![A_104, B_105]: (~v1_xboole_0(A_104) | k1_xboole_0=A_104 | k1_tarski(B_105)=A_104)), inference(resolution, [status(thm)], [c_518, c_8])).
% 2.81/1.44  tff(c_540, plain, (![B_105]: (k1_xboole_0='#skF_3' | k1_tarski(B_105)='#skF_3')), inference(resolution, [status(thm)], [c_502, c_537])).
% 2.81/1.44  tff(c_541, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_540])).
% 2.81/1.44  tff(c_545, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_541, c_30])).
% 2.81/1.44  tff(c_532, plain, (![A_102, B_103]: (m1_subset_1('#skF_2'(A_102, B_103), A_102) | v1_xboole_0(A_102) | k1_xboole_0=A_102 | k1_tarski(B_103)=A_102)), inference(resolution, [status(thm)], [c_518, c_18])).
% 2.81/1.44  tff(c_804, plain, (![A_147, B_148]: (m1_subset_1('#skF_2'(A_147, B_148), A_147) | v1_xboole_0(A_147) | A_147='#skF_3' | k1_tarski(B_148)=A_147)), inference(demodulation, [status(thm), theory('equality')], [c_541, c_532])).
% 2.81/1.44  tff(c_808, plain, (![B_148]: (v1_xboole_0('#skF_4') | '#skF_3'='#skF_4' | k1_tarski(B_148)='#skF_4')), inference(resolution, [status(thm)], [c_804, c_789])).
% 2.81/1.44  tff(c_821, plain, (![B_148]: (k1_tarski(B_148)='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_545, c_516, c_808])).
% 2.81/1.44  tff(c_835, plain, (![A_44]: (m1_subset_1(A_44, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_821, c_129])).
% 2.81/1.44  tff(c_841, plain, $false, inference(negUnitSimplification, [status(thm)], [c_789, c_835])).
% 2.81/1.44  tff(c_842, plain, (![B_105]: (k1_tarski(B_105)='#skF_3')), inference(splitRight, [status(thm)], [c_540])).
% 2.81/1.44  tff(c_848, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_842, c_116])).
% 2.81/1.44  tff(c_854, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_502, c_848])).
% 2.81/1.44  tff(c_855, plain, (![B_14]: (~v1_xboole_0(B_14))), inference(splitRight, [status(thm)], [c_514])).
% 2.81/1.44  tff(c_862, plain, $false, inference(negUnitSimplification, [status(thm)], [c_855, c_502])).
% 2.81/1.44  tff(c_863, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_60])).
% 2.81/1.44  tff(c_881, plain, (![A_157, B_158]: (r2_hidden('#skF_2'(A_157, B_158), A_157) | k1_xboole_0=A_157 | k1_tarski(B_158)=A_157)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.81/1.44  tff(c_903, plain, (![A_159, B_160]: (~v1_xboole_0(A_159) | k1_xboole_0=A_159 | k1_tarski(B_160)=A_159)), inference(resolution, [status(thm)], [c_881, c_8])).
% 2.81/1.44  tff(c_905, plain, (![B_160]: (k1_xboole_0='#skF_4' | k1_tarski(B_160)='#skF_4')), inference(resolution, [status(thm)], [c_863, c_903])).
% 2.81/1.44  tff(c_908, plain, (![B_160]: (k1_tarski(B_160)='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_30, c_905])).
% 2.81/1.44  tff(c_914, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_908, c_116])).
% 2.81/1.44  tff(c_920, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_863, c_914])).
% 2.81/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.44  
% 2.81/1.44  Inference rules
% 2.81/1.44  ----------------------
% 2.81/1.44  #Ref     : 0
% 2.81/1.44  #Sup     : 165
% 2.81/1.44  #Fact    : 0
% 2.81/1.44  #Define  : 0
% 2.81/1.44  #Split   : 10
% 2.81/1.44  #Chain   : 0
% 2.81/1.44  #Close   : 0
% 2.81/1.44  
% 2.81/1.44  Ordering : KBO
% 2.81/1.44  
% 2.81/1.44  Simplification rules
% 2.81/1.44  ----------------------
% 2.81/1.44  #Subsume      : 54
% 2.81/1.44  #Demod        : 79
% 2.81/1.44  #Tautology    : 34
% 2.81/1.44  #SimpNegUnit  : 33
% 2.81/1.44  #BackRed      : 55
% 2.81/1.44  
% 2.81/1.44  #Partial instantiations: 0
% 2.81/1.44  #Strategies tried      : 1
% 2.81/1.44  
% 2.81/1.44  Timing (in seconds)
% 2.81/1.44  ----------------------
% 2.81/1.44  Preprocessing        : 0.29
% 2.81/1.44  Parsing              : 0.15
% 2.81/1.44  CNF conversion       : 0.02
% 2.81/1.44  Main loop            : 0.38
% 2.81/1.44  Inferencing          : 0.14
% 2.81/1.44  Reduction            : 0.11
% 2.81/1.44  Demodulation         : 0.06
% 2.81/1.44  BG Simplification    : 0.02
% 2.81/1.44  Subsumption          : 0.08
% 2.81/1.44  Abstraction          : 0.02
% 2.81/1.44  MUC search           : 0.00
% 2.81/1.44  Cooper               : 0.00
% 2.81/1.44  Total                : 0.71
% 2.81/1.44  Index Insertion      : 0.00
% 2.81/1.44  Index Deletion       : 0.00
% 2.81/1.44  Index Matching       : 0.00
% 2.81/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
