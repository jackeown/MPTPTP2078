%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:52 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 206 expanded)
%              Number of leaves         :   30 (  86 expanded)
%              Depth                    :    7
%              Number of atoms          :  160 ( 576 expanded)
%              Number of equality atoms :   46 ( 115 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( B != k1_xboole_0
         => ! [E] :
              ( r2_hidden(E,k8_relset_1(A,B,D,C))
            <=> ( r2_hidden(E,A)
                & r2_hidden(k1_funct_1(D,E),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_funct_2)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_69,axiom,(
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

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_39,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( r2_hidden(D,k1_relat_1(A))
                & r2_hidden(k1_funct_1(A,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_273,plain,(
    ! [A_108,B_109,C_110,D_111] :
      ( k8_relset_1(A_108,B_109,C_110,D_111) = k10_relat_1(C_110,D_111)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_276,plain,(
    ! [D_111] : k8_relset_1('#skF_3','#skF_4','#skF_6',D_111) = k10_relat_1('#skF_6',D_111) ),
    inference(resolution,[status(thm)],[c_40,c_273])).

tff(c_50,plain,
    ( r2_hidden('#skF_7','#skF_3')
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),'#skF_5')
    | ~ r2_hidden('#skF_8','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_63,plain,(
    ~ r2_hidden('#skF_8','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_42,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_66,plain,(
    ! [A_31,B_32,C_33] :
      ( k1_relset_1(A_31,B_32,C_33) = k1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_70,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_66])).

tff(c_107,plain,(
    ! [B_51,A_52,C_53] :
      ( k1_xboole_0 = B_51
      | k1_relset_1(A_52,B_51,C_53) = A_52
      | ~ v1_funct_2(C_53,A_52,B_51)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_52,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_110,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_107])).

tff(c_113,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_70,c_110])).

tff(c_114,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_113])).

tff(c_57,plain,(
    ! [C_27,A_28,B_29] :
      ( v1_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_61,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_57])).

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_76,plain,(
    ! [A_37,B_38,C_39,D_40] :
      ( k8_relset_1(A_37,B_38,C_39,D_40) = k10_relat_1(C_39,D_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_79,plain,(
    ! [D_40] : k8_relset_1('#skF_3','#skF_4','#skF_6',D_40) = k10_relat_1('#skF_6',D_40) ),
    inference(resolution,[status(thm)],[c_40,c_76])).

tff(c_56,plain,
    ( r2_hidden('#skF_7','#skF_3')
    | r2_hidden('#skF_8',k8_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_62,plain,(
    r2_hidden('#skF_8',k8_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_80,plain,(
    r2_hidden('#skF_8',k10_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_62])).

tff(c_6,plain,(
    ! [D_12,A_1,B_8] :
      ( r2_hidden(D_12,k1_relat_1(A_1))
      | ~ r2_hidden(D_12,k10_relat_1(A_1,B_8))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_92,plain,
    ( r2_hidden('#skF_8',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_6])).

tff(c_95,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_44,c_92])).

tff(c_115,plain,(
    r2_hidden('#skF_8','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_95])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_115])).

tff(c_120,plain,(
    r2_hidden('#skF_8','#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_136,plain,(
    ! [A_61,B_62,C_63,D_64] :
      ( k8_relset_1(A_61,B_62,C_63,D_64) = k10_relat_1(C_63,D_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_139,plain,(
    ! [D_64] : k8_relset_1('#skF_3','#skF_4','#skF_6',D_64) = k10_relat_1('#skF_6',D_64) ),
    inference(resolution,[status(thm)],[c_40,c_136])).

tff(c_140,plain,(
    r2_hidden('#skF_8',k10_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_62])).

tff(c_159,plain,(
    ! [A_68,D_69,B_70] :
      ( r2_hidden(k1_funct_1(A_68,D_69),B_70)
      | ~ r2_hidden(D_69,k10_relat_1(A_68,B_70))
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_119,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),'#skF_5')
    | r2_hidden('#skF_7','#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_122,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_166,plain,
    ( ~ r2_hidden('#skF_8',k10_relat_1('#skF_6','#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_159,c_122])).

tff(c_171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_44,c_140,c_166])).

tff(c_173,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_195,plain,(
    ! [A_83,B_84,C_85,D_86] :
      ( k8_relset_1(A_83,B_84,C_85,D_86) = k10_relat_1(C_85,D_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_198,plain,(
    ! [D_86] : k8_relset_1('#skF_3','#skF_4','#skF_6',D_86) = k10_relat_1('#skF_6',D_86) ),
    inference(resolution,[status(thm)],[c_40,c_195])).

tff(c_46,plain,
    ( ~ r2_hidden('#skF_7',k8_relset_1('#skF_3','#skF_4','#skF_6','#skF_5'))
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),'#skF_5')
    | ~ r2_hidden('#skF_8','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_216,plain,(
    ~ r2_hidden('#skF_7',k10_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_173,c_198,c_46])).

tff(c_172,plain,(
    r2_hidden('#skF_7','#skF_3') ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_175,plain,(
    ! [A_72,B_73,C_74] :
      ( k1_relset_1(A_72,B_73,C_74) = k1_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_179,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_175])).

tff(c_226,plain,(
    ! [B_95,A_96,C_97] :
      ( k1_xboole_0 = B_95
      | k1_relset_1(A_96,B_95,C_97) = A_96
      | ~ v1_funct_2(C_97,A_96,B_95)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_96,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_229,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_226])).

tff(c_232,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_179,c_229])).

tff(c_233,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_232])).

tff(c_48,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_7'),'#skF_5')
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),'#skF_5')
    | ~ r2_hidden('#skF_8','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_181,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_173,c_48])).

tff(c_241,plain,(
    ! [D_98,A_99,B_100] :
      ( r2_hidden(D_98,k10_relat_1(A_99,B_100))
      | ~ r2_hidden(k1_funct_1(A_99,D_98),B_100)
      | ~ r2_hidden(D_98,k1_relat_1(A_99))
      | ~ v1_funct_1(A_99)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_247,plain,
    ( r2_hidden('#skF_7',k10_relat_1('#skF_6','#skF_5'))
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_181,c_241])).

tff(c_254,plain,(
    r2_hidden('#skF_7',k10_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_44,c_172,c_233,c_247])).

tff(c_256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_216,c_254])).

tff(c_258,plain,(
    ~ r2_hidden('#skF_8',k8_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_277,plain,(
    ~ r2_hidden('#skF_8',k10_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_258])).

tff(c_52,plain,
    ( ~ r2_hidden('#skF_7',k8_relset_1('#skF_3','#skF_4','#skF_6','#skF_5'))
    | r2_hidden('#skF_8',k8_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_287,plain,
    ( ~ r2_hidden('#skF_7',k10_relat_1('#skF_6','#skF_5'))
    | r2_hidden('#skF_8',k10_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_276,c_52])).

tff(c_288,plain,(
    ~ r2_hidden('#skF_7',k10_relat_1('#skF_6','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_277,c_287])).

tff(c_257,plain,(
    r2_hidden('#skF_7','#skF_3') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_261,plain,(
    ! [A_102,B_103,C_104] :
      ( k1_relset_1(A_102,B_103,C_104) = k1_relat_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_265,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_261])).

tff(c_306,plain,(
    ! [B_125,A_126,C_127] :
      ( k1_xboole_0 = B_125
      | k1_relset_1(A_126,B_125,C_127) = A_126
      | ~ v1_funct_2(C_127,A_126,B_125)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_126,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_309,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_306])).

tff(c_312,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_265,c_309])).

tff(c_313,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_312])).

tff(c_54,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_7'),'#skF_5')
    | r2_hidden('#skF_8',k8_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_270,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_7'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_258,c_54])).

tff(c_323,plain,(
    ! [D_128,A_129,B_130] :
      ( r2_hidden(D_128,k10_relat_1(A_129,B_130))
      | ~ r2_hidden(k1_funct_1(A_129,D_128),B_130)
      | ~ r2_hidden(D_128,k1_relat_1(A_129))
      | ~ v1_funct_1(A_129)
      | ~ v1_relat_1(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_329,plain,
    ( r2_hidden('#skF_7',k10_relat_1('#skF_6','#skF_5'))
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_270,c_323])).

tff(c_333,plain,(
    r2_hidden('#skF_7',k10_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_44,c_257,c_313,c_329])).

tff(c_335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_288,c_333])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:53:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.29  
% 2.21/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.29  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4
% 2.21/1.29  
% 2.21/1.29  %Foreground sorts:
% 2.21/1.29  
% 2.21/1.29  
% 2.21/1.29  %Background operators:
% 2.21/1.29  
% 2.21/1.29  
% 2.21/1.29  %Foreground operators:
% 2.21/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.21/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.21/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.29  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.21/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.29  tff('#skF_7', type, '#skF_7': $i).
% 2.21/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.21/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.21/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.21/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.21/1.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.21/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.21/1.29  tff('#skF_8', type, '#skF_8': $i).
% 2.21/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.29  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.21/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.21/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.21/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.29  
% 2.21/1.31  tff(f_86, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (~(B = k1_xboole_0) => (![E]: (r2_hidden(E, k8_relset_1(A, B, D, C)) <=> (r2_hidden(E, A) & r2_hidden(k1_funct_1(D, E), C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_funct_2)).
% 2.21/1.31  tff(f_51, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.21/1.31  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.21/1.31  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.21/1.31  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.21/1.31  tff(f_39, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, k1_relat_1(A)) & r2_hidden(k1_funct_1(A, D), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_funct_1)).
% 2.21/1.31  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.31  tff(c_273, plain, (![A_108, B_109, C_110, D_111]: (k8_relset_1(A_108, B_109, C_110, D_111)=k10_relat_1(C_110, D_111) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.21/1.31  tff(c_276, plain, (![D_111]: (k8_relset_1('#skF_3', '#skF_4', '#skF_6', D_111)=k10_relat_1('#skF_6', D_111))), inference(resolution, [status(thm)], [c_40, c_273])).
% 2.21/1.31  tff(c_50, plain, (r2_hidden('#skF_7', '#skF_3') | ~r2_hidden(k1_funct_1('#skF_6', '#skF_8'), '#skF_5') | ~r2_hidden('#skF_8', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.31  tff(c_63, plain, (~r2_hidden('#skF_8', '#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 2.21/1.31  tff(c_38, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.31  tff(c_42, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.31  tff(c_66, plain, (![A_31, B_32, C_33]: (k1_relset_1(A_31, B_32, C_33)=k1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.21/1.31  tff(c_70, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_66])).
% 2.21/1.31  tff(c_107, plain, (![B_51, A_52, C_53]: (k1_xboole_0=B_51 | k1_relset_1(A_52, B_51, C_53)=A_52 | ~v1_funct_2(C_53, A_52, B_51) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_52, B_51))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.21/1.31  tff(c_110, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_107])).
% 2.21/1.31  tff(c_113, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_70, c_110])).
% 2.21/1.31  tff(c_114, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_38, c_113])).
% 2.21/1.31  tff(c_57, plain, (![C_27, A_28, B_29]: (v1_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.21/1.31  tff(c_61, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_57])).
% 2.21/1.31  tff(c_44, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.31  tff(c_76, plain, (![A_37, B_38, C_39, D_40]: (k8_relset_1(A_37, B_38, C_39, D_40)=k10_relat_1(C_39, D_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.21/1.31  tff(c_79, plain, (![D_40]: (k8_relset_1('#skF_3', '#skF_4', '#skF_6', D_40)=k10_relat_1('#skF_6', D_40))), inference(resolution, [status(thm)], [c_40, c_76])).
% 2.21/1.31  tff(c_56, plain, (r2_hidden('#skF_7', '#skF_3') | r2_hidden('#skF_8', k8_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.31  tff(c_62, plain, (r2_hidden('#skF_8', k8_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_56])).
% 2.21/1.31  tff(c_80, plain, (r2_hidden('#skF_8', k10_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_62])).
% 2.21/1.31  tff(c_6, plain, (![D_12, A_1, B_8]: (r2_hidden(D_12, k1_relat_1(A_1)) | ~r2_hidden(D_12, k10_relat_1(A_1, B_8)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.21/1.31  tff(c_92, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_6])).
% 2.21/1.31  tff(c_95, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_44, c_92])).
% 2.21/1.31  tff(c_115, plain, (r2_hidden('#skF_8', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_95])).
% 2.21/1.31  tff(c_118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_115])).
% 2.21/1.31  tff(c_120, plain, (r2_hidden('#skF_8', '#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 2.21/1.31  tff(c_136, plain, (![A_61, B_62, C_63, D_64]: (k8_relset_1(A_61, B_62, C_63, D_64)=k10_relat_1(C_63, D_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.21/1.31  tff(c_139, plain, (![D_64]: (k8_relset_1('#skF_3', '#skF_4', '#skF_6', D_64)=k10_relat_1('#skF_6', D_64))), inference(resolution, [status(thm)], [c_40, c_136])).
% 2.21/1.31  tff(c_140, plain, (r2_hidden('#skF_8', k10_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_62])).
% 2.21/1.31  tff(c_159, plain, (![A_68, D_69, B_70]: (r2_hidden(k1_funct_1(A_68, D_69), B_70) | ~r2_hidden(D_69, k10_relat_1(A_68, B_70)) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.21/1.31  tff(c_119, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_8'), '#skF_5') | r2_hidden('#skF_7', '#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 2.21/1.31  tff(c_122, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_119])).
% 2.21/1.31  tff(c_166, plain, (~r2_hidden('#skF_8', k10_relat_1('#skF_6', '#skF_5')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_159, c_122])).
% 2.21/1.31  tff(c_171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_44, c_140, c_166])).
% 2.21/1.31  tff(c_173, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_8'), '#skF_5')), inference(splitRight, [status(thm)], [c_119])).
% 2.21/1.31  tff(c_195, plain, (![A_83, B_84, C_85, D_86]: (k8_relset_1(A_83, B_84, C_85, D_86)=k10_relat_1(C_85, D_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.21/1.31  tff(c_198, plain, (![D_86]: (k8_relset_1('#skF_3', '#skF_4', '#skF_6', D_86)=k10_relat_1('#skF_6', D_86))), inference(resolution, [status(thm)], [c_40, c_195])).
% 2.21/1.31  tff(c_46, plain, (~r2_hidden('#skF_7', k8_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5')) | ~r2_hidden(k1_funct_1('#skF_6', '#skF_8'), '#skF_5') | ~r2_hidden('#skF_8', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.31  tff(c_216, plain, (~r2_hidden('#skF_7', k10_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_173, c_198, c_46])).
% 2.21/1.31  tff(c_172, plain, (r2_hidden('#skF_7', '#skF_3')), inference(splitRight, [status(thm)], [c_119])).
% 2.21/1.31  tff(c_175, plain, (![A_72, B_73, C_74]: (k1_relset_1(A_72, B_73, C_74)=k1_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.21/1.31  tff(c_179, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_175])).
% 2.21/1.31  tff(c_226, plain, (![B_95, A_96, C_97]: (k1_xboole_0=B_95 | k1_relset_1(A_96, B_95, C_97)=A_96 | ~v1_funct_2(C_97, A_96, B_95) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_96, B_95))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.21/1.31  tff(c_229, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_226])).
% 2.21/1.31  tff(c_232, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_179, c_229])).
% 2.21/1.31  tff(c_233, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_38, c_232])).
% 2.21/1.31  tff(c_48, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_7'), '#skF_5') | ~r2_hidden(k1_funct_1('#skF_6', '#skF_8'), '#skF_5') | ~r2_hidden('#skF_8', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.31  tff(c_181, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_7'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_173, c_48])).
% 2.21/1.31  tff(c_241, plain, (![D_98, A_99, B_100]: (r2_hidden(D_98, k10_relat_1(A_99, B_100)) | ~r2_hidden(k1_funct_1(A_99, D_98), B_100) | ~r2_hidden(D_98, k1_relat_1(A_99)) | ~v1_funct_1(A_99) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.21/1.31  tff(c_247, plain, (r2_hidden('#skF_7', k10_relat_1('#skF_6', '#skF_5')) | ~r2_hidden('#skF_7', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_181, c_241])).
% 2.21/1.31  tff(c_254, plain, (r2_hidden('#skF_7', k10_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_44, c_172, c_233, c_247])).
% 2.21/1.31  tff(c_256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_216, c_254])).
% 2.21/1.31  tff(c_258, plain, (~r2_hidden('#skF_8', k8_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_56])).
% 2.21/1.31  tff(c_277, plain, (~r2_hidden('#skF_8', k10_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_258])).
% 2.21/1.31  tff(c_52, plain, (~r2_hidden('#skF_7', k8_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5')) | r2_hidden('#skF_8', k8_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.31  tff(c_287, plain, (~r2_hidden('#skF_7', k10_relat_1('#skF_6', '#skF_5')) | r2_hidden('#skF_8', k10_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_276, c_52])).
% 2.21/1.31  tff(c_288, plain, (~r2_hidden('#skF_7', k10_relat_1('#skF_6', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_277, c_287])).
% 2.21/1.31  tff(c_257, plain, (r2_hidden('#skF_7', '#skF_3')), inference(splitRight, [status(thm)], [c_56])).
% 2.21/1.31  tff(c_261, plain, (![A_102, B_103, C_104]: (k1_relset_1(A_102, B_103, C_104)=k1_relat_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.21/1.31  tff(c_265, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_261])).
% 2.21/1.31  tff(c_306, plain, (![B_125, A_126, C_127]: (k1_xboole_0=B_125 | k1_relset_1(A_126, B_125, C_127)=A_126 | ~v1_funct_2(C_127, A_126, B_125) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.21/1.31  tff(c_309, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_306])).
% 2.21/1.31  tff(c_312, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_265, c_309])).
% 2.21/1.31  tff(c_313, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_38, c_312])).
% 2.21/1.31  tff(c_54, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_7'), '#skF_5') | r2_hidden('#skF_8', k8_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.31  tff(c_270, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_7'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_258, c_54])).
% 2.21/1.31  tff(c_323, plain, (![D_128, A_129, B_130]: (r2_hidden(D_128, k10_relat_1(A_129, B_130)) | ~r2_hidden(k1_funct_1(A_129, D_128), B_130) | ~r2_hidden(D_128, k1_relat_1(A_129)) | ~v1_funct_1(A_129) | ~v1_relat_1(A_129))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.21/1.31  tff(c_329, plain, (r2_hidden('#skF_7', k10_relat_1('#skF_6', '#skF_5')) | ~r2_hidden('#skF_7', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_270, c_323])).
% 2.21/1.31  tff(c_333, plain, (r2_hidden('#skF_7', k10_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_44, c_257, c_313, c_329])).
% 2.21/1.31  tff(c_335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_288, c_333])).
% 2.21/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.31  
% 2.21/1.31  Inference rules
% 2.21/1.31  ----------------------
% 2.21/1.31  #Ref     : 0
% 2.21/1.31  #Sup     : 49
% 2.21/1.31  #Fact    : 0
% 2.21/1.31  #Define  : 0
% 2.21/1.31  #Split   : 4
% 2.21/1.31  #Chain   : 0
% 2.21/1.31  #Close   : 0
% 2.21/1.31  
% 2.21/1.31  Ordering : KBO
% 2.21/1.31  
% 2.21/1.31  Simplification rules
% 2.21/1.31  ----------------------
% 2.21/1.31  #Subsume      : 4
% 2.21/1.31  #Demod        : 57
% 2.21/1.31  #Tautology    : 33
% 2.21/1.31  #SimpNegUnit  : 10
% 2.21/1.31  #BackRed      : 9
% 2.21/1.31  
% 2.21/1.31  #Partial instantiations: 0
% 2.21/1.31  #Strategies tried      : 1
% 2.21/1.31  
% 2.21/1.31  Timing (in seconds)
% 2.21/1.31  ----------------------
% 2.21/1.31  Preprocessing        : 0.32
% 2.21/1.31  Parsing              : 0.17
% 2.21/1.31  CNF conversion       : 0.02
% 2.21/1.31  Main loop            : 0.23
% 2.21/1.31  Inferencing          : 0.09
% 2.21/1.31  Reduction            : 0.07
% 2.21/1.31  Demodulation         : 0.05
% 2.21/1.31  BG Simplification    : 0.02
% 2.21/1.31  Subsumption          : 0.04
% 2.21/1.31  Abstraction          : 0.01
% 2.21/1.31  MUC search           : 0.00
% 2.21/1.31  Cooper               : 0.00
% 2.21/1.31  Total                : 0.60
% 2.21/1.31  Index Insertion      : 0.00
% 2.21/1.31  Index Deletion       : 0.00
% 2.21/1.31  Index Matching       : 0.00
% 2.21/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
