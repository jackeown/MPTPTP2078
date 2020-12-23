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
% DateTime   : Thu Dec  3 10:07:10 EST 2020

% Result     : Theorem 12.20s
% Output     : CNFRefutation 12.31s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 738 expanded)
%              Number of leaves         :   31 ( 255 expanded)
%              Depth                    :   20
%              Number of atoms          :  195 (1743 expanded)
%              Number of equality atoms :   34 ( 424 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_9 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
        <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_110,plain,(
    ! [A_77,B_78,C_79] :
      ( k2_relset_1(A_77,B_78,C_79) = k2_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_114,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_110])).

tff(c_38,plain,
    ( k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7'
    | r2_hidden('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_57,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_115,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_57])).

tff(c_45,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_49,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_45])).

tff(c_60,plain,(
    ! [C_57,B_58,A_59] :
      ( v5_relat_1(C_57,B_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_59,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_64,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_60])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_51,plain,(
    ! [A_51,B_52] :
      ( ~ r2_hidden('#skF_1'(A_51,B_52),B_52)
      | r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_51])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_82,plain,(
    ! [C_68,B_69,A_70] :
      ( r2_hidden(C_68,B_69)
      | ~ r2_hidden(C_68,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_86,plain,(
    ! [A_71,B_72,B_73] :
      ( r2_hidden('#skF_1'(A_71,B_72),B_73)
      | ~ r1_tarski(A_71,B_73)
      | r1_tarski(A_71,B_72) ) ),
    inference(resolution,[status(thm)],[c_6,c_82])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1147,plain,(
    ! [A_170,B_171,B_172,B_173] :
      ( r2_hidden('#skF_1'(A_170,B_171),B_172)
      | ~ r1_tarski(B_173,B_172)
      | ~ r1_tarski(A_170,B_173)
      | r1_tarski(A_170,B_171) ) ),
    inference(resolution,[status(thm)],[c_86,c_2])).

tff(c_3556,plain,(
    ! [A_297,B_298,A_299,B_300] :
      ( r2_hidden('#skF_1'(A_297,B_298),A_299)
      | ~ r1_tarski(A_297,k2_relat_1(B_300))
      | r1_tarski(A_297,B_298)
      | ~ v5_relat_1(B_300,A_299)
      | ~ v1_relat_1(B_300) ) ),
    inference(resolution,[status(thm)],[c_10,c_1147])).

tff(c_3589,plain,(
    ! [B_301,B_302,A_303] :
      ( r2_hidden('#skF_1'(k2_relat_1(B_301),B_302),A_303)
      | r1_tarski(k2_relat_1(B_301),B_302)
      | ~ v5_relat_1(B_301,A_303)
      | ~ v1_relat_1(B_301) ) ),
    inference(resolution,[status(thm)],[c_56,c_3556])).

tff(c_44,plain,(
    ! [D_42] :
      ( r2_hidden(k4_tarski('#skF_9'(D_42),D_42),'#skF_8')
      | ~ r2_hidden(D_42,'#skF_7')
      | k2_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_7' ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_130,plain,(
    ! [D_42] :
      ( r2_hidden(k4_tarski('#skF_9'(D_42),D_42),'#skF_8')
      | ~ r2_hidden(D_42,'#skF_7')
      | k2_relat_1('#skF_8') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_44])).

tff(c_132,plain,(
    ! [D_86] :
      ( r2_hidden(k4_tarski('#skF_9'(D_86),D_86),'#skF_8')
      | ~ r2_hidden(D_86,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_130])).

tff(c_14,plain,(
    ! [C_23,A_8,D_26] :
      ( r2_hidden(C_23,k2_relat_1(A_8))
      | ~ r2_hidden(k4_tarski(D_26,C_23),A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_140,plain,(
    ! [D_87] :
      ( r2_hidden(D_87,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_87,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_132,c_14])).

tff(c_159,plain,(
    ! [D_88,B_89] :
      ( r2_hidden(D_88,B_89)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_89)
      | ~ r2_hidden(D_88,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_140,c_2])).

tff(c_162,plain,(
    ! [D_88,A_6] :
      ( r2_hidden(D_88,A_6)
      | ~ r2_hidden(D_88,'#skF_7')
      | ~ v5_relat_1('#skF_8',A_6)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_10,c_159])).

tff(c_168,plain,(
    ! [D_88,A_6] :
      ( r2_hidden(D_88,A_6)
      | ~ r2_hidden(D_88,'#skF_7')
      | ~ v5_relat_1('#skF_8',A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_162])).

tff(c_13004,plain,(
    ! [B_593,B_594,A_595] :
      ( r2_hidden('#skF_1'(k2_relat_1(B_593),B_594),A_595)
      | ~ v5_relat_1('#skF_8',A_595)
      | r1_tarski(k2_relat_1(B_593),B_594)
      | ~ v5_relat_1(B_593,'#skF_7')
      | ~ v1_relat_1(B_593) ) ),
    inference(resolution,[status(thm)],[c_3589,c_168])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_13103,plain,(
    ! [A_595,B_593] :
      ( ~ v5_relat_1('#skF_8',A_595)
      | r1_tarski(k2_relat_1(B_593),A_595)
      | ~ v5_relat_1(B_593,'#skF_7')
      | ~ v1_relat_1(B_593) ) ),
    inference(resolution,[status(thm)],[c_13004,c_4])).

tff(c_262,plain,(
    ! [A_99] :
      ( r1_tarski(A_99,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_99,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_140,c_4])).

tff(c_272,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_262])).

tff(c_454,plain,(
    ! [A_118,B_119] :
      ( r2_hidden(k4_tarski('#skF_3'(A_118,B_119),'#skF_2'(A_118,B_119)),A_118)
      | r2_hidden('#skF_4'(A_118,B_119),B_119)
      | k2_relat_1(A_118) = B_119 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_712,plain,(
    ! [A_143,B_144] :
      ( r2_hidden('#skF_2'(A_143,B_144),k2_relat_1(A_143))
      | r2_hidden('#skF_4'(A_143,B_144),B_144)
      | k2_relat_1(A_143) = B_144 ) ),
    inference(resolution,[status(thm)],[c_454,c_14])).

tff(c_1834,plain,(
    ! [A_212,B_213,B_214] :
      ( r2_hidden('#skF_2'(A_212,B_213),B_214)
      | ~ r1_tarski(k2_relat_1(A_212),B_214)
      | r2_hidden('#skF_4'(A_212,B_213),B_213)
      | k2_relat_1(A_212) = B_213 ) ),
    inference(resolution,[status(thm)],[c_712,c_2])).

tff(c_20,plain,(
    ! [A_8,B_9] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9),B_9)
      | r2_hidden('#skF_4'(A_8,B_9),B_9)
      | k2_relat_1(A_8) = B_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1924,plain,(
    ! [A_217,B_218] :
      ( ~ r1_tarski(k2_relat_1(A_217),B_218)
      | r2_hidden('#skF_4'(A_217,B_218),B_218)
      | k2_relat_1(A_217) = B_218 ) ),
    inference(resolution,[status(thm)],[c_1834,c_20])).

tff(c_2670,plain,(
    ! [A_249,A_250] :
      ( r2_hidden('#skF_4'(A_249,'#skF_7'),A_250)
      | ~ v5_relat_1('#skF_8',A_250)
      | ~ r1_tarski(k2_relat_1(A_249),'#skF_7')
      | k2_relat_1(A_249) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_1924,c_168])).

tff(c_14238,plain,(
    ! [A_623,B_624,A_625] :
      ( r2_hidden('#skF_4'(A_623,'#skF_7'),B_624)
      | ~ r1_tarski(A_625,B_624)
      | ~ v5_relat_1('#skF_8',A_625)
      | ~ r1_tarski(k2_relat_1(A_623),'#skF_7')
      | k2_relat_1(A_623) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_2670,c_2])).

tff(c_14284,plain,(
    ! [A_623] :
      ( r2_hidden('#skF_4'(A_623,'#skF_7'),k2_relat_1('#skF_8'))
      | ~ v5_relat_1('#skF_8','#skF_7')
      | ~ r1_tarski(k2_relat_1(A_623),'#skF_7')
      | k2_relat_1(A_623) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_272,c_14238])).

tff(c_14318,plain,(
    ! [A_626] :
      ( r2_hidden('#skF_4'(A_626,'#skF_7'),k2_relat_1('#skF_8'))
      | ~ r1_tarski(k2_relat_1(A_626),'#skF_7')
      | k2_relat_1(A_626) = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_14284])).

tff(c_12,plain,(
    ! [A_8,C_23] :
      ( r2_hidden(k4_tarski('#skF_5'(A_8,k2_relat_1(A_8),C_23),C_23),A_8)
      | ~ r2_hidden(C_23,k2_relat_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_557,plain,(
    ! [A_132,B_133,D_134] :
      ( r2_hidden(k4_tarski('#skF_3'(A_132,B_133),'#skF_2'(A_132,B_133)),A_132)
      | ~ r2_hidden(k4_tarski(D_134,'#skF_4'(A_132,B_133)),A_132)
      | k2_relat_1(A_132) = B_133 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_982,plain,(
    ! [A_158,B_159] :
      ( r2_hidden(k4_tarski('#skF_3'(A_158,B_159),'#skF_2'(A_158,B_159)),A_158)
      | k2_relat_1(A_158) = B_159
      | ~ r2_hidden('#skF_4'(A_158,B_159),k2_relat_1(A_158)) ) ),
    inference(resolution,[status(thm)],[c_12,c_557])).

tff(c_1324,plain,(
    ! [A_183,B_184] :
      ( r2_hidden('#skF_2'(A_183,B_184),k2_relat_1(A_183))
      | k2_relat_1(A_183) = B_184
      | ~ r2_hidden('#skF_4'(A_183,B_184),k2_relat_1(A_183)) ) ),
    inference(resolution,[status(thm)],[c_982,c_14])).

tff(c_1349,plain,(
    ! [A_183,B_184,B_2] :
      ( r2_hidden('#skF_2'(A_183,B_184),B_2)
      | ~ r1_tarski(k2_relat_1(A_183),B_2)
      | k2_relat_1(A_183) = B_184
      | ~ r2_hidden('#skF_4'(A_183,B_184),k2_relat_1(A_183)) ) ),
    inference(resolution,[status(thm)],[c_1324,c_2])).

tff(c_14323,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),B_2)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_2)
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7')
      | k2_relat_1('#skF_8') = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_14318,c_1349])).

tff(c_14336,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),B_2)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_2)
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_115,c_14323])).

tff(c_14441,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_14336])).

tff(c_14444,plain,
    ( ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_13103,c_14441])).

tff(c_14451,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_64,c_14444])).

tff(c_14453,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_14336])).

tff(c_14635,plain,(
    ! [B_630] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),B_630)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_630) ) ),
    inference(splitRight,[status(thm)],[c_14336])).

tff(c_14694,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_14635,c_20])).

tff(c_14724,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14453,c_14694])).

tff(c_14725,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_14724])).

tff(c_138,plain,(
    ! [D_86,B_2] :
      ( r2_hidden(k4_tarski('#skF_9'(D_86),D_86),B_2)
      | ~ r1_tarski('#skF_8',B_2)
      | ~ r2_hidden(D_86,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_132,c_2])).

tff(c_16,plain,(
    ! [A_8,B_9,D_22] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9),B_9)
      | ~ r2_hidden(k4_tarski(D_22,'#skF_4'(A_8,B_9)),A_8)
      | k2_relat_1(A_8) = B_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14687,plain,(
    ! [D_22] :
      ( ~ r2_hidden(k4_tarski(D_22,'#skF_4'('#skF_8','#skF_7')),'#skF_8')
      | k2_relat_1('#skF_8') = '#skF_7'
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_14635,c_16])).

tff(c_14717,plain,(
    ! [D_22] :
      ( ~ r2_hidden(k4_tarski(D_22,'#skF_4'('#skF_8','#skF_7')),'#skF_8')
      | k2_relat_1('#skF_8') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14453,c_14687])).

tff(c_14736,plain,(
    ! [D_631] : ~ r2_hidden(k4_tarski(D_631,'#skF_4'('#skF_8','#skF_7')),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_14717])).

tff(c_14748,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_138,c_14736])).

tff(c_14762,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14725,c_56,c_14748])).

tff(c_14763,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_14764,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_14824,plain,(
    ! [A_657,B_658,C_659] :
      ( k2_relset_1(A_657,B_658,C_659) = k2_relat_1(C_659)
      | ~ m1_subset_1(C_659,k1_zfmisc_1(k2_zfmisc_1(A_657,B_658))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14827,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_14824])).

tff(c_14829,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14764,c_14827])).

tff(c_14872,plain,(
    ! [A_664,C_665] :
      ( r2_hidden(k4_tarski('#skF_5'(A_664,k2_relat_1(A_664),C_665),C_665),A_664)
      | ~ r2_hidden(C_665,k2_relat_1(A_664)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    ! [E_45] :
      ( k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7'
      | ~ r2_hidden(k4_tarski(E_45,'#skF_10'),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_14777,plain,(
    ! [E_45] : ~ r2_hidden(k4_tarski(E_45,'#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14764,c_34])).

tff(c_14881,plain,(
    ~ r2_hidden('#skF_10',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_14872,c_14777])).

tff(c_14890,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14763,c_14829,c_14881])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:59:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.20/4.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.31/4.86  
% 12.31/4.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.31/4.87  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_9 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 12.31/4.87  
% 12.31/4.87  %Foreground sorts:
% 12.31/4.87  
% 12.31/4.87  
% 12.31/4.87  %Background operators:
% 12.31/4.87  
% 12.31/4.87  
% 12.31/4.87  %Foreground operators:
% 12.31/4.87  tff('#skF_9', type, '#skF_9': $i > $i).
% 12.31/4.87  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 12.31/4.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.31/4.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.31/4.87  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 12.31/4.87  tff('#skF_7', type, '#skF_7': $i).
% 12.31/4.87  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 12.31/4.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.31/4.87  tff('#skF_10', type, '#skF_10': $i).
% 12.31/4.87  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.31/4.87  tff('#skF_6', type, '#skF_6': $i).
% 12.31/4.87  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 12.31/4.87  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 12.31/4.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.31/4.87  tff('#skF_8', type, '#skF_8': $i).
% 12.31/4.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.31/4.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.31/4.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.31/4.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.31/4.87  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.31/4.87  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.31/4.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.31/4.87  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 12.31/4.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.31/4.87  
% 12.31/4.89  tff(f_73, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relset_1)).
% 12.31/4.89  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 12.31/4.89  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.31/4.89  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 12.31/4.89  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 12.31/4.89  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 12.31/4.89  tff(f_46, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 12.31/4.89  tff(c_32, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.31/4.89  tff(c_110, plain, (![A_77, B_78, C_79]: (k2_relset_1(A_77, B_78, C_79)=k2_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.31/4.89  tff(c_114, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_32, c_110])).
% 12.31/4.89  tff(c_38, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7' | r2_hidden('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.31/4.89  tff(c_57, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7'), inference(splitLeft, [status(thm)], [c_38])).
% 12.31/4.89  tff(c_115, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_57])).
% 12.31/4.89  tff(c_45, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.31/4.89  tff(c_49, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_32, c_45])).
% 12.31/4.89  tff(c_60, plain, (![C_57, B_58, A_59]: (v5_relat_1(C_57, B_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_59, B_58))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.31/4.89  tff(c_64, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_32, c_60])).
% 12.31/4.89  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.31/4.89  tff(c_51, plain, (![A_51, B_52]: (~r2_hidden('#skF_1'(A_51, B_52), B_52) | r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.31/4.89  tff(c_56, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_51])).
% 12.31/4.89  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.31/4.89  tff(c_82, plain, (![C_68, B_69, A_70]: (r2_hidden(C_68, B_69) | ~r2_hidden(C_68, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.31/4.89  tff(c_86, plain, (![A_71, B_72, B_73]: (r2_hidden('#skF_1'(A_71, B_72), B_73) | ~r1_tarski(A_71, B_73) | r1_tarski(A_71, B_72))), inference(resolution, [status(thm)], [c_6, c_82])).
% 12.31/4.89  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.31/4.89  tff(c_1147, plain, (![A_170, B_171, B_172, B_173]: (r2_hidden('#skF_1'(A_170, B_171), B_172) | ~r1_tarski(B_173, B_172) | ~r1_tarski(A_170, B_173) | r1_tarski(A_170, B_171))), inference(resolution, [status(thm)], [c_86, c_2])).
% 12.31/4.89  tff(c_3556, plain, (![A_297, B_298, A_299, B_300]: (r2_hidden('#skF_1'(A_297, B_298), A_299) | ~r1_tarski(A_297, k2_relat_1(B_300)) | r1_tarski(A_297, B_298) | ~v5_relat_1(B_300, A_299) | ~v1_relat_1(B_300))), inference(resolution, [status(thm)], [c_10, c_1147])).
% 12.31/4.89  tff(c_3589, plain, (![B_301, B_302, A_303]: (r2_hidden('#skF_1'(k2_relat_1(B_301), B_302), A_303) | r1_tarski(k2_relat_1(B_301), B_302) | ~v5_relat_1(B_301, A_303) | ~v1_relat_1(B_301))), inference(resolution, [status(thm)], [c_56, c_3556])).
% 12.31/4.89  tff(c_44, plain, (![D_42]: (r2_hidden(k4_tarski('#skF_9'(D_42), D_42), '#skF_8') | ~r2_hidden(D_42, '#skF_7') | k2_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_7')), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.31/4.89  tff(c_130, plain, (![D_42]: (r2_hidden(k4_tarski('#skF_9'(D_42), D_42), '#skF_8') | ~r2_hidden(D_42, '#skF_7') | k2_relat_1('#skF_8')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_44])).
% 12.31/4.89  tff(c_132, plain, (![D_86]: (r2_hidden(k4_tarski('#skF_9'(D_86), D_86), '#skF_8') | ~r2_hidden(D_86, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_115, c_130])).
% 12.31/4.89  tff(c_14, plain, (![C_23, A_8, D_26]: (r2_hidden(C_23, k2_relat_1(A_8)) | ~r2_hidden(k4_tarski(D_26, C_23), A_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.31/4.89  tff(c_140, plain, (![D_87]: (r2_hidden(D_87, k2_relat_1('#skF_8')) | ~r2_hidden(D_87, '#skF_7'))), inference(resolution, [status(thm)], [c_132, c_14])).
% 12.31/4.89  tff(c_159, plain, (![D_88, B_89]: (r2_hidden(D_88, B_89) | ~r1_tarski(k2_relat_1('#skF_8'), B_89) | ~r2_hidden(D_88, '#skF_7'))), inference(resolution, [status(thm)], [c_140, c_2])).
% 12.31/4.89  tff(c_162, plain, (![D_88, A_6]: (r2_hidden(D_88, A_6) | ~r2_hidden(D_88, '#skF_7') | ~v5_relat_1('#skF_8', A_6) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_10, c_159])).
% 12.31/4.89  tff(c_168, plain, (![D_88, A_6]: (r2_hidden(D_88, A_6) | ~r2_hidden(D_88, '#skF_7') | ~v5_relat_1('#skF_8', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_162])).
% 12.31/4.89  tff(c_13004, plain, (![B_593, B_594, A_595]: (r2_hidden('#skF_1'(k2_relat_1(B_593), B_594), A_595) | ~v5_relat_1('#skF_8', A_595) | r1_tarski(k2_relat_1(B_593), B_594) | ~v5_relat_1(B_593, '#skF_7') | ~v1_relat_1(B_593))), inference(resolution, [status(thm)], [c_3589, c_168])).
% 12.31/4.89  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.31/4.89  tff(c_13103, plain, (![A_595, B_593]: (~v5_relat_1('#skF_8', A_595) | r1_tarski(k2_relat_1(B_593), A_595) | ~v5_relat_1(B_593, '#skF_7') | ~v1_relat_1(B_593))), inference(resolution, [status(thm)], [c_13004, c_4])).
% 12.31/4.89  tff(c_262, plain, (![A_99]: (r1_tarski(A_99, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_99, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_140, c_4])).
% 12.31/4.89  tff(c_272, plain, (r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_262])).
% 12.31/4.89  tff(c_454, plain, (![A_118, B_119]: (r2_hidden(k4_tarski('#skF_3'(A_118, B_119), '#skF_2'(A_118, B_119)), A_118) | r2_hidden('#skF_4'(A_118, B_119), B_119) | k2_relat_1(A_118)=B_119)), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.31/4.89  tff(c_712, plain, (![A_143, B_144]: (r2_hidden('#skF_2'(A_143, B_144), k2_relat_1(A_143)) | r2_hidden('#skF_4'(A_143, B_144), B_144) | k2_relat_1(A_143)=B_144)), inference(resolution, [status(thm)], [c_454, c_14])).
% 12.31/4.89  tff(c_1834, plain, (![A_212, B_213, B_214]: (r2_hidden('#skF_2'(A_212, B_213), B_214) | ~r1_tarski(k2_relat_1(A_212), B_214) | r2_hidden('#skF_4'(A_212, B_213), B_213) | k2_relat_1(A_212)=B_213)), inference(resolution, [status(thm)], [c_712, c_2])).
% 12.31/4.89  tff(c_20, plain, (![A_8, B_9]: (~r2_hidden('#skF_2'(A_8, B_9), B_9) | r2_hidden('#skF_4'(A_8, B_9), B_9) | k2_relat_1(A_8)=B_9)), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.31/4.89  tff(c_1924, plain, (![A_217, B_218]: (~r1_tarski(k2_relat_1(A_217), B_218) | r2_hidden('#skF_4'(A_217, B_218), B_218) | k2_relat_1(A_217)=B_218)), inference(resolution, [status(thm)], [c_1834, c_20])).
% 12.31/4.89  tff(c_2670, plain, (![A_249, A_250]: (r2_hidden('#skF_4'(A_249, '#skF_7'), A_250) | ~v5_relat_1('#skF_8', A_250) | ~r1_tarski(k2_relat_1(A_249), '#skF_7') | k2_relat_1(A_249)='#skF_7')), inference(resolution, [status(thm)], [c_1924, c_168])).
% 12.31/4.89  tff(c_14238, plain, (![A_623, B_624, A_625]: (r2_hidden('#skF_4'(A_623, '#skF_7'), B_624) | ~r1_tarski(A_625, B_624) | ~v5_relat_1('#skF_8', A_625) | ~r1_tarski(k2_relat_1(A_623), '#skF_7') | k2_relat_1(A_623)='#skF_7')), inference(resolution, [status(thm)], [c_2670, c_2])).
% 12.31/4.89  tff(c_14284, plain, (![A_623]: (r2_hidden('#skF_4'(A_623, '#skF_7'), k2_relat_1('#skF_8')) | ~v5_relat_1('#skF_8', '#skF_7') | ~r1_tarski(k2_relat_1(A_623), '#skF_7') | k2_relat_1(A_623)='#skF_7')), inference(resolution, [status(thm)], [c_272, c_14238])).
% 12.31/4.89  tff(c_14318, plain, (![A_626]: (r2_hidden('#skF_4'(A_626, '#skF_7'), k2_relat_1('#skF_8')) | ~r1_tarski(k2_relat_1(A_626), '#skF_7') | k2_relat_1(A_626)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_14284])).
% 12.31/4.89  tff(c_12, plain, (![A_8, C_23]: (r2_hidden(k4_tarski('#skF_5'(A_8, k2_relat_1(A_8), C_23), C_23), A_8) | ~r2_hidden(C_23, k2_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.31/4.89  tff(c_557, plain, (![A_132, B_133, D_134]: (r2_hidden(k4_tarski('#skF_3'(A_132, B_133), '#skF_2'(A_132, B_133)), A_132) | ~r2_hidden(k4_tarski(D_134, '#skF_4'(A_132, B_133)), A_132) | k2_relat_1(A_132)=B_133)), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.31/4.89  tff(c_982, plain, (![A_158, B_159]: (r2_hidden(k4_tarski('#skF_3'(A_158, B_159), '#skF_2'(A_158, B_159)), A_158) | k2_relat_1(A_158)=B_159 | ~r2_hidden('#skF_4'(A_158, B_159), k2_relat_1(A_158)))), inference(resolution, [status(thm)], [c_12, c_557])).
% 12.31/4.89  tff(c_1324, plain, (![A_183, B_184]: (r2_hidden('#skF_2'(A_183, B_184), k2_relat_1(A_183)) | k2_relat_1(A_183)=B_184 | ~r2_hidden('#skF_4'(A_183, B_184), k2_relat_1(A_183)))), inference(resolution, [status(thm)], [c_982, c_14])).
% 12.31/4.89  tff(c_1349, plain, (![A_183, B_184, B_2]: (r2_hidden('#skF_2'(A_183, B_184), B_2) | ~r1_tarski(k2_relat_1(A_183), B_2) | k2_relat_1(A_183)=B_184 | ~r2_hidden('#skF_4'(A_183, B_184), k2_relat_1(A_183)))), inference(resolution, [status(thm)], [c_1324, c_2])).
% 12.31/4.89  tff(c_14323, plain, (![B_2]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), B_2) | ~r1_tarski(k2_relat_1('#skF_8'), B_2) | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7')), inference(resolution, [status(thm)], [c_14318, c_1349])).
% 12.31/4.89  tff(c_14336, plain, (![B_2]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), B_2) | ~r1_tarski(k2_relat_1('#skF_8'), B_2) | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_115, c_115, c_14323])).
% 12.31/4.89  tff(c_14441, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_14336])).
% 12.31/4.89  tff(c_14444, plain, (~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_13103, c_14441])).
% 12.31/4.89  tff(c_14451, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_49, c_64, c_14444])).
% 12.31/4.89  tff(c_14453, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_14336])).
% 12.31/4.89  tff(c_14635, plain, (![B_630]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), B_630) | ~r1_tarski(k2_relat_1('#skF_8'), B_630))), inference(splitRight, [status(thm)], [c_14336])).
% 12.31/4.89  tff(c_14694, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_14635, c_20])).
% 12.31/4.89  tff(c_14724, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_14453, c_14694])).
% 12.31/4.89  tff(c_14725, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_115, c_14724])).
% 12.31/4.89  tff(c_138, plain, (![D_86, B_2]: (r2_hidden(k4_tarski('#skF_9'(D_86), D_86), B_2) | ~r1_tarski('#skF_8', B_2) | ~r2_hidden(D_86, '#skF_7'))), inference(resolution, [status(thm)], [c_132, c_2])).
% 12.31/4.89  tff(c_16, plain, (![A_8, B_9, D_22]: (~r2_hidden('#skF_2'(A_8, B_9), B_9) | ~r2_hidden(k4_tarski(D_22, '#skF_4'(A_8, B_9)), A_8) | k2_relat_1(A_8)=B_9)), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.31/4.89  tff(c_14687, plain, (![D_22]: (~r2_hidden(k4_tarski(D_22, '#skF_4'('#skF_8', '#skF_7')), '#skF_8') | k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7'))), inference(resolution, [status(thm)], [c_14635, c_16])).
% 12.31/4.89  tff(c_14717, plain, (![D_22]: (~r2_hidden(k4_tarski(D_22, '#skF_4'('#skF_8', '#skF_7')), '#skF_8') | k2_relat_1('#skF_8')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_14453, c_14687])).
% 12.31/4.89  tff(c_14736, plain, (![D_631]: (~r2_hidden(k4_tarski(D_631, '#skF_4'('#skF_8', '#skF_7')), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_115, c_14717])).
% 12.31/4.89  tff(c_14748, plain, (~r1_tarski('#skF_8', '#skF_8') | ~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_138, c_14736])).
% 12.31/4.89  tff(c_14762, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14725, c_56, c_14748])).
% 12.31/4.89  tff(c_14763, plain, (r2_hidden('#skF_10', '#skF_7')), inference(splitRight, [status(thm)], [c_38])).
% 12.31/4.89  tff(c_14764, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_38])).
% 12.31/4.89  tff(c_14824, plain, (![A_657, B_658, C_659]: (k2_relset_1(A_657, B_658, C_659)=k2_relat_1(C_659) | ~m1_subset_1(C_659, k1_zfmisc_1(k2_zfmisc_1(A_657, B_658))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.31/4.89  tff(c_14827, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_32, c_14824])).
% 12.31/4.89  tff(c_14829, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_14764, c_14827])).
% 12.31/4.89  tff(c_14872, plain, (![A_664, C_665]: (r2_hidden(k4_tarski('#skF_5'(A_664, k2_relat_1(A_664), C_665), C_665), A_664) | ~r2_hidden(C_665, k2_relat_1(A_664)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.31/4.89  tff(c_34, plain, (![E_45]: (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7' | ~r2_hidden(k4_tarski(E_45, '#skF_10'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.31/4.89  tff(c_14777, plain, (![E_45]: (~r2_hidden(k4_tarski(E_45, '#skF_10'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_14764, c_34])).
% 12.31/4.89  tff(c_14881, plain, (~r2_hidden('#skF_10', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_14872, c_14777])).
% 12.31/4.89  tff(c_14890, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14763, c_14829, c_14881])).
% 12.31/4.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.31/4.89  
% 12.31/4.89  Inference rules
% 12.31/4.89  ----------------------
% 12.31/4.89  #Ref     : 0
% 12.31/4.89  #Sup     : 3619
% 12.31/4.89  #Fact    : 0
% 12.31/4.89  #Define  : 0
% 12.31/4.89  #Split   : 41
% 12.31/4.89  #Chain   : 0
% 12.31/4.89  #Close   : 0
% 12.31/4.89  
% 12.31/4.89  Ordering : KBO
% 12.31/4.89  
% 12.31/4.89  Simplification rules
% 12.31/4.89  ----------------------
% 12.31/4.89  #Subsume      : 1502
% 12.31/4.89  #Demod        : 693
% 12.31/4.89  #Tautology    : 152
% 12.31/4.89  #SimpNegUnit  : 13
% 12.31/4.89  #BackRed      : 15
% 12.31/4.89  
% 12.31/4.89  #Partial instantiations: 0
% 12.31/4.89  #Strategies tried      : 1
% 12.31/4.89  
% 12.31/4.89  Timing (in seconds)
% 12.31/4.89  ----------------------
% 12.31/4.89  Preprocessing        : 0.31
% 12.31/4.89  Parsing              : 0.16
% 12.31/4.89  CNF conversion       : 0.02
% 12.31/4.89  Main loop            : 3.81
% 12.31/4.89  Inferencing          : 0.70
% 12.31/4.89  Reduction            : 0.69
% 12.31/4.89  Demodulation         : 0.42
% 12.31/4.89  BG Simplification    : 0.07
% 12.31/4.89  Subsumption          : 2.12
% 12.31/4.89  Abstraction          : 0.11
% 12.31/4.89  MUC search           : 0.00
% 12.31/4.89  Cooper               : 0.00
% 12.31/4.89  Total                : 4.16
% 12.31/4.89  Index Insertion      : 0.00
% 12.31/4.89  Index Deletion       : 0.00
% 12.31/4.89  Index Matching       : 0.00
% 12.31/4.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
