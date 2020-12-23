%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:10 EST 2020

% Result     : Theorem 9.22s
% Output     : CNFRefutation 9.44s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 409 expanded)
%              Number of leaves         :   24 ( 144 expanded)
%              Depth                    :   14
%              Number of atoms          :  173 ( 918 expanded)
%              Number of equality atoms :   45 ( 229 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_8 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
        <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1943,plain,(
    ! [A_221,B_222,C_223] :
      ( k1_relset_1(A_221,B_222,C_223) = k1_relat_1(C_223)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_221,B_222))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1947,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_1943])).

tff(c_30,plain,
    ( k1_relset_1('#skF_6','#skF_5','#skF_7') != '#skF_6'
    | r2_hidden('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_37,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_7') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_1948,plain,(
    k1_relat_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1947,c_37])).

tff(c_7320,plain,(
    ! [A_511,B_512] :
      ( r2_hidden(k4_tarski('#skF_1'(A_511,B_512),'#skF_2'(A_511,B_512)),A_511)
      | r2_hidden('#skF_3'(A_511,B_512),B_512)
      | k1_relat_1(A_511) = B_512 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12,plain,(
    ! [C_24,A_9,D_27] :
      ( r2_hidden(C_24,k1_relat_1(A_9))
      | ~ r2_hidden(k4_tarski(C_24,D_27),A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_7363,plain,(
    ! [A_511,B_512] :
      ( r2_hidden('#skF_1'(A_511,B_512),k1_relat_1(A_511))
      | r2_hidden('#skF_3'(A_511,B_512),B_512)
      | k1_relat_1(A_511) = B_512 ) ),
    inference(resolution,[status(thm)],[c_7320,c_12])).

tff(c_5044,plain,(
    ! [C_376,A_377] :
      ( r2_hidden(k4_tarski(C_376,'#skF_4'(A_377,k1_relat_1(A_377),C_376)),A_377)
      | ~ r2_hidden(C_376,k1_relat_1(A_377)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14813,plain,(
    ! [C_889,A_890,A_891] :
      ( r2_hidden(k4_tarski(C_889,'#skF_4'(A_890,k1_relat_1(A_890),C_889)),A_891)
      | ~ m1_subset_1(A_890,k1_zfmisc_1(A_891))
      | ~ r2_hidden(C_889,k1_relat_1(A_890)) ) ),
    inference(resolution,[status(thm)],[c_5044,c_8])).

tff(c_14906,plain,(
    ! [C_892,A_893,A_894] :
      ( r2_hidden(C_892,k1_relat_1(A_893))
      | ~ m1_subset_1(A_894,k1_zfmisc_1(A_893))
      | ~ r2_hidden(C_892,k1_relat_1(A_894)) ) ),
    inference(resolution,[status(thm)],[c_14813,c_12])).

tff(c_14910,plain,(
    ! [C_895] :
      ( r2_hidden(C_895,k1_relat_1(k2_zfmisc_1('#skF_6','#skF_5')))
      | ~ r2_hidden(C_895,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_24,c_14906])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5066,plain,(
    ! [C_376,C_3,D_4] :
      ( r2_hidden(C_376,C_3)
      | ~ r2_hidden(C_376,k1_relat_1(k2_zfmisc_1(C_3,D_4))) ) ),
    inference(resolution,[status(thm)],[c_5044,c_6])).

tff(c_14960,plain,(
    ! [C_896] :
      ( r2_hidden(C_896,'#skF_6')
      | ~ r2_hidden(C_896,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_14910,c_5066])).

tff(c_15005,plain,(
    ! [B_512] :
      ( r2_hidden('#skF_1'('#skF_7',B_512),'#skF_6')
      | r2_hidden('#skF_3'('#skF_7',B_512),B_512)
      | k1_relat_1('#skF_7') = B_512 ) ),
    inference(resolution,[status(thm)],[c_7363,c_14960])).

tff(c_127,plain,(
    ! [A_71,B_72,C_73] :
      ( k1_relset_1(A_71,B_72,C_73) = k1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_131,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_127])).

tff(c_132,plain,(
    k1_relat_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_37])).

tff(c_532,plain,(
    ! [A_121,B_122] :
      ( r2_hidden(k4_tarski('#skF_1'(A_121,B_122),'#skF_2'(A_121,B_122)),A_121)
      | r2_hidden('#skF_3'(A_121,B_122),B_122)
      | k1_relat_1(A_121) = B_122 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_571,plain,(
    ! [A_121,B_122] :
      ( r2_hidden('#skF_1'(A_121,B_122),k1_relat_1(A_121))
      | r2_hidden('#skF_3'(A_121,B_122),B_122)
      | k1_relat_1(A_121) = B_122 ) ),
    inference(resolution,[status(thm)],[c_532,c_12])).

tff(c_144,plain,(
    ! [C_78,A_79] :
      ( r2_hidden(k4_tarski(C_78,'#skF_4'(A_79,k1_relat_1(A_79),C_78)),A_79)
      | ~ r2_hidden(C_78,k1_relat_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1279,plain,(
    ! [C_175,A_176,A_177] :
      ( r2_hidden(k4_tarski(C_175,'#skF_4'(A_176,k1_relat_1(A_176),C_175)),A_177)
      | ~ m1_subset_1(A_176,k1_zfmisc_1(A_177))
      | ~ r2_hidden(C_175,k1_relat_1(A_176)) ) ),
    inference(resolution,[status(thm)],[c_144,c_8])).

tff(c_1345,plain,(
    ! [C_178,A_179,A_180] :
      ( r2_hidden(C_178,k1_relat_1(A_179))
      | ~ m1_subset_1(A_180,k1_zfmisc_1(A_179))
      | ~ r2_hidden(C_178,k1_relat_1(A_180)) ) ),
    inference(resolution,[status(thm)],[c_1279,c_12])).

tff(c_1349,plain,(
    ! [C_181] :
      ( r2_hidden(C_181,k1_relat_1(k2_zfmisc_1('#skF_6','#skF_5')))
      | ~ r2_hidden(C_181,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_24,c_1345])).

tff(c_163,plain,(
    ! [C_78,C_3,D_4] :
      ( r2_hidden(C_78,C_3)
      | ~ r2_hidden(C_78,k1_relat_1(k2_zfmisc_1(C_3,D_4))) ) ),
    inference(resolution,[status(thm)],[c_144,c_6])).

tff(c_1392,plain,(
    ! [C_182] :
      ( r2_hidden(C_182,'#skF_6')
      | ~ r2_hidden(C_182,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_1349,c_163])).

tff(c_1433,plain,(
    ! [B_122] :
      ( r2_hidden('#skF_1'('#skF_7',B_122),'#skF_6')
      | r2_hidden('#skF_3'('#skF_7',B_122),B_122)
      | k1_relat_1('#skF_7') = B_122 ) ),
    inference(resolution,[status(thm)],[c_571,c_1392])).

tff(c_32,plain,(
    ! [D_37] :
      ( r2_hidden(k4_tarski(D_37,'#skF_8'(D_37)),'#skF_7')
      | ~ r2_hidden(D_37,'#skF_6')
      | r2_hidden('#skF_9','#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,(
    r2_hidden('#skF_9','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_49,plain,(
    ! [A_57,B_58,C_59] :
      ( k1_relset_1(A_57,B_58,C_59) = k1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_53,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_49])).

tff(c_54,plain,(
    k1_relat_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_37])).

tff(c_36,plain,(
    ! [D_37] :
      ( r2_hidden(k4_tarski(D_37,'#skF_8'(D_37)),'#skF_7')
      | ~ r2_hidden(D_37,'#skF_6')
      | k1_relset_1('#skF_6','#skF_5','#skF_7') = '#skF_6' ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_88,plain,(
    ! [D_37] :
      ( r2_hidden(k4_tarski(D_37,'#skF_8'(D_37)),'#skF_7')
      | ~ r2_hidden(D_37,'#skF_6')
      | k1_relat_1('#skF_7') = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_36])).

tff(c_90,plain,(
    ! [D_65] :
      ( r2_hidden(k4_tarski(D_65,'#skF_8'(D_65)),'#skF_7')
      | ~ r2_hidden(D_65,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_88])).

tff(c_28,plain,(
    ! [D_37,E_40] :
      ( r2_hidden(k4_tarski(D_37,'#skF_8'(D_37)),'#skF_7')
      | ~ r2_hidden(D_37,'#skF_6')
      | ~ r2_hidden(k4_tarski('#skF_9',E_40),'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_43,plain,(
    ! [E_40] : ~ r2_hidden(k4_tarski('#skF_9',E_40),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_94,plain,(
    ~ r2_hidden('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_90,c_43])).

tff(c_103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_94])).

tff(c_104,plain,(
    ! [D_37] :
      ( r2_hidden(k4_tarski(D_37,'#skF_8'(D_37)),'#skF_7')
      | ~ r2_hidden(D_37,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_685,plain,(
    ! [A_135,B_136,D_137] :
      ( r2_hidden(k4_tarski('#skF_1'(A_135,B_136),'#skF_2'(A_135,B_136)),A_135)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_135,B_136),D_137),A_135)
      | k1_relat_1(A_135) = B_136 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_880,plain,(
    ! [B_144] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_7',B_144),'#skF_2'('#skF_7',B_144)),'#skF_7')
      | k1_relat_1('#skF_7') = B_144
      | ~ r2_hidden('#skF_3'('#skF_7',B_144),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_104,c_685])).

tff(c_1835,plain,(
    ! [B_207] :
      ( r2_hidden('#skF_1'('#skF_7',B_207),k1_relat_1('#skF_7'))
      | k1_relat_1('#skF_7') = B_207
      | ~ r2_hidden('#skF_3'('#skF_7',B_207),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_880,c_12])).

tff(c_1389,plain,(
    ! [C_181] :
      ( r2_hidden(C_181,'#skF_6')
      | ~ r2_hidden(C_181,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_1349,c_163])).

tff(c_1858,plain,(
    ! [B_213] :
      ( r2_hidden('#skF_1'('#skF_7',B_213),'#skF_6')
      | k1_relat_1('#skF_7') = B_213
      | ~ r2_hidden('#skF_3'('#skF_7',B_213),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1835,c_1389])).

tff(c_1862,plain,
    ( r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k1_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1433,c_1858])).

tff(c_1871,plain,(
    r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_132,c_1862])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( ~ r2_hidden('#skF_1'(A_9,B_10),B_10)
      | r2_hidden('#skF_3'(A_9,B_10),B_10)
      | k1_relat_1(A_9) = B_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14,plain,(
    ! [A_9,B_10,D_23] :
      ( ~ r2_hidden('#skF_1'(A_9,B_10),B_10)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_9,B_10),D_23),A_9)
      | k1_relat_1(A_9) = B_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1876,plain,(
    ! [D_23] :
      ( ~ r2_hidden(k4_tarski('#skF_3'('#skF_7','#skF_6'),D_23),'#skF_7')
      | k1_relat_1('#skF_7') = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_1871,c_14])).

tff(c_1886,plain,(
    ! [D_214] : ~ r2_hidden(k4_tarski('#skF_3'('#skF_7','#skF_6'),D_214),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_1876])).

tff(c_1906,plain,(
    ~ r2_hidden('#skF_3'('#skF_7','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_104,c_1886])).

tff(c_1913,plain,
    ( ~ r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k1_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_18,c_1906])).

tff(c_1919,plain,(
    k1_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1871,c_1913])).

tff(c_1921,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_1919])).

tff(c_1922,plain,(
    ! [D_37] :
      ( r2_hidden(k4_tarski(D_37,'#skF_8'(D_37)),'#skF_7')
      | ~ r2_hidden(D_37,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_10207,plain,(
    ! [A_651,B_652,D_653] :
      ( r2_hidden(k4_tarski('#skF_1'(A_651,B_652),'#skF_2'(A_651,B_652)),A_651)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_651,B_652),D_653),A_651)
      | k1_relat_1(A_651) = B_652 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10329,plain,(
    ! [B_659] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_7',B_659),'#skF_2'('#skF_7',B_659)),'#skF_7')
      | k1_relat_1('#skF_7') = B_659
      | ~ r2_hidden('#skF_3'('#skF_7',B_659),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1922,c_10207])).

tff(c_10348,plain,(
    ! [B_659] :
      ( r2_hidden('#skF_1'('#skF_7',B_659),k1_relat_1('#skF_7'))
      | k1_relat_1('#skF_7') = B_659
      | ~ r2_hidden('#skF_3'('#skF_7',B_659),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_10329,c_12])).

tff(c_15363,plain,(
    ! [B_910] :
      ( r2_hidden('#skF_1'('#skF_7',B_910),'#skF_6')
      | k1_relat_1('#skF_7') = B_910
      | ~ r2_hidden('#skF_3'('#skF_7',B_910),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_10348,c_14960])).

tff(c_15367,plain,
    ( r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k1_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_15005,c_15363])).

tff(c_15376,plain,(
    r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1948,c_1948,c_15367])).

tff(c_15385,plain,(
    ! [D_23] :
      ( ~ r2_hidden(k4_tarski('#skF_3'('#skF_7','#skF_6'),D_23),'#skF_7')
      | k1_relat_1('#skF_7') = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_15376,c_14])).

tff(c_15400,plain,(
    ! [D_913] : ~ r2_hidden(k4_tarski('#skF_3'('#skF_7','#skF_6'),D_913),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_1948,c_15385])).

tff(c_15420,plain,(
    ~ r2_hidden('#skF_3'('#skF_7','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1922,c_15400])).

tff(c_15427,plain,
    ( ~ r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k1_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_18,c_15420])).

tff(c_15433,plain,(
    k1_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15376,c_15427])).

tff(c_15435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1948,c_15433])).

tff(c_15436,plain,(
    r2_hidden('#skF_9','#skF_6') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_15437,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_15453,plain,(
    ! [A_930,B_931,C_932] :
      ( k1_relset_1(A_930,B_931,C_932) = k1_relat_1(C_932)
      | ~ m1_subset_1(C_932,k1_zfmisc_1(k2_zfmisc_1(A_930,B_931))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_15456,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_15453])).

tff(c_15458,plain,(
    k1_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15437,c_15456])).

tff(c_15514,plain,(
    ! [C_948,A_949] :
      ( r2_hidden(k4_tarski(C_948,'#skF_4'(A_949,k1_relat_1(A_949),C_948)),A_949)
      | ~ r2_hidden(C_948,k1_relat_1(A_949)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,(
    ! [E_40] :
      ( k1_relset_1('#skF_6','#skF_5','#skF_7') != '#skF_6'
      | ~ r2_hidden(k4_tarski('#skF_9',E_40),'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_15451,plain,(
    ! [E_40] : ~ r2_hidden(k4_tarski('#skF_9',E_40),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15437,c_26])).

tff(c_15522,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_15514,c_15451])).

tff(c_15544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15436,c_15458,c_15522])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.22/3.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.22/3.14  
% 9.22/3.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.22/3.14  %$ r2_hidden > m1_subset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_8 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_2 > #skF_1
% 9.22/3.14  
% 9.22/3.14  %Foreground sorts:
% 9.22/3.14  
% 9.22/3.14  
% 9.22/3.14  %Background operators:
% 9.22/3.14  
% 9.22/3.14  
% 9.22/3.14  %Foreground operators:
% 9.22/3.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.22/3.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.22/3.14  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.22/3.14  tff('#skF_8', type, '#skF_8': $i > $i).
% 9.22/3.14  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 9.22/3.14  tff('#skF_7', type, '#skF_7': $i).
% 9.22/3.14  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.22/3.14  tff('#skF_5', type, '#skF_5': $i).
% 9.22/3.14  tff('#skF_6', type, '#skF_6': $i).
% 9.22/3.14  tff('#skF_9', type, '#skF_9': $i).
% 9.22/3.14  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.22/3.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.22/3.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.22/3.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.22/3.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.22/3.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.22/3.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.22/3.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.22/3.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.22/3.14  
% 9.44/3.16  tff(f_63, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 9.44/3.16  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.44/3.16  tff(f_46, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 9.44/3.16  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 9.44/3.16  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 9.44/3.16  tff(c_24, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.44/3.16  tff(c_1943, plain, (![A_221, B_222, C_223]: (k1_relset_1(A_221, B_222, C_223)=k1_relat_1(C_223) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_221, B_222))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.44/3.16  tff(c_1947, plain, (k1_relset_1('#skF_6', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_24, c_1943])).
% 9.44/3.16  tff(c_30, plain, (k1_relset_1('#skF_6', '#skF_5', '#skF_7')!='#skF_6' | r2_hidden('#skF_9', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.44/3.16  tff(c_37, plain, (k1_relset_1('#skF_6', '#skF_5', '#skF_7')!='#skF_6'), inference(splitLeft, [status(thm)], [c_30])).
% 9.44/3.16  tff(c_1948, plain, (k1_relat_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1947, c_37])).
% 9.44/3.16  tff(c_7320, plain, (![A_511, B_512]: (r2_hidden(k4_tarski('#skF_1'(A_511, B_512), '#skF_2'(A_511, B_512)), A_511) | r2_hidden('#skF_3'(A_511, B_512), B_512) | k1_relat_1(A_511)=B_512)), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.44/3.16  tff(c_12, plain, (![C_24, A_9, D_27]: (r2_hidden(C_24, k1_relat_1(A_9)) | ~r2_hidden(k4_tarski(C_24, D_27), A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.44/3.16  tff(c_7363, plain, (![A_511, B_512]: (r2_hidden('#skF_1'(A_511, B_512), k1_relat_1(A_511)) | r2_hidden('#skF_3'(A_511, B_512), B_512) | k1_relat_1(A_511)=B_512)), inference(resolution, [status(thm)], [c_7320, c_12])).
% 9.44/3.16  tff(c_5044, plain, (![C_376, A_377]: (r2_hidden(k4_tarski(C_376, '#skF_4'(A_377, k1_relat_1(A_377), C_376)), A_377) | ~r2_hidden(C_376, k1_relat_1(A_377)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.44/3.16  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.44/3.16  tff(c_14813, plain, (![C_889, A_890, A_891]: (r2_hidden(k4_tarski(C_889, '#skF_4'(A_890, k1_relat_1(A_890), C_889)), A_891) | ~m1_subset_1(A_890, k1_zfmisc_1(A_891)) | ~r2_hidden(C_889, k1_relat_1(A_890)))), inference(resolution, [status(thm)], [c_5044, c_8])).
% 9.44/3.16  tff(c_14906, plain, (![C_892, A_893, A_894]: (r2_hidden(C_892, k1_relat_1(A_893)) | ~m1_subset_1(A_894, k1_zfmisc_1(A_893)) | ~r2_hidden(C_892, k1_relat_1(A_894)))), inference(resolution, [status(thm)], [c_14813, c_12])).
% 9.44/3.16  tff(c_14910, plain, (![C_895]: (r2_hidden(C_895, k1_relat_1(k2_zfmisc_1('#skF_6', '#skF_5'))) | ~r2_hidden(C_895, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_24, c_14906])).
% 9.44/3.16  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.44/3.16  tff(c_5066, plain, (![C_376, C_3, D_4]: (r2_hidden(C_376, C_3) | ~r2_hidden(C_376, k1_relat_1(k2_zfmisc_1(C_3, D_4))))), inference(resolution, [status(thm)], [c_5044, c_6])).
% 9.44/3.16  tff(c_14960, plain, (![C_896]: (r2_hidden(C_896, '#skF_6') | ~r2_hidden(C_896, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_14910, c_5066])).
% 9.44/3.16  tff(c_15005, plain, (![B_512]: (r2_hidden('#skF_1'('#skF_7', B_512), '#skF_6') | r2_hidden('#skF_3'('#skF_7', B_512), B_512) | k1_relat_1('#skF_7')=B_512)), inference(resolution, [status(thm)], [c_7363, c_14960])).
% 9.44/3.16  tff(c_127, plain, (![A_71, B_72, C_73]: (k1_relset_1(A_71, B_72, C_73)=k1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.44/3.16  tff(c_131, plain, (k1_relset_1('#skF_6', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_24, c_127])).
% 9.44/3.16  tff(c_132, plain, (k1_relat_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_37])).
% 9.44/3.16  tff(c_532, plain, (![A_121, B_122]: (r2_hidden(k4_tarski('#skF_1'(A_121, B_122), '#skF_2'(A_121, B_122)), A_121) | r2_hidden('#skF_3'(A_121, B_122), B_122) | k1_relat_1(A_121)=B_122)), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.44/3.16  tff(c_571, plain, (![A_121, B_122]: (r2_hidden('#skF_1'(A_121, B_122), k1_relat_1(A_121)) | r2_hidden('#skF_3'(A_121, B_122), B_122) | k1_relat_1(A_121)=B_122)), inference(resolution, [status(thm)], [c_532, c_12])).
% 9.44/3.16  tff(c_144, plain, (![C_78, A_79]: (r2_hidden(k4_tarski(C_78, '#skF_4'(A_79, k1_relat_1(A_79), C_78)), A_79) | ~r2_hidden(C_78, k1_relat_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.44/3.16  tff(c_1279, plain, (![C_175, A_176, A_177]: (r2_hidden(k4_tarski(C_175, '#skF_4'(A_176, k1_relat_1(A_176), C_175)), A_177) | ~m1_subset_1(A_176, k1_zfmisc_1(A_177)) | ~r2_hidden(C_175, k1_relat_1(A_176)))), inference(resolution, [status(thm)], [c_144, c_8])).
% 9.44/3.16  tff(c_1345, plain, (![C_178, A_179, A_180]: (r2_hidden(C_178, k1_relat_1(A_179)) | ~m1_subset_1(A_180, k1_zfmisc_1(A_179)) | ~r2_hidden(C_178, k1_relat_1(A_180)))), inference(resolution, [status(thm)], [c_1279, c_12])).
% 9.44/3.16  tff(c_1349, plain, (![C_181]: (r2_hidden(C_181, k1_relat_1(k2_zfmisc_1('#skF_6', '#skF_5'))) | ~r2_hidden(C_181, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_24, c_1345])).
% 9.44/3.16  tff(c_163, plain, (![C_78, C_3, D_4]: (r2_hidden(C_78, C_3) | ~r2_hidden(C_78, k1_relat_1(k2_zfmisc_1(C_3, D_4))))), inference(resolution, [status(thm)], [c_144, c_6])).
% 9.44/3.16  tff(c_1392, plain, (![C_182]: (r2_hidden(C_182, '#skF_6') | ~r2_hidden(C_182, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_1349, c_163])).
% 9.44/3.16  tff(c_1433, plain, (![B_122]: (r2_hidden('#skF_1'('#skF_7', B_122), '#skF_6') | r2_hidden('#skF_3'('#skF_7', B_122), B_122) | k1_relat_1('#skF_7')=B_122)), inference(resolution, [status(thm)], [c_571, c_1392])).
% 9.44/3.16  tff(c_32, plain, (![D_37]: (r2_hidden(k4_tarski(D_37, '#skF_8'(D_37)), '#skF_7') | ~r2_hidden(D_37, '#skF_6') | r2_hidden('#skF_9', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.44/3.16  tff(c_42, plain, (r2_hidden('#skF_9', '#skF_6')), inference(splitLeft, [status(thm)], [c_32])).
% 9.44/3.16  tff(c_49, plain, (![A_57, B_58, C_59]: (k1_relset_1(A_57, B_58, C_59)=k1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.44/3.16  tff(c_53, plain, (k1_relset_1('#skF_6', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_24, c_49])).
% 9.44/3.16  tff(c_54, plain, (k1_relat_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_53, c_37])).
% 9.44/3.16  tff(c_36, plain, (![D_37]: (r2_hidden(k4_tarski(D_37, '#skF_8'(D_37)), '#skF_7') | ~r2_hidden(D_37, '#skF_6') | k1_relset_1('#skF_6', '#skF_5', '#skF_7')='#skF_6')), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.44/3.16  tff(c_88, plain, (![D_37]: (r2_hidden(k4_tarski(D_37, '#skF_8'(D_37)), '#skF_7') | ~r2_hidden(D_37, '#skF_6') | k1_relat_1('#skF_7')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_36])).
% 9.44/3.16  tff(c_90, plain, (![D_65]: (r2_hidden(k4_tarski(D_65, '#skF_8'(D_65)), '#skF_7') | ~r2_hidden(D_65, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_54, c_88])).
% 9.44/3.16  tff(c_28, plain, (![D_37, E_40]: (r2_hidden(k4_tarski(D_37, '#skF_8'(D_37)), '#skF_7') | ~r2_hidden(D_37, '#skF_6') | ~r2_hidden(k4_tarski('#skF_9', E_40), '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.44/3.16  tff(c_43, plain, (![E_40]: (~r2_hidden(k4_tarski('#skF_9', E_40), '#skF_7'))), inference(splitLeft, [status(thm)], [c_28])).
% 9.44/3.16  tff(c_94, plain, (~r2_hidden('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_90, c_43])).
% 9.44/3.16  tff(c_103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_94])).
% 9.44/3.16  tff(c_104, plain, (![D_37]: (r2_hidden(k4_tarski(D_37, '#skF_8'(D_37)), '#skF_7') | ~r2_hidden(D_37, '#skF_6'))), inference(splitRight, [status(thm)], [c_28])).
% 9.44/3.16  tff(c_685, plain, (![A_135, B_136, D_137]: (r2_hidden(k4_tarski('#skF_1'(A_135, B_136), '#skF_2'(A_135, B_136)), A_135) | ~r2_hidden(k4_tarski('#skF_3'(A_135, B_136), D_137), A_135) | k1_relat_1(A_135)=B_136)), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.44/3.16  tff(c_880, plain, (![B_144]: (r2_hidden(k4_tarski('#skF_1'('#skF_7', B_144), '#skF_2'('#skF_7', B_144)), '#skF_7') | k1_relat_1('#skF_7')=B_144 | ~r2_hidden('#skF_3'('#skF_7', B_144), '#skF_6'))), inference(resolution, [status(thm)], [c_104, c_685])).
% 9.44/3.16  tff(c_1835, plain, (![B_207]: (r2_hidden('#skF_1'('#skF_7', B_207), k1_relat_1('#skF_7')) | k1_relat_1('#skF_7')=B_207 | ~r2_hidden('#skF_3'('#skF_7', B_207), '#skF_6'))), inference(resolution, [status(thm)], [c_880, c_12])).
% 9.44/3.16  tff(c_1389, plain, (![C_181]: (r2_hidden(C_181, '#skF_6') | ~r2_hidden(C_181, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_1349, c_163])).
% 9.44/3.16  tff(c_1858, plain, (![B_213]: (r2_hidden('#skF_1'('#skF_7', B_213), '#skF_6') | k1_relat_1('#skF_7')=B_213 | ~r2_hidden('#skF_3'('#skF_7', B_213), '#skF_6'))), inference(resolution, [status(thm)], [c_1835, c_1389])).
% 9.44/3.16  tff(c_1862, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6') | k1_relat_1('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_1433, c_1858])).
% 9.44/3.16  tff(c_1871, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_132, c_132, c_1862])).
% 9.44/3.16  tff(c_18, plain, (![A_9, B_10]: (~r2_hidden('#skF_1'(A_9, B_10), B_10) | r2_hidden('#skF_3'(A_9, B_10), B_10) | k1_relat_1(A_9)=B_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.44/3.16  tff(c_14, plain, (![A_9, B_10, D_23]: (~r2_hidden('#skF_1'(A_9, B_10), B_10) | ~r2_hidden(k4_tarski('#skF_3'(A_9, B_10), D_23), A_9) | k1_relat_1(A_9)=B_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.44/3.16  tff(c_1876, plain, (![D_23]: (~r2_hidden(k4_tarski('#skF_3'('#skF_7', '#skF_6'), D_23), '#skF_7') | k1_relat_1('#skF_7')='#skF_6')), inference(resolution, [status(thm)], [c_1871, c_14])).
% 9.44/3.16  tff(c_1886, plain, (![D_214]: (~r2_hidden(k4_tarski('#skF_3'('#skF_7', '#skF_6'), D_214), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_132, c_1876])).
% 9.44/3.16  tff(c_1906, plain, (~r2_hidden('#skF_3'('#skF_7', '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_104, c_1886])).
% 9.44/3.16  tff(c_1913, plain, (~r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6') | k1_relat_1('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_18, c_1906])).
% 9.44/3.16  tff(c_1919, plain, (k1_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1871, c_1913])).
% 9.44/3.16  tff(c_1921, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_1919])).
% 9.44/3.16  tff(c_1922, plain, (![D_37]: (r2_hidden(k4_tarski(D_37, '#skF_8'(D_37)), '#skF_7') | ~r2_hidden(D_37, '#skF_6'))), inference(splitRight, [status(thm)], [c_32])).
% 9.44/3.16  tff(c_10207, plain, (![A_651, B_652, D_653]: (r2_hidden(k4_tarski('#skF_1'(A_651, B_652), '#skF_2'(A_651, B_652)), A_651) | ~r2_hidden(k4_tarski('#skF_3'(A_651, B_652), D_653), A_651) | k1_relat_1(A_651)=B_652)), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.44/3.16  tff(c_10329, plain, (![B_659]: (r2_hidden(k4_tarski('#skF_1'('#skF_7', B_659), '#skF_2'('#skF_7', B_659)), '#skF_7') | k1_relat_1('#skF_7')=B_659 | ~r2_hidden('#skF_3'('#skF_7', B_659), '#skF_6'))), inference(resolution, [status(thm)], [c_1922, c_10207])).
% 9.44/3.16  tff(c_10348, plain, (![B_659]: (r2_hidden('#skF_1'('#skF_7', B_659), k1_relat_1('#skF_7')) | k1_relat_1('#skF_7')=B_659 | ~r2_hidden('#skF_3'('#skF_7', B_659), '#skF_6'))), inference(resolution, [status(thm)], [c_10329, c_12])).
% 9.44/3.16  tff(c_15363, plain, (![B_910]: (r2_hidden('#skF_1'('#skF_7', B_910), '#skF_6') | k1_relat_1('#skF_7')=B_910 | ~r2_hidden('#skF_3'('#skF_7', B_910), '#skF_6'))), inference(resolution, [status(thm)], [c_10348, c_14960])).
% 9.44/3.16  tff(c_15367, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6') | k1_relat_1('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_15005, c_15363])).
% 9.44/3.16  tff(c_15376, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_1948, c_1948, c_15367])).
% 9.44/3.16  tff(c_15385, plain, (![D_23]: (~r2_hidden(k4_tarski('#skF_3'('#skF_7', '#skF_6'), D_23), '#skF_7') | k1_relat_1('#skF_7')='#skF_6')), inference(resolution, [status(thm)], [c_15376, c_14])).
% 9.44/3.16  tff(c_15400, plain, (![D_913]: (~r2_hidden(k4_tarski('#skF_3'('#skF_7', '#skF_6'), D_913), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_1948, c_15385])).
% 9.44/3.16  tff(c_15420, plain, (~r2_hidden('#skF_3'('#skF_7', '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_1922, c_15400])).
% 9.44/3.16  tff(c_15427, plain, (~r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6') | k1_relat_1('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_18, c_15420])).
% 9.44/3.16  tff(c_15433, plain, (k1_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_15376, c_15427])).
% 9.44/3.16  tff(c_15435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1948, c_15433])).
% 9.44/3.16  tff(c_15436, plain, (r2_hidden('#skF_9', '#skF_6')), inference(splitRight, [status(thm)], [c_30])).
% 9.44/3.16  tff(c_15437, plain, (k1_relset_1('#skF_6', '#skF_5', '#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_30])).
% 9.44/3.16  tff(c_15453, plain, (![A_930, B_931, C_932]: (k1_relset_1(A_930, B_931, C_932)=k1_relat_1(C_932) | ~m1_subset_1(C_932, k1_zfmisc_1(k2_zfmisc_1(A_930, B_931))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.44/3.16  tff(c_15456, plain, (k1_relset_1('#skF_6', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_24, c_15453])).
% 9.44/3.16  tff(c_15458, plain, (k1_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_15437, c_15456])).
% 9.44/3.16  tff(c_15514, plain, (![C_948, A_949]: (r2_hidden(k4_tarski(C_948, '#skF_4'(A_949, k1_relat_1(A_949), C_948)), A_949) | ~r2_hidden(C_948, k1_relat_1(A_949)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.44/3.16  tff(c_26, plain, (![E_40]: (k1_relset_1('#skF_6', '#skF_5', '#skF_7')!='#skF_6' | ~r2_hidden(k4_tarski('#skF_9', E_40), '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.44/3.16  tff(c_15451, plain, (![E_40]: (~r2_hidden(k4_tarski('#skF_9', E_40), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_15437, c_26])).
% 9.44/3.16  tff(c_15522, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_15514, c_15451])).
% 9.44/3.16  tff(c_15544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15436, c_15458, c_15522])).
% 9.44/3.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.44/3.16  
% 9.44/3.16  Inference rules
% 9.44/3.16  ----------------------
% 9.44/3.16  #Ref     : 0
% 9.44/3.16  #Sup     : 3713
% 9.44/3.16  #Fact    : 2
% 9.44/3.16  #Define  : 0
% 9.44/3.16  #Split   : 15
% 9.44/3.16  #Chain   : 0
% 9.44/3.16  #Close   : 0
% 9.44/3.16  
% 9.44/3.16  Ordering : KBO
% 9.44/3.16  
% 9.44/3.16  Simplification rules
% 9.44/3.16  ----------------------
% 9.44/3.16  #Subsume      : 1098
% 9.44/3.16  #Demod        : 1208
% 9.44/3.16  #Tautology    : 496
% 9.44/3.16  #SimpNegUnit  : 188
% 9.44/3.16  #BackRed      : 44
% 9.44/3.16  
% 9.44/3.16  #Partial instantiations: 0
% 9.44/3.16  #Strategies tried      : 1
% 9.44/3.16  
% 9.44/3.16  Timing (in seconds)
% 9.44/3.16  ----------------------
% 9.44/3.17  Preprocessing        : 0.29
% 9.44/3.17  Parsing              : 0.14
% 9.44/3.17  CNF conversion       : 0.02
% 9.44/3.17  Main loop            : 2.08
% 9.44/3.17  Inferencing          : 0.65
% 9.44/3.17  Reduction            : 0.53
% 9.44/3.17  Demodulation         : 0.33
% 9.44/3.17  BG Simplification    : 0.08
% 9.44/3.17  Subsumption          : 0.60
% 9.44/3.17  Abstraction          : 0.13
% 9.44/3.17  MUC search           : 0.00
% 9.44/3.17  Cooper               : 0.00
% 9.44/3.17  Total                : 2.40
% 9.44/3.17  Index Insertion      : 0.00
% 9.44/3.17  Index Deletion       : 0.00
% 9.44/3.17  Index Matching       : 0.00
% 9.44/3.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
