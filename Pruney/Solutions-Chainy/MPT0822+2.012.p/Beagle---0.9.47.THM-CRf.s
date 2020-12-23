%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:12 EST 2020

% Result     : Theorem 10.51s
% Output     : CNFRefutation 10.51s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 409 expanded)
%              Number of leaves         :   24 ( 144 expanded)
%              Depth                    :   14
%              Number of atoms          :  171 ( 918 expanded)
%              Number of equality atoms :   45 ( 229 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_8 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
        <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

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
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3640,plain,(
    ! [A_273,B_274,C_275] :
      ( k2_relset_1(A_273,B_274,C_275) = k2_relat_1(C_275)
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(A_273,B_274))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3644,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_3640])).

tff(c_30,plain,
    ( k2_relset_1('#skF_5','#skF_6','#skF_7') != '#skF_6'
    | r2_hidden('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_37,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_3645,plain,(
    k2_relat_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3644,c_37])).

tff(c_9822,plain,(
    ! [A_587,B_588] :
      ( r2_hidden(k4_tarski('#skF_2'(A_587,B_588),'#skF_1'(A_587,B_588)),A_587)
      | r2_hidden('#skF_3'(A_587,B_588),B_588)
      | k2_relat_1(A_587) = B_588 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12,plain,(
    ! [C_24,A_9,D_27] :
      ( r2_hidden(C_24,k2_relat_1(A_9))
      | ~ r2_hidden(k4_tarski(D_27,C_24),A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_9861,plain,(
    ! [A_587,B_588] :
      ( r2_hidden('#skF_1'(A_587,B_588),k2_relat_1(A_587))
      | r2_hidden('#skF_3'(A_587,B_588),B_588)
      | k2_relat_1(A_587) = B_588 ) ),
    inference(resolution,[status(thm)],[c_9822,c_12])).

tff(c_3652,plain,(
    ! [A_280,C_281] :
      ( r2_hidden(k4_tarski('#skF_4'(A_280,k2_relat_1(A_280),C_281),C_281),A_280)
      | ~ r2_hidden(C_281,k2_relat_1(A_280)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20675,plain,(
    ! [A_1146,C_1147,A_1148] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1146,k2_relat_1(A_1146),C_1147),C_1147),A_1148)
      | ~ m1_subset_1(A_1146,k1_zfmisc_1(A_1148))
      | ~ r2_hidden(C_1147,k2_relat_1(A_1146)) ) ),
    inference(resolution,[status(thm)],[c_3652,c_8])).

tff(c_20781,plain,(
    ! [C_1149,A_1150,A_1151] :
      ( r2_hidden(C_1149,k2_relat_1(A_1150))
      | ~ m1_subset_1(A_1151,k1_zfmisc_1(A_1150))
      | ~ r2_hidden(C_1149,k2_relat_1(A_1151)) ) ),
    inference(resolution,[status(thm)],[c_20675,c_12])).

tff(c_20785,plain,(
    ! [C_1152] :
      ( r2_hidden(C_1152,k2_relat_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ r2_hidden(C_1152,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_24,c_20781])).

tff(c_4,plain,(
    ! [B_2,D_4,A_1,C_3] :
      ( r2_hidden(B_2,D_4)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3672,plain,(
    ! [C_281,D_4,C_3] :
      ( r2_hidden(C_281,D_4)
      | ~ r2_hidden(C_281,k2_relat_1(k2_zfmisc_1(C_3,D_4))) ) ),
    inference(resolution,[status(thm)],[c_3652,c_4])).

tff(c_20850,plain,(
    ! [C_1153] :
      ( r2_hidden(C_1153,'#skF_6')
      | ~ r2_hidden(C_1153,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_20785,c_3672])).

tff(c_20900,plain,(
    ! [B_588] :
      ( r2_hidden('#skF_1'('#skF_7',B_588),'#skF_6')
      | r2_hidden('#skF_3'('#skF_7',B_588),B_588)
      | k2_relat_1('#skF_7') = B_588 ) ),
    inference(resolution,[status(thm)],[c_9861,c_20850])).

tff(c_127,plain,(
    ! [A_71,B_72,C_73] :
      ( k2_relset_1(A_71,B_72,C_73) = k2_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_131,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_127])).

tff(c_132,plain,(
    k2_relat_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_37])).

tff(c_532,plain,(
    ! [A_121,B_122] :
      ( r2_hidden(k4_tarski('#skF_2'(A_121,B_122),'#skF_1'(A_121,B_122)),A_121)
      | r2_hidden('#skF_3'(A_121,B_122),B_122)
      | k2_relat_1(A_121) = B_122 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_571,plain,(
    ! [A_121,B_122] :
      ( r2_hidden('#skF_1'(A_121,B_122),k2_relat_1(A_121))
      | r2_hidden('#skF_3'(A_121,B_122),B_122)
      | k2_relat_1(A_121) = B_122 ) ),
    inference(resolution,[status(thm)],[c_532,c_12])).

tff(c_144,plain,(
    ! [A_78,C_79] :
      ( r2_hidden(k4_tarski('#skF_4'(A_78,k2_relat_1(A_78),C_79),C_79),A_78)
      | ~ r2_hidden(C_79,k2_relat_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2933,plain,(
    ! [A_247,C_248,A_249] :
      ( r2_hidden(k4_tarski('#skF_4'(A_247,k2_relat_1(A_247),C_248),C_248),A_249)
      | ~ m1_subset_1(A_247,k1_zfmisc_1(A_249))
      | ~ r2_hidden(C_248,k2_relat_1(A_247)) ) ),
    inference(resolution,[status(thm)],[c_144,c_8])).

tff(c_3036,plain,(
    ! [C_250,A_251,A_252] :
      ( r2_hidden(C_250,k2_relat_1(A_251))
      | ~ m1_subset_1(A_252,k1_zfmisc_1(A_251))
      | ~ r2_hidden(C_250,k2_relat_1(A_252)) ) ),
    inference(resolution,[status(thm)],[c_2933,c_12])).

tff(c_3040,plain,(
    ! [C_253] :
      ( r2_hidden(C_253,k2_relat_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ r2_hidden(C_253,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_24,c_3036])).

tff(c_164,plain,(
    ! [C_79,D_4,C_3] :
      ( r2_hidden(C_79,D_4)
      | ~ r2_hidden(C_79,k2_relat_1(k2_zfmisc_1(C_3,D_4))) ) ),
    inference(resolution,[status(thm)],[c_144,c_4])).

tff(c_3101,plain,(
    ! [C_254] :
      ( r2_hidden(C_254,'#skF_6')
      | ~ r2_hidden(C_254,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_3040,c_164])).

tff(c_3151,plain,(
    ! [B_122] :
      ( r2_hidden('#skF_1'('#skF_7',B_122),'#skF_6')
      | r2_hidden('#skF_3'('#skF_7',B_122),B_122)
      | k2_relat_1('#skF_7') = B_122 ) ),
    inference(resolution,[status(thm)],[c_571,c_3101])).

tff(c_32,plain,(
    ! [D_37] :
      ( r2_hidden(k4_tarski('#skF_8'(D_37),D_37),'#skF_7')
      | ~ r2_hidden(D_37,'#skF_6')
      | r2_hidden('#skF_9','#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,(
    r2_hidden('#skF_9','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_49,plain,(
    ! [A_57,B_58,C_59] :
      ( k2_relset_1(A_57,B_58,C_59) = k2_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_53,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_49])).

tff(c_54,plain,(
    k2_relat_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_37])).

tff(c_36,plain,(
    ! [D_37] :
      ( r2_hidden(k4_tarski('#skF_8'(D_37),D_37),'#skF_7')
      | ~ r2_hidden(D_37,'#skF_6')
      | k2_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_6' ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_88,plain,(
    ! [D_37] :
      ( r2_hidden(k4_tarski('#skF_8'(D_37),D_37),'#skF_7')
      | ~ r2_hidden(D_37,'#skF_6')
      | k2_relat_1('#skF_7') = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_36])).

tff(c_90,plain,(
    ! [D_65] :
      ( r2_hidden(k4_tarski('#skF_8'(D_65),D_65),'#skF_7')
      | ~ r2_hidden(D_65,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_88])).

tff(c_28,plain,(
    ! [D_37,E_40] :
      ( r2_hidden(k4_tarski('#skF_8'(D_37),D_37),'#skF_7')
      | ~ r2_hidden(D_37,'#skF_6')
      | ~ r2_hidden(k4_tarski(E_40,'#skF_9'),'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_43,plain,(
    ! [E_40] : ~ r2_hidden(k4_tarski(E_40,'#skF_9'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_94,plain,(
    ~ r2_hidden('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_90,c_43])).

tff(c_103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_94])).

tff(c_104,plain,(
    ! [D_37] :
      ( r2_hidden(k4_tarski('#skF_8'(D_37),D_37),'#skF_7')
      | ~ r2_hidden(D_37,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_685,plain,(
    ! [A_135,B_136,D_137] :
      ( r2_hidden(k4_tarski('#skF_2'(A_135,B_136),'#skF_1'(A_135,B_136)),A_135)
      | ~ r2_hidden(k4_tarski(D_137,'#skF_3'(A_135,B_136)),A_135)
      | k2_relat_1(A_135) = B_136 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_880,plain,(
    ! [B_144] :
      ( r2_hidden(k4_tarski('#skF_2'('#skF_7',B_144),'#skF_1'('#skF_7',B_144)),'#skF_7')
      | k2_relat_1('#skF_7') = B_144
      | ~ r2_hidden('#skF_3'('#skF_7',B_144),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_104,c_685])).

tff(c_899,plain,(
    ! [B_144] :
      ( r2_hidden('#skF_1'('#skF_7',B_144),k2_relat_1('#skF_7'))
      | k2_relat_1('#skF_7') = B_144
      | ~ r2_hidden('#skF_3'('#skF_7',B_144),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_880,c_12])).

tff(c_3545,plain,(
    ! [B_267] :
      ( r2_hidden('#skF_1'('#skF_7',B_267),'#skF_6')
      | k2_relat_1('#skF_7') = B_267
      | ~ r2_hidden('#skF_3'('#skF_7',B_267),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_899,c_3101])).

tff(c_3549,plain,
    ( r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k2_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3151,c_3545])).

tff(c_3558,plain,(
    r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_132,c_3549])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( ~ r2_hidden('#skF_1'(A_9,B_10),B_10)
      | r2_hidden('#skF_3'(A_9,B_10),B_10)
      | k2_relat_1(A_9) = B_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14,plain,(
    ! [A_9,B_10,D_23] :
      ( ~ r2_hidden('#skF_1'(A_9,B_10),B_10)
      | ~ r2_hidden(k4_tarski(D_23,'#skF_3'(A_9,B_10)),A_9)
      | k2_relat_1(A_9) = B_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3569,plain,(
    ! [D_23] :
      ( ~ r2_hidden(k4_tarski(D_23,'#skF_3'('#skF_7','#skF_6')),'#skF_7')
      | k2_relat_1('#skF_7') = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_3558,c_14])).

tff(c_3585,plain,(
    ! [D_270] : ~ r2_hidden(k4_tarski(D_270,'#skF_3'('#skF_7','#skF_6')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_3569])).

tff(c_3605,plain,(
    ~ r2_hidden('#skF_3'('#skF_7','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_104,c_3585])).

tff(c_3612,plain,
    ( ~ r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k2_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_18,c_3605])).

tff(c_3618,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3558,c_3612])).

tff(c_3620,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_3618])).

tff(c_3621,plain,(
    ! [D_37] :
      ( r2_hidden(k4_tarski('#skF_8'(D_37),D_37),'#skF_7')
      | ~ r2_hidden(D_37,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_11039,plain,(
    ! [A_677,B_678,D_679] :
      ( r2_hidden(k4_tarski('#skF_2'(A_677,B_678),'#skF_1'(A_677,B_678)),A_677)
      | ~ r2_hidden(k4_tarski(D_679,'#skF_3'(A_677,B_678)),A_677)
      | k2_relat_1(A_677) = B_678 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_11157,plain,(
    ! [B_686] :
      ( r2_hidden(k4_tarski('#skF_2'('#skF_7',B_686),'#skF_1'('#skF_7',B_686)),'#skF_7')
      | k2_relat_1('#skF_7') = B_686
      | ~ r2_hidden('#skF_3'('#skF_7',B_686),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_3621,c_11039])).

tff(c_11176,plain,(
    ! [B_686] :
      ( r2_hidden('#skF_1'('#skF_7',B_686),k2_relat_1('#skF_7'))
      | k2_relat_1('#skF_7') = B_686
      | ~ r2_hidden('#skF_3'('#skF_7',B_686),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_11157,c_12])).

tff(c_21362,plain,(
    ! [B_1167] :
      ( r2_hidden('#skF_1'('#skF_7',B_1167),'#skF_6')
      | k2_relat_1('#skF_7') = B_1167
      | ~ r2_hidden('#skF_3'('#skF_7',B_1167),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_11176,c_20850])).

tff(c_21366,plain,
    ( r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k2_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_20900,c_21362])).

tff(c_21375,plain,(
    r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_3645,c_3645,c_21366])).

tff(c_21387,plain,(
    ! [D_23] :
      ( ~ r2_hidden(k4_tarski(D_23,'#skF_3'('#skF_7','#skF_6')),'#skF_7')
      | k2_relat_1('#skF_7') = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_21375,c_14])).

tff(c_21402,plain,(
    ! [D_1170] : ~ r2_hidden(k4_tarski(D_1170,'#skF_3'('#skF_7','#skF_6')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_3645,c_21387])).

tff(c_21422,plain,(
    ~ r2_hidden('#skF_3'('#skF_7','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_3621,c_21402])).

tff(c_21429,plain,
    ( ~ r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k2_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_18,c_21422])).

tff(c_21435,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21375,c_21429])).

tff(c_21437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3645,c_21435])).

tff(c_21438,plain,(
    r2_hidden('#skF_9','#skF_6') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_21439,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_21455,plain,(
    ! [A_1187,B_1188,C_1189] :
      ( k2_relset_1(A_1187,B_1188,C_1189) = k2_relat_1(C_1189)
      | ~ m1_subset_1(C_1189,k1_zfmisc_1(k2_zfmisc_1(A_1187,B_1188))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_21458,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_21455])).

tff(c_21460,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21439,c_21458])).

tff(c_21517,plain,(
    ! [A_1205,C_1206] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1205,k2_relat_1(A_1205),C_1206),C_1206),A_1205)
      | ~ r2_hidden(C_1206,k2_relat_1(A_1205)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,(
    ! [E_40] :
      ( k2_relset_1('#skF_5','#skF_6','#skF_7') != '#skF_6'
      | ~ r2_hidden(k4_tarski(E_40,'#skF_9'),'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_21452,plain,(
    ! [E_40] : ~ r2_hidden(k4_tarski(E_40,'#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21439,c_26])).

tff(c_21529,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_21517,c_21452])).

tff(c_21548,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21438,c_21460,c_21529])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:30:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.51/3.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.51/3.79  
% 10.51/3.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.51/3.79  %$ r2_hidden > m1_subset_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_8 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_2 > #skF_1
% 10.51/3.79  
% 10.51/3.79  %Foreground sorts:
% 10.51/3.79  
% 10.51/3.79  
% 10.51/3.79  %Background operators:
% 10.51/3.79  
% 10.51/3.79  
% 10.51/3.79  %Foreground operators:
% 10.51/3.79  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.51/3.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.51/3.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.51/3.79  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.51/3.79  tff('#skF_8', type, '#skF_8': $i > $i).
% 10.51/3.79  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 10.51/3.79  tff('#skF_7', type, '#skF_7': $i).
% 10.51/3.79  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.51/3.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.51/3.79  tff('#skF_5', type, '#skF_5': $i).
% 10.51/3.79  tff('#skF_6', type, '#skF_6': $i).
% 10.51/3.79  tff('#skF_9', type, '#skF_9': $i).
% 10.51/3.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.51/3.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.51/3.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.51/3.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.51/3.79  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.51/3.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.51/3.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.51/3.79  
% 10.51/3.81  tff(f_63, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_relset_1)).
% 10.51/3.81  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.51/3.81  tff(f_46, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 10.51/3.81  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 10.51/3.81  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 10.51/3.81  tff(c_24, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.51/3.81  tff(c_3640, plain, (![A_273, B_274, C_275]: (k2_relset_1(A_273, B_274, C_275)=k2_relat_1(C_275) | ~m1_subset_1(C_275, k1_zfmisc_1(k2_zfmisc_1(A_273, B_274))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.51/3.81  tff(c_3644, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_24, c_3640])).
% 10.51/3.81  tff(c_30, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')!='#skF_6' | r2_hidden('#skF_9', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.51/3.81  tff(c_37, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')!='#skF_6'), inference(splitLeft, [status(thm)], [c_30])).
% 10.51/3.81  tff(c_3645, plain, (k2_relat_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3644, c_37])).
% 10.51/3.81  tff(c_9822, plain, (![A_587, B_588]: (r2_hidden(k4_tarski('#skF_2'(A_587, B_588), '#skF_1'(A_587, B_588)), A_587) | r2_hidden('#skF_3'(A_587, B_588), B_588) | k2_relat_1(A_587)=B_588)), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.51/3.81  tff(c_12, plain, (![C_24, A_9, D_27]: (r2_hidden(C_24, k2_relat_1(A_9)) | ~r2_hidden(k4_tarski(D_27, C_24), A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.51/3.81  tff(c_9861, plain, (![A_587, B_588]: (r2_hidden('#skF_1'(A_587, B_588), k2_relat_1(A_587)) | r2_hidden('#skF_3'(A_587, B_588), B_588) | k2_relat_1(A_587)=B_588)), inference(resolution, [status(thm)], [c_9822, c_12])).
% 10.51/3.81  tff(c_3652, plain, (![A_280, C_281]: (r2_hidden(k4_tarski('#skF_4'(A_280, k2_relat_1(A_280), C_281), C_281), A_280) | ~r2_hidden(C_281, k2_relat_1(A_280)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.51/3.81  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.51/3.81  tff(c_20675, plain, (![A_1146, C_1147, A_1148]: (r2_hidden(k4_tarski('#skF_4'(A_1146, k2_relat_1(A_1146), C_1147), C_1147), A_1148) | ~m1_subset_1(A_1146, k1_zfmisc_1(A_1148)) | ~r2_hidden(C_1147, k2_relat_1(A_1146)))), inference(resolution, [status(thm)], [c_3652, c_8])).
% 10.51/3.81  tff(c_20781, plain, (![C_1149, A_1150, A_1151]: (r2_hidden(C_1149, k2_relat_1(A_1150)) | ~m1_subset_1(A_1151, k1_zfmisc_1(A_1150)) | ~r2_hidden(C_1149, k2_relat_1(A_1151)))), inference(resolution, [status(thm)], [c_20675, c_12])).
% 10.51/3.81  tff(c_20785, plain, (![C_1152]: (r2_hidden(C_1152, k2_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~r2_hidden(C_1152, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_24, c_20781])).
% 10.51/3.81  tff(c_4, plain, (![B_2, D_4, A_1, C_3]: (r2_hidden(B_2, D_4) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.51/3.81  tff(c_3672, plain, (![C_281, D_4, C_3]: (r2_hidden(C_281, D_4) | ~r2_hidden(C_281, k2_relat_1(k2_zfmisc_1(C_3, D_4))))), inference(resolution, [status(thm)], [c_3652, c_4])).
% 10.51/3.81  tff(c_20850, plain, (![C_1153]: (r2_hidden(C_1153, '#skF_6') | ~r2_hidden(C_1153, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_20785, c_3672])).
% 10.51/3.81  tff(c_20900, plain, (![B_588]: (r2_hidden('#skF_1'('#skF_7', B_588), '#skF_6') | r2_hidden('#skF_3'('#skF_7', B_588), B_588) | k2_relat_1('#skF_7')=B_588)), inference(resolution, [status(thm)], [c_9861, c_20850])).
% 10.51/3.81  tff(c_127, plain, (![A_71, B_72, C_73]: (k2_relset_1(A_71, B_72, C_73)=k2_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.51/3.81  tff(c_131, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_24, c_127])).
% 10.51/3.81  tff(c_132, plain, (k2_relat_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_37])).
% 10.51/3.81  tff(c_532, plain, (![A_121, B_122]: (r2_hidden(k4_tarski('#skF_2'(A_121, B_122), '#skF_1'(A_121, B_122)), A_121) | r2_hidden('#skF_3'(A_121, B_122), B_122) | k2_relat_1(A_121)=B_122)), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.51/3.81  tff(c_571, plain, (![A_121, B_122]: (r2_hidden('#skF_1'(A_121, B_122), k2_relat_1(A_121)) | r2_hidden('#skF_3'(A_121, B_122), B_122) | k2_relat_1(A_121)=B_122)), inference(resolution, [status(thm)], [c_532, c_12])).
% 10.51/3.81  tff(c_144, plain, (![A_78, C_79]: (r2_hidden(k4_tarski('#skF_4'(A_78, k2_relat_1(A_78), C_79), C_79), A_78) | ~r2_hidden(C_79, k2_relat_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.51/3.81  tff(c_2933, plain, (![A_247, C_248, A_249]: (r2_hidden(k4_tarski('#skF_4'(A_247, k2_relat_1(A_247), C_248), C_248), A_249) | ~m1_subset_1(A_247, k1_zfmisc_1(A_249)) | ~r2_hidden(C_248, k2_relat_1(A_247)))), inference(resolution, [status(thm)], [c_144, c_8])).
% 10.51/3.81  tff(c_3036, plain, (![C_250, A_251, A_252]: (r2_hidden(C_250, k2_relat_1(A_251)) | ~m1_subset_1(A_252, k1_zfmisc_1(A_251)) | ~r2_hidden(C_250, k2_relat_1(A_252)))), inference(resolution, [status(thm)], [c_2933, c_12])).
% 10.51/3.81  tff(c_3040, plain, (![C_253]: (r2_hidden(C_253, k2_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~r2_hidden(C_253, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_24, c_3036])).
% 10.51/3.81  tff(c_164, plain, (![C_79, D_4, C_3]: (r2_hidden(C_79, D_4) | ~r2_hidden(C_79, k2_relat_1(k2_zfmisc_1(C_3, D_4))))), inference(resolution, [status(thm)], [c_144, c_4])).
% 10.51/3.81  tff(c_3101, plain, (![C_254]: (r2_hidden(C_254, '#skF_6') | ~r2_hidden(C_254, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_3040, c_164])).
% 10.51/3.81  tff(c_3151, plain, (![B_122]: (r2_hidden('#skF_1'('#skF_7', B_122), '#skF_6') | r2_hidden('#skF_3'('#skF_7', B_122), B_122) | k2_relat_1('#skF_7')=B_122)), inference(resolution, [status(thm)], [c_571, c_3101])).
% 10.51/3.81  tff(c_32, plain, (![D_37]: (r2_hidden(k4_tarski('#skF_8'(D_37), D_37), '#skF_7') | ~r2_hidden(D_37, '#skF_6') | r2_hidden('#skF_9', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.51/3.81  tff(c_42, plain, (r2_hidden('#skF_9', '#skF_6')), inference(splitLeft, [status(thm)], [c_32])).
% 10.51/3.81  tff(c_49, plain, (![A_57, B_58, C_59]: (k2_relset_1(A_57, B_58, C_59)=k2_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.51/3.81  tff(c_53, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_24, c_49])).
% 10.51/3.81  tff(c_54, plain, (k2_relat_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_53, c_37])).
% 10.51/3.81  tff(c_36, plain, (![D_37]: (r2_hidden(k4_tarski('#skF_8'(D_37), D_37), '#skF_7') | ~r2_hidden(D_37, '#skF_6') | k2_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_6')), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.51/3.81  tff(c_88, plain, (![D_37]: (r2_hidden(k4_tarski('#skF_8'(D_37), D_37), '#skF_7') | ~r2_hidden(D_37, '#skF_6') | k2_relat_1('#skF_7')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_36])).
% 10.51/3.81  tff(c_90, plain, (![D_65]: (r2_hidden(k4_tarski('#skF_8'(D_65), D_65), '#skF_7') | ~r2_hidden(D_65, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_54, c_88])).
% 10.51/3.81  tff(c_28, plain, (![D_37, E_40]: (r2_hidden(k4_tarski('#skF_8'(D_37), D_37), '#skF_7') | ~r2_hidden(D_37, '#skF_6') | ~r2_hidden(k4_tarski(E_40, '#skF_9'), '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.51/3.81  tff(c_43, plain, (![E_40]: (~r2_hidden(k4_tarski(E_40, '#skF_9'), '#skF_7'))), inference(splitLeft, [status(thm)], [c_28])).
% 10.51/3.81  tff(c_94, plain, (~r2_hidden('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_90, c_43])).
% 10.51/3.81  tff(c_103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_94])).
% 10.51/3.81  tff(c_104, plain, (![D_37]: (r2_hidden(k4_tarski('#skF_8'(D_37), D_37), '#skF_7') | ~r2_hidden(D_37, '#skF_6'))), inference(splitRight, [status(thm)], [c_28])).
% 10.51/3.81  tff(c_685, plain, (![A_135, B_136, D_137]: (r2_hidden(k4_tarski('#skF_2'(A_135, B_136), '#skF_1'(A_135, B_136)), A_135) | ~r2_hidden(k4_tarski(D_137, '#skF_3'(A_135, B_136)), A_135) | k2_relat_1(A_135)=B_136)), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.51/3.81  tff(c_880, plain, (![B_144]: (r2_hidden(k4_tarski('#skF_2'('#skF_7', B_144), '#skF_1'('#skF_7', B_144)), '#skF_7') | k2_relat_1('#skF_7')=B_144 | ~r2_hidden('#skF_3'('#skF_7', B_144), '#skF_6'))), inference(resolution, [status(thm)], [c_104, c_685])).
% 10.51/3.81  tff(c_899, plain, (![B_144]: (r2_hidden('#skF_1'('#skF_7', B_144), k2_relat_1('#skF_7')) | k2_relat_1('#skF_7')=B_144 | ~r2_hidden('#skF_3'('#skF_7', B_144), '#skF_6'))), inference(resolution, [status(thm)], [c_880, c_12])).
% 10.51/3.81  tff(c_3545, plain, (![B_267]: (r2_hidden('#skF_1'('#skF_7', B_267), '#skF_6') | k2_relat_1('#skF_7')=B_267 | ~r2_hidden('#skF_3'('#skF_7', B_267), '#skF_6'))), inference(resolution, [status(thm)], [c_899, c_3101])).
% 10.51/3.81  tff(c_3549, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6') | k2_relat_1('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_3151, c_3545])).
% 10.51/3.81  tff(c_3558, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_132, c_132, c_3549])).
% 10.51/3.81  tff(c_18, plain, (![A_9, B_10]: (~r2_hidden('#skF_1'(A_9, B_10), B_10) | r2_hidden('#skF_3'(A_9, B_10), B_10) | k2_relat_1(A_9)=B_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.51/3.81  tff(c_14, plain, (![A_9, B_10, D_23]: (~r2_hidden('#skF_1'(A_9, B_10), B_10) | ~r2_hidden(k4_tarski(D_23, '#skF_3'(A_9, B_10)), A_9) | k2_relat_1(A_9)=B_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.51/3.81  tff(c_3569, plain, (![D_23]: (~r2_hidden(k4_tarski(D_23, '#skF_3'('#skF_7', '#skF_6')), '#skF_7') | k2_relat_1('#skF_7')='#skF_6')), inference(resolution, [status(thm)], [c_3558, c_14])).
% 10.51/3.81  tff(c_3585, plain, (![D_270]: (~r2_hidden(k4_tarski(D_270, '#skF_3'('#skF_7', '#skF_6')), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_132, c_3569])).
% 10.51/3.81  tff(c_3605, plain, (~r2_hidden('#skF_3'('#skF_7', '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_104, c_3585])).
% 10.51/3.81  tff(c_3612, plain, (~r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6') | k2_relat_1('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_18, c_3605])).
% 10.51/3.81  tff(c_3618, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3558, c_3612])).
% 10.51/3.81  tff(c_3620, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_3618])).
% 10.51/3.81  tff(c_3621, plain, (![D_37]: (r2_hidden(k4_tarski('#skF_8'(D_37), D_37), '#skF_7') | ~r2_hidden(D_37, '#skF_6'))), inference(splitRight, [status(thm)], [c_32])).
% 10.51/3.81  tff(c_11039, plain, (![A_677, B_678, D_679]: (r2_hidden(k4_tarski('#skF_2'(A_677, B_678), '#skF_1'(A_677, B_678)), A_677) | ~r2_hidden(k4_tarski(D_679, '#skF_3'(A_677, B_678)), A_677) | k2_relat_1(A_677)=B_678)), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.51/3.81  tff(c_11157, plain, (![B_686]: (r2_hidden(k4_tarski('#skF_2'('#skF_7', B_686), '#skF_1'('#skF_7', B_686)), '#skF_7') | k2_relat_1('#skF_7')=B_686 | ~r2_hidden('#skF_3'('#skF_7', B_686), '#skF_6'))), inference(resolution, [status(thm)], [c_3621, c_11039])).
% 10.51/3.81  tff(c_11176, plain, (![B_686]: (r2_hidden('#skF_1'('#skF_7', B_686), k2_relat_1('#skF_7')) | k2_relat_1('#skF_7')=B_686 | ~r2_hidden('#skF_3'('#skF_7', B_686), '#skF_6'))), inference(resolution, [status(thm)], [c_11157, c_12])).
% 10.51/3.81  tff(c_21362, plain, (![B_1167]: (r2_hidden('#skF_1'('#skF_7', B_1167), '#skF_6') | k2_relat_1('#skF_7')=B_1167 | ~r2_hidden('#skF_3'('#skF_7', B_1167), '#skF_6'))), inference(resolution, [status(thm)], [c_11176, c_20850])).
% 10.51/3.81  tff(c_21366, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6') | k2_relat_1('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_20900, c_21362])).
% 10.51/3.81  tff(c_21375, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_3645, c_3645, c_21366])).
% 10.51/3.81  tff(c_21387, plain, (![D_23]: (~r2_hidden(k4_tarski(D_23, '#skF_3'('#skF_7', '#skF_6')), '#skF_7') | k2_relat_1('#skF_7')='#skF_6')), inference(resolution, [status(thm)], [c_21375, c_14])).
% 10.51/3.81  tff(c_21402, plain, (![D_1170]: (~r2_hidden(k4_tarski(D_1170, '#skF_3'('#skF_7', '#skF_6')), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_3645, c_21387])).
% 10.51/3.81  tff(c_21422, plain, (~r2_hidden('#skF_3'('#skF_7', '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_3621, c_21402])).
% 10.51/3.81  tff(c_21429, plain, (~r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6') | k2_relat_1('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_18, c_21422])).
% 10.51/3.81  tff(c_21435, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_21375, c_21429])).
% 10.51/3.81  tff(c_21437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3645, c_21435])).
% 10.51/3.81  tff(c_21438, plain, (r2_hidden('#skF_9', '#skF_6')), inference(splitRight, [status(thm)], [c_30])).
% 10.51/3.81  tff(c_21439, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_30])).
% 10.51/3.81  tff(c_21455, plain, (![A_1187, B_1188, C_1189]: (k2_relset_1(A_1187, B_1188, C_1189)=k2_relat_1(C_1189) | ~m1_subset_1(C_1189, k1_zfmisc_1(k2_zfmisc_1(A_1187, B_1188))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.51/3.81  tff(c_21458, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_24, c_21455])).
% 10.51/3.81  tff(c_21460, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_21439, c_21458])).
% 10.51/3.81  tff(c_21517, plain, (![A_1205, C_1206]: (r2_hidden(k4_tarski('#skF_4'(A_1205, k2_relat_1(A_1205), C_1206), C_1206), A_1205) | ~r2_hidden(C_1206, k2_relat_1(A_1205)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.51/3.81  tff(c_26, plain, (![E_40]: (k2_relset_1('#skF_5', '#skF_6', '#skF_7')!='#skF_6' | ~r2_hidden(k4_tarski(E_40, '#skF_9'), '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.51/3.81  tff(c_21452, plain, (![E_40]: (~r2_hidden(k4_tarski(E_40, '#skF_9'), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_21439, c_26])).
% 10.51/3.81  tff(c_21529, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_21517, c_21452])).
% 10.51/3.81  tff(c_21548, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21438, c_21460, c_21529])).
% 10.51/3.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.51/3.81  
% 10.51/3.81  Inference rules
% 10.51/3.81  ----------------------
% 10.51/3.81  #Ref     : 0
% 10.51/3.81  #Sup     : 5210
% 10.51/3.81  #Fact    : 4
% 10.51/3.81  #Define  : 0
% 10.51/3.81  #Split   : 24
% 10.51/3.81  #Chain   : 0
% 10.51/3.81  #Close   : 0
% 10.51/3.81  
% 10.51/3.81  Ordering : KBO
% 10.51/3.81  
% 10.51/3.81  Simplification rules
% 10.51/3.81  ----------------------
% 10.51/3.81  #Subsume      : 1431
% 10.51/3.81  #Demod        : 1352
% 10.51/3.81  #Tautology    : 517
% 10.51/3.81  #SimpNegUnit  : 225
% 10.51/3.81  #BackRed      : 64
% 10.51/3.81  
% 10.51/3.81  #Partial instantiations: 0
% 10.51/3.81  #Strategies tried      : 1
% 10.51/3.81  
% 10.51/3.81  Timing (in seconds)
% 10.51/3.81  ----------------------
% 10.51/3.82  Preprocessing        : 0.30
% 10.51/3.82  Parsing              : 0.15
% 10.51/3.82  CNF conversion       : 0.02
% 10.51/3.82  Main loop            : 2.75
% 10.51/3.82  Inferencing          : 0.80
% 10.51/3.82  Reduction            : 0.70
% 10.51/3.82  Demodulation         : 0.43
% 10.51/3.82  BG Simplification    : 0.11
% 10.51/3.82  Subsumption          : 0.88
% 10.51/3.82  Abstraction          : 0.15
% 10.51/3.82  MUC search           : 0.00
% 10.51/3.82  Cooper               : 0.00
% 10.51/3.82  Total                : 3.09
% 10.51/3.82  Index Insertion      : 0.00
% 10.51/3.82  Index Deletion       : 0.00
% 10.51/3.82  Index Matching       : 0.00
% 10.51/3.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
