%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:10 EST 2020

% Result     : Theorem 5.02s
% Output     : CNFRefutation 5.36s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 401 expanded)
%              Number of leaves         :   27 ( 139 expanded)
%              Depth                    :   15
%              Number of atoms          :  171 ( 874 expanded)
%              Number of equality atoms :   41 ( 207 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_8 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_2 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
        <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3323,plain,(
    ! [A_299,B_300,C_301] :
      ( k1_relset_1(A_299,B_300,C_301) = k1_relat_1(C_301)
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(A_299,B_300))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3327,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_3323])).

tff(c_34,plain,
    ( k1_relset_1('#skF_6','#skF_5','#skF_7') != '#skF_6'
    | r2_hidden('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_42,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_7') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_3328,plain,(
    k1_relat_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3327,c_42])).

tff(c_81,plain,(
    ! [A_70,B_71,C_72] :
      ( k1_relset_1(A_70,B_71,C_72) = k1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_85,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_81])).

tff(c_86,plain,(
    k1_relat_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_42])).

tff(c_661,plain,(
    ! [A_131,B_132] :
      ( r2_hidden(k4_tarski('#skF_1'(A_131,B_132),'#skF_2'(A_131,B_132)),A_131)
      | r2_hidden('#skF_3'(A_131,B_132),B_132)
      | k1_relat_1(A_131) = B_132 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    ! [C_28,A_13,D_31] :
      ( r2_hidden(C_28,k1_relat_1(A_13))
      | ~ r2_hidden(k4_tarski(C_28,D_31),A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1318,plain,(
    ! [A_165,B_166] :
      ( r2_hidden('#skF_1'(A_165,B_166),k1_relat_1(A_165))
      | r2_hidden('#skF_3'(A_165,B_166),B_166)
      | k1_relat_1(A_165) = B_166 ) ),
    inference(resolution,[status(thm)],[c_661,c_16])).

tff(c_127,plain,(
    ! [C_82,A_83] :
      ( r2_hidden(k4_tarski(C_82,'#skF_4'(A_83,k1_relat_1(A_83),C_82)),A_83)
      | ~ r2_hidden(C_82,k1_relat_1(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_49,plain,(
    ! [C_50,B_51,A_52] :
      ( ~ v1_xboole_0(C_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(C_50))
      | ~ r2_hidden(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_52,plain,(
    ! [A_52] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_5'))
      | ~ r2_hidden(A_52,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_28,c_49])).

tff(c_53,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_54,plain,(
    ! [A_53,C_54,B_55] :
      ( m1_subset_1(A_53,C_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(C_54))
      | ~ r2_hidden(A_53,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_57,plain,(
    ! [A_53] :
      ( m1_subset_1(A_53,k2_zfmisc_1('#skF_6','#skF_5'))
      | ~ r2_hidden(A_53,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_28,c_54])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_43,plain,(
    ! [C_47,A_48,D_49] :
      ( r2_hidden(C_47,k1_relat_1(A_48))
      | ~ r2_hidden(k4_tarski(C_47,D_49),A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_69,plain,(
    ! [C_65,B_66,D_67] :
      ( r2_hidden(C_65,k1_relat_1(B_66))
      | v1_xboole_0(B_66)
      | ~ m1_subset_1(k4_tarski(C_65,D_67),B_66) ) ),
    inference(resolution,[status(thm)],[c_8,c_43])).

tff(c_72,plain,(
    ! [C_65,D_67] :
      ( r2_hidden(C_65,k1_relat_1(k2_zfmisc_1('#skF_6','#skF_5')))
      | v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_5'))
      | ~ r2_hidden(k4_tarski(C_65,D_67),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_57,c_69])).

tff(c_75,plain,(
    ! [C_65,D_67] :
      ( r2_hidden(C_65,k1_relat_1(k2_zfmisc_1('#skF_6','#skF_5')))
      | ~ r2_hidden(k4_tarski(C_65,D_67),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_72])).

tff(c_180,plain,(
    ! [C_88] :
      ( r2_hidden(C_88,k1_relat_1(k2_zfmisc_1('#skF_6','#skF_5')))
      | ~ r2_hidden(C_88,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_127,c_75])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_151,plain,(
    ! [C_82,C_3,D_4] :
      ( r2_hidden(C_82,C_3)
      | ~ r2_hidden(C_82,k1_relat_1(k2_zfmisc_1(C_3,D_4))) ) ),
    inference(resolution,[status(thm)],[c_127,c_6])).

tff(c_188,plain,(
    ! [C_88] :
      ( r2_hidden(C_88,'#skF_6')
      | ~ r2_hidden(C_88,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_180,c_151])).

tff(c_1357,plain,(
    ! [B_166] :
      ( r2_hidden('#skF_1'('#skF_7',B_166),'#skF_6')
      | r2_hidden('#skF_3'('#skF_7',B_166),B_166)
      | k1_relat_1('#skF_7') = B_166 ) ),
    inference(resolution,[status(thm)],[c_1318,c_188])).

tff(c_40,plain,(
    ! [D_41] :
      ( r2_hidden(k4_tarski(D_41,'#skF_8'(D_41)),'#skF_7')
      | ~ r2_hidden(D_41,'#skF_6')
      | k1_relset_1('#skF_6','#skF_5','#skF_7') = '#skF_6' ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_92,plain,(
    ! [D_41] :
      ( r2_hidden(k4_tarski(D_41,'#skF_8'(D_41)),'#skF_7')
      | ~ r2_hidden(D_41,'#skF_6')
      | k1_relat_1('#skF_7') = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_40])).

tff(c_94,plain,(
    ! [D_73] :
      ( r2_hidden(k4_tarski(D_73,'#skF_8'(D_73)),'#skF_7')
      | ~ r2_hidden(D_73,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_92])).

tff(c_101,plain,(
    ! [D_73] :
      ( r2_hidden(D_73,k1_relat_1('#skF_7'))
      | ~ r2_hidden(D_73,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_94,c_16])).

tff(c_14,plain,(
    ! [C_28,A_13] :
      ( r2_hidden(k4_tarski(C_28,'#skF_4'(A_13,k1_relat_1(A_13),C_28)),A_13)
      | ~ r2_hidden(C_28,k1_relat_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_875,plain,(
    ! [A_144,B_145,D_146] :
      ( r2_hidden(k4_tarski('#skF_1'(A_144,B_145),'#skF_2'(A_144,B_145)),A_144)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_144,B_145),D_146),A_144)
      | k1_relat_1(A_144) = B_145 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2519,plain,(
    ! [A_228,B_229] :
      ( r2_hidden(k4_tarski('#skF_1'(A_228,B_229),'#skF_2'(A_228,B_229)),A_228)
      | k1_relat_1(A_228) = B_229
      | ~ r2_hidden('#skF_3'(A_228,B_229),k1_relat_1(A_228)) ) ),
    inference(resolution,[status(thm)],[c_14,c_875])).

tff(c_64,plain,(
    ! [A_61,C_62,B_63,D_64] :
      ( r2_hidden(A_61,C_62)
      | ~ r2_hidden(k4_tarski(A_61,B_63),k2_zfmisc_1(C_62,D_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1556,plain,(
    ! [A_180,C_181,D_182,B_183] :
      ( r2_hidden(A_180,C_181)
      | v1_xboole_0(k2_zfmisc_1(C_181,D_182))
      | ~ m1_subset_1(k4_tarski(A_180,B_183),k2_zfmisc_1(C_181,D_182)) ) ),
    inference(resolution,[status(thm)],[c_8,c_64])).

tff(c_1560,plain,(
    ! [A_180,B_183] :
      ( r2_hidden(A_180,'#skF_6')
      | v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_5'))
      | ~ r2_hidden(k4_tarski(A_180,B_183),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_57,c_1556])).

tff(c_1563,plain,(
    ! [A_180,B_183] :
      ( r2_hidden(A_180,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_180,B_183),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_1560])).

tff(c_2680,plain,(
    ! [B_232] :
      ( r2_hidden('#skF_1'('#skF_7',B_232),'#skF_6')
      | k1_relat_1('#skF_7') = B_232
      | ~ r2_hidden('#skF_3'('#skF_7',B_232),k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_2519,c_1563])).

tff(c_2713,plain,(
    ! [B_233] :
      ( r2_hidden('#skF_1'('#skF_7',B_233),'#skF_6')
      | k1_relat_1('#skF_7') = B_233
      | ~ r2_hidden('#skF_3'('#skF_7',B_233),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_101,c_2680])).

tff(c_2721,plain,
    ( r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k1_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1357,c_2713])).

tff(c_2736,plain,(
    r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_86,c_2721])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( ~ r2_hidden('#skF_1'(A_13,B_14),B_14)
      | r2_hidden('#skF_3'(A_13,B_14),B_14)
      | k1_relat_1(A_13) = B_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_93,plain,(
    ! [D_41] :
      ( r2_hidden(k4_tarski(D_41,'#skF_8'(D_41)),'#skF_7')
      | ~ r2_hidden(D_41,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_92])).

tff(c_18,plain,(
    ! [A_13,B_14,D_27] :
      ( ~ r2_hidden('#skF_1'(A_13,B_14),B_14)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_13,B_14),D_27),A_13)
      | k1_relat_1(A_13) = B_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2747,plain,(
    ! [D_27] :
      ( ~ r2_hidden(k4_tarski('#skF_3'('#skF_7','#skF_6'),D_27),'#skF_7')
      | k1_relat_1('#skF_7') = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_2736,c_18])).

tff(c_2756,plain,(
    ! [D_234] : ~ r2_hidden(k4_tarski('#skF_3'('#skF_7','#skF_6'),D_234),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_2747])).

tff(c_2769,plain,(
    ~ r2_hidden('#skF_3'('#skF_7','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_93,c_2756])).

tff(c_2781,plain,
    ( ~ r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k1_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_22,c_2769])).

tff(c_2793,plain,(
    k1_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2736,c_2781])).

tff(c_2795,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_2793])).

tff(c_2796,plain,(
    ! [A_52] : ~ r2_hidden(A_52,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_3365,plain,(
    ! [D_41] :
      ( r2_hidden(k4_tarski(D_41,'#skF_8'(D_41)),'#skF_7')
      | ~ r2_hidden(D_41,'#skF_6')
      | k1_relat_1('#skF_7') = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3327,c_40])).

tff(c_3366,plain,(
    ! [D_41] : ~ r2_hidden(D_41,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_3328,c_2796,c_3365])).

tff(c_3111,plain,(
    ! [A_289,B_290] :
      ( r2_hidden(k4_tarski('#skF_1'(A_289,B_290),'#skF_2'(A_289,B_290)),A_289)
      | r2_hidden('#skF_3'(A_289,B_290),B_290)
      | k1_relat_1(A_289) = B_290 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36,plain,(
    ! [D_41] :
      ( r2_hidden(k4_tarski(D_41,'#skF_8'(D_41)),'#skF_7')
      | ~ r2_hidden(D_41,'#skF_6')
      | r2_hidden('#skF_9','#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2815,plain,(
    ! [D_41] :
      ( ~ r2_hidden(D_41,'#skF_6')
      | r2_hidden('#skF_9','#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2796,c_36])).

tff(c_2816,plain,(
    ! [D_41] : ~ r2_hidden(D_41,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2815])).

tff(c_3199,plain,(
    ! [B_291] :
      ( r2_hidden('#skF_3'('#skF_6',B_291),B_291)
      | k1_relat_1('#skF_6') = B_291 ) ),
    inference(resolution,[status(thm)],[c_3111,c_2816])).

tff(c_3272,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3199,c_2816])).

tff(c_3273,plain,(
    k1_relat_1('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_3199,c_2796])).

tff(c_3292,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3272,c_3273])).

tff(c_2831,plain,(
    ! [A_253,B_254,C_255] :
      ( k1_relset_1(A_253,B_254,C_255) = k1_relat_1(C_255)
      | ~ m1_subset_1(C_255,k1_zfmisc_1(k2_zfmisc_1(A_253,B_254))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2835,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_2831])).

tff(c_2836,plain,(
    k1_relat_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2835,c_42])).

tff(c_3300,plain,(
    k1_relat_1('#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3292,c_2836])).

tff(c_3314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3272,c_3300])).

tff(c_3315,plain,(
    r2_hidden('#skF_9','#skF_6') ),
    inference(splitRight,[status(thm)],[c_2815])).

tff(c_3368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3366,c_3315])).

tff(c_3369,plain,(
    r2_hidden('#skF_9','#skF_6') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_3370,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_3422,plain,(
    ! [A_337,B_338,C_339] :
      ( k1_relset_1(A_337,B_338,C_339) = k1_relat_1(C_339)
      | ~ m1_subset_1(C_339,k1_zfmisc_1(k2_zfmisc_1(A_337,B_338))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3425,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_3422])).

tff(c_3427,plain,(
    k1_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3370,c_3425])).

tff(c_3477,plain,(
    ! [C_353,A_354] :
      ( r2_hidden(k4_tarski(C_353,'#skF_4'(A_354,k1_relat_1(A_354),C_353)),A_354)
      | ~ r2_hidden(C_353,k1_relat_1(A_354)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,(
    ! [E_44] :
      ( k1_relset_1('#skF_6','#skF_5','#skF_7') != '#skF_6'
      | ~ r2_hidden(k4_tarski('#skF_9',E_44),'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3397,plain,(
    ! [E_44] : ~ r2_hidden(k4_tarski('#skF_9',E_44),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3370,c_30])).

tff(c_3492,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_3477,c_3397])).

tff(c_3511,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3369,c_3427,c_3492])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:06:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.02/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.36/2.00  
% 5.36/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.36/2.00  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_8 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_2 > #skF_1
% 5.36/2.00  
% 5.36/2.00  %Foreground sorts:
% 5.36/2.00  
% 5.36/2.00  
% 5.36/2.00  %Background operators:
% 5.36/2.00  
% 5.36/2.00  
% 5.36/2.00  %Foreground operators:
% 5.36/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.36/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.36/2.00  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.36/2.00  tff('#skF_8', type, '#skF_8': $i > $i).
% 5.36/2.00  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.36/2.00  tff('#skF_7', type, '#skF_7': $i).
% 5.36/2.00  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.36/2.00  tff('#skF_5', type, '#skF_5': $i).
% 5.36/2.00  tff('#skF_6', type, '#skF_6': $i).
% 5.36/2.00  tff('#skF_9', type, '#skF_9': $i).
% 5.36/2.00  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.36/2.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.36/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.36/2.00  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.36/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.36/2.00  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.36/2.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.36/2.00  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.36/2.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.36/2.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.36/2.00  
% 5.36/2.02  tff(f_75, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 5.36/2.02  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.36/2.02  tff(f_58, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 5.36/2.02  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 5.36/2.02  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 5.36/2.02  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.36/2.02  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 5.36/2.02  tff(c_28, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.36/2.02  tff(c_3323, plain, (![A_299, B_300, C_301]: (k1_relset_1(A_299, B_300, C_301)=k1_relat_1(C_301) | ~m1_subset_1(C_301, k1_zfmisc_1(k2_zfmisc_1(A_299, B_300))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.36/2.02  tff(c_3327, plain, (k1_relset_1('#skF_6', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_28, c_3323])).
% 5.36/2.02  tff(c_34, plain, (k1_relset_1('#skF_6', '#skF_5', '#skF_7')!='#skF_6' | r2_hidden('#skF_9', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.36/2.02  tff(c_42, plain, (k1_relset_1('#skF_6', '#skF_5', '#skF_7')!='#skF_6'), inference(splitLeft, [status(thm)], [c_34])).
% 5.36/2.02  tff(c_3328, plain, (k1_relat_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3327, c_42])).
% 5.36/2.02  tff(c_81, plain, (![A_70, B_71, C_72]: (k1_relset_1(A_70, B_71, C_72)=k1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.36/2.02  tff(c_85, plain, (k1_relset_1('#skF_6', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_28, c_81])).
% 5.36/2.02  tff(c_86, plain, (k1_relat_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_85, c_42])).
% 5.36/2.02  tff(c_661, plain, (![A_131, B_132]: (r2_hidden(k4_tarski('#skF_1'(A_131, B_132), '#skF_2'(A_131, B_132)), A_131) | r2_hidden('#skF_3'(A_131, B_132), B_132) | k1_relat_1(A_131)=B_132)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.36/2.02  tff(c_16, plain, (![C_28, A_13, D_31]: (r2_hidden(C_28, k1_relat_1(A_13)) | ~r2_hidden(k4_tarski(C_28, D_31), A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.36/2.02  tff(c_1318, plain, (![A_165, B_166]: (r2_hidden('#skF_1'(A_165, B_166), k1_relat_1(A_165)) | r2_hidden('#skF_3'(A_165, B_166), B_166) | k1_relat_1(A_165)=B_166)), inference(resolution, [status(thm)], [c_661, c_16])).
% 5.36/2.02  tff(c_127, plain, (![C_82, A_83]: (r2_hidden(k4_tarski(C_82, '#skF_4'(A_83, k1_relat_1(A_83), C_82)), A_83) | ~r2_hidden(C_82, k1_relat_1(A_83)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.36/2.02  tff(c_49, plain, (![C_50, B_51, A_52]: (~v1_xboole_0(C_50) | ~m1_subset_1(B_51, k1_zfmisc_1(C_50)) | ~r2_hidden(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.36/2.02  tff(c_52, plain, (![A_52]: (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_5')) | ~r2_hidden(A_52, '#skF_7'))), inference(resolution, [status(thm)], [c_28, c_49])).
% 5.36/2.02  tff(c_53, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_52])).
% 5.36/2.02  tff(c_54, plain, (![A_53, C_54, B_55]: (m1_subset_1(A_53, C_54) | ~m1_subset_1(B_55, k1_zfmisc_1(C_54)) | ~r2_hidden(A_53, B_55))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.36/2.02  tff(c_57, plain, (![A_53]: (m1_subset_1(A_53, k2_zfmisc_1('#skF_6', '#skF_5')) | ~r2_hidden(A_53, '#skF_7'))), inference(resolution, [status(thm)], [c_28, c_54])).
% 5.36/2.02  tff(c_8, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.36/2.02  tff(c_43, plain, (![C_47, A_48, D_49]: (r2_hidden(C_47, k1_relat_1(A_48)) | ~r2_hidden(k4_tarski(C_47, D_49), A_48))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.36/2.02  tff(c_69, plain, (![C_65, B_66, D_67]: (r2_hidden(C_65, k1_relat_1(B_66)) | v1_xboole_0(B_66) | ~m1_subset_1(k4_tarski(C_65, D_67), B_66))), inference(resolution, [status(thm)], [c_8, c_43])).
% 5.36/2.02  tff(c_72, plain, (![C_65, D_67]: (r2_hidden(C_65, k1_relat_1(k2_zfmisc_1('#skF_6', '#skF_5'))) | v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_5')) | ~r2_hidden(k4_tarski(C_65, D_67), '#skF_7'))), inference(resolution, [status(thm)], [c_57, c_69])).
% 5.36/2.02  tff(c_75, plain, (![C_65, D_67]: (r2_hidden(C_65, k1_relat_1(k2_zfmisc_1('#skF_6', '#skF_5'))) | ~r2_hidden(k4_tarski(C_65, D_67), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_53, c_72])).
% 5.36/2.02  tff(c_180, plain, (![C_88]: (r2_hidden(C_88, k1_relat_1(k2_zfmisc_1('#skF_6', '#skF_5'))) | ~r2_hidden(C_88, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_127, c_75])).
% 5.36/2.02  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.36/2.02  tff(c_151, plain, (![C_82, C_3, D_4]: (r2_hidden(C_82, C_3) | ~r2_hidden(C_82, k1_relat_1(k2_zfmisc_1(C_3, D_4))))), inference(resolution, [status(thm)], [c_127, c_6])).
% 5.36/2.02  tff(c_188, plain, (![C_88]: (r2_hidden(C_88, '#skF_6') | ~r2_hidden(C_88, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_180, c_151])).
% 5.36/2.02  tff(c_1357, plain, (![B_166]: (r2_hidden('#skF_1'('#skF_7', B_166), '#skF_6') | r2_hidden('#skF_3'('#skF_7', B_166), B_166) | k1_relat_1('#skF_7')=B_166)), inference(resolution, [status(thm)], [c_1318, c_188])).
% 5.36/2.02  tff(c_40, plain, (![D_41]: (r2_hidden(k4_tarski(D_41, '#skF_8'(D_41)), '#skF_7') | ~r2_hidden(D_41, '#skF_6') | k1_relset_1('#skF_6', '#skF_5', '#skF_7')='#skF_6')), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.36/2.02  tff(c_92, plain, (![D_41]: (r2_hidden(k4_tarski(D_41, '#skF_8'(D_41)), '#skF_7') | ~r2_hidden(D_41, '#skF_6') | k1_relat_1('#skF_7')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_40])).
% 5.36/2.02  tff(c_94, plain, (![D_73]: (r2_hidden(k4_tarski(D_73, '#skF_8'(D_73)), '#skF_7') | ~r2_hidden(D_73, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_86, c_92])).
% 5.36/2.02  tff(c_101, plain, (![D_73]: (r2_hidden(D_73, k1_relat_1('#skF_7')) | ~r2_hidden(D_73, '#skF_6'))), inference(resolution, [status(thm)], [c_94, c_16])).
% 5.36/2.02  tff(c_14, plain, (![C_28, A_13]: (r2_hidden(k4_tarski(C_28, '#skF_4'(A_13, k1_relat_1(A_13), C_28)), A_13) | ~r2_hidden(C_28, k1_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.36/2.02  tff(c_875, plain, (![A_144, B_145, D_146]: (r2_hidden(k4_tarski('#skF_1'(A_144, B_145), '#skF_2'(A_144, B_145)), A_144) | ~r2_hidden(k4_tarski('#skF_3'(A_144, B_145), D_146), A_144) | k1_relat_1(A_144)=B_145)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.36/2.02  tff(c_2519, plain, (![A_228, B_229]: (r2_hidden(k4_tarski('#skF_1'(A_228, B_229), '#skF_2'(A_228, B_229)), A_228) | k1_relat_1(A_228)=B_229 | ~r2_hidden('#skF_3'(A_228, B_229), k1_relat_1(A_228)))), inference(resolution, [status(thm)], [c_14, c_875])).
% 5.36/2.02  tff(c_64, plain, (![A_61, C_62, B_63, D_64]: (r2_hidden(A_61, C_62) | ~r2_hidden(k4_tarski(A_61, B_63), k2_zfmisc_1(C_62, D_64)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.36/2.02  tff(c_1556, plain, (![A_180, C_181, D_182, B_183]: (r2_hidden(A_180, C_181) | v1_xboole_0(k2_zfmisc_1(C_181, D_182)) | ~m1_subset_1(k4_tarski(A_180, B_183), k2_zfmisc_1(C_181, D_182)))), inference(resolution, [status(thm)], [c_8, c_64])).
% 5.36/2.02  tff(c_1560, plain, (![A_180, B_183]: (r2_hidden(A_180, '#skF_6') | v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_5')) | ~r2_hidden(k4_tarski(A_180, B_183), '#skF_7'))), inference(resolution, [status(thm)], [c_57, c_1556])).
% 5.36/2.02  tff(c_1563, plain, (![A_180, B_183]: (r2_hidden(A_180, '#skF_6') | ~r2_hidden(k4_tarski(A_180, B_183), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_53, c_1560])).
% 5.36/2.02  tff(c_2680, plain, (![B_232]: (r2_hidden('#skF_1'('#skF_7', B_232), '#skF_6') | k1_relat_1('#skF_7')=B_232 | ~r2_hidden('#skF_3'('#skF_7', B_232), k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_2519, c_1563])).
% 5.36/2.02  tff(c_2713, plain, (![B_233]: (r2_hidden('#skF_1'('#skF_7', B_233), '#skF_6') | k1_relat_1('#skF_7')=B_233 | ~r2_hidden('#skF_3'('#skF_7', B_233), '#skF_6'))), inference(resolution, [status(thm)], [c_101, c_2680])).
% 5.36/2.02  tff(c_2721, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6') | k1_relat_1('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_1357, c_2713])).
% 5.36/2.02  tff(c_2736, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_86, c_86, c_2721])).
% 5.36/2.02  tff(c_22, plain, (![A_13, B_14]: (~r2_hidden('#skF_1'(A_13, B_14), B_14) | r2_hidden('#skF_3'(A_13, B_14), B_14) | k1_relat_1(A_13)=B_14)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.36/2.02  tff(c_93, plain, (![D_41]: (r2_hidden(k4_tarski(D_41, '#skF_8'(D_41)), '#skF_7') | ~r2_hidden(D_41, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_86, c_92])).
% 5.36/2.02  tff(c_18, plain, (![A_13, B_14, D_27]: (~r2_hidden('#skF_1'(A_13, B_14), B_14) | ~r2_hidden(k4_tarski('#skF_3'(A_13, B_14), D_27), A_13) | k1_relat_1(A_13)=B_14)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.36/2.02  tff(c_2747, plain, (![D_27]: (~r2_hidden(k4_tarski('#skF_3'('#skF_7', '#skF_6'), D_27), '#skF_7') | k1_relat_1('#skF_7')='#skF_6')), inference(resolution, [status(thm)], [c_2736, c_18])).
% 5.36/2.02  tff(c_2756, plain, (![D_234]: (~r2_hidden(k4_tarski('#skF_3'('#skF_7', '#skF_6'), D_234), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_86, c_2747])).
% 5.36/2.02  tff(c_2769, plain, (~r2_hidden('#skF_3'('#skF_7', '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_93, c_2756])).
% 5.36/2.02  tff(c_2781, plain, (~r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6') | k1_relat_1('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_22, c_2769])).
% 5.36/2.02  tff(c_2793, plain, (k1_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2736, c_2781])).
% 5.36/2.02  tff(c_2795, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_2793])).
% 5.36/2.02  tff(c_2796, plain, (![A_52]: (~r2_hidden(A_52, '#skF_7'))), inference(splitRight, [status(thm)], [c_52])).
% 5.36/2.02  tff(c_3365, plain, (![D_41]: (r2_hidden(k4_tarski(D_41, '#skF_8'(D_41)), '#skF_7') | ~r2_hidden(D_41, '#skF_6') | k1_relat_1('#skF_7')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3327, c_40])).
% 5.36/2.02  tff(c_3366, plain, (![D_41]: (~r2_hidden(D_41, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_3328, c_2796, c_3365])).
% 5.36/2.02  tff(c_3111, plain, (![A_289, B_290]: (r2_hidden(k4_tarski('#skF_1'(A_289, B_290), '#skF_2'(A_289, B_290)), A_289) | r2_hidden('#skF_3'(A_289, B_290), B_290) | k1_relat_1(A_289)=B_290)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.36/2.02  tff(c_36, plain, (![D_41]: (r2_hidden(k4_tarski(D_41, '#skF_8'(D_41)), '#skF_7') | ~r2_hidden(D_41, '#skF_6') | r2_hidden('#skF_9', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.36/2.02  tff(c_2815, plain, (![D_41]: (~r2_hidden(D_41, '#skF_6') | r2_hidden('#skF_9', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_2796, c_36])).
% 5.36/2.02  tff(c_2816, plain, (![D_41]: (~r2_hidden(D_41, '#skF_6'))), inference(splitLeft, [status(thm)], [c_2815])).
% 5.36/2.02  tff(c_3199, plain, (![B_291]: (r2_hidden('#skF_3'('#skF_6', B_291), B_291) | k1_relat_1('#skF_6')=B_291)), inference(resolution, [status(thm)], [c_3111, c_2816])).
% 5.36/2.02  tff(c_3272, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_3199, c_2816])).
% 5.36/2.02  tff(c_3273, plain, (k1_relat_1('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_3199, c_2796])).
% 5.36/2.02  tff(c_3292, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3272, c_3273])).
% 5.36/2.02  tff(c_2831, plain, (![A_253, B_254, C_255]: (k1_relset_1(A_253, B_254, C_255)=k1_relat_1(C_255) | ~m1_subset_1(C_255, k1_zfmisc_1(k2_zfmisc_1(A_253, B_254))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.36/2.02  tff(c_2835, plain, (k1_relset_1('#skF_6', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_28, c_2831])).
% 5.36/2.02  tff(c_2836, plain, (k1_relat_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2835, c_42])).
% 5.36/2.02  tff(c_3300, plain, (k1_relat_1('#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3292, c_2836])).
% 5.36/2.02  tff(c_3314, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3272, c_3300])).
% 5.36/2.02  tff(c_3315, plain, (r2_hidden('#skF_9', '#skF_6')), inference(splitRight, [status(thm)], [c_2815])).
% 5.36/2.02  tff(c_3368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3366, c_3315])).
% 5.36/2.02  tff(c_3369, plain, (r2_hidden('#skF_9', '#skF_6')), inference(splitRight, [status(thm)], [c_34])).
% 5.36/2.02  tff(c_3370, plain, (k1_relset_1('#skF_6', '#skF_5', '#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_34])).
% 5.36/2.02  tff(c_3422, plain, (![A_337, B_338, C_339]: (k1_relset_1(A_337, B_338, C_339)=k1_relat_1(C_339) | ~m1_subset_1(C_339, k1_zfmisc_1(k2_zfmisc_1(A_337, B_338))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.36/2.02  tff(c_3425, plain, (k1_relset_1('#skF_6', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_28, c_3422])).
% 5.36/2.02  tff(c_3427, plain, (k1_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3370, c_3425])).
% 5.36/2.02  tff(c_3477, plain, (![C_353, A_354]: (r2_hidden(k4_tarski(C_353, '#skF_4'(A_354, k1_relat_1(A_354), C_353)), A_354) | ~r2_hidden(C_353, k1_relat_1(A_354)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.36/2.02  tff(c_30, plain, (![E_44]: (k1_relset_1('#skF_6', '#skF_5', '#skF_7')!='#skF_6' | ~r2_hidden(k4_tarski('#skF_9', E_44), '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.36/2.02  tff(c_3397, plain, (![E_44]: (~r2_hidden(k4_tarski('#skF_9', E_44), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_3370, c_30])).
% 5.36/2.02  tff(c_3492, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_3477, c_3397])).
% 5.36/2.02  tff(c_3511, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3369, c_3427, c_3492])).
% 5.36/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.36/2.02  
% 5.36/2.02  Inference rules
% 5.36/2.02  ----------------------
% 5.36/2.02  #Ref     : 0
% 5.36/2.02  #Sup     : 824
% 5.36/2.02  #Fact    : 0
% 5.36/2.02  #Define  : 0
% 5.36/2.02  #Split   : 21
% 5.36/2.02  #Chain   : 0
% 5.36/2.02  #Close   : 0
% 5.36/2.02  
% 5.36/2.02  Ordering : KBO
% 5.36/2.02  
% 5.36/2.02  Simplification rules
% 5.36/2.02  ----------------------
% 5.36/2.02  #Subsume      : 118
% 5.36/2.02  #Demod        : 87
% 5.36/2.02  #Tautology    : 57
% 5.36/2.02  #SimpNegUnit  : 36
% 5.36/2.02  #BackRed      : 40
% 5.36/2.02  
% 5.36/2.02  #Partial instantiations: 0
% 5.36/2.02  #Strategies tried      : 1
% 5.36/2.02  
% 5.36/2.02  Timing (in seconds)
% 5.36/2.02  ----------------------
% 5.36/2.03  Preprocessing        : 0.31
% 5.36/2.03  Parsing              : 0.16
% 5.36/2.03  CNF conversion       : 0.03
% 5.36/2.03  Main loop            : 0.93
% 5.36/2.03  Inferencing          : 0.30
% 5.36/2.03  Reduction            : 0.23
% 5.36/2.03  Demodulation         : 0.14
% 5.36/2.03  BG Simplification    : 0.04
% 5.36/2.03  Subsumption          : 0.27
% 5.36/2.03  Abstraction          : 0.06
% 5.36/2.03  MUC search           : 0.00
% 5.36/2.03  Cooper               : 0.00
% 5.36/2.03  Total                : 1.28
% 5.36/2.03  Index Insertion      : 0.00
% 5.36/2.03  Index Deletion       : 0.00
% 5.36/2.03  Index Matching       : 0.00
% 5.36/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
