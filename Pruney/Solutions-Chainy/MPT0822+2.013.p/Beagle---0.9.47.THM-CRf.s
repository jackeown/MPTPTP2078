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
% DateTime   : Thu Dec  3 10:07:12 EST 2020

% Result     : Theorem 5.43s
% Output     : CNFRefutation 5.57s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 389 expanded)
%              Number of leaves         :   27 ( 135 expanded)
%              Depth                    :   15
%              Number of atoms          :  164 ( 850 expanded)
%              Number of equality atoms :   37 ( 197 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_8 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_2 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
        <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

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

tff(c_34,plain,
    ( k2_relset_1('#skF_5','#skF_6','#skF_7') != '#skF_6'
    | r2_hidden('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_42,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_28,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_81,plain,(
    ! [A_70,B_71,C_72] :
      ( k2_relset_1(A_70,B_71,C_72) = k2_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_85,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_81])).

tff(c_86,plain,(
    k2_relat_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_42])).

tff(c_661,plain,(
    ! [A_131,B_132] :
      ( r2_hidden(k4_tarski('#skF_2'(A_131,B_132),'#skF_1'(A_131,B_132)),A_131)
      | r2_hidden('#skF_3'(A_131,B_132),B_132)
      | k2_relat_1(A_131) = B_132 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    ! [C_28,A_13,D_31] :
      ( r2_hidden(C_28,k2_relat_1(A_13))
      | ~ r2_hidden(k4_tarski(D_31,C_28),A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1318,plain,(
    ! [A_165,B_166] :
      ( r2_hidden('#skF_1'(A_165,B_166),k2_relat_1(A_165))
      | r2_hidden('#skF_3'(A_165,B_166),B_166)
      | k2_relat_1(A_165) = B_166 ) ),
    inference(resolution,[status(thm)],[c_661,c_16])).

tff(c_127,plain,(
    ! [A_82,C_83] :
      ( r2_hidden(k4_tarski('#skF_4'(A_82,k2_relat_1(A_82),C_83),C_83),A_82)
      | ~ r2_hidden(C_83,k2_relat_1(A_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_49,plain,(
    ! [C_50,B_51,A_52] :
      ( ~ v1_xboole_0(C_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(C_50))
      | ~ r2_hidden(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_52,plain,(
    ! [A_52] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(A_52,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_28,c_49])).

tff(c_53,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_54,plain,(
    ! [A_53,C_54,B_55] :
      ( m1_subset_1(A_53,C_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(C_54))
      | ~ r2_hidden(A_53,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_57,plain,(
    ! [A_53] :
      ( m1_subset_1(A_53,k2_zfmisc_1('#skF_5','#skF_6'))
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
      ( r2_hidden(C_47,k2_relat_1(A_48))
      | ~ r2_hidden(k4_tarski(D_49,C_47),A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_69,plain,(
    ! [C_65,B_66,D_67] :
      ( r2_hidden(C_65,k2_relat_1(B_66))
      | v1_xboole_0(B_66)
      | ~ m1_subset_1(k4_tarski(D_67,C_65),B_66) ) ),
    inference(resolution,[status(thm)],[c_8,c_43])).

tff(c_72,plain,(
    ! [C_65,D_67] :
      ( r2_hidden(C_65,k2_relat_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(k4_tarski(D_67,C_65),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_57,c_69])).

tff(c_75,plain,(
    ! [C_65,D_67] :
      ( r2_hidden(C_65,k2_relat_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ r2_hidden(k4_tarski(D_67,C_65),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_72])).

tff(c_180,plain,(
    ! [C_88] :
      ( r2_hidden(C_88,k2_relat_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ r2_hidden(C_88,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_127,c_75])).

tff(c_4,plain,(
    ! [B_2,D_4,A_1,C_3] :
      ( r2_hidden(B_2,D_4)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_152,plain,(
    ! [C_83,D_4,C_3] :
      ( r2_hidden(C_83,D_4)
      | ~ r2_hidden(C_83,k2_relat_1(k2_zfmisc_1(C_3,D_4))) ) ),
    inference(resolution,[status(thm)],[c_127,c_4])).

tff(c_188,plain,(
    ! [C_88] :
      ( r2_hidden(C_88,'#skF_6')
      | ~ r2_hidden(C_88,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_180,c_152])).

tff(c_1357,plain,(
    ! [B_166] :
      ( r2_hidden('#skF_1'('#skF_7',B_166),'#skF_6')
      | r2_hidden('#skF_3'('#skF_7',B_166),B_166)
      | k2_relat_1('#skF_7') = B_166 ) ),
    inference(resolution,[status(thm)],[c_1318,c_188])).

tff(c_40,plain,(
    ! [D_41] :
      ( r2_hidden(k4_tarski('#skF_8'(D_41),D_41),'#skF_7')
      | ~ r2_hidden(D_41,'#skF_6')
      | k2_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_6' ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_92,plain,(
    ! [D_41] :
      ( r2_hidden(k4_tarski('#skF_8'(D_41),D_41),'#skF_7')
      | ~ r2_hidden(D_41,'#skF_6')
      | k2_relat_1('#skF_7') = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_40])).

tff(c_94,plain,(
    ! [D_73] :
      ( r2_hidden(k4_tarski('#skF_8'(D_73),D_73),'#skF_7')
      | ~ r2_hidden(D_73,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_92])).

tff(c_101,plain,(
    ! [D_73] :
      ( r2_hidden(D_73,k2_relat_1('#skF_7'))
      | ~ r2_hidden(D_73,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_94,c_16])).

tff(c_14,plain,(
    ! [A_13,C_28] :
      ( r2_hidden(k4_tarski('#skF_4'(A_13,k2_relat_1(A_13),C_28),C_28),A_13)
      | ~ r2_hidden(C_28,k2_relat_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_875,plain,(
    ! [A_144,B_145,D_146] :
      ( r2_hidden(k4_tarski('#skF_2'(A_144,B_145),'#skF_1'(A_144,B_145)),A_144)
      | ~ r2_hidden(k4_tarski(D_146,'#skF_3'(A_144,B_145)),A_144)
      | k2_relat_1(A_144) = B_145 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2519,plain,(
    ! [A_228,B_229] :
      ( r2_hidden(k4_tarski('#skF_2'(A_228,B_229),'#skF_1'(A_228,B_229)),A_228)
      | k2_relat_1(A_228) = B_229
      | ~ r2_hidden('#skF_3'(A_228,B_229),k2_relat_1(A_228)) ) ),
    inference(resolution,[status(thm)],[c_14,c_875])).

tff(c_59,plain,(
    ! [B_57,D_58,A_59,C_60] :
      ( r2_hidden(B_57,D_58)
      | ~ r2_hidden(k4_tarski(A_59,B_57),k2_zfmisc_1(C_60,D_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1528,plain,(
    ! [B_174,D_175,C_176,A_177] :
      ( r2_hidden(B_174,D_175)
      | v1_xboole_0(k2_zfmisc_1(C_176,D_175))
      | ~ m1_subset_1(k4_tarski(A_177,B_174),k2_zfmisc_1(C_176,D_175)) ) ),
    inference(resolution,[status(thm)],[c_8,c_59])).

tff(c_1532,plain,(
    ! [B_174,A_177] :
      ( r2_hidden(B_174,'#skF_6')
      | v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(k4_tarski(A_177,B_174),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_57,c_1528])).

tff(c_1535,plain,(
    ! [B_174,A_177] :
      ( r2_hidden(B_174,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_177,B_174),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_1532])).

tff(c_2862,plain,(
    ! [B_238] :
      ( r2_hidden('#skF_1'('#skF_7',B_238),'#skF_6')
      | k2_relat_1('#skF_7') = B_238
      | ~ r2_hidden('#skF_3'('#skF_7',B_238),k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_2519,c_1535])).

tff(c_2950,plain,(
    ! [B_242] :
      ( r2_hidden('#skF_1'('#skF_7',B_242),'#skF_6')
      | k2_relat_1('#skF_7') = B_242
      | ~ r2_hidden('#skF_3'('#skF_7',B_242),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_101,c_2862])).

tff(c_2958,plain,
    ( r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k2_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1357,c_2950])).

tff(c_2973,plain,(
    r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_86,c_2958])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( ~ r2_hidden('#skF_1'(A_13,B_14),B_14)
      | r2_hidden('#skF_3'(A_13,B_14),B_14)
      | k2_relat_1(A_13) = B_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_93,plain,(
    ! [D_41] :
      ( r2_hidden(k4_tarski('#skF_8'(D_41),D_41),'#skF_7')
      | ~ r2_hidden(D_41,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_92])).

tff(c_18,plain,(
    ! [A_13,B_14,D_27] :
      ( ~ r2_hidden('#skF_1'(A_13,B_14),B_14)
      | ~ r2_hidden(k4_tarski(D_27,'#skF_3'(A_13,B_14)),A_13)
      | k2_relat_1(A_13) = B_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2984,plain,(
    ! [D_27] :
      ( ~ r2_hidden(k4_tarski(D_27,'#skF_3'('#skF_7','#skF_6')),'#skF_7')
      | k2_relat_1('#skF_7') = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_2973,c_18])).

tff(c_2993,plain,(
    ! [D_243] : ~ r2_hidden(k4_tarski(D_243,'#skF_3'('#skF_7','#skF_6')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_2984])).

tff(c_3006,plain,(
    ~ r2_hidden('#skF_3'('#skF_7','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_93,c_2993])).

tff(c_3018,plain,
    ( ~ r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k2_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_22,c_3006])).

tff(c_3030,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2973,c_3018])).

tff(c_3032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_3030])).

tff(c_3033,plain,(
    ! [A_52] : ~ r2_hidden(A_52,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_3728,plain,(
    ! [D_41] : ~ r2_hidden(D_41,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_3033,c_40])).

tff(c_3450,plain,(
    ! [A_307,B_308] :
      ( r2_hidden(k4_tarski('#skF_2'(A_307,B_308),'#skF_1'(A_307,B_308)),A_307)
      | r2_hidden('#skF_3'(A_307,B_308),B_308)
      | k2_relat_1(A_307) = B_308 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36,plain,(
    ! [D_41] :
      ( r2_hidden(k4_tarski('#skF_8'(D_41),D_41),'#skF_7')
      | ~ r2_hidden(D_41,'#skF_6')
      | r2_hidden('#skF_9','#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3058,plain,(
    ! [D_41] :
      ( ~ r2_hidden(D_41,'#skF_6')
      | r2_hidden('#skF_9','#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3033,c_36])).

tff(c_3059,plain,(
    ! [D_41] : ~ r2_hidden(D_41,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_3058])).

tff(c_3568,plain,(
    ! [B_309] :
      ( r2_hidden('#skF_3'('#skF_6',B_309),B_309)
      | k2_relat_1('#skF_6') = B_309 ) ),
    inference(resolution,[status(thm)],[c_3450,c_3059])).

tff(c_3671,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3568,c_3059])).

tff(c_3672,plain,(
    k2_relat_1('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_3568,c_3033])).

tff(c_3696,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3671,c_3672])).

tff(c_3068,plain,(
    ! [A_262,B_263,C_264] :
      ( k2_relset_1(A_262,B_263,C_264) = k2_relat_1(C_264)
      | ~ m1_subset_1(C_264,k1_zfmisc_1(k2_zfmisc_1(A_262,B_263))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3072,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_3068])).

tff(c_3073,plain,(
    k2_relat_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3072,c_42])).

tff(c_3708,plain,(
    k2_relat_1('#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3696,c_3073])).

tff(c_3726,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3671,c_3708])).

tff(c_3727,plain,(
    r2_hidden('#skF_9','#skF_6') ),
    inference(splitRight,[status(thm)],[c_3058])).

tff(c_3735,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3728,c_3727])).

tff(c_3736,plain,(
    r2_hidden('#skF_9','#skF_6') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_3737,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_3784,plain,(
    ! [A_334,B_335,C_336] :
      ( k2_relset_1(A_334,B_335,C_336) = k2_relat_1(C_336)
      | ~ m1_subset_1(C_336,k1_zfmisc_1(k2_zfmisc_1(A_334,B_335))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3787,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_3784])).

tff(c_3789,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3737,c_3787])).

tff(c_3848,plain,(
    ! [A_354,C_355] :
      ( r2_hidden(k4_tarski('#skF_4'(A_354,k2_relat_1(A_354),C_355),C_355),A_354)
      | ~ r2_hidden(C_355,k2_relat_1(A_354)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,(
    ! [E_44] :
      ( k2_relset_1('#skF_5','#skF_6','#skF_7') != '#skF_6'
      | ~ r2_hidden(k4_tarski(E_44,'#skF_9'),'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3763,plain,(
    ! [E_44] : ~ r2_hidden(k4_tarski(E_44,'#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3737,c_30])).

tff(c_3863,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_3848,c_3763])).

tff(c_3882,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3736,c_3789,c_3863])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.43/2.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.43/2.10  
% 5.43/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.43/2.11  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_8 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_2 > #skF_1
% 5.43/2.11  
% 5.43/2.11  %Foreground sorts:
% 5.43/2.11  
% 5.43/2.11  
% 5.43/2.11  %Background operators:
% 5.43/2.11  
% 5.43/2.11  
% 5.43/2.11  %Foreground operators:
% 5.43/2.11  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.43/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.43/2.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.43/2.11  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.43/2.11  tff('#skF_8', type, '#skF_8': $i > $i).
% 5.43/2.11  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.43/2.11  tff('#skF_7', type, '#skF_7': $i).
% 5.43/2.11  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.43/2.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.43/2.11  tff('#skF_5', type, '#skF_5': $i).
% 5.43/2.11  tff('#skF_6', type, '#skF_6': $i).
% 5.43/2.11  tff('#skF_9', type, '#skF_9': $i).
% 5.43/2.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.43/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.43/2.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.43/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.43/2.11  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.43/2.11  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.43/2.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.43/2.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.43/2.11  
% 5.57/2.12  tff(f_75, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_relset_1)).
% 5.57/2.12  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.57/2.12  tff(f_58, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 5.57/2.12  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 5.57/2.12  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 5.57/2.12  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.57/2.12  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 5.57/2.12  tff(c_34, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')!='#skF_6' | r2_hidden('#skF_9', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.57/2.12  tff(c_42, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')!='#skF_6'), inference(splitLeft, [status(thm)], [c_34])).
% 5.57/2.12  tff(c_28, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.57/2.12  tff(c_81, plain, (![A_70, B_71, C_72]: (k2_relset_1(A_70, B_71, C_72)=k2_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.57/2.12  tff(c_85, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_28, c_81])).
% 5.57/2.12  tff(c_86, plain, (k2_relat_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_85, c_42])).
% 5.57/2.12  tff(c_661, plain, (![A_131, B_132]: (r2_hidden(k4_tarski('#skF_2'(A_131, B_132), '#skF_1'(A_131, B_132)), A_131) | r2_hidden('#skF_3'(A_131, B_132), B_132) | k2_relat_1(A_131)=B_132)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.57/2.12  tff(c_16, plain, (![C_28, A_13, D_31]: (r2_hidden(C_28, k2_relat_1(A_13)) | ~r2_hidden(k4_tarski(D_31, C_28), A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.57/2.12  tff(c_1318, plain, (![A_165, B_166]: (r2_hidden('#skF_1'(A_165, B_166), k2_relat_1(A_165)) | r2_hidden('#skF_3'(A_165, B_166), B_166) | k2_relat_1(A_165)=B_166)), inference(resolution, [status(thm)], [c_661, c_16])).
% 5.57/2.12  tff(c_127, plain, (![A_82, C_83]: (r2_hidden(k4_tarski('#skF_4'(A_82, k2_relat_1(A_82), C_83), C_83), A_82) | ~r2_hidden(C_83, k2_relat_1(A_82)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.57/2.13  tff(c_49, plain, (![C_50, B_51, A_52]: (~v1_xboole_0(C_50) | ~m1_subset_1(B_51, k1_zfmisc_1(C_50)) | ~r2_hidden(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.57/2.13  tff(c_52, plain, (![A_52]: (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(A_52, '#skF_7'))), inference(resolution, [status(thm)], [c_28, c_49])).
% 5.57/2.13  tff(c_53, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_52])).
% 5.57/2.13  tff(c_54, plain, (![A_53, C_54, B_55]: (m1_subset_1(A_53, C_54) | ~m1_subset_1(B_55, k1_zfmisc_1(C_54)) | ~r2_hidden(A_53, B_55))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.57/2.13  tff(c_57, plain, (![A_53]: (m1_subset_1(A_53, k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(A_53, '#skF_7'))), inference(resolution, [status(thm)], [c_28, c_54])).
% 5.57/2.13  tff(c_8, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.57/2.13  tff(c_43, plain, (![C_47, A_48, D_49]: (r2_hidden(C_47, k2_relat_1(A_48)) | ~r2_hidden(k4_tarski(D_49, C_47), A_48))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.57/2.13  tff(c_69, plain, (![C_65, B_66, D_67]: (r2_hidden(C_65, k2_relat_1(B_66)) | v1_xboole_0(B_66) | ~m1_subset_1(k4_tarski(D_67, C_65), B_66))), inference(resolution, [status(thm)], [c_8, c_43])).
% 5.57/2.13  tff(c_72, plain, (![C_65, D_67]: (r2_hidden(C_65, k2_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(k4_tarski(D_67, C_65), '#skF_7'))), inference(resolution, [status(thm)], [c_57, c_69])).
% 5.57/2.13  tff(c_75, plain, (![C_65, D_67]: (r2_hidden(C_65, k2_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~r2_hidden(k4_tarski(D_67, C_65), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_53, c_72])).
% 5.57/2.13  tff(c_180, plain, (![C_88]: (r2_hidden(C_88, k2_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~r2_hidden(C_88, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_127, c_75])).
% 5.57/2.13  tff(c_4, plain, (![B_2, D_4, A_1, C_3]: (r2_hidden(B_2, D_4) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.57/2.13  tff(c_152, plain, (![C_83, D_4, C_3]: (r2_hidden(C_83, D_4) | ~r2_hidden(C_83, k2_relat_1(k2_zfmisc_1(C_3, D_4))))), inference(resolution, [status(thm)], [c_127, c_4])).
% 5.57/2.13  tff(c_188, plain, (![C_88]: (r2_hidden(C_88, '#skF_6') | ~r2_hidden(C_88, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_180, c_152])).
% 5.57/2.13  tff(c_1357, plain, (![B_166]: (r2_hidden('#skF_1'('#skF_7', B_166), '#skF_6') | r2_hidden('#skF_3'('#skF_7', B_166), B_166) | k2_relat_1('#skF_7')=B_166)), inference(resolution, [status(thm)], [c_1318, c_188])).
% 5.57/2.13  tff(c_40, plain, (![D_41]: (r2_hidden(k4_tarski('#skF_8'(D_41), D_41), '#skF_7') | ~r2_hidden(D_41, '#skF_6') | k2_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_6')), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.57/2.13  tff(c_92, plain, (![D_41]: (r2_hidden(k4_tarski('#skF_8'(D_41), D_41), '#skF_7') | ~r2_hidden(D_41, '#skF_6') | k2_relat_1('#skF_7')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_40])).
% 5.57/2.13  tff(c_94, plain, (![D_73]: (r2_hidden(k4_tarski('#skF_8'(D_73), D_73), '#skF_7') | ~r2_hidden(D_73, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_86, c_92])).
% 5.57/2.13  tff(c_101, plain, (![D_73]: (r2_hidden(D_73, k2_relat_1('#skF_7')) | ~r2_hidden(D_73, '#skF_6'))), inference(resolution, [status(thm)], [c_94, c_16])).
% 5.57/2.13  tff(c_14, plain, (![A_13, C_28]: (r2_hidden(k4_tarski('#skF_4'(A_13, k2_relat_1(A_13), C_28), C_28), A_13) | ~r2_hidden(C_28, k2_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.57/2.13  tff(c_875, plain, (![A_144, B_145, D_146]: (r2_hidden(k4_tarski('#skF_2'(A_144, B_145), '#skF_1'(A_144, B_145)), A_144) | ~r2_hidden(k4_tarski(D_146, '#skF_3'(A_144, B_145)), A_144) | k2_relat_1(A_144)=B_145)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.57/2.13  tff(c_2519, plain, (![A_228, B_229]: (r2_hidden(k4_tarski('#skF_2'(A_228, B_229), '#skF_1'(A_228, B_229)), A_228) | k2_relat_1(A_228)=B_229 | ~r2_hidden('#skF_3'(A_228, B_229), k2_relat_1(A_228)))), inference(resolution, [status(thm)], [c_14, c_875])).
% 5.57/2.13  tff(c_59, plain, (![B_57, D_58, A_59, C_60]: (r2_hidden(B_57, D_58) | ~r2_hidden(k4_tarski(A_59, B_57), k2_zfmisc_1(C_60, D_58)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.57/2.13  tff(c_1528, plain, (![B_174, D_175, C_176, A_177]: (r2_hidden(B_174, D_175) | v1_xboole_0(k2_zfmisc_1(C_176, D_175)) | ~m1_subset_1(k4_tarski(A_177, B_174), k2_zfmisc_1(C_176, D_175)))), inference(resolution, [status(thm)], [c_8, c_59])).
% 5.57/2.13  tff(c_1532, plain, (![B_174, A_177]: (r2_hidden(B_174, '#skF_6') | v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(k4_tarski(A_177, B_174), '#skF_7'))), inference(resolution, [status(thm)], [c_57, c_1528])).
% 5.57/2.13  tff(c_1535, plain, (![B_174, A_177]: (r2_hidden(B_174, '#skF_6') | ~r2_hidden(k4_tarski(A_177, B_174), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_53, c_1532])).
% 5.57/2.13  tff(c_2862, plain, (![B_238]: (r2_hidden('#skF_1'('#skF_7', B_238), '#skF_6') | k2_relat_1('#skF_7')=B_238 | ~r2_hidden('#skF_3'('#skF_7', B_238), k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_2519, c_1535])).
% 5.57/2.13  tff(c_2950, plain, (![B_242]: (r2_hidden('#skF_1'('#skF_7', B_242), '#skF_6') | k2_relat_1('#skF_7')=B_242 | ~r2_hidden('#skF_3'('#skF_7', B_242), '#skF_6'))), inference(resolution, [status(thm)], [c_101, c_2862])).
% 5.57/2.13  tff(c_2958, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6') | k2_relat_1('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_1357, c_2950])).
% 5.57/2.13  tff(c_2973, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_86, c_86, c_2958])).
% 5.57/2.13  tff(c_22, plain, (![A_13, B_14]: (~r2_hidden('#skF_1'(A_13, B_14), B_14) | r2_hidden('#skF_3'(A_13, B_14), B_14) | k2_relat_1(A_13)=B_14)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.57/2.13  tff(c_93, plain, (![D_41]: (r2_hidden(k4_tarski('#skF_8'(D_41), D_41), '#skF_7') | ~r2_hidden(D_41, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_86, c_92])).
% 5.57/2.13  tff(c_18, plain, (![A_13, B_14, D_27]: (~r2_hidden('#skF_1'(A_13, B_14), B_14) | ~r2_hidden(k4_tarski(D_27, '#skF_3'(A_13, B_14)), A_13) | k2_relat_1(A_13)=B_14)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.57/2.13  tff(c_2984, plain, (![D_27]: (~r2_hidden(k4_tarski(D_27, '#skF_3'('#skF_7', '#skF_6')), '#skF_7') | k2_relat_1('#skF_7')='#skF_6')), inference(resolution, [status(thm)], [c_2973, c_18])).
% 5.57/2.13  tff(c_2993, plain, (![D_243]: (~r2_hidden(k4_tarski(D_243, '#skF_3'('#skF_7', '#skF_6')), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_86, c_2984])).
% 5.57/2.13  tff(c_3006, plain, (~r2_hidden('#skF_3'('#skF_7', '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_93, c_2993])).
% 5.57/2.13  tff(c_3018, plain, (~r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6') | k2_relat_1('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_22, c_3006])).
% 5.57/2.13  tff(c_3030, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2973, c_3018])).
% 5.57/2.13  tff(c_3032, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_3030])).
% 5.57/2.13  tff(c_3033, plain, (![A_52]: (~r2_hidden(A_52, '#skF_7'))), inference(splitRight, [status(thm)], [c_52])).
% 5.57/2.13  tff(c_3728, plain, (![D_41]: (~r2_hidden(D_41, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_42, c_3033, c_40])).
% 5.57/2.13  tff(c_3450, plain, (![A_307, B_308]: (r2_hidden(k4_tarski('#skF_2'(A_307, B_308), '#skF_1'(A_307, B_308)), A_307) | r2_hidden('#skF_3'(A_307, B_308), B_308) | k2_relat_1(A_307)=B_308)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.57/2.13  tff(c_36, plain, (![D_41]: (r2_hidden(k4_tarski('#skF_8'(D_41), D_41), '#skF_7') | ~r2_hidden(D_41, '#skF_6') | r2_hidden('#skF_9', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.57/2.13  tff(c_3058, plain, (![D_41]: (~r2_hidden(D_41, '#skF_6') | r2_hidden('#skF_9', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_3033, c_36])).
% 5.57/2.13  tff(c_3059, plain, (![D_41]: (~r2_hidden(D_41, '#skF_6'))), inference(splitLeft, [status(thm)], [c_3058])).
% 5.57/2.13  tff(c_3568, plain, (![B_309]: (r2_hidden('#skF_3'('#skF_6', B_309), B_309) | k2_relat_1('#skF_6')=B_309)), inference(resolution, [status(thm)], [c_3450, c_3059])).
% 5.57/2.13  tff(c_3671, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_3568, c_3059])).
% 5.57/2.13  tff(c_3672, plain, (k2_relat_1('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_3568, c_3033])).
% 5.57/2.13  tff(c_3696, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3671, c_3672])).
% 5.57/2.13  tff(c_3068, plain, (![A_262, B_263, C_264]: (k2_relset_1(A_262, B_263, C_264)=k2_relat_1(C_264) | ~m1_subset_1(C_264, k1_zfmisc_1(k2_zfmisc_1(A_262, B_263))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.57/2.13  tff(c_3072, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_28, c_3068])).
% 5.57/2.13  tff(c_3073, plain, (k2_relat_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3072, c_42])).
% 5.57/2.13  tff(c_3708, plain, (k2_relat_1('#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3696, c_3073])).
% 5.57/2.13  tff(c_3726, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3671, c_3708])).
% 5.57/2.13  tff(c_3727, plain, (r2_hidden('#skF_9', '#skF_6')), inference(splitRight, [status(thm)], [c_3058])).
% 5.57/2.13  tff(c_3735, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3728, c_3727])).
% 5.57/2.13  tff(c_3736, plain, (r2_hidden('#skF_9', '#skF_6')), inference(splitRight, [status(thm)], [c_34])).
% 5.57/2.13  tff(c_3737, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_34])).
% 5.57/2.13  tff(c_3784, plain, (![A_334, B_335, C_336]: (k2_relset_1(A_334, B_335, C_336)=k2_relat_1(C_336) | ~m1_subset_1(C_336, k1_zfmisc_1(k2_zfmisc_1(A_334, B_335))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.57/2.13  tff(c_3787, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_28, c_3784])).
% 5.57/2.13  tff(c_3789, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3737, c_3787])).
% 5.57/2.13  tff(c_3848, plain, (![A_354, C_355]: (r2_hidden(k4_tarski('#skF_4'(A_354, k2_relat_1(A_354), C_355), C_355), A_354) | ~r2_hidden(C_355, k2_relat_1(A_354)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.57/2.13  tff(c_30, plain, (![E_44]: (k2_relset_1('#skF_5', '#skF_6', '#skF_7')!='#skF_6' | ~r2_hidden(k4_tarski(E_44, '#skF_9'), '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.57/2.13  tff(c_3763, plain, (![E_44]: (~r2_hidden(k4_tarski(E_44, '#skF_9'), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_3737, c_30])).
% 5.57/2.13  tff(c_3863, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_3848, c_3763])).
% 5.57/2.13  tff(c_3882, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3736, c_3789, c_3863])).
% 5.57/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.57/2.13  
% 5.57/2.13  Inference rules
% 5.57/2.13  ----------------------
% 5.57/2.13  #Ref     : 0
% 5.57/2.13  #Sup     : 899
% 5.57/2.13  #Fact    : 0
% 5.57/2.13  #Define  : 0
% 5.57/2.13  #Split   : 24
% 5.57/2.13  #Chain   : 0
% 5.57/2.13  #Close   : 0
% 5.57/2.13  
% 5.57/2.13  Ordering : KBO
% 5.57/2.13  
% 5.57/2.13  Simplification rules
% 5.57/2.13  ----------------------
% 5.57/2.13  #Subsume      : 134
% 5.57/2.13  #Demod        : 150
% 5.57/2.13  #Tautology    : 65
% 5.57/2.13  #SimpNegUnit  : 38
% 5.57/2.13  #BackRed      : 47
% 5.57/2.13  
% 5.57/2.13  #Partial instantiations: 0
% 5.57/2.13  #Strategies tried      : 1
% 5.57/2.13  
% 5.57/2.13  Timing (in seconds)
% 5.57/2.13  ----------------------
% 5.57/2.13  Preprocessing        : 0.31
% 5.57/2.13  Parsing              : 0.16
% 5.57/2.13  CNF conversion       : 0.02
% 5.57/2.13  Main loop            : 0.97
% 5.57/2.13  Inferencing          : 0.30
% 5.57/2.13  Reduction            : 0.24
% 5.57/2.13  Demodulation         : 0.15
% 5.57/2.13  BG Simplification    : 0.04
% 5.57/2.13  Subsumption          : 0.29
% 5.57/2.13  Abstraction          : 0.05
% 5.57/2.13  MUC search           : 0.00
% 5.57/2.13  Cooper               : 0.00
% 5.57/2.13  Total                : 1.32
% 5.57/2.13  Index Insertion      : 0.00
% 5.57/2.13  Index Deletion       : 0.00
% 5.57/2.13  Index Matching       : 0.00
% 5.57/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
