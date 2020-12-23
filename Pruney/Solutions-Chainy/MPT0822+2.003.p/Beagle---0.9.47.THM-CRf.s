%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:10 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 396 expanded)
%              Number of leaves         :   28 ( 141 expanded)
%              Depth                    :   20
%              Number of atoms          :  141 ( 914 expanded)
%              Number of equality atoms :   33 ( 252 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_8 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_2 > #skF_1

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
        <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_44,plain,(
    ! [C_49,B_50,A_51] :
      ( v5_relat_1(C_49,B_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_51,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_48,plain,(
    v5_relat_1('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_44])).

tff(c_54,plain,(
    ! [A_55,B_56,C_57] :
      ( k2_relset_1(A_55,B_56,C_57) = k2_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_58,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_54])).

tff(c_30,plain,
    ( k2_relset_1('#skF_5','#skF_6','#skF_7') != '#skF_6'
    | r2_hidden('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_42,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_59,plain,(
    k2_relat_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_42])).

tff(c_37,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_41,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_37])).

tff(c_180,plain,(
    ! [A_84,B_85] :
      ( r2_hidden(k4_tarski('#skF_2'(A_84,B_85),'#skF_1'(A_84,B_85)),A_84)
      | r2_hidden('#skF_3'(A_84,B_85),B_85)
      | k2_relat_1(A_84) = B_85 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [C_16,A_1,D_19] :
      ( r2_hidden(C_16,k2_relat_1(A_1))
      | ~ r2_hidden(k4_tarski(D_19,C_16),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_234,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_1'(A_89,B_90),k2_relat_1(A_89))
      | r2_hidden('#skF_3'(A_89,B_90),B_90)
      | k2_relat_1(A_89) = B_90 ) ),
    inference(resolution,[status(thm)],[c_180,c_4])).

tff(c_14,plain,(
    ! [C_23,A_20,B_21] :
      ( r2_hidden(C_23,A_20)
      | ~ r2_hidden(C_23,k2_relat_1(B_21))
      | ~ v5_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_581,plain,(
    ! [A_113,B_114,A_115] :
      ( r2_hidden('#skF_1'(A_113,B_114),A_115)
      | ~ v5_relat_1(A_113,A_115)
      | ~ v1_relat_1(A_113)
      | r2_hidden('#skF_3'(A_113,B_114),B_114)
      | k2_relat_1(A_113) = B_114 ) ),
    inference(resolution,[status(thm)],[c_234,c_14])).

tff(c_36,plain,(
    ! [D_39] :
      ( r2_hidden(k4_tarski('#skF_8'(D_39),D_39),'#skF_7')
      | ~ r2_hidden(D_39,'#skF_6')
      | k2_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_6' ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_80,plain,(
    ! [D_39] :
      ( r2_hidden(k4_tarski('#skF_8'(D_39),D_39),'#skF_7')
      | ~ r2_hidden(D_39,'#skF_6')
      | k2_relat_1('#skF_7') = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_36])).

tff(c_81,plain,(
    ! [D_39] :
      ( r2_hidden(k4_tarski('#skF_8'(D_39),D_39),'#skF_7')
      | ~ r2_hidden(D_39,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_80])).

tff(c_205,plain,(
    ! [A_86,B_87,D_88] :
      ( r2_hidden(k4_tarski('#skF_2'(A_86,B_87),'#skF_1'(A_86,B_87)),A_86)
      | ~ r2_hidden(k4_tarski(D_88,'#skF_3'(A_86,B_87)),A_86)
      | k2_relat_1(A_86) = B_87 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_252,plain,(
    ! [B_92] :
      ( r2_hidden(k4_tarski('#skF_2'('#skF_7',B_92),'#skF_1'('#skF_7',B_92)),'#skF_7')
      | k2_relat_1('#skF_7') = B_92
      | ~ r2_hidden('#skF_3'('#skF_7',B_92),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_81,c_205])).

tff(c_257,plain,(
    ! [B_93] :
      ( r2_hidden('#skF_1'('#skF_7',B_93),k2_relat_1('#skF_7'))
      | k2_relat_1('#skF_7') = B_93
      | ~ r2_hidden('#skF_3'('#skF_7',B_93),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_252,c_4])).

tff(c_262,plain,(
    ! [B_93,A_20] :
      ( r2_hidden('#skF_1'('#skF_7',B_93),A_20)
      | ~ v5_relat_1('#skF_7',A_20)
      | ~ v1_relat_1('#skF_7')
      | k2_relat_1('#skF_7') = B_93
      | ~ r2_hidden('#skF_3'('#skF_7',B_93),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_257,c_14])).

tff(c_267,plain,(
    ! [B_93,A_20] :
      ( r2_hidden('#skF_1'('#skF_7',B_93),A_20)
      | ~ v5_relat_1('#skF_7',A_20)
      | k2_relat_1('#skF_7') = B_93
      | ~ r2_hidden('#skF_3'('#skF_7',B_93),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_262])).

tff(c_612,plain,(
    ! [A_20,A_115] :
      ( r2_hidden('#skF_1'('#skF_7','#skF_6'),A_20)
      | ~ v5_relat_1('#skF_7',A_20)
      | r2_hidden('#skF_1'('#skF_7','#skF_6'),A_115)
      | ~ v5_relat_1('#skF_7',A_115)
      | ~ v1_relat_1('#skF_7')
      | k2_relat_1('#skF_7') = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_581,c_267])).

tff(c_627,plain,(
    ! [A_20,A_115] :
      ( r2_hidden('#skF_1'('#skF_7','#skF_6'),A_20)
      | ~ v5_relat_1('#skF_7',A_20)
      | r2_hidden('#skF_1'('#skF_7','#skF_6'),A_115)
      | ~ v5_relat_1('#skF_7',A_115)
      | k2_relat_1('#skF_7') = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_612])).

tff(c_628,plain,(
    ! [A_20,A_115] :
      ( r2_hidden('#skF_1'('#skF_7','#skF_6'),A_20)
      | ~ v5_relat_1('#skF_7',A_20)
      | r2_hidden('#skF_1'('#skF_7','#skF_6'),A_115)
      | ~ v5_relat_1('#skF_7',A_115) ) ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_627])).

tff(c_667,plain,(
    ! [A_115] :
      ( r2_hidden('#skF_1'('#skF_7','#skF_6'),A_115)
      | ~ v5_relat_1('#skF_7',A_115) ) ),
    inference(splitLeft,[status(thm)],[c_628])).

tff(c_10,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_3'(A_1,B_2),B_2)
      | k2_relat_1(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_668,plain,(
    ! [A_119] :
      ( r2_hidden('#skF_1'('#skF_7','#skF_6'),A_119)
      | ~ v5_relat_1('#skF_7',A_119) ) ),
    inference(splitLeft,[status(thm)],[c_628])).

tff(c_6,plain,(
    ! [A_1,B_2,D_15] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | ~ r2_hidden(k4_tarski(D_15,'#skF_3'(A_1,B_2)),A_1)
      | k2_relat_1(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_681,plain,(
    ! [D_15] :
      ( ~ r2_hidden(k4_tarski(D_15,'#skF_3'('#skF_7','#skF_6')),'#skF_7')
      | k2_relat_1('#skF_7') = '#skF_6'
      | ~ v5_relat_1('#skF_7','#skF_6') ) ),
    inference(resolution,[status(thm)],[c_668,c_6])).

tff(c_690,plain,(
    ! [D_15] :
      ( ~ r2_hidden(k4_tarski(D_15,'#skF_3'('#skF_7','#skF_6')),'#skF_7')
      | k2_relat_1('#skF_7') = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_681])).

tff(c_693,plain,(
    ! [D_120] : ~ r2_hidden(k4_tarski(D_120,'#skF_3'('#skF_7','#skF_6')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_690])).

tff(c_707,plain,(
    ~ r2_hidden('#skF_3'('#skF_7','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_81,c_693])).

tff(c_715,plain,
    ( ~ r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k2_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_10,c_707])).

tff(c_722,plain,(
    ~ r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_715])).

tff(c_725,plain,(
    ~ v5_relat_1('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_667,c_722])).

tff(c_730,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_725])).

tff(c_731,plain,(
    ! [A_20] :
      ( r2_hidden('#skF_1'('#skF_7','#skF_6'),A_20)
      | ~ v5_relat_1('#skF_7',A_20) ) ),
    inference(splitRight,[status(thm)],[c_628])).

tff(c_732,plain,(
    ! [A_121] :
      ( r2_hidden('#skF_1'('#skF_7','#skF_6'),A_121)
      | ~ v5_relat_1('#skF_7',A_121) ) ),
    inference(splitRight,[status(thm)],[c_628])).

tff(c_745,plain,(
    ! [D_15] :
      ( ~ r2_hidden(k4_tarski(D_15,'#skF_3'('#skF_7','#skF_6')),'#skF_7')
      | k2_relat_1('#skF_7') = '#skF_6'
      | ~ v5_relat_1('#skF_7','#skF_6') ) ),
    inference(resolution,[status(thm)],[c_732,c_6])).

tff(c_754,plain,(
    ! [D_15] :
      ( ~ r2_hidden(k4_tarski(D_15,'#skF_3'('#skF_7','#skF_6')),'#skF_7')
      | k2_relat_1('#skF_7') = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_745])).

tff(c_757,plain,(
    ! [D_122] : ~ r2_hidden(k4_tarski(D_122,'#skF_3'('#skF_7','#skF_6')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_754])).

tff(c_771,plain,(
    ~ r2_hidden('#skF_3'('#skF_7','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_81,c_757])).

tff(c_779,plain,
    ( ~ r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k2_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_10,c_771])).

tff(c_786,plain,(
    ~ r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_779])).

tff(c_789,plain,(
    ~ v5_relat_1('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_731,c_786])).

tff(c_794,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_789])).

tff(c_795,plain,(
    r2_hidden('#skF_9','#skF_6') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_796,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_816,plain,(
    ! [A_133,B_134,C_135] :
      ( k2_relset_1(A_133,B_134,C_135) = k2_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_819,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_816])).

tff(c_821,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_819])).

tff(c_851,plain,(
    ! [A_144,C_145] :
      ( r2_hidden(k4_tarski('#skF_4'(A_144,k2_relat_1(A_144),C_145),C_145),A_144)
      | ~ r2_hidden(C_145,k2_relat_1(A_144)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ! [E_42] :
      ( k2_relset_1('#skF_5','#skF_6','#skF_7') != '#skF_6'
      | ~ r2_hidden(k4_tarski(E_42,'#skF_9'),'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_808,plain,(
    ! [E_42] : ~ r2_hidden(k4_tarski(E_42,'#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_26])).

tff(c_861,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_851,c_808])).

tff(c_873,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_795,c_821,c_861])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:32:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.47  
% 3.04/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.48  %$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_8 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_2 > #skF_1
% 3.04/1.48  
% 3.04/1.48  %Foreground sorts:
% 3.04/1.48  
% 3.04/1.48  
% 3.04/1.48  %Background operators:
% 3.04/1.48  
% 3.04/1.48  
% 3.04/1.48  %Foreground operators:
% 3.04/1.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.04/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.04/1.48  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.04/1.48  tff('#skF_8', type, '#skF_8': $i > $i).
% 3.04/1.48  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.04/1.48  tff('#skF_7', type, '#skF_7': $i).
% 3.04/1.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.04/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.04/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.04/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.04/1.48  tff('#skF_9', type, '#skF_9': $i).
% 3.04/1.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.04/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.04/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.04/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.04/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.04/1.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.04/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.04/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.04/1.48  
% 3.04/1.49  tff(f_69, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_relset_1)).
% 3.04/1.49  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.04/1.49  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.04/1.49  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.04/1.49  tff(f_33, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 3.04/1.49  tff(f_42, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t202_relat_1)).
% 3.04/1.49  tff(c_24, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.04/1.49  tff(c_44, plain, (![C_49, B_50, A_51]: (v5_relat_1(C_49, B_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_51, B_50))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.04/1.49  tff(c_48, plain, (v5_relat_1('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_24, c_44])).
% 3.04/1.49  tff(c_54, plain, (![A_55, B_56, C_57]: (k2_relset_1(A_55, B_56, C_57)=k2_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.04/1.49  tff(c_58, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_24, c_54])).
% 3.04/1.49  tff(c_30, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')!='#skF_6' | r2_hidden('#skF_9', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.04/1.49  tff(c_42, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')!='#skF_6'), inference(splitLeft, [status(thm)], [c_30])).
% 3.04/1.49  tff(c_59, plain, (k2_relat_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_42])).
% 3.04/1.49  tff(c_37, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.04/1.49  tff(c_41, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_24, c_37])).
% 3.04/1.49  tff(c_180, plain, (![A_84, B_85]: (r2_hidden(k4_tarski('#skF_2'(A_84, B_85), '#skF_1'(A_84, B_85)), A_84) | r2_hidden('#skF_3'(A_84, B_85), B_85) | k2_relat_1(A_84)=B_85)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.04/1.49  tff(c_4, plain, (![C_16, A_1, D_19]: (r2_hidden(C_16, k2_relat_1(A_1)) | ~r2_hidden(k4_tarski(D_19, C_16), A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.04/1.49  tff(c_234, plain, (![A_89, B_90]: (r2_hidden('#skF_1'(A_89, B_90), k2_relat_1(A_89)) | r2_hidden('#skF_3'(A_89, B_90), B_90) | k2_relat_1(A_89)=B_90)), inference(resolution, [status(thm)], [c_180, c_4])).
% 3.04/1.49  tff(c_14, plain, (![C_23, A_20, B_21]: (r2_hidden(C_23, A_20) | ~r2_hidden(C_23, k2_relat_1(B_21)) | ~v5_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.04/1.49  tff(c_581, plain, (![A_113, B_114, A_115]: (r2_hidden('#skF_1'(A_113, B_114), A_115) | ~v5_relat_1(A_113, A_115) | ~v1_relat_1(A_113) | r2_hidden('#skF_3'(A_113, B_114), B_114) | k2_relat_1(A_113)=B_114)), inference(resolution, [status(thm)], [c_234, c_14])).
% 3.04/1.49  tff(c_36, plain, (![D_39]: (r2_hidden(k4_tarski('#skF_8'(D_39), D_39), '#skF_7') | ~r2_hidden(D_39, '#skF_6') | k2_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_6')), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.04/1.49  tff(c_80, plain, (![D_39]: (r2_hidden(k4_tarski('#skF_8'(D_39), D_39), '#skF_7') | ~r2_hidden(D_39, '#skF_6') | k2_relat_1('#skF_7')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_36])).
% 3.04/1.49  tff(c_81, plain, (![D_39]: (r2_hidden(k4_tarski('#skF_8'(D_39), D_39), '#skF_7') | ~r2_hidden(D_39, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_59, c_80])).
% 3.04/1.49  tff(c_205, plain, (![A_86, B_87, D_88]: (r2_hidden(k4_tarski('#skF_2'(A_86, B_87), '#skF_1'(A_86, B_87)), A_86) | ~r2_hidden(k4_tarski(D_88, '#skF_3'(A_86, B_87)), A_86) | k2_relat_1(A_86)=B_87)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.04/1.49  tff(c_252, plain, (![B_92]: (r2_hidden(k4_tarski('#skF_2'('#skF_7', B_92), '#skF_1'('#skF_7', B_92)), '#skF_7') | k2_relat_1('#skF_7')=B_92 | ~r2_hidden('#skF_3'('#skF_7', B_92), '#skF_6'))), inference(resolution, [status(thm)], [c_81, c_205])).
% 3.04/1.49  tff(c_257, plain, (![B_93]: (r2_hidden('#skF_1'('#skF_7', B_93), k2_relat_1('#skF_7')) | k2_relat_1('#skF_7')=B_93 | ~r2_hidden('#skF_3'('#skF_7', B_93), '#skF_6'))), inference(resolution, [status(thm)], [c_252, c_4])).
% 3.04/1.49  tff(c_262, plain, (![B_93, A_20]: (r2_hidden('#skF_1'('#skF_7', B_93), A_20) | ~v5_relat_1('#skF_7', A_20) | ~v1_relat_1('#skF_7') | k2_relat_1('#skF_7')=B_93 | ~r2_hidden('#skF_3'('#skF_7', B_93), '#skF_6'))), inference(resolution, [status(thm)], [c_257, c_14])).
% 3.04/1.49  tff(c_267, plain, (![B_93, A_20]: (r2_hidden('#skF_1'('#skF_7', B_93), A_20) | ~v5_relat_1('#skF_7', A_20) | k2_relat_1('#skF_7')=B_93 | ~r2_hidden('#skF_3'('#skF_7', B_93), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_262])).
% 3.04/1.49  tff(c_612, plain, (![A_20, A_115]: (r2_hidden('#skF_1'('#skF_7', '#skF_6'), A_20) | ~v5_relat_1('#skF_7', A_20) | r2_hidden('#skF_1'('#skF_7', '#skF_6'), A_115) | ~v5_relat_1('#skF_7', A_115) | ~v1_relat_1('#skF_7') | k2_relat_1('#skF_7')='#skF_6')), inference(resolution, [status(thm)], [c_581, c_267])).
% 3.04/1.49  tff(c_627, plain, (![A_20, A_115]: (r2_hidden('#skF_1'('#skF_7', '#skF_6'), A_20) | ~v5_relat_1('#skF_7', A_20) | r2_hidden('#skF_1'('#skF_7', '#skF_6'), A_115) | ~v5_relat_1('#skF_7', A_115) | k2_relat_1('#skF_7')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_612])).
% 3.04/1.49  tff(c_628, plain, (![A_20, A_115]: (r2_hidden('#skF_1'('#skF_7', '#skF_6'), A_20) | ~v5_relat_1('#skF_7', A_20) | r2_hidden('#skF_1'('#skF_7', '#skF_6'), A_115) | ~v5_relat_1('#skF_7', A_115))), inference(negUnitSimplification, [status(thm)], [c_59, c_627])).
% 3.04/1.49  tff(c_667, plain, (![A_115]: (r2_hidden('#skF_1'('#skF_7', '#skF_6'), A_115) | ~v5_relat_1('#skF_7', A_115))), inference(splitLeft, [status(thm)], [c_628])).
% 3.04/1.49  tff(c_10, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_3'(A_1, B_2), B_2) | k2_relat_1(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.04/1.49  tff(c_668, plain, (![A_119]: (r2_hidden('#skF_1'('#skF_7', '#skF_6'), A_119) | ~v5_relat_1('#skF_7', A_119))), inference(splitLeft, [status(thm)], [c_628])).
% 3.04/1.49  tff(c_6, plain, (![A_1, B_2, D_15]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | ~r2_hidden(k4_tarski(D_15, '#skF_3'(A_1, B_2)), A_1) | k2_relat_1(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.04/1.49  tff(c_681, plain, (![D_15]: (~r2_hidden(k4_tarski(D_15, '#skF_3'('#skF_7', '#skF_6')), '#skF_7') | k2_relat_1('#skF_7')='#skF_6' | ~v5_relat_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_668, c_6])).
% 3.04/1.49  tff(c_690, plain, (![D_15]: (~r2_hidden(k4_tarski(D_15, '#skF_3'('#skF_7', '#skF_6')), '#skF_7') | k2_relat_1('#skF_7')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_681])).
% 3.04/1.49  tff(c_693, plain, (![D_120]: (~r2_hidden(k4_tarski(D_120, '#skF_3'('#skF_7', '#skF_6')), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_59, c_690])).
% 3.04/1.49  tff(c_707, plain, (~r2_hidden('#skF_3'('#skF_7', '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_81, c_693])).
% 3.04/1.49  tff(c_715, plain, (~r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6') | k2_relat_1('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_10, c_707])).
% 3.04/1.49  tff(c_722, plain, (~r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_59, c_715])).
% 3.04/1.49  tff(c_725, plain, (~v5_relat_1('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_667, c_722])).
% 3.04/1.49  tff(c_730, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_725])).
% 3.04/1.49  tff(c_731, plain, (![A_20]: (r2_hidden('#skF_1'('#skF_7', '#skF_6'), A_20) | ~v5_relat_1('#skF_7', A_20))), inference(splitRight, [status(thm)], [c_628])).
% 3.04/1.49  tff(c_732, plain, (![A_121]: (r2_hidden('#skF_1'('#skF_7', '#skF_6'), A_121) | ~v5_relat_1('#skF_7', A_121))), inference(splitRight, [status(thm)], [c_628])).
% 3.04/1.49  tff(c_745, plain, (![D_15]: (~r2_hidden(k4_tarski(D_15, '#skF_3'('#skF_7', '#skF_6')), '#skF_7') | k2_relat_1('#skF_7')='#skF_6' | ~v5_relat_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_732, c_6])).
% 3.04/1.49  tff(c_754, plain, (![D_15]: (~r2_hidden(k4_tarski(D_15, '#skF_3'('#skF_7', '#skF_6')), '#skF_7') | k2_relat_1('#skF_7')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_745])).
% 3.04/1.49  tff(c_757, plain, (![D_122]: (~r2_hidden(k4_tarski(D_122, '#skF_3'('#skF_7', '#skF_6')), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_59, c_754])).
% 3.04/1.49  tff(c_771, plain, (~r2_hidden('#skF_3'('#skF_7', '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_81, c_757])).
% 3.04/1.49  tff(c_779, plain, (~r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6') | k2_relat_1('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_10, c_771])).
% 3.04/1.49  tff(c_786, plain, (~r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_59, c_779])).
% 3.04/1.49  tff(c_789, plain, (~v5_relat_1('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_731, c_786])).
% 3.04/1.49  tff(c_794, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_789])).
% 3.04/1.49  tff(c_795, plain, (r2_hidden('#skF_9', '#skF_6')), inference(splitRight, [status(thm)], [c_30])).
% 3.04/1.49  tff(c_796, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_30])).
% 3.04/1.49  tff(c_816, plain, (![A_133, B_134, C_135]: (k2_relset_1(A_133, B_134, C_135)=k2_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.04/1.49  tff(c_819, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_24, c_816])).
% 3.04/1.49  tff(c_821, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_796, c_819])).
% 3.04/1.49  tff(c_851, plain, (![A_144, C_145]: (r2_hidden(k4_tarski('#skF_4'(A_144, k2_relat_1(A_144), C_145), C_145), A_144) | ~r2_hidden(C_145, k2_relat_1(A_144)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.04/1.49  tff(c_26, plain, (![E_42]: (k2_relset_1('#skF_5', '#skF_6', '#skF_7')!='#skF_6' | ~r2_hidden(k4_tarski(E_42, '#skF_9'), '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.04/1.49  tff(c_808, plain, (![E_42]: (~r2_hidden(k4_tarski(E_42, '#skF_9'), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_796, c_26])).
% 3.04/1.49  tff(c_861, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_851, c_808])).
% 3.04/1.49  tff(c_873, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_795, c_821, c_861])).
% 3.04/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.49  
% 3.04/1.49  Inference rules
% 3.04/1.49  ----------------------
% 3.04/1.49  #Ref     : 0
% 3.04/1.49  #Sup     : 175
% 3.04/1.49  #Fact    : 0
% 3.04/1.49  #Define  : 0
% 3.04/1.49  #Split   : 6
% 3.04/1.49  #Chain   : 0
% 3.04/1.49  #Close   : 0
% 3.04/1.49  
% 3.04/1.49  Ordering : KBO
% 3.04/1.49  
% 3.04/1.49  Simplification rules
% 3.04/1.49  ----------------------
% 3.04/1.49  #Subsume      : 21
% 3.04/1.49  #Demod        : 31
% 3.04/1.49  #Tautology    : 19
% 3.04/1.49  #SimpNegUnit  : 9
% 3.04/1.49  #BackRed      : 1
% 3.04/1.49  
% 3.04/1.49  #Partial instantiations: 0
% 3.04/1.49  #Strategies tried      : 1
% 3.04/1.49  
% 3.04/1.49  Timing (in seconds)
% 3.04/1.49  ----------------------
% 3.04/1.49  Preprocessing        : 0.29
% 3.04/1.49  Parsing              : 0.15
% 3.04/1.49  CNF conversion       : 0.02
% 3.04/1.49  Main loop            : 0.42
% 3.04/1.49  Inferencing          : 0.15
% 3.04/1.49  Reduction            : 0.11
% 3.04/1.49  Demodulation         : 0.08
% 3.04/1.49  BG Simplification    : 0.02
% 3.04/1.49  Subsumption          : 0.10
% 3.04/1.49  Abstraction          : 0.02
% 3.04/1.49  MUC search           : 0.00
% 3.04/1.49  Cooper               : 0.00
% 3.04/1.50  Total                : 0.75
% 3.04/1.50  Index Insertion      : 0.00
% 3.04/1.50  Index Deletion       : 0.00
% 3.04/1.50  Index Matching       : 0.00
% 3.04/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
