%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:09 EST 2020

% Result     : Theorem 5.61s
% Output     : CNFRefutation 5.73s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 197 expanded)
%              Number of leaves         :   29 (  78 expanded)
%              Depth                    :    8
%              Number of atoms          :  128 ( 443 expanded)
%              Number of equality atoms :    8 (  34 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ! [D] :
                    ( r2_hidden(D,k2_relset_1(B,A,C))
                  <=> ? [E] :
                        ( m1_subset_1(E,B)
                        & r2_hidden(k4_tarski(E,D),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_3587,plain,(
    ! [A_478,C_479] :
      ( r2_hidden(k4_tarski('#skF_4'(A_478,k2_relat_1(A_478),C_479),C_479),A_478)
      | ~ r2_hidden(C_479,k2_relat_1(A_478)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_30,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3503,plain,(
    ! [A_451,B_452,C_453] :
      ( k2_relset_1(A_451,B_452,C_453) = k2_relat_1(C_453)
      | ~ m1_subset_1(C_453,k1_zfmisc_1(k2_zfmisc_1(A_451,B_452))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3507,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_3503])).

tff(c_1002,plain,(
    ! [A_211,B_212,C_213] :
      ( k2_relset_1(A_211,B_212,C_213) = k2_relat_1(C_213)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(A_211,B_212))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1006,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_1002])).

tff(c_46,plain,
    ( m1_subset_1('#skF_9','#skF_6')
    | r2_hidden('#skF_10',k2_relset_1('#skF_6','#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_64,plain,(
    r2_hidden('#skF_10',k2_relset_1('#skF_6','#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_1008,plain,(
    r2_hidden('#skF_10',k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1006,c_64])).

tff(c_16,plain,(
    ! [A_15,C_30] :
      ( r2_hidden(k4_tarski('#skF_4'(A_15,k2_relat_1(A_15),C_30),C_30),A_15)
      | ~ r2_hidden(C_30,k2_relat_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_53,plain,(
    ! [C_83,B_84,A_85] :
      ( ~ v1_xboole_0(C_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(C_83))
      | ~ r2_hidden(A_85,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_56,plain,(
    ! [A_85] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_5'))
      | ~ r2_hidden(A_85,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_30,c_53])).

tff(c_57,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_69,plain,(
    ! [A_89,C_90,B_91] :
      ( m1_subset_1(A_89,C_90)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(C_90))
      | ~ r2_hidden(A_89,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_72,plain,(
    ! [A_89] :
      ( m1_subset_1(A_89,k2_zfmisc_1('#skF_6','#skF_5'))
      | ~ r2_hidden(A_89,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_30,c_69])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_79,plain,(
    ! [A_97,C_98,B_99,D_100] :
      ( r2_hidden(A_97,C_98)
      | ~ r2_hidden(k4_tarski(A_97,B_99),k2_zfmisc_1(C_98,D_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3346,plain,(
    ! [A_424,C_425,D_426,B_427] :
      ( r2_hidden(A_424,C_425)
      | v1_xboole_0(k2_zfmisc_1(C_425,D_426))
      | ~ m1_subset_1(k4_tarski(A_424,B_427),k2_zfmisc_1(C_425,D_426)) ) ),
    inference(resolution,[status(thm)],[c_10,c_79])).

tff(c_3357,plain,(
    ! [A_424,B_427] :
      ( r2_hidden(A_424,'#skF_6')
      | v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_5'))
      | ~ r2_hidden(k4_tarski(A_424,B_427),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_3346])).

tff(c_3363,plain,(
    ! [A_428,B_429] :
      ( r2_hidden(A_428,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_428,B_429),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_3357])).

tff(c_3441,plain,(
    ! [C_434] :
      ( r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_434),'#skF_6')
      | ~ r2_hidden(C_434,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_16,c_3363])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3449,plain,(
    ! [C_435] :
      ( m1_subset_1('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_435),'#skF_6')
      | ~ r2_hidden(C_435,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_3441,c_8])).

tff(c_2126,plain,(
    ! [A_319,C_320,D_321,B_322] :
      ( r2_hidden(A_319,C_320)
      | v1_xboole_0(k2_zfmisc_1(C_320,D_321))
      | ~ m1_subset_1(k4_tarski(A_319,B_322),k2_zfmisc_1(C_320,D_321)) ) ),
    inference(resolution,[status(thm)],[c_10,c_79])).

tff(c_2137,plain,(
    ! [A_319,B_322] :
      ( r2_hidden(A_319,'#skF_6')
      | v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_5'))
      | ~ r2_hidden(k4_tarski(A_319,B_322),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_2126])).

tff(c_2143,plain,(
    ! [A_323,B_324] :
      ( r2_hidden(A_323,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_323,B_324),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_2137])).

tff(c_2189,plain,(
    ! [C_325] :
      ( r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_325),'#skF_6')
      | ~ r2_hidden(C_325,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_16,c_2143])).

tff(c_2203,plain,(
    ! [C_326] :
      ( m1_subset_1('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_326),'#skF_6')
      | ~ r2_hidden(C_326,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_2189,c_8])).

tff(c_1074,plain,(
    ! [A_228,C_229] :
      ( r2_hidden(k4_tarski('#skF_4'(A_228,k2_relat_1(A_228),C_229),C_229),A_228)
      | ~ r2_hidden(C_229,k2_relat_1(A_228)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_38,plain,(
    ! [E_78] :
      ( r2_hidden(k4_tarski('#skF_9','#skF_8'),'#skF_7')
      | ~ r2_hidden(k4_tarski(E_78,'#skF_10'),'#skF_7')
      | ~ m1_subset_1(E_78,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1040,plain,(
    ! [E_78] :
      ( ~ r2_hidden(k4_tarski(E_78,'#skF_10'),'#skF_7')
      | ~ m1_subset_1(E_78,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_1080,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_7',k2_relat_1('#skF_7'),'#skF_10'),'#skF_6')
    | ~ r2_hidden('#skF_10',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1074,c_1040])).

tff(c_1101,plain,(
    ~ m1_subset_1('#skF_4'('#skF_7',k2_relat_1('#skF_7'),'#skF_10'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_1080])).

tff(c_2206,plain,(
    ~ r2_hidden('#skF_10',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_2203,c_1101])).

tff(c_2210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_2206])).

tff(c_2211,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_18,plain,(
    ! [C_30,A_15,D_33] :
      ( r2_hidden(C_30,k2_relat_1(A_15))
      | ~ r2_hidden(k4_tarski(D_33,C_30),A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2221,plain,(
    r2_hidden('#skF_8',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_2211,c_18])).

tff(c_36,plain,(
    ! [E_78] :
      ( ~ r2_hidden('#skF_8',k2_relset_1('#skF_6','#skF_5','#skF_7'))
      | ~ r2_hidden(k4_tarski(E_78,'#skF_10'),'#skF_7')
      | ~ m1_subset_1(E_78,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2260,plain,(
    ! [E_329] :
      ( ~ r2_hidden(k4_tarski(E_329,'#skF_10'),'#skF_7')
      | ~ m1_subset_1(E_329,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2221,c_1006,c_36])).

tff(c_2264,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_7',k2_relat_1('#skF_7'),'#skF_10'),'#skF_6')
    | ~ r2_hidden('#skF_10',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_16,c_2260])).

tff(c_2270,plain,(
    ~ m1_subset_1('#skF_4'('#skF_7',k2_relat_1('#skF_7'),'#skF_10'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_2264])).

tff(c_3452,plain,(
    ~ r2_hidden('#skF_10',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_3449,c_2270])).

tff(c_3456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_3452])).

tff(c_3458,plain,(
    ~ r2_hidden('#skF_10',k2_relset_1('#skF_6','#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_3508,plain,(
    ~ r2_hidden('#skF_10',k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3507,c_3458])).

tff(c_44,plain,
    ( r2_hidden(k4_tarski('#skF_9','#skF_8'),'#skF_7')
    | r2_hidden('#skF_10',k2_relset_1('#skF_6','#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3479,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_3458,c_44])).

tff(c_3486,plain,(
    r2_hidden('#skF_8',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_3479,c_18])).

tff(c_42,plain,
    ( ~ r2_hidden('#skF_8',k2_relset_1('#skF_6','#skF_5','#skF_7'))
    | r2_hidden('#skF_10',k2_relset_1('#skF_6','#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3519,plain,(
    r2_hidden('#skF_10',k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3507,c_3486,c_3507,c_42])).

tff(c_3520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3508,c_3519])).

tff(c_3521,plain,(
    ! [A_85] : ~ r2_hidden(A_85,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_3609,plain,(
    ! [C_479] : ~ r2_hidden(C_479,k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_3587,c_3521])).

tff(c_3560,plain,(
    ! [A_473,B_474,C_475] :
      ( k2_relset_1(A_473,B_474,C_475) = k2_relat_1(C_475)
      | ~ m1_subset_1(C_475,k1_zfmisc_1(k2_zfmisc_1(A_473,B_474))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3564,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_3560])).

tff(c_3537,plain,(
    r2_hidden('#skF_10',k2_relset_1('#skF_6','#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_3566,plain,(
    r2_hidden('#skF_10',k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3564,c_3537])).

tff(c_3612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3609,c_3566])).

tff(c_3614,plain,(
    ~ r2_hidden('#skF_10',k2_relset_1('#skF_6','#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_3634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3614,c_3521,c_44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:15:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.61/2.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.73/2.08  
% 5.73/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.73/2.08  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 5.73/2.08  
% 5.73/2.08  %Foreground sorts:
% 5.73/2.08  
% 5.73/2.08  
% 5.73/2.08  %Background operators:
% 5.73/2.08  
% 5.73/2.08  
% 5.73/2.08  %Foreground operators:
% 5.73/2.08  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.73/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.73/2.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.73/2.08  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.73/2.08  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.73/2.08  tff('#skF_7', type, '#skF_7': $i).
% 5.73/2.08  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.73/2.08  tff('#skF_10', type, '#skF_10': $i).
% 5.73/2.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.73/2.08  tff('#skF_5', type, '#skF_5': $i).
% 5.73/2.08  tff('#skF_6', type, '#skF_6': $i).
% 5.73/2.08  tff('#skF_9', type, '#skF_9': $i).
% 5.73/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.73/2.08  tff('#skF_8', type, '#skF_8': $i).
% 5.73/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.73/2.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.73/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.73/2.08  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.73/2.08  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.73/2.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.73/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.73/2.08  
% 5.73/2.10  tff(f_62, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 5.73/2.10  tff(f_85, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (![D]: (r2_hidden(D, k2_relset_1(B, A, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(E, D), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relset_1)).
% 5.73/2.10  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.73/2.10  tff(f_54, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.73/2.10  tff(f_47, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 5.73/2.10  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 5.73/2.10  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 5.73/2.10  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 5.73/2.10  tff(c_3587, plain, (![A_478, C_479]: (r2_hidden(k4_tarski('#skF_4'(A_478, k2_relat_1(A_478), C_479), C_479), A_478) | ~r2_hidden(C_479, k2_relat_1(A_478)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.73/2.10  tff(c_30, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.73/2.10  tff(c_3503, plain, (![A_451, B_452, C_453]: (k2_relset_1(A_451, B_452, C_453)=k2_relat_1(C_453) | ~m1_subset_1(C_453, k1_zfmisc_1(k2_zfmisc_1(A_451, B_452))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.73/2.10  tff(c_3507, plain, (k2_relset_1('#skF_6', '#skF_5', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_30, c_3503])).
% 5.73/2.10  tff(c_1002, plain, (![A_211, B_212, C_213]: (k2_relset_1(A_211, B_212, C_213)=k2_relat_1(C_213) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(A_211, B_212))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.73/2.10  tff(c_1006, plain, (k2_relset_1('#skF_6', '#skF_5', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_30, c_1002])).
% 5.73/2.10  tff(c_46, plain, (m1_subset_1('#skF_9', '#skF_6') | r2_hidden('#skF_10', k2_relset_1('#skF_6', '#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.73/2.10  tff(c_64, plain, (r2_hidden('#skF_10', k2_relset_1('#skF_6', '#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_46])).
% 5.73/2.10  tff(c_1008, plain, (r2_hidden('#skF_10', k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1006, c_64])).
% 5.73/2.10  tff(c_16, plain, (![A_15, C_30]: (r2_hidden(k4_tarski('#skF_4'(A_15, k2_relat_1(A_15), C_30), C_30), A_15) | ~r2_hidden(C_30, k2_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.73/2.10  tff(c_53, plain, (![C_83, B_84, A_85]: (~v1_xboole_0(C_83) | ~m1_subset_1(B_84, k1_zfmisc_1(C_83)) | ~r2_hidden(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.73/2.10  tff(c_56, plain, (![A_85]: (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_5')) | ~r2_hidden(A_85, '#skF_7'))), inference(resolution, [status(thm)], [c_30, c_53])).
% 5.73/2.10  tff(c_57, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_56])).
% 5.73/2.10  tff(c_69, plain, (![A_89, C_90, B_91]: (m1_subset_1(A_89, C_90) | ~m1_subset_1(B_91, k1_zfmisc_1(C_90)) | ~r2_hidden(A_89, B_91))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.73/2.10  tff(c_72, plain, (![A_89]: (m1_subset_1(A_89, k2_zfmisc_1('#skF_6', '#skF_5')) | ~r2_hidden(A_89, '#skF_7'))), inference(resolution, [status(thm)], [c_30, c_69])).
% 5.73/2.10  tff(c_10, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.73/2.10  tff(c_79, plain, (![A_97, C_98, B_99, D_100]: (r2_hidden(A_97, C_98) | ~r2_hidden(k4_tarski(A_97, B_99), k2_zfmisc_1(C_98, D_100)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.73/2.10  tff(c_3346, plain, (![A_424, C_425, D_426, B_427]: (r2_hidden(A_424, C_425) | v1_xboole_0(k2_zfmisc_1(C_425, D_426)) | ~m1_subset_1(k4_tarski(A_424, B_427), k2_zfmisc_1(C_425, D_426)))), inference(resolution, [status(thm)], [c_10, c_79])).
% 5.73/2.10  tff(c_3357, plain, (![A_424, B_427]: (r2_hidden(A_424, '#skF_6') | v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_5')) | ~r2_hidden(k4_tarski(A_424, B_427), '#skF_7'))), inference(resolution, [status(thm)], [c_72, c_3346])).
% 5.73/2.10  tff(c_3363, plain, (![A_428, B_429]: (r2_hidden(A_428, '#skF_6') | ~r2_hidden(k4_tarski(A_428, B_429), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_57, c_3357])).
% 5.73/2.10  tff(c_3441, plain, (![C_434]: (r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_434), '#skF_6') | ~r2_hidden(C_434, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_16, c_3363])).
% 5.73/2.10  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.73/2.10  tff(c_3449, plain, (![C_435]: (m1_subset_1('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_435), '#skF_6') | ~r2_hidden(C_435, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_3441, c_8])).
% 5.73/2.10  tff(c_2126, plain, (![A_319, C_320, D_321, B_322]: (r2_hidden(A_319, C_320) | v1_xboole_0(k2_zfmisc_1(C_320, D_321)) | ~m1_subset_1(k4_tarski(A_319, B_322), k2_zfmisc_1(C_320, D_321)))), inference(resolution, [status(thm)], [c_10, c_79])).
% 5.73/2.10  tff(c_2137, plain, (![A_319, B_322]: (r2_hidden(A_319, '#skF_6') | v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_5')) | ~r2_hidden(k4_tarski(A_319, B_322), '#skF_7'))), inference(resolution, [status(thm)], [c_72, c_2126])).
% 5.73/2.10  tff(c_2143, plain, (![A_323, B_324]: (r2_hidden(A_323, '#skF_6') | ~r2_hidden(k4_tarski(A_323, B_324), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_57, c_2137])).
% 5.73/2.10  tff(c_2189, plain, (![C_325]: (r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_325), '#skF_6') | ~r2_hidden(C_325, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_16, c_2143])).
% 5.73/2.10  tff(c_2203, plain, (![C_326]: (m1_subset_1('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_326), '#skF_6') | ~r2_hidden(C_326, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_2189, c_8])).
% 5.73/2.10  tff(c_1074, plain, (![A_228, C_229]: (r2_hidden(k4_tarski('#skF_4'(A_228, k2_relat_1(A_228), C_229), C_229), A_228) | ~r2_hidden(C_229, k2_relat_1(A_228)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.73/2.10  tff(c_38, plain, (![E_78]: (r2_hidden(k4_tarski('#skF_9', '#skF_8'), '#skF_7') | ~r2_hidden(k4_tarski(E_78, '#skF_10'), '#skF_7') | ~m1_subset_1(E_78, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.73/2.10  tff(c_1040, plain, (![E_78]: (~r2_hidden(k4_tarski(E_78, '#skF_10'), '#skF_7') | ~m1_subset_1(E_78, '#skF_6'))), inference(splitLeft, [status(thm)], [c_38])).
% 5.73/2.10  tff(c_1080, plain, (~m1_subset_1('#skF_4'('#skF_7', k2_relat_1('#skF_7'), '#skF_10'), '#skF_6') | ~r2_hidden('#skF_10', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_1074, c_1040])).
% 5.73/2.10  tff(c_1101, plain, (~m1_subset_1('#skF_4'('#skF_7', k2_relat_1('#skF_7'), '#skF_10'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_1080])).
% 5.73/2.10  tff(c_2206, plain, (~r2_hidden('#skF_10', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_2203, c_1101])).
% 5.73/2.10  tff(c_2210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1008, c_2206])).
% 5.73/2.10  tff(c_2211, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_38])).
% 5.73/2.10  tff(c_18, plain, (![C_30, A_15, D_33]: (r2_hidden(C_30, k2_relat_1(A_15)) | ~r2_hidden(k4_tarski(D_33, C_30), A_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.73/2.10  tff(c_2221, plain, (r2_hidden('#skF_8', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_2211, c_18])).
% 5.73/2.10  tff(c_36, plain, (![E_78]: (~r2_hidden('#skF_8', k2_relset_1('#skF_6', '#skF_5', '#skF_7')) | ~r2_hidden(k4_tarski(E_78, '#skF_10'), '#skF_7') | ~m1_subset_1(E_78, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.73/2.10  tff(c_2260, plain, (![E_329]: (~r2_hidden(k4_tarski(E_329, '#skF_10'), '#skF_7') | ~m1_subset_1(E_329, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2221, c_1006, c_36])).
% 5.73/2.10  tff(c_2264, plain, (~m1_subset_1('#skF_4'('#skF_7', k2_relat_1('#skF_7'), '#skF_10'), '#skF_6') | ~r2_hidden('#skF_10', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_16, c_2260])).
% 5.73/2.10  tff(c_2270, plain, (~m1_subset_1('#skF_4'('#skF_7', k2_relat_1('#skF_7'), '#skF_10'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_2264])).
% 5.73/2.10  tff(c_3452, plain, (~r2_hidden('#skF_10', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_3449, c_2270])).
% 5.73/2.10  tff(c_3456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1008, c_3452])).
% 5.73/2.10  tff(c_3458, plain, (~r2_hidden('#skF_10', k2_relset_1('#skF_6', '#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_46])).
% 5.73/2.10  tff(c_3508, plain, (~r2_hidden('#skF_10', k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_3507, c_3458])).
% 5.73/2.10  tff(c_44, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_8'), '#skF_7') | r2_hidden('#skF_10', k2_relset_1('#skF_6', '#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.73/2.10  tff(c_3479, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_3458, c_44])).
% 5.73/2.10  tff(c_3486, plain, (r2_hidden('#skF_8', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_3479, c_18])).
% 5.73/2.10  tff(c_42, plain, (~r2_hidden('#skF_8', k2_relset_1('#skF_6', '#skF_5', '#skF_7')) | r2_hidden('#skF_10', k2_relset_1('#skF_6', '#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.73/2.10  tff(c_3519, plain, (r2_hidden('#skF_10', k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_3507, c_3486, c_3507, c_42])).
% 5.73/2.10  tff(c_3520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3508, c_3519])).
% 5.73/2.10  tff(c_3521, plain, (![A_85]: (~r2_hidden(A_85, '#skF_7'))), inference(splitRight, [status(thm)], [c_56])).
% 5.73/2.10  tff(c_3609, plain, (![C_479]: (~r2_hidden(C_479, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_3587, c_3521])).
% 5.73/2.10  tff(c_3560, plain, (![A_473, B_474, C_475]: (k2_relset_1(A_473, B_474, C_475)=k2_relat_1(C_475) | ~m1_subset_1(C_475, k1_zfmisc_1(k2_zfmisc_1(A_473, B_474))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.73/2.10  tff(c_3564, plain, (k2_relset_1('#skF_6', '#skF_5', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_30, c_3560])).
% 5.73/2.10  tff(c_3537, plain, (r2_hidden('#skF_10', k2_relset_1('#skF_6', '#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_46])).
% 5.73/2.10  tff(c_3566, plain, (r2_hidden('#skF_10', k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_3564, c_3537])).
% 5.73/2.10  tff(c_3612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3609, c_3566])).
% 5.73/2.10  tff(c_3614, plain, (~r2_hidden('#skF_10', k2_relset_1('#skF_6', '#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_46])).
% 5.73/2.10  tff(c_3634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3614, c_3521, c_44])).
% 5.73/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.73/2.10  
% 5.73/2.10  Inference rules
% 5.73/2.10  ----------------------
% 5.73/2.10  #Ref     : 0
% 5.73/2.10  #Sup     : 833
% 5.73/2.10  #Fact    : 0
% 5.73/2.10  #Define  : 0
% 5.73/2.10  #Split   : 18
% 5.73/2.10  #Chain   : 0
% 5.73/2.10  #Close   : 0
% 5.73/2.10  
% 5.73/2.10  Ordering : KBO
% 5.73/2.10  
% 5.73/2.10  Simplification rules
% 5.73/2.10  ----------------------
% 5.73/2.10  #Subsume      : 47
% 5.73/2.10  #Demod        : 93
% 5.73/2.10  #Tautology    : 72
% 5.73/2.10  #SimpNegUnit  : 15
% 5.73/2.10  #BackRed      : 51
% 5.73/2.10  
% 5.73/2.10  #Partial instantiations: 0
% 5.73/2.10  #Strategies tried      : 1
% 5.73/2.10  
% 5.73/2.10  Timing (in seconds)
% 5.73/2.10  ----------------------
% 5.73/2.10  Preprocessing        : 0.32
% 5.73/2.10  Parsing              : 0.16
% 5.73/2.10  CNF conversion       : 0.03
% 5.73/2.10  Main loop            : 1.01
% 5.73/2.10  Inferencing          : 0.35
% 5.73/2.11  Reduction            : 0.27
% 5.73/2.11  Demodulation         : 0.18
% 5.73/2.11  BG Simplification    : 0.04
% 5.73/2.11  Subsumption          : 0.25
% 5.73/2.11  Abstraction          : 0.05
% 5.73/2.11  MUC search           : 0.00
% 5.73/2.11  Cooper               : 0.00
% 5.73/2.11  Total                : 1.36
% 5.73/2.11  Index Insertion      : 0.00
% 5.73/2.11  Index Deletion       : 0.00
% 5.73/2.11  Index Matching       : 0.00
% 5.73/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
