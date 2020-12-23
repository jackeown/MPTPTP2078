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
% DateTime   : Thu Dec  3 10:07:11 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 424 expanded)
%              Number of leaves         :   29 ( 150 expanded)
%              Depth                    :   20
%              Number of atoms          :  150 ( 970 expanded)
%              Number of equality atoms :   35 ( 255 expanded)
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

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
        <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_54,plain,(
    ! [C_55,B_56,A_57] :
      ( v5_relat_1(C_55,B_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_57,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_58,plain,(
    v5_relat_1('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_54])).

tff(c_60,plain,(
    ! [A_58,B_59,C_60] :
      ( k2_relset_1(A_58,B_59,C_60) = k2_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_64,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_26,c_60])).

tff(c_32,plain,
    ( k2_relset_1('#skF_5','#skF_6','#skF_7') != '#skF_6'
    | r2_hidden('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_47,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_66,plain,(
    k2_relat_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_47])).

tff(c_16,plain,(
    ! [A_23,B_24] : v1_relat_1(k2_zfmisc_1(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_40,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_43,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_26,c_40])).

tff(c_46,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_43])).

tff(c_185,plain,(
    ! [A_87,B_88] :
      ( r2_hidden(k4_tarski('#skF_2'(A_87,B_88),'#skF_1'(A_87,B_88)),A_87)
      | r2_hidden('#skF_3'(A_87,B_88),B_88)
      | k2_relat_1(A_87) = B_88 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6,plain,(
    ! [C_19,A_4,D_22] :
      ( r2_hidden(C_19,k2_relat_1(A_4))
      | ~ r2_hidden(k4_tarski(D_22,C_19),A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_210,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_1'(A_89,B_90),k2_relat_1(A_89))
      | r2_hidden('#skF_3'(A_89,B_90),B_90)
      | k2_relat_1(A_89) = B_90 ) ),
    inference(resolution,[status(thm)],[c_185,c_6])).

tff(c_18,plain,(
    ! [C_28,A_25,B_26] :
      ( r2_hidden(C_28,A_25)
      | ~ r2_hidden(C_28,k2_relat_1(B_26))
      | ~ v5_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_217,plain,(
    ! [A_89,B_90,A_25] :
      ( r2_hidden('#skF_1'(A_89,B_90),A_25)
      | ~ v5_relat_1(A_89,A_25)
      | ~ v1_relat_1(A_89)
      | r2_hidden('#skF_3'(A_89,B_90),B_90)
      | k2_relat_1(A_89) = B_90 ) ),
    inference(resolution,[status(thm)],[c_210,c_18])).

tff(c_38,plain,(
    ! [D_41] :
      ( r2_hidden(k4_tarski('#skF_8'(D_41),D_41),'#skF_7')
      | ~ r2_hidden(D_41,'#skF_6')
      | k2_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_6' ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_76,plain,(
    ! [D_41] :
      ( r2_hidden(k4_tarski('#skF_8'(D_41),D_41),'#skF_7')
      | ~ r2_hidden(D_41,'#skF_6')
      | k2_relat_1('#skF_7') = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_38])).

tff(c_77,plain,(
    ! [D_41] :
      ( r2_hidden(k4_tarski('#skF_8'(D_41),D_41),'#skF_7')
      | ~ r2_hidden(D_41,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_76])).

tff(c_353,plain,(
    ! [A_101,B_102,D_103] :
      ( r2_hidden(k4_tarski('#skF_2'(A_101,B_102),'#skF_1'(A_101,B_102)),A_101)
      | ~ r2_hidden(k4_tarski(D_103,'#skF_3'(A_101,B_102)),A_101)
      | k2_relat_1(A_101) = B_102 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_386,plain,(
    ! [B_104] :
      ( r2_hidden(k4_tarski('#skF_2'('#skF_7',B_104),'#skF_1'('#skF_7',B_104)),'#skF_7')
      | k2_relat_1('#skF_7') = B_104
      | ~ r2_hidden('#skF_3'('#skF_7',B_104),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_77,c_353])).

tff(c_391,plain,(
    ! [B_105] :
      ( r2_hidden('#skF_1'('#skF_7',B_105),k2_relat_1('#skF_7'))
      | k2_relat_1('#skF_7') = B_105
      | ~ r2_hidden('#skF_3'('#skF_7',B_105),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_386,c_6])).

tff(c_396,plain,(
    ! [B_105,A_25] :
      ( r2_hidden('#skF_1'('#skF_7',B_105),A_25)
      | ~ v5_relat_1('#skF_7',A_25)
      | ~ v1_relat_1('#skF_7')
      | k2_relat_1('#skF_7') = B_105
      | ~ r2_hidden('#skF_3'('#skF_7',B_105),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_391,c_18])).

tff(c_402,plain,(
    ! [B_106,A_107] :
      ( r2_hidden('#skF_1'('#skF_7',B_106),A_107)
      | ~ v5_relat_1('#skF_7',A_107)
      | k2_relat_1('#skF_7') = B_106
      | ~ r2_hidden('#skF_3'('#skF_7',B_106),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_396])).

tff(c_405,plain,(
    ! [A_107,A_25] :
      ( r2_hidden('#skF_1'('#skF_7','#skF_6'),A_107)
      | ~ v5_relat_1('#skF_7',A_107)
      | r2_hidden('#skF_1'('#skF_7','#skF_6'),A_25)
      | ~ v5_relat_1('#skF_7',A_25)
      | ~ v1_relat_1('#skF_7')
      | k2_relat_1('#skF_7') = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_217,c_402])).

tff(c_412,plain,(
    ! [A_107,A_25] :
      ( r2_hidden('#skF_1'('#skF_7','#skF_6'),A_107)
      | ~ v5_relat_1('#skF_7',A_107)
      | r2_hidden('#skF_1'('#skF_7','#skF_6'),A_25)
      | ~ v5_relat_1('#skF_7',A_25)
      | k2_relat_1('#skF_7') = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_405])).

tff(c_413,plain,(
    ! [A_107,A_25] :
      ( r2_hidden('#skF_1'('#skF_7','#skF_6'),A_107)
      | ~ v5_relat_1('#skF_7',A_107)
      | r2_hidden('#skF_1'('#skF_7','#skF_6'),A_25)
      | ~ v5_relat_1('#skF_7',A_25) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_412])).

tff(c_416,plain,(
    ! [A_25] :
      ( r2_hidden('#skF_1'('#skF_7','#skF_6'),A_25)
      | ~ v5_relat_1('#skF_7',A_25) ) ),
    inference(splitLeft,[status(thm)],[c_413])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( ~ r2_hidden('#skF_1'(A_4,B_5),B_5)
      | r2_hidden('#skF_3'(A_4,B_5),B_5)
      | k2_relat_1(A_4) = B_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_417,plain,(
    ! [A_108] :
      ( r2_hidden('#skF_1'('#skF_7','#skF_6'),A_108)
      | ~ v5_relat_1('#skF_7',A_108) ) ),
    inference(splitLeft,[status(thm)],[c_413])).

tff(c_8,plain,(
    ! [A_4,B_5,D_18] :
      ( ~ r2_hidden('#skF_1'(A_4,B_5),B_5)
      | ~ r2_hidden(k4_tarski(D_18,'#skF_3'(A_4,B_5)),A_4)
      | k2_relat_1(A_4) = B_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_420,plain,(
    ! [D_18] :
      ( ~ r2_hidden(k4_tarski(D_18,'#skF_3'('#skF_7','#skF_6')),'#skF_7')
      | k2_relat_1('#skF_7') = '#skF_6'
      | ~ v5_relat_1('#skF_7','#skF_6') ) ),
    inference(resolution,[status(thm)],[c_417,c_8])).

tff(c_426,plain,(
    ! [D_18] :
      ( ~ r2_hidden(k4_tarski(D_18,'#skF_3'('#skF_7','#skF_6')),'#skF_7')
      | k2_relat_1('#skF_7') = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_420])).

tff(c_429,plain,(
    ! [D_109] : ~ r2_hidden(k4_tarski(D_109,'#skF_3'('#skF_7','#skF_6')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_426])).

tff(c_439,plain,(
    ~ r2_hidden('#skF_3'('#skF_7','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_77,c_429])).

tff(c_446,plain,
    ( ~ r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k2_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_12,c_439])).

tff(c_453,plain,(
    ~ r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_446])).

tff(c_456,plain,(
    ~ v5_relat_1('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_416,c_453])).

tff(c_461,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_456])).

tff(c_462,plain,(
    ! [A_107] :
      ( r2_hidden('#skF_1'('#skF_7','#skF_6'),A_107)
      | ~ v5_relat_1('#skF_7',A_107) ) ),
    inference(splitRight,[status(thm)],[c_413])).

tff(c_463,plain,(
    ! [A_110] :
      ( r2_hidden('#skF_1'('#skF_7','#skF_6'),A_110)
      | ~ v5_relat_1('#skF_7',A_110) ) ),
    inference(splitRight,[status(thm)],[c_413])).

tff(c_466,plain,(
    ! [D_18] :
      ( ~ r2_hidden(k4_tarski(D_18,'#skF_3'('#skF_7','#skF_6')),'#skF_7')
      | k2_relat_1('#skF_7') = '#skF_6'
      | ~ v5_relat_1('#skF_7','#skF_6') ) ),
    inference(resolution,[status(thm)],[c_463,c_8])).

tff(c_472,plain,(
    ! [D_18] :
      ( ~ r2_hidden(k4_tarski(D_18,'#skF_3'('#skF_7','#skF_6')),'#skF_7')
      | k2_relat_1('#skF_7') = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_466])).

tff(c_504,plain,(
    ! [D_113] : ~ r2_hidden(k4_tarski(D_113,'#skF_3'('#skF_7','#skF_6')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_472])).

tff(c_514,plain,(
    ~ r2_hidden('#skF_3'('#skF_7','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_77,c_504])).

tff(c_521,plain,
    ( ~ r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k2_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_12,c_514])).

tff(c_528,plain,(
    ~ r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_521])).

tff(c_531,plain,(
    ~ v5_relat_1('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_462,c_528])).

tff(c_536,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_531])).

tff(c_537,plain,(
    r2_hidden('#skF_9','#skF_6') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_538,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_28,plain,(
    ! [E_44] :
      ( k2_relset_1('#skF_5','#skF_6','#skF_7') != '#skF_6'
      | ~ r2_hidden(k4_tarski(E_44,'#skF_9'),'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_539,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_539])).

tff(c_547,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_566,plain,(
    ! [A_124,B_125,C_126] :
      ( k2_relset_1(A_124,B_125,C_126) = k2_relat_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_569,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_26,c_566])).

tff(c_571,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_569])).

tff(c_591,plain,(
    ! [A_133,C_134] :
      ( r2_hidden(k4_tarski('#skF_4'(A_133,k2_relat_1(A_133),C_134),C_134),A_133)
      | ~ r2_hidden(C_134,k2_relat_1(A_133)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_546,plain,(
    ! [E_44] : ~ r2_hidden(k4_tarski(E_44,'#skF_9'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_604,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_591,c_546])).

tff(c_614,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_571,c_604])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:06:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.36  
% 2.62/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.36  %$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_8 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_2 > #skF_1
% 2.62/1.36  
% 2.62/1.36  %Foreground sorts:
% 2.62/1.36  
% 2.62/1.36  
% 2.62/1.36  %Background operators:
% 2.62/1.36  
% 2.62/1.36  
% 2.62/1.36  %Foreground operators:
% 2.62/1.36  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.62/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.62/1.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.62/1.36  tff('#skF_8', type, '#skF_8': $i > $i).
% 2.62/1.36  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.62/1.36  tff('#skF_7', type, '#skF_7': $i).
% 2.62/1.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.62/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.62/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.62/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.62/1.36  tff('#skF_9', type, '#skF_9': $i).
% 2.62/1.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.62/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.62/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.62/1.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.62/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.62/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.36  
% 2.62/1.38  tff(f_74, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_relset_1)).
% 2.62/1.38  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.62/1.38  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.62/1.38  tff(f_42, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.62/1.38  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.62/1.38  tff(f_40, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 2.62/1.38  tff(f_51, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t202_relat_1)).
% 2.62/1.38  tff(c_26, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.62/1.38  tff(c_54, plain, (![C_55, B_56, A_57]: (v5_relat_1(C_55, B_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_57, B_56))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.62/1.38  tff(c_58, plain, (v5_relat_1('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_26, c_54])).
% 2.62/1.38  tff(c_60, plain, (![A_58, B_59, C_60]: (k2_relset_1(A_58, B_59, C_60)=k2_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.62/1.38  tff(c_64, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_26, c_60])).
% 2.62/1.38  tff(c_32, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')!='#skF_6' | r2_hidden('#skF_9', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.62/1.38  tff(c_47, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')!='#skF_6'), inference(splitLeft, [status(thm)], [c_32])).
% 2.62/1.38  tff(c_66, plain, (k2_relat_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_47])).
% 2.62/1.38  tff(c_16, plain, (![A_23, B_24]: (v1_relat_1(k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.62/1.38  tff(c_40, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.62/1.38  tff(c_43, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_26, c_40])).
% 2.62/1.38  tff(c_46, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_43])).
% 2.62/1.38  tff(c_185, plain, (![A_87, B_88]: (r2_hidden(k4_tarski('#skF_2'(A_87, B_88), '#skF_1'(A_87, B_88)), A_87) | r2_hidden('#skF_3'(A_87, B_88), B_88) | k2_relat_1(A_87)=B_88)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.62/1.38  tff(c_6, plain, (![C_19, A_4, D_22]: (r2_hidden(C_19, k2_relat_1(A_4)) | ~r2_hidden(k4_tarski(D_22, C_19), A_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.62/1.38  tff(c_210, plain, (![A_89, B_90]: (r2_hidden('#skF_1'(A_89, B_90), k2_relat_1(A_89)) | r2_hidden('#skF_3'(A_89, B_90), B_90) | k2_relat_1(A_89)=B_90)), inference(resolution, [status(thm)], [c_185, c_6])).
% 2.62/1.38  tff(c_18, plain, (![C_28, A_25, B_26]: (r2_hidden(C_28, A_25) | ~r2_hidden(C_28, k2_relat_1(B_26)) | ~v5_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.62/1.38  tff(c_217, plain, (![A_89, B_90, A_25]: (r2_hidden('#skF_1'(A_89, B_90), A_25) | ~v5_relat_1(A_89, A_25) | ~v1_relat_1(A_89) | r2_hidden('#skF_3'(A_89, B_90), B_90) | k2_relat_1(A_89)=B_90)), inference(resolution, [status(thm)], [c_210, c_18])).
% 2.62/1.38  tff(c_38, plain, (![D_41]: (r2_hidden(k4_tarski('#skF_8'(D_41), D_41), '#skF_7') | ~r2_hidden(D_41, '#skF_6') | k2_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_6')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.62/1.38  tff(c_76, plain, (![D_41]: (r2_hidden(k4_tarski('#skF_8'(D_41), D_41), '#skF_7') | ~r2_hidden(D_41, '#skF_6') | k2_relat_1('#skF_7')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_38])).
% 2.62/1.38  tff(c_77, plain, (![D_41]: (r2_hidden(k4_tarski('#skF_8'(D_41), D_41), '#skF_7') | ~r2_hidden(D_41, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_66, c_76])).
% 2.62/1.38  tff(c_353, plain, (![A_101, B_102, D_103]: (r2_hidden(k4_tarski('#skF_2'(A_101, B_102), '#skF_1'(A_101, B_102)), A_101) | ~r2_hidden(k4_tarski(D_103, '#skF_3'(A_101, B_102)), A_101) | k2_relat_1(A_101)=B_102)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.62/1.38  tff(c_386, plain, (![B_104]: (r2_hidden(k4_tarski('#skF_2'('#skF_7', B_104), '#skF_1'('#skF_7', B_104)), '#skF_7') | k2_relat_1('#skF_7')=B_104 | ~r2_hidden('#skF_3'('#skF_7', B_104), '#skF_6'))), inference(resolution, [status(thm)], [c_77, c_353])).
% 2.62/1.38  tff(c_391, plain, (![B_105]: (r2_hidden('#skF_1'('#skF_7', B_105), k2_relat_1('#skF_7')) | k2_relat_1('#skF_7')=B_105 | ~r2_hidden('#skF_3'('#skF_7', B_105), '#skF_6'))), inference(resolution, [status(thm)], [c_386, c_6])).
% 2.62/1.38  tff(c_396, plain, (![B_105, A_25]: (r2_hidden('#skF_1'('#skF_7', B_105), A_25) | ~v5_relat_1('#skF_7', A_25) | ~v1_relat_1('#skF_7') | k2_relat_1('#skF_7')=B_105 | ~r2_hidden('#skF_3'('#skF_7', B_105), '#skF_6'))), inference(resolution, [status(thm)], [c_391, c_18])).
% 2.62/1.38  tff(c_402, plain, (![B_106, A_107]: (r2_hidden('#skF_1'('#skF_7', B_106), A_107) | ~v5_relat_1('#skF_7', A_107) | k2_relat_1('#skF_7')=B_106 | ~r2_hidden('#skF_3'('#skF_7', B_106), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_396])).
% 2.62/1.38  tff(c_405, plain, (![A_107, A_25]: (r2_hidden('#skF_1'('#skF_7', '#skF_6'), A_107) | ~v5_relat_1('#skF_7', A_107) | r2_hidden('#skF_1'('#skF_7', '#skF_6'), A_25) | ~v5_relat_1('#skF_7', A_25) | ~v1_relat_1('#skF_7') | k2_relat_1('#skF_7')='#skF_6')), inference(resolution, [status(thm)], [c_217, c_402])).
% 2.62/1.38  tff(c_412, plain, (![A_107, A_25]: (r2_hidden('#skF_1'('#skF_7', '#skF_6'), A_107) | ~v5_relat_1('#skF_7', A_107) | r2_hidden('#skF_1'('#skF_7', '#skF_6'), A_25) | ~v5_relat_1('#skF_7', A_25) | k2_relat_1('#skF_7')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_405])).
% 2.62/1.38  tff(c_413, plain, (![A_107, A_25]: (r2_hidden('#skF_1'('#skF_7', '#skF_6'), A_107) | ~v5_relat_1('#skF_7', A_107) | r2_hidden('#skF_1'('#skF_7', '#skF_6'), A_25) | ~v5_relat_1('#skF_7', A_25))), inference(negUnitSimplification, [status(thm)], [c_66, c_412])).
% 2.62/1.38  tff(c_416, plain, (![A_25]: (r2_hidden('#skF_1'('#skF_7', '#skF_6'), A_25) | ~v5_relat_1('#skF_7', A_25))), inference(splitLeft, [status(thm)], [c_413])).
% 2.62/1.38  tff(c_12, plain, (![A_4, B_5]: (~r2_hidden('#skF_1'(A_4, B_5), B_5) | r2_hidden('#skF_3'(A_4, B_5), B_5) | k2_relat_1(A_4)=B_5)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.62/1.38  tff(c_417, plain, (![A_108]: (r2_hidden('#skF_1'('#skF_7', '#skF_6'), A_108) | ~v5_relat_1('#skF_7', A_108))), inference(splitLeft, [status(thm)], [c_413])).
% 2.62/1.38  tff(c_8, plain, (![A_4, B_5, D_18]: (~r2_hidden('#skF_1'(A_4, B_5), B_5) | ~r2_hidden(k4_tarski(D_18, '#skF_3'(A_4, B_5)), A_4) | k2_relat_1(A_4)=B_5)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.62/1.38  tff(c_420, plain, (![D_18]: (~r2_hidden(k4_tarski(D_18, '#skF_3'('#skF_7', '#skF_6')), '#skF_7') | k2_relat_1('#skF_7')='#skF_6' | ~v5_relat_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_417, c_8])).
% 2.62/1.38  tff(c_426, plain, (![D_18]: (~r2_hidden(k4_tarski(D_18, '#skF_3'('#skF_7', '#skF_6')), '#skF_7') | k2_relat_1('#skF_7')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_420])).
% 2.62/1.38  tff(c_429, plain, (![D_109]: (~r2_hidden(k4_tarski(D_109, '#skF_3'('#skF_7', '#skF_6')), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_66, c_426])).
% 2.62/1.38  tff(c_439, plain, (~r2_hidden('#skF_3'('#skF_7', '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_77, c_429])).
% 2.62/1.38  tff(c_446, plain, (~r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6') | k2_relat_1('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_12, c_439])).
% 2.62/1.38  tff(c_453, plain, (~r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_66, c_446])).
% 2.62/1.38  tff(c_456, plain, (~v5_relat_1('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_416, c_453])).
% 2.62/1.38  tff(c_461, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_456])).
% 2.62/1.38  tff(c_462, plain, (![A_107]: (r2_hidden('#skF_1'('#skF_7', '#skF_6'), A_107) | ~v5_relat_1('#skF_7', A_107))), inference(splitRight, [status(thm)], [c_413])).
% 2.62/1.38  tff(c_463, plain, (![A_110]: (r2_hidden('#skF_1'('#skF_7', '#skF_6'), A_110) | ~v5_relat_1('#skF_7', A_110))), inference(splitRight, [status(thm)], [c_413])).
% 2.62/1.38  tff(c_466, plain, (![D_18]: (~r2_hidden(k4_tarski(D_18, '#skF_3'('#skF_7', '#skF_6')), '#skF_7') | k2_relat_1('#skF_7')='#skF_6' | ~v5_relat_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_463, c_8])).
% 2.62/1.38  tff(c_472, plain, (![D_18]: (~r2_hidden(k4_tarski(D_18, '#skF_3'('#skF_7', '#skF_6')), '#skF_7') | k2_relat_1('#skF_7')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_466])).
% 2.62/1.38  tff(c_504, plain, (![D_113]: (~r2_hidden(k4_tarski(D_113, '#skF_3'('#skF_7', '#skF_6')), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_66, c_472])).
% 2.62/1.38  tff(c_514, plain, (~r2_hidden('#skF_3'('#skF_7', '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_77, c_504])).
% 2.62/1.38  tff(c_521, plain, (~r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6') | k2_relat_1('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_12, c_514])).
% 2.62/1.38  tff(c_528, plain, (~r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_66, c_521])).
% 2.62/1.38  tff(c_531, plain, (~v5_relat_1('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_462, c_528])).
% 2.62/1.38  tff(c_536, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_531])).
% 2.62/1.38  tff(c_537, plain, (r2_hidden('#skF_9', '#skF_6')), inference(splitRight, [status(thm)], [c_32])).
% 2.62/1.38  tff(c_538, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_32])).
% 2.62/1.38  tff(c_28, plain, (![E_44]: (k2_relset_1('#skF_5', '#skF_6', '#skF_7')!='#skF_6' | ~r2_hidden(k4_tarski(E_44, '#skF_9'), '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.62/1.38  tff(c_539, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')!='#skF_6'), inference(splitLeft, [status(thm)], [c_28])).
% 2.62/1.38  tff(c_545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_538, c_539])).
% 2.62/1.38  tff(c_547, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_28])).
% 2.62/1.38  tff(c_566, plain, (![A_124, B_125, C_126]: (k2_relset_1(A_124, B_125, C_126)=k2_relat_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.62/1.38  tff(c_569, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_26, c_566])).
% 2.62/1.38  tff(c_571, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_547, c_569])).
% 2.62/1.38  tff(c_591, plain, (![A_133, C_134]: (r2_hidden(k4_tarski('#skF_4'(A_133, k2_relat_1(A_133), C_134), C_134), A_133) | ~r2_hidden(C_134, k2_relat_1(A_133)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.62/1.38  tff(c_546, plain, (![E_44]: (~r2_hidden(k4_tarski(E_44, '#skF_9'), '#skF_7'))), inference(splitRight, [status(thm)], [c_28])).
% 2.62/1.38  tff(c_604, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_591, c_546])).
% 2.62/1.38  tff(c_614, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_537, c_571, c_604])).
% 2.62/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.38  
% 2.62/1.38  Inference rules
% 2.62/1.38  ----------------------
% 2.62/1.38  #Ref     : 0
% 2.62/1.38  #Sup     : 115
% 2.62/1.38  #Fact    : 0
% 2.62/1.38  #Define  : 0
% 2.62/1.38  #Split   : 6
% 2.62/1.38  #Chain   : 0
% 2.62/1.38  #Close   : 0
% 2.62/1.38  
% 2.62/1.38  Ordering : KBO
% 2.62/1.38  
% 2.62/1.38  Simplification rules
% 2.62/1.38  ----------------------
% 2.62/1.38  #Subsume      : 8
% 2.62/1.38  #Demod        : 21
% 2.62/1.38  #Tautology    : 19
% 2.62/1.38  #SimpNegUnit  : 9
% 2.62/1.38  #BackRed      : 1
% 2.62/1.38  
% 2.62/1.38  #Partial instantiations: 0
% 2.62/1.38  #Strategies tried      : 1
% 2.62/1.38  
% 2.62/1.38  Timing (in seconds)
% 2.62/1.38  ----------------------
% 2.62/1.38  Preprocessing        : 0.29
% 2.62/1.38  Parsing              : 0.15
% 2.62/1.38  CNF conversion       : 0.02
% 2.62/1.38  Main loop            : 0.32
% 2.62/1.38  Inferencing          : 0.12
% 2.62/1.38  Reduction            : 0.08
% 2.62/1.38  Demodulation         : 0.05
% 2.62/1.38  BG Simplification    : 0.02
% 2.62/1.38  Subsumption          : 0.07
% 2.62/1.38  Abstraction          : 0.02
% 2.86/1.38  MUC search           : 0.00
% 2.86/1.38  Cooper               : 0.00
% 2.86/1.38  Total                : 0.65
% 2.86/1.38  Index Insertion      : 0.00
% 2.86/1.38  Index Deletion       : 0.00
% 2.86/1.38  Index Matching       : 0.00
% 2.86/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
