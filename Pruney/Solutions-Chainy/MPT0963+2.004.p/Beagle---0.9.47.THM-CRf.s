%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:59 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 407 expanded)
%              Number of leaves         :   26 ( 165 expanded)
%              Depth                    :   11
%              Number of atoms          :  203 (1608 expanded)
%              Number of equality atoms :   35 ( 250 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( k1_relat_1(C) = A
            & ! [D] :
                ( r2_hidden(D,A)
               => r2_hidden(k1_funct_1(C,D),B) ) )
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( r2_hidden(D,k1_relat_1(A))
                & r2_hidden(k1_funct_1(A,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_34,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_600,plain,(
    ! [B_109,A_110] :
      ( m1_subset_1(B_109,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_109),A_110)))
      | ~ r1_tarski(k2_relat_1(B_109),A_110)
      | ~ v1_funct_1(B_109)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_603,plain,(
    ! [A_110] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_110)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_110)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_600])).

tff(c_606,plain,(
    ! [A_111] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_111)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_603])).

tff(c_30,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_40,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30])).

tff(c_60,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_46,plain,(
    ! [A_21] :
      ( k9_relat_1(A_21,k1_relat_1(A_21)) = k2_relat_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,
    ( k9_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_46])).

tff(c_59,plain,(
    k9_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_55])).

tff(c_138,plain,(
    ! [A_47,B_48,C_49] :
      ( r2_hidden('#skF_1'(A_47,B_48,C_49),k1_relat_1(A_47))
      | r2_hidden('#skF_2'(A_47,B_48,C_49),C_49)
      | k10_relat_1(A_47,B_48) = C_49
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_149,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_1'('#skF_5',B_48,C_49),'#skF_3')
      | r2_hidden('#skF_2'('#skF_5',B_48,C_49),C_49)
      | k10_relat_1('#skF_5',B_48) = C_49
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_138])).

tff(c_154,plain,(
    ! [B_50,C_51] :
      ( r2_hidden('#skF_1'('#skF_5',B_50,C_51),'#skF_3')
      | r2_hidden('#skF_2'('#skF_5',B_50,C_51),C_51)
      | k10_relat_1('#skF_5',B_50) = C_51 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_149])).

tff(c_16,plain,(
    ! [A_2,B_9,C_10] :
      ( ~ r2_hidden('#skF_1'(A_2,B_9,C_10),C_10)
      | r2_hidden('#skF_2'(A_2,B_9,C_10),C_10)
      | k10_relat_1(A_2,B_9) = C_10
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_158,plain,(
    ! [B_50] :
      ( ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | r2_hidden('#skF_2'('#skF_5',B_50,'#skF_3'),'#skF_3')
      | k10_relat_1('#skF_5',B_50) = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_154,c_16])).

tff(c_165,plain,(
    ! [B_50] :
      ( r2_hidden('#skF_2'('#skF_5',B_50,'#skF_3'),'#skF_3')
      | k10_relat_1('#skF_5',B_50) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_158])).

tff(c_32,plain,(
    ! [D_19] :
      ( r2_hidden(k1_funct_1('#skF_5',D_19),'#skF_4')
      | ~ r2_hidden(D_19,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_324,plain,(
    ! [A_85,B_86,C_87] :
      ( r2_hidden('#skF_1'(A_85,B_86,C_87),k1_relat_1(A_85))
      | ~ r2_hidden(k1_funct_1(A_85,'#skF_2'(A_85,B_86,C_87)),B_86)
      | ~ r2_hidden('#skF_2'(A_85,B_86,C_87),k1_relat_1(A_85))
      | k10_relat_1(A_85,B_86) = C_87
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_344,plain,(
    ! [C_87] :
      ( r2_hidden('#skF_1'('#skF_5','#skF_4',C_87),k1_relat_1('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5','#skF_4',C_87),k1_relat_1('#skF_5'))
      | k10_relat_1('#skF_5','#skF_4') = C_87
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden('#skF_2'('#skF_5','#skF_4',C_87),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_324])).

tff(c_372,plain,(
    ! [C_91] :
      ( r2_hidden('#skF_1'('#skF_5','#skF_4',C_91),'#skF_3')
      | k10_relat_1('#skF_5','#skF_4') = C_91
      | ~ r2_hidden('#skF_2'('#skF_5','#skF_4',C_91),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_34,c_344])).

tff(c_10,plain,(
    ! [A_2,B_9,C_10] :
      ( ~ r2_hidden('#skF_1'(A_2,B_9,C_10),C_10)
      | ~ r2_hidden(k1_funct_1(A_2,'#skF_2'(A_2,B_9,C_10)),B_9)
      | ~ r2_hidden('#skF_2'(A_2,B_9,C_10),k1_relat_1(A_2))
      | k10_relat_1(A_2,B_9) = C_10
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_375,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_4','#skF_3')),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_5','#skF_4','#skF_3'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | k10_relat_1('#skF_5','#skF_4') = '#skF_3'
    | ~ r2_hidden('#skF_2'('#skF_5','#skF_4','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_372,c_10])).

tff(c_386,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_4','#skF_3')),'#skF_4')
    | k10_relat_1('#skF_5','#skF_4') = '#skF_3'
    | ~ r2_hidden('#skF_2'('#skF_5','#skF_4','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_375])).

tff(c_393,plain,(
    ~ r2_hidden('#skF_2'('#skF_5','#skF_4','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_386])).

tff(c_401,plain,(
    k10_relat_1('#skF_5','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_165,c_393])).

tff(c_22,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k9_relat_1(B_15,k10_relat_1(B_15,A_14)),A_14)
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_445,plain,
    ( r1_tarski(k9_relat_1('#skF_5','#skF_3'),'#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_22])).

tff(c_463,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_59,c_445])).

tff(c_67,plain,(
    ! [B_27,A_28] :
      ( v1_funct_2(B_27,k1_relat_1(B_27),A_28)
      | ~ r1_tarski(k2_relat_1(B_27),A_28)
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_70,plain,(
    ! [A_28] :
      ( v1_funct_2('#skF_5','#skF_3',A_28)
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_28)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_67])).

tff(c_72,plain,(
    ! [A_28] :
      ( v1_funct_2('#skF_5','#skF_3',A_28)
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_70])).

tff(c_467,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_463,c_72])).

tff(c_471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_467])).

tff(c_473,plain,(
    r2_hidden('#skF_2'('#skF_5','#skF_4','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_386])).

tff(c_472,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_4','#skF_3')),'#skF_4')
    | k10_relat_1('#skF_5','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_386])).

tff(c_474,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_4','#skF_3')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_472])).

tff(c_480,plain,(
    ~ r2_hidden('#skF_2'('#skF_5','#skF_4','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_474])).

tff(c_487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_480])).

tff(c_488,plain,(
    k10_relat_1('#skF_5','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_551,plain,
    ( r1_tarski(k9_relat_1('#skF_5','#skF_3'),'#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_488,c_22])).

tff(c_570,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_59,c_551])).

tff(c_574,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_570,c_72])).

tff(c_578,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_574])).

tff(c_579,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_610,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_606,c_579])).

tff(c_655,plain,(
    ! [A_121,B_122,C_123] :
      ( r2_hidden('#skF_1'(A_121,B_122,C_123),k1_relat_1(A_121))
      | r2_hidden('#skF_2'(A_121,B_122,C_123),C_123)
      | k10_relat_1(A_121,B_122) = C_123
      | ~ v1_funct_1(A_121)
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_666,plain,(
    ! [B_122,C_123] :
      ( r2_hidden('#skF_1'('#skF_5',B_122,C_123),'#skF_3')
      | r2_hidden('#skF_2'('#skF_5',B_122,C_123),C_123)
      | k10_relat_1('#skF_5',B_122) = C_123
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_655])).

tff(c_671,plain,(
    ! [B_124,C_125] :
      ( r2_hidden('#skF_1'('#skF_5',B_124,C_125),'#skF_3')
      | r2_hidden('#skF_2'('#skF_5',B_124,C_125),C_125)
      | k10_relat_1('#skF_5',B_124) = C_125 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_666])).

tff(c_675,plain,(
    ! [B_124] :
      ( ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | r2_hidden('#skF_2'('#skF_5',B_124,'#skF_3'),'#skF_3')
      | k10_relat_1('#skF_5',B_124) = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_671,c_16])).

tff(c_682,plain,(
    ! [B_124] :
      ( r2_hidden('#skF_2'('#skF_5',B_124,'#skF_3'),'#skF_3')
      | k10_relat_1('#skF_5',B_124) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_675])).

tff(c_781,plain,(
    ! [A_149,B_150,C_151] :
      ( r2_hidden('#skF_1'(A_149,B_150,C_151),k1_relat_1(A_149))
      | ~ r2_hidden(k1_funct_1(A_149,'#skF_2'(A_149,B_150,C_151)),B_150)
      | ~ r2_hidden('#skF_2'(A_149,B_150,C_151),k1_relat_1(A_149))
      | k10_relat_1(A_149,B_150) = C_151
      | ~ v1_funct_1(A_149)
      | ~ v1_relat_1(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_797,plain,(
    ! [C_151] :
      ( r2_hidden('#skF_1'('#skF_5','#skF_4',C_151),k1_relat_1('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5','#skF_4',C_151),k1_relat_1('#skF_5'))
      | k10_relat_1('#skF_5','#skF_4') = C_151
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden('#skF_2'('#skF_5','#skF_4',C_151),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_781])).

tff(c_804,plain,(
    ! [C_152] :
      ( r2_hidden('#skF_1'('#skF_5','#skF_4',C_152),'#skF_3')
      | k10_relat_1('#skF_5','#skF_4') = C_152
      | ~ r2_hidden('#skF_2'('#skF_5','#skF_4',C_152),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_34,c_797])).

tff(c_807,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_4','#skF_3')),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_5','#skF_4','#skF_3'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | k10_relat_1('#skF_5','#skF_4') = '#skF_3'
    | ~ r2_hidden('#skF_2'('#skF_5','#skF_4','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_804,c_10])).

tff(c_818,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_4','#skF_3')),'#skF_4')
    | k10_relat_1('#skF_5','#skF_4') = '#skF_3'
    | ~ r2_hidden('#skF_2'('#skF_5','#skF_4','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_807])).

tff(c_825,plain,(
    ~ r2_hidden('#skF_2'('#skF_5','#skF_4','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_818])).

tff(c_832,plain,(
    k10_relat_1('#skF_5','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_682,c_825])).

tff(c_878,plain,
    ( r1_tarski(k9_relat_1('#skF_5','#skF_3'),'#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_832,c_22])).

tff(c_889,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_59,c_878])).

tff(c_891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_610,c_889])).

tff(c_893,plain,(
    r2_hidden('#skF_2'('#skF_5','#skF_4','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_818])).

tff(c_892,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_4','#skF_3')),'#skF_4')
    | k10_relat_1('#skF_5','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_818])).

tff(c_894,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_4','#skF_3')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_892])).

tff(c_900,plain,(
    ~ r2_hidden('#skF_2'('#skF_5','#skF_4','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_894])).

tff(c_907,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_893,c_900])).

tff(c_908,plain,(
    k10_relat_1('#skF_5','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_892])).

tff(c_930,plain,
    ( r1_tarski(k9_relat_1('#skF_5','#skF_3'),'#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_908,c_22])).

tff(c_941,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_59,c_930])).

tff(c_943,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_610,c_941])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:00:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.55  
% 3.44/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.55  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 3.44/1.55  
% 3.44/1.55  %Foreground sorts:
% 3.44/1.55  
% 3.44/1.55  
% 3.44/1.55  %Background operators:
% 3.44/1.55  
% 3.44/1.55  
% 3.44/1.55  %Foreground operators:
% 3.44/1.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.44/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.44/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.44/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.44/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.44/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.44/1.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.44/1.55  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.44/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.44/1.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.44/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.44/1.55  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.44/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.55  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.44/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.44/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.44/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.44/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.44/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.44/1.55  
% 3.44/1.56  tff(f_79, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_funct_2)).
% 3.44/1.56  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 3.44/1.56  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 3.44/1.56  tff(f_43, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, k1_relat_1(A)) & r2_hidden(k1_funct_1(A, D), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_1)).
% 3.44/1.56  tff(f_49, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 3.44/1.56  tff(c_38, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.44/1.56  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.44/1.56  tff(c_34, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.44/1.56  tff(c_600, plain, (![B_109, A_110]: (m1_subset_1(B_109, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_109), A_110))) | ~r1_tarski(k2_relat_1(B_109), A_110) | ~v1_funct_1(B_109) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.44/1.56  tff(c_603, plain, (![A_110]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_110))) | ~r1_tarski(k2_relat_1('#skF_5'), A_110) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_600])).
% 3.44/1.56  tff(c_606, plain, (![A_111]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_111))) | ~r1_tarski(k2_relat_1('#skF_5'), A_111))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_603])).
% 3.44/1.56  tff(c_30, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.44/1.56  tff(c_40, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30])).
% 3.44/1.56  tff(c_60, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_40])).
% 3.44/1.56  tff(c_46, plain, (![A_21]: (k9_relat_1(A_21, k1_relat_1(A_21))=k2_relat_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.44/1.56  tff(c_55, plain, (k9_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_34, c_46])).
% 3.44/1.56  tff(c_59, plain, (k9_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_55])).
% 3.44/1.56  tff(c_138, plain, (![A_47, B_48, C_49]: (r2_hidden('#skF_1'(A_47, B_48, C_49), k1_relat_1(A_47)) | r2_hidden('#skF_2'(A_47, B_48, C_49), C_49) | k10_relat_1(A_47, B_48)=C_49 | ~v1_funct_1(A_47) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.44/1.56  tff(c_149, plain, (![B_48, C_49]: (r2_hidden('#skF_1'('#skF_5', B_48, C_49), '#skF_3') | r2_hidden('#skF_2'('#skF_5', B_48, C_49), C_49) | k10_relat_1('#skF_5', B_48)=C_49 | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_138])).
% 3.44/1.56  tff(c_154, plain, (![B_50, C_51]: (r2_hidden('#skF_1'('#skF_5', B_50, C_51), '#skF_3') | r2_hidden('#skF_2'('#skF_5', B_50, C_51), C_51) | k10_relat_1('#skF_5', B_50)=C_51)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_149])).
% 3.44/1.56  tff(c_16, plain, (![A_2, B_9, C_10]: (~r2_hidden('#skF_1'(A_2, B_9, C_10), C_10) | r2_hidden('#skF_2'(A_2, B_9, C_10), C_10) | k10_relat_1(A_2, B_9)=C_10 | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.44/1.56  tff(c_158, plain, (![B_50]: (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | r2_hidden('#skF_2'('#skF_5', B_50, '#skF_3'), '#skF_3') | k10_relat_1('#skF_5', B_50)='#skF_3')), inference(resolution, [status(thm)], [c_154, c_16])).
% 3.44/1.56  tff(c_165, plain, (![B_50]: (r2_hidden('#skF_2'('#skF_5', B_50, '#skF_3'), '#skF_3') | k10_relat_1('#skF_5', B_50)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_158])).
% 3.44/1.56  tff(c_32, plain, (![D_19]: (r2_hidden(k1_funct_1('#skF_5', D_19), '#skF_4') | ~r2_hidden(D_19, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.44/1.56  tff(c_324, plain, (![A_85, B_86, C_87]: (r2_hidden('#skF_1'(A_85, B_86, C_87), k1_relat_1(A_85)) | ~r2_hidden(k1_funct_1(A_85, '#skF_2'(A_85, B_86, C_87)), B_86) | ~r2_hidden('#skF_2'(A_85, B_86, C_87), k1_relat_1(A_85)) | k10_relat_1(A_85, B_86)=C_87 | ~v1_funct_1(A_85) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.44/1.56  tff(c_344, plain, (![C_87]: (r2_hidden('#skF_1'('#skF_5', '#skF_4', C_87), k1_relat_1('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5', '#skF_4', C_87), k1_relat_1('#skF_5')) | k10_relat_1('#skF_5', '#skF_4')=C_87 | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden('#skF_2'('#skF_5', '#skF_4', C_87), '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_324])).
% 3.44/1.56  tff(c_372, plain, (![C_91]: (r2_hidden('#skF_1'('#skF_5', '#skF_4', C_91), '#skF_3') | k10_relat_1('#skF_5', '#skF_4')=C_91 | ~r2_hidden('#skF_2'('#skF_5', '#skF_4', C_91), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_34, c_344])).
% 3.44/1.56  tff(c_10, plain, (![A_2, B_9, C_10]: (~r2_hidden('#skF_1'(A_2, B_9, C_10), C_10) | ~r2_hidden(k1_funct_1(A_2, '#skF_2'(A_2, B_9, C_10)), B_9) | ~r2_hidden('#skF_2'(A_2, B_9, C_10), k1_relat_1(A_2)) | k10_relat_1(A_2, B_9)=C_10 | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.44/1.56  tff(c_375, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_4', '#skF_3')), '#skF_4') | ~r2_hidden('#skF_2'('#skF_5', '#skF_4', '#skF_3'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | k10_relat_1('#skF_5', '#skF_4')='#skF_3' | ~r2_hidden('#skF_2'('#skF_5', '#skF_4', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_372, c_10])).
% 3.44/1.56  tff(c_386, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_4', '#skF_3')), '#skF_4') | k10_relat_1('#skF_5', '#skF_4')='#skF_3' | ~r2_hidden('#skF_2'('#skF_5', '#skF_4', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_375])).
% 3.44/1.56  tff(c_393, plain, (~r2_hidden('#skF_2'('#skF_5', '#skF_4', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_386])).
% 3.44/1.56  tff(c_401, plain, (k10_relat_1('#skF_5', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_165, c_393])).
% 3.44/1.56  tff(c_22, plain, (![B_15, A_14]: (r1_tarski(k9_relat_1(B_15, k10_relat_1(B_15, A_14)), A_14) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.44/1.56  tff(c_445, plain, (r1_tarski(k9_relat_1('#skF_5', '#skF_3'), '#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_401, c_22])).
% 3.44/1.56  tff(c_463, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_59, c_445])).
% 3.44/1.56  tff(c_67, plain, (![B_27, A_28]: (v1_funct_2(B_27, k1_relat_1(B_27), A_28) | ~r1_tarski(k2_relat_1(B_27), A_28) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.44/1.56  tff(c_70, plain, (![A_28]: (v1_funct_2('#skF_5', '#skF_3', A_28) | ~r1_tarski(k2_relat_1('#skF_5'), A_28) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_67])).
% 3.44/1.56  tff(c_72, plain, (![A_28]: (v1_funct_2('#skF_5', '#skF_3', A_28) | ~r1_tarski(k2_relat_1('#skF_5'), A_28))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_70])).
% 3.44/1.56  tff(c_467, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_463, c_72])).
% 3.44/1.56  tff(c_471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_467])).
% 3.44/1.56  tff(c_473, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_4', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_386])).
% 3.44/1.56  tff(c_472, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_4', '#skF_3')), '#skF_4') | k10_relat_1('#skF_5', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_386])).
% 3.44/1.56  tff(c_474, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_4', '#skF_3')), '#skF_4')), inference(splitLeft, [status(thm)], [c_472])).
% 3.44/1.56  tff(c_480, plain, (~r2_hidden('#skF_2'('#skF_5', '#skF_4', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_32, c_474])).
% 3.44/1.56  tff(c_487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_473, c_480])).
% 3.44/1.56  tff(c_488, plain, (k10_relat_1('#skF_5', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_472])).
% 3.44/1.56  tff(c_551, plain, (r1_tarski(k9_relat_1('#skF_5', '#skF_3'), '#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_488, c_22])).
% 3.44/1.56  tff(c_570, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_59, c_551])).
% 3.44/1.56  tff(c_574, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_570, c_72])).
% 3.44/1.56  tff(c_578, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_574])).
% 3.44/1.56  tff(c_579, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_40])).
% 3.44/1.56  tff(c_610, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_606, c_579])).
% 3.44/1.56  tff(c_655, plain, (![A_121, B_122, C_123]: (r2_hidden('#skF_1'(A_121, B_122, C_123), k1_relat_1(A_121)) | r2_hidden('#skF_2'(A_121, B_122, C_123), C_123) | k10_relat_1(A_121, B_122)=C_123 | ~v1_funct_1(A_121) | ~v1_relat_1(A_121))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.44/1.56  tff(c_666, plain, (![B_122, C_123]: (r2_hidden('#skF_1'('#skF_5', B_122, C_123), '#skF_3') | r2_hidden('#skF_2'('#skF_5', B_122, C_123), C_123) | k10_relat_1('#skF_5', B_122)=C_123 | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_655])).
% 3.44/1.56  tff(c_671, plain, (![B_124, C_125]: (r2_hidden('#skF_1'('#skF_5', B_124, C_125), '#skF_3') | r2_hidden('#skF_2'('#skF_5', B_124, C_125), C_125) | k10_relat_1('#skF_5', B_124)=C_125)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_666])).
% 3.44/1.56  tff(c_675, plain, (![B_124]: (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | r2_hidden('#skF_2'('#skF_5', B_124, '#skF_3'), '#skF_3') | k10_relat_1('#skF_5', B_124)='#skF_3')), inference(resolution, [status(thm)], [c_671, c_16])).
% 3.44/1.56  tff(c_682, plain, (![B_124]: (r2_hidden('#skF_2'('#skF_5', B_124, '#skF_3'), '#skF_3') | k10_relat_1('#skF_5', B_124)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_675])).
% 3.44/1.56  tff(c_781, plain, (![A_149, B_150, C_151]: (r2_hidden('#skF_1'(A_149, B_150, C_151), k1_relat_1(A_149)) | ~r2_hidden(k1_funct_1(A_149, '#skF_2'(A_149, B_150, C_151)), B_150) | ~r2_hidden('#skF_2'(A_149, B_150, C_151), k1_relat_1(A_149)) | k10_relat_1(A_149, B_150)=C_151 | ~v1_funct_1(A_149) | ~v1_relat_1(A_149))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.44/1.56  tff(c_797, plain, (![C_151]: (r2_hidden('#skF_1'('#skF_5', '#skF_4', C_151), k1_relat_1('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5', '#skF_4', C_151), k1_relat_1('#skF_5')) | k10_relat_1('#skF_5', '#skF_4')=C_151 | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden('#skF_2'('#skF_5', '#skF_4', C_151), '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_781])).
% 3.44/1.56  tff(c_804, plain, (![C_152]: (r2_hidden('#skF_1'('#skF_5', '#skF_4', C_152), '#skF_3') | k10_relat_1('#skF_5', '#skF_4')=C_152 | ~r2_hidden('#skF_2'('#skF_5', '#skF_4', C_152), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_34, c_797])).
% 3.44/1.56  tff(c_807, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_4', '#skF_3')), '#skF_4') | ~r2_hidden('#skF_2'('#skF_5', '#skF_4', '#skF_3'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | k10_relat_1('#skF_5', '#skF_4')='#skF_3' | ~r2_hidden('#skF_2'('#skF_5', '#skF_4', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_804, c_10])).
% 3.44/1.56  tff(c_818, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_4', '#skF_3')), '#skF_4') | k10_relat_1('#skF_5', '#skF_4')='#skF_3' | ~r2_hidden('#skF_2'('#skF_5', '#skF_4', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_807])).
% 3.44/1.56  tff(c_825, plain, (~r2_hidden('#skF_2'('#skF_5', '#skF_4', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_818])).
% 3.44/1.56  tff(c_832, plain, (k10_relat_1('#skF_5', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_682, c_825])).
% 3.44/1.56  tff(c_878, plain, (r1_tarski(k9_relat_1('#skF_5', '#skF_3'), '#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_832, c_22])).
% 3.44/1.56  tff(c_889, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_59, c_878])).
% 3.44/1.56  tff(c_891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_610, c_889])).
% 3.44/1.56  tff(c_893, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_4', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_818])).
% 3.44/1.56  tff(c_892, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_4', '#skF_3')), '#skF_4') | k10_relat_1('#skF_5', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_818])).
% 3.44/1.56  tff(c_894, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_4', '#skF_3')), '#skF_4')), inference(splitLeft, [status(thm)], [c_892])).
% 3.44/1.56  tff(c_900, plain, (~r2_hidden('#skF_2'('#skF_5', '#skF_4', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_32, c_894])).
% 3.44/1.56  tff(c_907, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_893, c_900])).
% 3.44/1.56  tff(c_908, plain, (k10_relat_1('#skF_5', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_892])).
% 3.44/1.56  tff(c_930, plain, (r1_tarski(k9_relat_1('#skF_5', '#skF_3'), '#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_908, c_22])).
% 3.44/1.56  tff(c_941, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_59, c_930])).
% 3.44/1.56  tff(c_943, plain, $false, inference(negUnitSimplification, [status(thm)], [c_610, c_941])).
% 3.44/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.56  
% 3.44/1.56  Inference rules
% 3.44/1.56  ----------------------
% 3.44/1.56  #Ref     : 0
% 3.44/1.56  #Sup     : 167
% 3.44/1.56  #Fact    : 0
% 3.44/1.56  #Define  : 0
% 3.44/1.56  #Split   : 5
% 3.44/1.56  #Chain   : 0
% 3.44/1.56  #Close   : 0
% 3.44/1.56  
% 3.44/1.56  Ordering : KBO
% 3.44/1.56  
% 3.44/1.56  Simplification rules
% 3.44/1.56  ----------------------
% 3.44/1.56  #Subsume      : 45
% 3.44/1.56  #Demod        : 272
% 3.44/1.56  #Tautology    : 37
% 3.44/1.56  #SimpNegUnit  : 4
% 3.44/1.56  #BackRed      : 21
% 3.44/1.56  
% 3.44/1.56  #Partial instantiations: 0
% 3.44/1.56  #Strategies tried      : 1
% 3.44/1.56  
% 3.44/1.56  Timing (in seconds)
% 3.44/1.56  ----------------------
% 3.44/1.57  Preprocessing        : 0.30
% 3.44/1.57  Parsing              : 0.17
% 3.44/1.57  CNF conversion       : 0.02
% 3.44/1.57  Main loop            : 0.46
% 3.44/1.57  Inferencing          : 0.19
% 3.44/1.57  Reduction            : 0.12
% 3.44/1.57  Demodulation         : 0.09
% 3.44/1.57  BG Simplification    : 0.02
% 3.44/1.57  Subsumption          : 0.09
% 3.44/1.57  Abstraction          : 0.02
% 3.44/1.57  MUC search           : 0.00
% 3.44/1.57  Cooper               : 0.00
% 3.44/1.57  Total                : 0.80
% 3.44/1.57  Index Insertion      : 0.00
% 3.44/1.57  Index Deletion       : 0.00
% 3.44/1.57  Index Matching       : 0.00
% 3.44/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
