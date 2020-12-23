%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:16 EST 2020

% Result     : Theorem 5.48s
% Output     : CNFRefutation 5.90s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 166 expanded)
%              Number of leaves         :   25 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :  158 ( 502 expanded)
%              Number of equality atoms :   15 (  26 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
            <=> ( r2_hidden(A,k1_relat_1(C))
                & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_30,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_34,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_46,plain,
    ( r2_hidden('#skF_3',k1_relat_1(k5_relat_1('#skF_5','#skF_4')))
    | r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_69,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,
    ( r2_hidden('#skF_3',k1_relat_1(k5_relat_1('#skF_5','#skF_4')))
    | r2_hidden(k1_funct_1('#skF_5','#skF_3'),k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_93,plain,(
    r2_hidden(k1_funct_1('#skF_5','#skF_3'),k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_36,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),k1_relat_1('#skF_4'))
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ r2_hidden('#skF_3',k1_relat_1(k5_relat_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_121,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1(k5_relat_1('#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_93,c_36])).

tff(c_20,plain,(
    ! [A_15,B_17] :
      ( k10_relat_1(A_15,k1_relat_1(B_17)) = k1_relat_1(k5_relat_1(A_15,B_17))
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    ! [A_14] :
      ( k10_relat_1(A_14,k2_relat_1(A_14)) = k1_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_22,plain,(
    ! [A_18,C_20] :
      ( r2_hidden(k4_tarski(A_18,k1_funct_1(C_20,A_18)),C_20)
      | ~ r2_hidden(A_18,k1_relat_1(C_20))
      | ~ v1_funct_1(C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_288,plain,(
    ! [A_84,C_85,B_86,D_87] :
      ( r2_hidden(A_84,k10_relat_1(C_85,B_86))
      | ~ r2_hidden(D_87,B_86)
      | ~ r2_hidden(k4_tarski(A_84,D_87),C_85)
      | ~ r2_hidden(D_87,k2_relat_1(C_85))
      | ~ v1_relat_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_375,plain,(
    ! [A_94,C_95] :
      ( r2_hidden(A_94,k10_relat_1(C_95,k1_relat_1('#skF_4')))
      | ~ r2_hidden(k4_tarski(A_94,k1_funct_1('#skF_5','#skF_3')),C_95)
      | ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),k2_relat_1(C_95))
      | ~ v1_relat_1(C_95) ) ),
    inference(resolution,[status(thm)],[c_93,c_288])).

tff(c_383,plain,
    ( r2_hidden('#skF_3',k10_relat_1('#skF_5',k1_relat_1('#skF_4')))
    | ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),k2_relat_1('#skF_5'))
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_375])).

tff(c_387,plain,
    ( r2_hidden('#skF_3',k10_relat_1('#skF_5',k1_relat_1('#skF_4')))
    | ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_69,c_383])).

tff(c_388,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),k2_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_387])).

tff(c_136,plain,(
    ! [A_56,B_57,C_58] :
      ( r2_hidden(k4_tarski(A_56,'#skF_2'(A_56,B_57,C_58)),C_58)
      | ~ r2_hidden(A_56,k10_relat_1(C_58,B_57))
      | ~ v1_relat_1(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [C_20,A_18,B_19] :
      ( k1_funct_1(C_20,A_18) = B_19
      | ~ r2_hidden(k4_tarski(A_18,B_19),C_20)
      | ~ v1_funct_1(C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_213,plain,(
    ! [C_70,A_71,B_72] :
      ( k1_funct_1(C_70,A_71) = '#skF_2'(A_71,B_72,C_70)
      | ~ v1_funct_1(C_70)
      | ~ r2_hidden(A_71,k10_relat_1(C_70,B_72))
      | ~ v1_relat_1(C_70) ) ),
    inference(resolution,[status(thm)],[c_136,c_24])).

tff(c_625,plain,(
    ! [A_124,A_125] :
      ( '#skF_2'(A_124,k2_relat_1(A_125),A_125) = k1_funct_1(A_125,A_124)
      | ~ v1_funct_1(A_125)
      | ~ r2_hidden(A_124,k1_relat_1(A_125))
      | ~ v1_relat_1(A_125)
      | ~ v1_relat_1(A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_213])).

tff(c_664,plain,
    ( '#skF_2'('#skF_3',k2_relat_1('#skF_5'),'#skF_5') = k1_funct_1('#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_69,c_625])).

tff(c_686,plain,(
    '#skF_2'('#skF_3',k2_relat_1('#skF_5'),'#skF_5') = k1_funct_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_664])).

tff(c_14,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),k2_relat_1(C_8))
      | ~ r2_hidden(A_6,k10_relat_1(C_8,B_7))
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_703,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),k2_relat_1('#skF_5'))
    | ~ r2_hidden('#skF_3',k10_relat_1('#skF_5',k2_relat_1('#skF_5')))
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_686,c_14])).

tff(c_718,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),k2_relat_1('#skF_5'))
    | ~ r2_hidden('#skF_3',k10_relat_1('#skF_5',k2_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_703])).

tff(c_719,plain,(
    ~ r2_hidden('#skF_3',k10_relat_1('#skF_5',k2_relat_1('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_388,c_718])).

tff(c_726,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_719])).

tff(c_729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_69,c_726])).

tff(c_730,plain,(
    r2_hidden('#skF_3',k10_relat_1('#skF_5',k1_relat_1('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_387])).

tff(c_764,plain,
    ( r2_hidden('#skF_3',k1_relat_1(k5_relat_1('#skF_5','#skF_4')))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_730])).

tff(c_774,plain,(
    r2_hidden('#skF_3',k1_relat_1(k5_relat_1('#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34,c_764])).

tff(c_776,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_774])).

tff(c_777,plain,(
    r2_hidden('#skF_3',k1_relat_1(k5_relat_1('#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_778,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_831,plain,(
    ! [A_150,B_151,C_152] :
      ( r2_hidden(k4_tarski(A_150,'#skF_2'(A_150,B_151,C_152)),C_152)
      | ~ r2_hidden(A_150,k10_relat_1(C_152,B_151))
      | ~ v1_relat_1(C_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_897,plain,(
    ! [C_162,A_163,B_164] :
      ( k1_funct_1(C_162,A_163) = '#skF_2'(A_163,B_164,C_162)
      | ~ v1_funct_1(C_162)
      | ~ r2_hidden(A_163,k10_relat_1(C_162,B_164))
      | ~ v1_relat_1(C_162) ) ),
    inference(resolution,[status(thm)],[c_831,c_24])).

tff(c_3575,plain,(
    ! [A_392,B_393,A_394] :
      ( '#skF_2'(A_392,k1_relat_1(B_393),A_394) = k1_funct_1(A_394,A_392)
      | ~ v1_funct_1(A_394)
      | ~ r2_hidden(A_392,k1_relat_1(k5_relat_1(A_394,B_393)))
      | ~ v1_relat_1(A_394)
      | ~ v1_relat_1(B_393)
      | ~ v1_relat_1(A_394) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_897])).

tff(c_3641,plain,
    ( '#skF_2'('#skF_3',k1_relat_1('#skF_4'),'#skF_5') = k1_funct_1('#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_777,c_3575])).

tff(c_3670,plain,(
    '#skF_2'('#skF_3',k1_relat_1('#skF_4'),'#skF_5') = k1_funct_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34,c_28,c_3641])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | ~ r2_hidden(A_6,k10_relat_1(C_8,B_7))
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3700,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),k1_relat_1('#skF_4'))
    | ~ r2_hidden('#skF_3',k10_relat_1('#skF_5',k1_relat_1('#skF_4')))
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3670,c_10])).

tff(c_3720,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),k1_relat_1('#skF_4'))
    | ~ r2_hidden('#skF_3',k10_relat_1('#skF_5',k1_relat_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3700])).

tff(c_3721,plain,(
    ~ r2_hidden('#skF_3',k10_relat_1('#skF_5',k1_relat_1('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_778,c_3720])).

tff(c_3725,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1(k5_relat_1('#skF_5','#skF_4')))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_3721])).

tff(c_3728,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34,c_777,c_3725])).

tff(c_3730,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_3753,plain,(
    ! [A_400,B_401] :
      ( k10_relat_1(A_400,k1_relat_1(B_401)) = k1_relat_1(k5_relat_1(A_400,B_401))
      | ~ v1_relat_1(B_401)
      | ~ v1_relat_1(A_400) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k10_relat_1(B_13,A_12),k1_relat_1(B_13))
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3789,plain,(
    ! [A_416,B_417] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_416,B_417)),k1_relat_1(A_416))
      | ~ v1_relat_1(A_416)
      | ~ v1_relat_1(B_417)
      | ~ v1_relat_1(A_416) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3753,c_16])).

tff(c_3729,plain,(
    r2_hidden('#skF_3',k1_relat_1(k5_relat_1('#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_3732,plain,(
    ! [C_395,B_396,A_397] :
      ( r2_hidden(C_395,B_396)
      | ~ r2_hidden(C_395,A_397)
      | ~ r1_tarski(A_397,B_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3740,plain,(
    ! [B_396] :
      ( r2_hidden('#skF_3',B_396)
      | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_5','#skF_4')),B_396) ) ),
    inference(resolution,[status(thm)],[c_3729,c_3732])).

tff(c_3795,plain,
    ( r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3789,c_3740])).

tff(c_3799,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34,c_3795])).

tff(c_3801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3730,c_3799])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.48/2.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.48/2.15  
% 5.48/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.48/2.15  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 5.48/2.15  
% 5.48/2.15  %Foreground sorts:
% 5.48/2.15  
% 5.48/2.15  
% 5.48/2.15  %Background operators:
% 5.48/2.15  
% 5.48/2.15  
% 5.48/2.15  %Foreground operators:
% 5.48/2.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.48/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.48/2.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.48/2.15  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.48/2.15  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.48/2.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.48/2.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.48/2.15  tff('#skF_5', type, '#skF_5': $i).
% 5.48/2.15  tff('#skF_3', type, '#skF_3': $i).
% 5.48/2.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.48/2.15  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.48/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.48/2.15  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.48/2.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.48/2.15  tff('#skF_4', type, '#skF_4': $i).
% 5.48/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.48/2.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.48/2.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.48/2.15  
% 5.90/2.17  tff(f_84, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), k1_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_1)).
% 5.90/2.17  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 5.90/2.17  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 5.90/2.17  tff(f_68, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 5.90/2.17  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 5.90/2.17  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 5.90/2.17  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.90/2.17  tff(c_30, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.90/2.17  tff(c_34, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.90/2.17  tff(c_46, plain, (r2_hidden('#skF_3', k1_relat_1(k5_relat_1('#skF_5', '#skF_4'))) | r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.90/2.17  tff(c_69, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_46])).
% 5.90/2.17  tff(c_42, plain, (r2_hidden('#skF_3', k1_relat_1(k5_relat_1('#skF_5', '#skF_4'))) | r2_hidden(k1_funct_1('#skF_5', '#skF_3'), k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.90/2.17  tff(c_93, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_42])).
% 5.90/2.17  tff(c_36, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), k1_relat_1('#skF_4')) | ~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~r2_hidden('#skF_3', k1_relat_1(k5_relat_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.90/2.17  tff(c_121, plain, (~r2_hidden('#skF_3', k1_relat_1(k5_relat_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_93, c_36])).
% 5.90/2.17  tff(c_20, plain, (![A_15, B_17]: (k10_relat_1(A_15, k1_relat_1(B_17))=k1_relat_1(k5_relat_1(A_15, B_17)) | ~v1_relat_1(B_17) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.90/2.17  tff(c_18, plain, (![A_14]: (k10_relat_1(A_14, k2_relat_1(A_14))=k1_relat_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.90/2.17  tff(c_28, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.90/2.17  tff(c_22, plain, (![A_18, C_20]: (r2_hidden(k4_tarski(A_18, k1_funct_1(C_20, A_18)), C_20) | ~r2_hidden(A_18, k1_relat_1(C_20)) | ~v1_funct_1(C_20) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.90/2.17  tff(c_288, plain, (![A_84, C_85, B_86, D_87]: (r2_hidden(A_84, k10_relat_1(C_85, B_86)) | ~r2_hidden(D_87, B_86) | ~r2_hidden(k4_tarski(A_84, D_87), C_85) | ~r2_hidden(D_87, k2_relat_1(C_85)) | ~v1_relat_1(C_85))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.90/2.17  tff(c_375, plain, (![A_94, C_95]: (r2_hidden(A_94, k10_relat_1(C_95, k1_relat_1('#skF_4'))) | ~r2_hidden(k4_tarski(A_94, k1_funct_1('#skF_5', '#skF_3')), C_95) | ~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), k2_relat_1(C_95)) | ~v1_relat_1(C_95))), inference(resolution, [status(thm)], [c_93, c_288])).
% 5.90/2.17  tff(c_383, plain, (r2_hidden('#skF_3', k10_relat_1('#skF_5', k1_relat_1('#skF_4'))) | ~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), k2_relat_1('#skF_5')) | ~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_375])).
% 5.90/2.17  tff(c_387, plain, (r2_hidden('#skF_3', k10_relat_1('#skF_5', k1_relat_1('#skF_4'))) | ~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_69, c_383])).
% 5.90/2.17  tff(c_388, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), k2_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_387])).
% 5.90/2.17  tff(c_136, plain, (![A_56, B_57, C_58]: (r2_hidden(k4_tarski(A_56, '#skF_2'(A_56, B_57, C_58)), C_58) | ~r2_hidden(A_56, k10_relat_1(C_58, B_57)) | ~v1_relat_1(C_58))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.90/2.17  tff(c_24, plain, (![C_20, A_18, B_19]: (k1_funct_1(C_20, A_18)=B_19 | ~r2_hidden(k4_tarski(A_18, B_19), C_20) | ~v1_funct_1(C_20) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.90/2.17  tff(c_213, plain, (![C_70, A_71, B_72]: (k1_funct_1(C_70, A_71)='#skF_2'(A_71, B_72, C_70) | ~v1_funct_1(C_70) | ~r2_hidden(A_71, k10_relat_1(C_70, B_72)) | ~v1_relat_1(C_70))), inference(resolution, [status(thm)], [c_136, c_24])).
% 5.90/2.17  tff(c_625, plain, (![A_124, A_125]: ('#skF_2'(A_124, k2_relat_1(A_125), A_125)=k1_funct_1(A_125, A_124) | ~v1_funct_1(A_125) | ~r2_hidden(A_124, k1_relat_1(A_125)) | ~v1_relat_1(A_125) | ~v1_relat_1(A_125))), inference(superposition, [status(thm), theory('equality')], [c_18, c_213])).
% 5.90/2.17  tff(c_664, plain, ('#skF_2'('#skF_3', k2_relat_1('#skF_5'), '#skF_5')=k1_funct_1('#skF_5', '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_69, c_625])).
% 5.90/2.17  tff(c_686, plain, ('#skF_2'('#skF_3', k2_relat_1('#skF_5'), '#skF_5')=k1_funct_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_664])).
% 5.90/2.17  tff(c_14, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), k2_relat_1(C_8)) | ~r2_hidden(A_6, k10_relat_1(C_8, B_7)) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.90/2.17  tff(c_703, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), k2_relat_1('#skF_5')) | ~r2_hidden('#skF_3', k10_relat_1('#skF_5', k2_relat_1('#skF_5'))) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_686, c_14])).
% 5.90/2.17  tff(c_718, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), k2_relat_1('#skF_5')) | ~r2_hidden('#skF_3', k10_relat_1('#skF_5', k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_703])).
% 5.90/2.17  tff(c_719, plain, (~r2_hidden('#skF_3', k10_relat_1('#skF_5', k2_relat_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_388, c_718])).
% 5.90/2.17  tff(c_726, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_18, c_719])).
% 5.90/2.17  tff(c_729, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_69, c_726])).
% 5.90/2.17  tff(c_730, plain, (r2_hidden('#skF_3', k10_relat_1('#skF_5', k1_relat_1('#skF_4')))), inference(splitRight, [status(thm)], [c_387])).
% 5.90/2.17  tff(c_764, plain, (r2_hidden('#skF_3', k1_relat_1(k5_relat_1('#skF_5', '#skF_4'))) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_20, c_730])).
% 5.90/2.17  tff(c_774, plain, (r2_hidden('#skF_3', k1_relat_1(k5_relat_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34, c_764])).
% 5.90/2.17  tff(c_776, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_774])).
% 5.90/2.17  tff(c_777, plain, (r2_hidden('#skF_3', k1_relat_1(k5_relat_1('#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_42])).
% 5.90/2.17  tff(c_778, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_42])).
% 5.90/2.17  tff(c_831, plain, (![A_150, B_151, C_152]: (r2_hidden(k4_tarski(A_150, '#skF_2'(A_150, B_151, C_152)), C_152) | ~r2_hidden(A_150, k10_relat_1(C_152, B_151)) | ~v1_relat_1(C_152))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.90/2.17  tff(c_897, plain, (![C_162, A_163, B_164]: (k1_funct_1(C_162, A_163)='#skF_2'(A_163, B_164, C_162) | ~v1_funct_1(C_162) | ~r2_hidden(A_163, k10_relat_1(C_162, B_164)) | ~v1_relat_1(C_162))), inference(resolution, [status(thm)], [c_831, c_24])).
% 5.90/2.17  tff(c_3575, plain, (![A_392, B_393, A_394]: ('#skF_2'(A_392, k1_relat_1(B_393), A_394)=k1_funct_1(A_394, A_392) | ~v1_funct_1(A_394) | ~r2_hidden(A_392, k1_relat_1(k5_relat_1(A_394, B_393))) | ~v1_relat_1(A_394) | ~v1_relat_1(B_393) | ~v1_relat_1(A_394))), inference(superposition, [status(thm), theory('equality')], [c_20, c_897])).
% 5.90/2.17  tff(c_3641, plain, ('#skF_2'('#skF_3', k1_relat_1('#skF_4'), '#skF_5')=k1_funct_1('#skF_5', '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_777, c_3575])).
% 5.90/2.17  tff(c_3670, plain, ('#skF_2'('#skF_3', k1_relat_1('#skF_4'), '#skF_5')=k1_funct_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34, c_28, c_3641])).
% 5.90/2.17  tff(c_10, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | ~r2_hidden(A_6, k10_relat_1(C_8, B_7)) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.90/2.17  tff(c_3700, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), k1_relat_1('#skF_4')) | ~r2_hidden('#skF_3', k10_relat_1('#skF_5', k1_relat_1('#skF_4'))) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3670, c_10])).
% 5.90/2.17  tff(c_3720, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), k1_relat_1('#skF_4')) | ~r2_hidden('#skF_3', k10_relat_1('#skF_5', k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3700])).
% 5.90/2.17  tff(c_3721, plain, (~r2_hidden('#skF_3', k10_relat_1('#skF_5', k1_relat_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_778, c_3720])).
% 5.90/2.17  tff(c_3725, plain, (~r2_hidden('#skF_3', k1_relat_1(k5_relat_1('#skF_5', '#skF_4'))) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_20, c_3721])).
% 5.90/2.17  tff(c_3728, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_34, c_777, c_3725])).
% 5.90/2.17  tff(c_3730, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_46])).
% 5.90/2.17  tff(c_3753, plain, (![A_400, B_401]: (k10_relat_1(A_400, k1_relat_1(B_401))=k1_relat_1(k5_relat_1(A_400, B_401)) | ~v1_relat_1(B_401) | ~v1_relat_1(A_400))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.90/2.17  tff(c_16, plain, (![B_13, A_12]: (r1_tarski(k10_relat_1(B_13, A_12), k1_relat_1(B_13)) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.90/2.17  tff(c_3789, plain, (![A_416, B_417]: (r1_tarski(k1_relat_1(k5_relat_1(A_416, B_417)), k1_relat_1(A_416)) | ~v1_relat_1(A_416) | ~v1_relat_1(B_417) | ~v1_relat_1(A_416))), inference(superposition, [status(thm), theory('equality')], [c_3753, c_16])).
% 5.90/2.17  tff(c_3729, plain, (r2_hidden('#skF_3', k1_relat_1(k5_relat_1('#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_46])).
% 5.90/2.17  tff(c_3732, plain, (![C_395, B_396, A_397]: (r2_hidden(C_395, B_396) | ~r2_hidden(C_395, A_397) | ~r1_tarski(A_397, B_396))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.90/2.17  tff(c_3740, plain, (![B_396]: (r2_hidden('#skF_3', B_396) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_5', '#skF_4')), B_396))), inference(resolution, [status(thm)], [c_3729, c_3732])).
% 5.90/2.17  tff(c_3795, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_3789, c_3740])).
% 5.90/2.17  tff(c_3799, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34, c_3795])).
% 5.90/2.17  tff(c_3801, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3730, c_3799])).
% 5.90/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.90/2.17  
% 5.90/2.17  Inference rules
% 5.90/2.17  ----------------------
% 5.90/2.17  #Ref     : 0
% 5.90/2.17  #Sup     : 901
% 5.90/2.17  #Fact    : 0
% 5.90/2.17  #Define  : 0
% 5.90/2.17  #Split   : 6
% 5.90/2.17  #Chain   : 0
% 5.90/2.17  #Close   : 0
% 5.90/2.17  
% 5.90/2.17  Ordering : KBO
% 5.90/2.17  
% 5.90/2.17  Simplification rules
% 5.90/2.17  ----------------------
% 5.90/2.17  #Subsume      : 174
% 5.90/2.17  #Demod        : 169
% 5.90/2.17  #Tautology    : 74
% 5.90/2.17  #SimpNegUnit  : 5
% 5.90/2.17  #BackRed      : 0
% 5.90/2.17  
% 5.90/2.17  #Partial instantiations: 0
% 5.90/2.17  #Strategies tried      : 1
% 5.90/2.17  
% 5.90/2.17  Timing (in seconds)
% 5.90/2.17  ----------------------
% 5.90/2.17  Preprocessing        : 0.31
% 5.90/2.17  Parsing              : 0.16
% 5.90/2.17  CNF conversion       : 0.02
% 5.90/2.17  Main loop            : 1.04
% 5.90/2.17  Inferencing          : 0.37
% 5.90/2.17  Reduction            : 0.27
% 5.90/2.17  Demodulation         : 0.18
% 5.90/2.17  BG Simplification    : 0.05
% 5.90/2.17  Subsumption          : 0.26
% 5.90/2.17  Abstraction          : 0.06
% 5.90/2.17  MUC search           : 0.00
% 5.90/2.17  Cooper               : 0.00
% 5.90/2.17  Total                : 1.38
% 5.90/2.17  Index Insertion      : 0.00
% 5.90/2.17  Index Deletion       : 0.00
% 5.90/2.17  Index Matching       : 0.00
% 5.90/2.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
