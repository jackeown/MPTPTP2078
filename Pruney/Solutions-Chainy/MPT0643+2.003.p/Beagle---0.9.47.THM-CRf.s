%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:40 EST 2020

% Result     : Theorem 10.75s
% Output     : CNFRefutation 10.88s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 332 expanded)
%              Number of leaves         :   37 ( 145 expanded)
%              Depth                    :   15
%              Number of atoms          :  178 (1368 expanded)
%              Number of equality atoms :   49 ( 515 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_15 > #skF_3 > #skF_12 > #skF_14 > #skF_10 > #skF_13 > #skF_5 > #skF_8 > #skF_9 > #skF_11 > #skF_2 > #skF_7 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_11',type,(
    '#skF_11': $i > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_121,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( ( k1_relat_1(B) = A
                & k1_relat_1(C) = A
                & r1_tarski(k2_relat_1(C),A)
                & v2_funct_1(B)
                & k5_relat_1(C,B) = B )
             => C = k6_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

tff(c_58,plain,(
    k6_relat_1('#skF_13') != '#skF_15' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_72,plain,(
    v1_relat_1('#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_70,plain,(
    v1_funct_1('#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_66,plain,(
    k1_relat_1('#skF_15') = '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_634,plain,(
    ! [B_143] :
      ( r2_hidden('#skF_12'(k1_relat_1(B_143),B_143),k1_relat_1(B_143))
      | k6_relat_1(k1_relat_1(B_143)) = B_143
      | ~ v1_funct_1(B_143)
      | ~ v1_relat_1(B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_639,plain,
    ( r2_hidden('#skF_12'('#skF_13','#skF_15'),k1_relat_1('#skF_15'))
    | k6_relat_1(k1_relat_1('#skF_15')) = '#skF_15'
    | ~ v1_funct_1('#skF_15')
    | ~ v1_relat_1('#skF_15') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_634])).

tff(c_651,plain,
    ( r2_hidden('#skF_12'('#skF_13','#skF_15'),'#skF_13')
    | k6_relat_1('#skF_13') = '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_66,c_639])).

tff(c_652,plain,(
    r2_hidden('#skF_12'('#skF_13','#skF_15'),'#skF_13') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_651])).

tff(c_143,plain,(
    ! [C_85,A_86] :
      ( r2_hidden(k4_tarski(C_85,'#skF_5'(A_86,k1_relat_1(A_86),C_85)),A_86)
      | ~ r2_hidden(C_85,k1_relat_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_154,plain,(
    ! [C_85] :
      ( r2_hidden(k4_tarski(C_85,'#skF_5'('#skF_15','#skF_13',C_85)),'#skF_15')
      | ~ r2_hidden(C_85,k1_relat_1('#skF_15')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_143])).

tff(c_161,plain,(
    ! [C_85] :
      ( r2_hidden(k4_tarski(C_85,'#skF_5'('#skF_15','#skF_13',C_85)),'#skF_15')
      | ~ r2_hidden(C_85,'#skF_13') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_154])).

tff(c_290,plain,(
    ! [C_107,A_108,B_109] :
      ( k1_funct_1(C_107,A_108) = B_109
      | ~ r2_hidden(k4_tarski(A_108,B_109),C_107)
      | ~ v1_funct_1(C_107)
      | ~ v1_relat_1(C_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_306,plain,(
    ! [C_85] :
      ( k1_funct_1('#skF_15',C_85) = '#skF_5'('#skF_15','#skF_13',C_85)
      | ~ v1_funct_1('#skF_15')
      | ~ v1_relat_1('#skF_15')
      | ~ r2_hidden(C_85,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_161,c_290])).

tff(c_318,plain,(
    ! [C_85] :
      ( k1_funct_1('#skF_15',C_85) = '#skF_5'('#skF_15','#skF_13',C_85)
      | ~ r2_hidden(C_85,'#skF_13') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_306])).

tff(c_668,plain,(
    k1_funct_1('#skF_15','#skF_12'('#skF_13','#skF_15')) = '#skF_5'('#skF_15','#skF_13','#skF_12'('#skF_13','#skF_15')) ),
    inference(resolution,[status(thm)],[c_652,c_318])).

tff(c_6105,plain,(
    ! [B_371] :
      ( k1_funct_1(B_371,'#skF_12'(k1_relat_1(B_371),B_371)) != '#skF_12'(k1_relat_1(B_371),B_371)
      | k6_relat_1(k1_relat_1(B_371)) = B_371
      | ~ v1_funct_1(B_371)
      | ~ v1_relat_1(B_371) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6108,plain,
    ( k1_funct_1('#skF_15','#skF_12'('#skF_13','#skF_15')) != '#skF_12'(k1_relat_1('#skF_15'),'#skF_15')
    | k6_relat_1(k1_relat_1('#skF_15')) = '#skF_15'
    | ~ v1_funct_1('#skF_15')
    | ~ v1_relat_1('#skF_15') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_6105])).

tff(c_6113,plain,
    ( '#skF_5'('#skF_15','#skF_13','#skF_12'('#skF_13','#skF_15')) != '#skF_12'('#skF_13','#skF_15')
    | k6_relat_1('#skF_13') = '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_668,c_66,c_6108])).

tff(c_6114,plain,(
    '#skF_5'('#skF_15','#skF_13','#skF_12'('#skF_13','#skF_15')) != '#skF_12'('#skF_13','#skF_15') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_6113])).

tff(c_90,plain,(
    ! [A_66,B_67] :
      ( r2_hidden('#skF_1'(A_66,B_67),A_66)
      | r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_95,plain,(
    ! [A_66] : r1_tarski(A_66,A_66) ),
    inference(resolution,[status(thm)],[c_90,c_4])).

tff(c_64,plain,(
    r1_tarski(k2_relat_1('#skF_15'),'#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_5342,plain,(
    ! [A_315,C_316] :
      ( r2_hidden(k4_tarski(A_315,k1_funct_1(C_316,A_315)),C_316)
      | ~ r2_hidden(A_315,k1_relat_1(C_316))
      | ~ v1_funct_1(C_316)
      | ~ v1_relat_1(C_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_5373,plain,
    ( r2_hidden(k4_tarski('#skF_12'('#skF_13','#skF_15'),'#skF_5'('#skF_15','#skF_13','#skF_12'('#skF_13','#skF_15'))),'#skF_15')
    | ~ r2_hidden('#skF_12'('#skF_13','#skF_15'),k1_relat_1('#skF_15'))
    | ~ v1_funct_1('#skF_15')
    | ~ v1_relat_1('#skF_15') ),
    inference(superposition,[status(thm),theory(equality)],[c_668,c_5342])).

tff(c_5395,plain,(
    r2_hidden(k4_tarski('#skF_12'('#skF_13','#skF_15'),'#skF_5'('#skF_15','#skF_13','#skF_12'('#skF_13','#skF_15'))),'#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_652,c_66,c_5373])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7311,plain,(
    ! [B_445] :
      ( r2_hidden(k4_tarski('#skF_12'('#skF_13','#skF_15'),'#skF_5'('#skF_15','#skF_13','#skF_12'('#skF_13','#skF_15'))),B_445)
      | ~ r1_tarski('#skF_15',B_445) ) ),
    inference(resolution,[status(thm)],[c_5395,c_2])).

tff(c_22,plain,(
    ! [C_40,A_25,D_43] :
      ( r2_hidden(C_40,k2_relat_1(A_25))
      | ~ r2_hidden(k4_tarski(D_43,C_40),A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8007,plain,(
    ! [B_455] :
      ( r2_hidden('#skF_5'('#skF_15','#skF_13','#skF_12'('#skF_13','#skF_15')),k2_relat_1(B_455))
      | ~ r1_tarski('#skF_15',B_455) ) ),
    inference(resolution,[status(thm)],[c_7311,c_22])).

tff(c_15827,plain,(
    ! [B_627,B_628] :
      ( r2_hidden('#skF_5'('#skF_15','#skF_13','#skF_12'('#skF_13','#skF_15')),B_627)
      | ~ r1_tarski(k2_relat_1(B_628),B_627)
      | ~ r1_tarski('#skF_15',B_628) ) ),
    inference(resolution,[status(thm)],[c_8007,c_2])).

tff(c_15844,plain,
    ( r2_hidden('#skF_5'('#skF_15','#skF_13','#skF_12'('#skF_13','#skF_15')),'#skF_13')
    | ~ r1_tarski('#skF_15','#skF_15') ),
    inference(resolution,[status(thm)],[c_64,c_15827])).

tff(c_15857,plain,(
    r2_hidden('#skF_5'('#skF_15','#skF_13','#skF_12'('#skF_13','#skF_15')),'#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_15844])).

tff(c_76,plain,(
    v1_relat_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_74,plain,(
    v1_funct_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_68,plain,(
    k1_relat_1('#skF_14') = '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_157,plain,(
    ! [C_85] :
      ( r2_hidden(k4_tarski(C_85,'#skF_5'('#skF_14','#skF_13',C_85)),'#skF_14')
      | ~ r2_hidden(C_85,k1_relat_1('#skF_14')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_143])).

tff(c_162,plain,(
    ! [C_85] :
      ( r2_hidden(k4_tarski(C_85,'#skF_5'('#skF_14','#skF_13',C_85)),'#skF_14')
      | ~ r2_hidden(C_85,'#skF_13') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_157])).

tff(c_300,plain,(
    ! [C_85] :
      ( k1_funct_1('#skF_14',C_85) = '#skF_5'('#skF_14','#skF_13',C_85)
      | ~ v1_funct_1('#skF_14')
      | ~ v1_relat_1('#skF_14')
      | ~ r2_hidden(C_85,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_162,c_290])).

tff(c_314,plain,(
    ! [C_85] :
      ( k1_funct_1('#skF_14',C_85) = '#skF_5'('#skF_14','#skF_13',C_85)
      | ~ r2_hidden(C_85,'#skF_13') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_300])).

tff(c_669,plain,(
    k1_funct_1('#skF_14','#skF_12'('#skF_13','#skF_15')) = '#skF_5'('#skF_14','#skF_13','#skF_12'('#skF_13','#skF_15')) ),
    inference(resolution,[status(thm)],[c_652,c_314])).

tff(c_60,plain,(
    k5_relat_1('#skF_15','#skF_14') = '#skF_14' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_6883,plain,(
    ! [B_431,C_432,A_433] :
      ( k1_funct_1(k5_relat_1(B_431,C_432),A_433) = k1_funct_1(C_432,k1_funct_1(B_431,A_433))
      | ~ r2_hidden(A_433,k1_relat_1(B_431))
      | ~ v1_funct_1(C_432)
      | ~ v1_relat_1(C_432)
      | ~ v1_funct_1(B_431)
      | ~ v1_relat_1(B_431) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_7033,plain,(
    ! [C_432,A_433] :
      ( k1_funct_1(k5_relat_1('#skF_15',C_432),A_433) = k1_funct_1(C_432,k1_funct_1('#skF_15',A_433))
      | ~ r2_hidden(A_433,'#skF_13')
      | ~ v1_funct_1(C_432)
      | ~ v1_relat_1(C_432)
      | ~ v1_funct_1('#skF_15')
      | ~ v1_relat_1('#skF_15') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_6883])).

tff(c_9209,plain,(
    ! [C_473,A_474] :
      ( k1_funct_1(k5_relat_1('#skF_15',C_473),A_474) = k1_funct_1(C_473,k1_funct_1('#skF_15',A_474))
      | ~ r2_hidden(A_474,'#skF_13')
      | ~ v1_funct_1(C_473)
      | ~ v1_relat_1(C_473) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_7033])).

tff(c_9248,plain,(
    ! [A_474] :
      ( k1_funct_1('#skF_14',k1_funct_1('#skF_15',A_474)) = k1_funct_1('#skF_14',A_474)
      | ~ r2_hidden(A_474,'#skF_13')
      | ~ v1_funct_1('#skF_14')
      | ~ v1_relat_1('#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_9209])).

tff(c_9253,plain,(
    ! [A_475] :
      ( k1_funct_1('#skF_14',k1_funct_1('#skF_15',A_475)) = k1_funct_1('#skF_14',A_475)
      | ~ r2_hidden(A_475,'#skF_13') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_9248])).

tff(c_9282,plain,
    ( k1_funct_1('#skF_14','#skF_5'('#skF_15','#skF_13','#skF_12'('#skF_13','#skF_15'))) = k1_funct_1('#skF_14','#skF_12'('#skF_13','#skF_15'))
    | ~ r2_hidden('#skF_12'('#skF_13','#skF_15'),'#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_668,c_9253])).

tff(c_9303,plain,(
    k1_funct_1('#skF_14','#skF_5'('#skF_15','#skF_13','#skF_12'('#skF_13','#skF_15'))) = '#skF_5'('#skF_14','#skF_13','#skF_12'('#skF_13','#skF_15')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_669,c_9282])).

tff(c_62,plain,(
    v2_funct_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_6630,plain,(
    ! [C_411,B_412,A_413] :
      ( C_411 = B_412
      | k1_funct_1(A_413,C_411) != k1_funct_1(A_413,B_412)
      | ~ r2_hidden(C_411,k1_relat_1(A_413))
      | ~ r2_hidden(B_412,k1_relat_1(A_413))
      | ~ v2_funct_1(A_413)
      | ~ v1_funct_1(A_413)
      | ~ v1_relat_1(A_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6658,plain,(
    ! [C_411] :
      ( C_411 = '#skF_12'('#skF_13','#skF_15')
      | k1_funct_1('#skF_14',C_411) != '#skF_5'('#skF_14','#skF_13','#skF_12'('#skF_13','#skF_15'))
      | ~ r2_hidden(C_411,k1_relat_1('#skF_14'))
      | ~ r2_hidden('#skF_12'('#skF_13','#skF_15'),k1_relat_1('#skF_14'))
      | ~ v2_funct_1('#skF_14')
      | ~ v1_funct_1('#skF_14')
      | ~ v1_relat_1('#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_669,c_6630])).

tff(c_17201,plain,(
    ! [C_680] :
      ( C_680 = '#skF_12'('#skF_13','#skF_15')
      | k1_funct_1('#skF_14',C_680) != '#skF_5'('#skF_14','#skF_13','#skF_12'('#skF_13','#skF_15'))
      | ~ r2_hidden(C_680,'#skF_13') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_62,c_652,c_68,c_68,c_6658])).

tff(c_17209,plain,
    ( '#skF_5'('#skF_15','#skF_13','#skF_12'('#skF_13','#skF_15')) = '#skF_12'('#skF_13','#skF_15')
    | ~ r2_hidden('#skF_5'('#skF_15','#skF_13','#skF_12'('#skF_13','#skF_15')),'#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_9303,c_17201])).

tff(c_17230,plain,(
    '#skF_5'('#skF_15','#skF_13','#skF_12'('#skF_13','#skF_15')) = '#skF_12'('#skF_13','#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15857,c_17209])).

tff(c_17232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6114,c_17230])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:04:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.75/4.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.88/4.10  
% 10.88/4.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.88/4.10  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_15 > #skF_3 > #skF_12 > #skF_14 > #skF_10 > #skF_13 > #skF_5 > #skF_8 > #skF_9 > #skF_11 > #skF_2 > #skF_7 > #skF_1 > #skF_4
% 10.88/4.10  
% 10.88/4.10  %Foreground sorts:
% 10.88/4.10  
% 10.88/4.10  
% 10.88/4.10  %Background operators:
% 10.88/4.10  
% 10.88/4.10  
% 10.88/4.10  %Foreground operators:
% 10.88/4.10  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 10.88/4.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.88/4.10  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.88/4.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.88/4.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.88/4.10  tff('#skF_15', type, '#skF_15': $i).
% 10.88/4.10  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.88/4.10  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.88/4.10  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.88/4.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.88/4.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.88/4.10  tff('#skF_12', type, '#skF_12': ($i * $i) > $i).
% 10.88/4.10  tff('#skF_14', type, '#skF_14': $i).
% 10.88/4.10  tff('#skF_10', type, '#skF_10': $i > $i).
% 10.88/4.10  tff('#skF_13', type, '#skF_13': $i).
% 10.88/4.10  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 10.88/4.10  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 10.88/4.10  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.88/4.10  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 10.88/4.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.88/4.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.88/4.10  tff('#skF_11', type, '#skF_11': $i > $i).
% 10.88/4.10  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.88/4.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.88/4.10  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.88/4.10  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 10.88/4.10  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.88/4.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.88/4.10  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.88/4.10  
% 10.88/4.11  tff(f_121, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) & r1_tarski(k2_relat_1(C), A)) & v2_funct_1(B)) & (k5_relat_1(C, B) = B)) => (C = k6_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_funct_1)).
% 10.88/4.11  tff(f_89, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 10.88/4.11  tff(f_40, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 10.88/4.11  tff(f_99, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 10.88/4.11  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 10.88/4.12  tff(f_48, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 10.88/4.12  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 10.88/4.12  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 10.88/4.12  tff(c_58, plain, (k6_relat_1('#skF_13')!='#skF_15'), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.88/4.12  tff(c_72, plain, (v1_relat_1('#skF_15')), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.88/4.12  tff(c_70, plain, (v1_funct_1('#skF_15')), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.88/4.12  tff(c_66, plain, (k1_relat_1('#skF_15')='#skF_13'), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.88/4.12  tff(c_634, plain, (![B_143]: (r2_hidden('#skF_12'(k1_relat_1(B_143), B_143), k1_relat_1(B_143)) | k6_relat_1(k1_relat_1(B_143))=B_143 | ~v1_funct_1(B_143) | ~v1_relat_1(B_143))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.88/4.12  tff(c_639, plain, (r2_hidden('#skF_12'('#skF_13', '#skF_15'), k1_relat_1('#skF_15')) | k6_relat_1(k1_relat_1('#skF_15'))='#skF_15' | ~v1_funct_1('#skF_15') | ~v1_relat_1('#skF_15')), inference(superposition, [status(thm), theory('equality')], [c_66, c_634])).
% 10.88/4.12  tff(c_651, plain, (r2_hidden('#skF_12'('#skF_13', '#skF_15'), '#skF_13') | k6_relat_1('#skF_13')='#skF_15'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_66, c_639])).
% 10.88/4.12  tff(c_652, plain, (r2_hidden('#skF_12'('#skF_13', '#skF_15'), '#skF_13')), inference(negUnitSimplification, [status(thm)], [c_58, c_651])).
% 10.88/4.12  tff(c_143, plain, (![C_85, A_86]: (r2_hidden(k4_tarski(C_85, '#skF_5'(A_86, k1_relat_1(A_86), C_85)), A_86) | ~r2_hidden(C_85, k1_relat_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 10.88/4.12  tff(c_154, plain, (![C_85]: (r2_hidden(k4_tarski(C_85, '#skF_5'('#skF_15', '#skF_13', C_85)), '#skF_15') | ~r2_hidden(C_85, k1_relat_1('#skF_15')))), inference(superposition, [status(thm), theory('equality')], [c_66, c_143])).
% 10.88/4.12  tff(c_161, plain, (![C_85]: (r2_hidden(k4_tarski(C_85, '#skF_5'('#skF_15', '#skF_13', C_85)), '#skF_15') | ~r2_hidden(C_85, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_154])).
% 10.88/4.12  tff(c_290, plain, (![C_107, A_108, B_109]: (k1_funct_1(C_107, A_108)=B_109 | ~r2_hidden(k4_tarski(A_108, B_109), C_107) | ~v1_funct_1(C_107) | ~v1_relat_1(C_107))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.88/4.12  tff(c_306, plain, (![C_85]: (k1_funct_1('#skF_15', C_85)='#skF_5'('#skF_15', '#skF_13', C_85) | ~v1_funct_1('#skF_15') | ~v1_relat_1('#skF_15') | ~r2_hidden(C_85, '#skF_13'))), inference(resolution, [status(thm)], [c_161, c_290])).
% 10.88/4.12  tff(c_318, plain, (![C_85]: (k1_funct_1('#skF_15', C_85)='#skF_5'('#skF_15', '#skF_13', C_85) | ~r2_hidden(C_85, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_306])).
% 10.88/4.12  tff(c_668, plain, (k1_funct_1('#skF_15', '#skF_12'('#skF_13', '#skF_15'))='#skF_5'('#skF_15', '#skF_13', '#skF_12'('#skF_13', '#skF_15'))), inference(resolution, [status(thm)], [c_652, c_318])).
% 10.88/4.12  tff(c_6105, plain, (![B_371]: (k1_funct_1(B_371, '#skF_12'(k1_relat_1(B_371), B_371))!='#skF_12'(k1_relat_1(B_371), B_371) | k6_relat_1(k1_relat_1(B_371))=B_371 | ~v1_funct_1(B_371) | ~v1_relat_1(B_371))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.88/4.12  tff(c_6108, plain, (k1_funct_1('#skF_15', '#skF_12'('#skF_13', '#skF_15'))!='#skF_12'(k1_relat_1('#skF_15'), '#skF_15') | k6_relat_1(k1_relat_1('#skF_15'))='#skF_15' | ~v1_funct_1('#skF_15') | ~v1_relat_1('#skF_15')), inference(superposition, [status(thm), theory('equality')], [c_66, c_6105])).
% 10.88/4.12  tff(c_6113, plain, ('#skF_5'('#skF_15', '#skF_13', '#skF_12'('#skF_13', '#skF_15'))!='#skF_12'('#skF_13', '#skF_15') | k6_relat_1('#skF_13')='#skF_15'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_668, c_66, c_6108])).
% 10.88/4.12  tff(c_6114, plain, ('#skF_5'('#skF_15', '#skF_13', '#skF_12'('#skF_13', '#skF_15'))!='#skF_12'('#skF_13', '#skF_15')), inference(negUnitSimplification, [status(thm)], [c_58, c_6113])).
% 10.88/4.12  tff(c_90, plain, (![A_66, B_67]: (r2_hidden('#skF_1'(A_66, B_67), A_66) | r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.88/4.12  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.88/4.12  tff(c_95, plain, (![A_66]: (r1_tarski(A_66, A_66))), inference(resolution, [status(thm)], [c_90, c_4])).
% 10.88/4.12  tff(c_64, plain, (r1_tarski(k2_relat_1('#skF_15'), '#skF_13')), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.88/4.12  tff(c_5342, plain, (![A_315, C_316]: (r2_hidden(k4_tarski(A_315, k1_funct_1(C_316, A_315)), C_316) | ~r2_hidden(A_315, k1_relat_1(C_316)) | ~v1_funct_1(C_316) | ~v1_relat_1(C_316))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.88/4.12  tff(c_5373, plain, (r2_hidden(k4_tarski('#skF_12'('#skF_13', '#skF_15'), '#skF_5'('#skF_15', '#skF_13', '#skF_12'('#skF_13', '#skF_15'))), '#skF_15') | ~r2_hidden('#skF_12'('#skF_13', '#skF_15'), k1_relat_1('#skF_15')) | ~v1_funct_1('#skF_15') | ~v1_relat_1('#skF_15')), inference(superposition, [status(thm), theory('equality')], [c_668, c_5342])).
% 10.88/4.12  tff(c_5395, plain, (r2_hidden(k4_tarski('#skF_12'('#skF_13', '#skF_15'), '#skF_5'('#skF_15', '#skF_13', '#skF_12'('#skF_13', '#skF_15'))), '#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_652, c_66, c_5373])).
% 10.88/4.12  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.88/4.12  tff(c_7311, plain, (![B_445]: (r2_hidden(k4_tarski('#skF_12'('#skF_13', '#skF_15'), '#skF_5'('#skF_15', '#skF_13', '#skF_12'('#skF_13', '#skF_15'))), B_445) | ~r1_tarski('#skF_15', B_445))), inference(resolution, [status(thm)], [c_5395, c_2])).
% 10.88/4.12  tff(c_22, plain, (![C_40, A_25, D_43]: (r2_hidden(C_40, k2_relat_1(A_25)) | ~r2_hidden(k4_tarski(D_43, C_40), A_25))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.88/4.12  tff(c_8007, plain, (![B_455]: (r2_hidden('#skF_5'('#skF_15', '#skF_13', '#skF_12'('#skF_13', '#skF_15')), k2_relat_1(B_455)) | ~r1_tarski('#skF_15', B_455))), inference(resolution, [status(thm)], [c_7311, c_22])).
% 10.88/4.12  tff(c_15827, plain, (![B_627, B_628]: (r2_hidden('#skF_5'('#skF_15', '#skF_13', '#skF_12'('#skF_13', '#skF_15')), B_627) | ~r1_tarski(k2_relat_1(B_628), B_627) | ~r1_tarski('#skF_15', B_628))), inference(resolution, [status(thm)], [c_8007, c_2])).
% 10.88/4.12  tff(c_15844, plain, (r2_hidden('#skF_5'('#skF_15', '#skF_13', '#skF_12'('#skF_13', '#skF_15')), '#skF_13') | ~r1_tarski('#skF_15', '#skF_15')), inference(resolution, [status(thm)], [c_64, c_15827])).
% 10.88/4.12  tff(c_15857, plain, (r2_hidden('#skF_5'('#skF_15', '#skF_13', '#skF_12'('#skF_13', '#skF_15')), '#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_15844])).
% 10.88/4.12  tff(c_76, plain, (v1_relat_1('#skF_14')), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.88/4.12  tff(c_74, plain, (v1_funct_1('#skF_14')), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.88/4.12  tff(c_68, plain, (k1_relat_1('#skF_14')='#skF_13'), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.88/4.12  tff(c_157, plain, (![C_85]: (r2_hidden(k4_tarski(C_85, '#skF_5'('#skF_14', '#skF_13', C_85)), '#skF_14') | ~r2_hidden(C_85, k1_relat_1('#skF_14')))), inference(superposition, [status(thm), theory('equality')], [c_68, c_143])).
% 10.88/4.12  tff(c_162, plain, (![C_85]: (r2_hidden(k4_tarski(C_85, '#skF_5'('#skF_14', '#skF_13', C_85)), '#skF_14') | ~r2_hidden(C_85, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_157])).
% 10.88/4.12  tff(c_300, plain, (![C_85]: (k1_funct_1('#skF_14', C_85)='#skF_5'('#skF_14', '#skF_13', C_85) | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14') | ~r2_hidden(C_85, '#skF_13'))), inference(resolution, [status(thm)], [c_162, c_290])).
% 10.88/4.12  tff(c_314, plain, (![C_85]: (k1_funct_1('#skF_14', C_85)='#skF_5'('#skF_14', '#skF_13', C_85) | ~r2_hidden(C_85, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_300])).
% 10.88/4.12  tff(c_669, plain, (k1_funct_1('#skF_14', '#skF_12'('#skF_13', '#skF_15'))='#skF_5'('#skF_14', '#skF_13', '#skF_12'('#skF_13', '#skF_15'))), inference(resolution, [status(thm)], [c_652, c_314])).
% 10.88/4.12  tff(c_60, plain, (k5_relat_1('#skF_15', '#skF_14')='#skF_14'), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.88/4.12  tff(c_6883, plain, (![B_431, C_432, A_433]: (k1_funct_1(k5_relat_1(B_431, C_432), A_433)=k1_funct_1(C_432, k1_funct_1(B_431, A_433)) | ~r2_hidden(A_433, k1_relat_1(B_431)) | ~v1_funct_1(C_432) | ~v1_relat_1(C_432) | ~v1_funct_1(B_431) | ~v1_relat_1(B_431))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.88/4.12  tff(c_7033, plain, (![C_432, A_433]: (k1_funct_1(k5_relat_1('#skF_15', C_432), A_433)=k1_funct_1(C_432, k1_funct_1('#skF_15', A_433)) | ~r2_hidden(A_433, '#skF_13') | ~v1_funct_1(C_432) | ~v1_relat_1(C_432) | ~v1_funct_1('#skF_15') | ~v1_relat_1('#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_6883])).
% 10.88/4.12  tff(c_9209, plain, (![C_473, A_474]: (k1_funct_1(k5_relat_1('#skF_15', C_473), A_474)=k1_funct_1(C_473, k1_funct_1('#skF_15', A_474)) | ~r2_hidden(A_474, '#skF_13') | ~v1_funct_1(C_473) | ~v1_relat_1(C_473))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_7033])).
% 10.88/4.12  tff(c_9248, plain, (![A_474]: (k1_funct_1('#skF_14', k1_funct_1('#skF_15', A_474))=k1_funct_1('#skF_14', A_474) | ~r2_hidden(A_474, '#skF_13') | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_9209])).
% 10.88/4.12  tff(c_9253, plain, (![A_475]: (k1_funct_1('#skF_14', k1_funct_1('#skF_15', A_475))=k1_funct_1('#skF_14', A_475) | ~r2_hidden(A_475, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_9248])).
% 10.88/4.12  tff(c_9282, plain, (k1_funct_1('#skF_14', '#skF_5'('#skF_15', '#skF_13', '#skF_12'('#skF_13', '#skF_15')))=k1_funct_1('#skF_14', '#skF_12'('#skF_13', '#skF_15')) | ~r2_hidden('#skF_12'('#skF_13', '#skF_15'), '#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_668, c_9253])).
% 10.88/4.12  tff(c_9303, plain, (k1_funct_1('#skF_14', '#skF_5'('#skF_15', '#skF_13', '#skF_12'('#skF_13', '#skF_15')))='#skF_5'('#skF_14', '#skF_13', '#skF_12'('#skF_13', '#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_652, c_669, c_9282])).
% 10.88/4.12  tff(c_62, plain, (v2_funct_1('#skF_14')), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.88/4.12  tff(c_6630, plain, (![C_411, B_412, A_413]: (C_411=B_412 | k1_funct_1(A_413, C_411)!=k1_funct_1(A_413, B_412) | ~r2_hidden(C_411, k1_relat_1(A_413)) | ~r2_hidden(B_412, k1_relat_1(A_413)) | ~v2_funct_1(A_413) | ~v1_funct_1(A_413) | ~v1_relat_1(A_413))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.88/4.12  tff(c_6658, plain, (![C_411]: (C_411='#skF_12'('#skF_13', '#skF_15') | k1_funct_1('#skF_14', C_411)!='#skF_5'('#skF_14', '#skF_13', '#skF_12'('#skF_13', '#skF_15')) | ~r2_hidden(C_411, k1_relat_1('#skF_14')) | ~r2_hidden('#skF_12'('#skF_13', '#skF_15'), k1_relat_1('#skF_14')) | ~v2_funct_1('#skF_14') | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_669, c_6630])).
% 10.88/4.12  tff(c_17201, plain, (![C_680]: (C_680='#skF_12'('#skF_13', '#skF_15') | k1_funct_1('#skF_14', C_680)!='#skF_5'('#skF_14', '#skF_13', '#skF_12'('#skF_13', '#skF_15')) | ~r2_hidden(C_680, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_62, c_652, c_68, c_68, c_6658])).
% 10.88/4.12  tff(c_17209, plain, ('#skF_5'('#skF_15', '#skF_13', '#skF_12'('#skF_13', '#skF_15'))='#skF_12'('#skF_13', '#skF_15') | ~r2_hidden('#skF_5'('#skF_15', '#skF_13', '#skF_12'('#skF_13', '#skF_15')), '#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_9303, c_17201])).
% 10.88/4.12  tff(c_17230, plain, ('#skF_5'('#skF_15', '#skF_13', '#skF_12'('#skF_13', '#skF_15'))='#skF_12'('#skF_13', '#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_15857, c_17209])).
% 10.88/4.12  tff(c_17232, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6114, c_17230])).
% 10.88/4.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.88/4.12  
% 10.88/4.12  Inference rules
% 10.88/4.12  ----------------------
% 10.88/4.12  #Ref     : 2
% 10.88/4.12  #Sup     : 3918
% 10.88/4.12  #Fact    : 0
% 10.88/4.12  #Define  : 0
% 10.88/4.12  #Split   : 39
% 10.88/4.12  #Chain   : 0
% 10.88/4.12  #Close   : 0
% 10.88/4.12  
% 10.88/4.12  Ordering : KBO
% 10.88/4.12  
% 10.88/4.12  Simplification rules
% 10.88/4.12  ----------------------
% 10.88/4.12  #Subsume      : 680
% 10.88/4.12  #Demod        : 1481
% 10.88/4.12  #Tautology    : 383
% 10.88/4.12  #SimpNegUnit  : 18
% 10.88/4.12  #BackRed      : 1
% 10.88/4.12  
% 10.88/4.12  #Partial instantiations: 0
% 10.88/4.12  #Strategies tried      : 1
% 10.88/4.12  
% 10.88/4.12  Timing (in seconds)
% 10.88/4.12  ----------------------
% 10.88/4.12  Preprocessing        : 0.37
% 10.88/4.12  Parsing              : 0.18
% 10.88/4.12  CNF conversion       : 0.03
% 10.88/4.12  Main loop            : 2.91
% 10.88/4.12  Inferencing          : 0.81
% 10.88/4.12  Reduction            : 0.83
% 10.88/4.12  Demodulation         : 0.56
% 10.88/4.12  BG Simplification    : 0.10
% 10.88/4.12  Subsumption          : 0.91
% 10.88/4.12  Abstraction          : 0.14
% 10.88/4.12  MUC search           : 0.00
% 10.88/4.12  Cooper               : 0.00
% 10.88/4.12  Total                : 3.32
% 10.88/4.12  Index Insertion      : 0.00
% 10.88/4.12  Index Deletion       : 0.00
% 10.88/4.12  Index Matching       : 0.00
% 10.88/4.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
