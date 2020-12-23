%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:38 EST 2020

% Result     : Theorem 12.55s
% Output     : CNFRefutation 12.55s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 284 expanded)
%              Number of leaves         :   31 ( 108 expanded)
%              Depth                    :   14
%              Number of atoms          :  151 ( 603 expanded)
%              Number of equality atoms :   36 ( 172 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_4 > #skF_10 > #skF_2 > #skF_8 > #skF_9 > #skF_5 > #skF_3 > #skF_7 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_77,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_49,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5147,plain,(
    ! [A_364,B_365,C_366] :
      ( ~ r1_xboole_0(A_364,B_365)
      | ~ r2_hidden(C_366,B_365)
      | ~ r2_hidden(C_366,A_364) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5151,plain,(
    ! [C_367,B_368,A_369] :
      ( ~ r2_hidden(C_367,B_368)
      | ~ r2_hidden(C_367,A_369)
      | k3_xboole_0(A_369,B_368) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_5147])).

tff(c_5176,plain,(
    ! [A_372,B_373,A_374] :
      ( ~ r2_hidden('#skF_1'(A_372,B_373),A_374)
      | k3_xboole_0(A_374,A_372) != k1_xboole_0
      | r1_xboole_0(A_372,B_373) ) ),
    inference(resolution,[status(thm)],[c_10,c_5151])).

tff(c_5185,plain,(
    ! [B_375,A_376] :
      ( k3_xboole_0(B_375,A_376) != k1_xboole_0
      | r1_xboole_0(A_376,B_375) ) ),
    inference(resolution,[status(thm)],[c_8,c_5176])).

tff(c_58,plain,
    ( k10_relat_1('#skF_11','#skF_10') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_11'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_80,plain,(
    r1_xboole_0(k2_relat_1('#skF_11'),'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_52,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_11'),'#skF_10')
    | k10_relat_1('#skF_11','#skF_10') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_90,plain,(
    k10_relat_1('#skF_11','#skF_10') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_52])).

tff(c_46,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_466,plain,(
    ! [A_151,B_152] :
      ( r2_hidden(k4_tarski('#skF_7'(A_151,B_152),'#skF_6'(A_151,B_152)),A_151)
      | r2_hidden('#skF_8'(A_151,B_152),B_152)
      | k2_relat_1(A_151) = B_152 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_34,plain,(
    ! [C_66,A_51,D_69] :
      ( r2_hidden(C_66,k2_relat_1(A_51))
      | ~ r2_hidden(k4_tarski(D_69,C_66),A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2994,plain,(
    ! [A_284,B_285] :
      ( r2_hidden('#skF_6'(A_284,B_285),k2_relat_1(A_284))
      | r2_hidden('#skF_8'(A_284,B_285),B_285)
      | k2_relat_1(A_284) = B_285 ) ),
    inference(resolution,[status(thm)],[c_466,c_34])).

tff(c_3112,plain,(
    ! [B_285] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_285),k1_xboole_0)
      | r2_hidden('#skF_8'(k1_xboole_0,B_285),B_285)
      | k2_relat_1(k1_xboole_0) = B_285 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2994])).

tff(c_4968,plain,(
    ! [B_356] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_356),k1_xboole_0)
      | r2_hidden('#skF_8'(k1_xboole_0,B_356),B_356)
      | k1_xboole_0 = B_356 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3112])).

tff(c_50,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_84,plain,(
    k3_xboole_0(k2_relat_1('#skF_11'),'#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80,c_2])).

tff(c_112,plain,(
    ! [B_88,A_89] :
      ( k10_relat_1(B_88,k3_xboole_0(k2_relat_1(B_88),A_89)) = k10_relat_1(B_88,A_89)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_121,plain,
    ( k10_relat_1('#skF_11',k1_xboole_0) = k10_relat_1('#skF_11','#skF_10')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_112])).

tff(c_132,plain,(
    k10_relat_1('#skF_11',k1_xboole_0) = k10_relat_1('#skF_11','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_121])).

tff(c_379,plain,(
    ! [A_140,B_141,D_142] :
      ( r2_hidden('#skF_5'(A_140,B_141,k10_relat_1(A_140,B_141),D_142),B_141)
      | ~ r2_hidden(D_142,k10_relat_1(A_140,B_141))
      | ~ v1_relat_1(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_395,plain,(
    ! [D_142] :
      ( r2_hidden('#skF_5'('#skF_11',k1_xboole_0,k10_relat_1('#skF_11','#skF_10'),D_142),k1_xboole_0)
      | ~ r2_hidden(D_142,k10_relat_1('#skF_11',k1_xboole_0))
      | ~ v1_relat_1('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_379])).

tff(c_405,plain,(
    ! [D_142] :
      ( r2_hidden('#skF_5'('#skF_11',k1_xboole_0,k10_relat_1('#skF_11','#skF_10'),D_142),k1_xboole_0)
      | ~ r2_hidden(D_142,k10_relat_1('#skF_11','#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_132,c_395])).

tff(c_12,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_407,plain,(
    ! [D_145] :
      ( r2_hidden('#skF_5'('#skF_11',k1_xboole_0,k10_relat_1('#skF_11','#skF_10'),D_145),k1_xboole_0)
      | ~ r2_hidden(D_145,k10_relat_1('#skF_11','#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_132,c_395])).

tff(c_94,plain,(
    ! [A_84,B_85,C_86] :
      ( ~ r1_xboole_0(A_84,B_85)
      | ~ r2_hidden(C_86,B_85)
      | ~ r2_hidden(C_86,A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_100,plain,(
    ! [C_86,B_2,A_1] :
      ( ~ r2_hidden(C_86,B_2)
      | ~ r2_hidden(C_86,A_1)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_94])).

tff(c_415,plain,(
    ! [D_145,A_1] :
      ( ~ r2_hidden('#skF_5'('#skF_11',k1_xboole_0,k10_relat_1('#skF_11','#skF_10'),D_145),A_1)
      | k3_xboole_0(A_1,k1_xboole_0) != k1_xboole_0
      | ~ r2_hidden(D_145,k10_relat_1('#skF_11','#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_407,c_100])).

tff(c_424,plain,(
    ! [D_146,A_147] :
      ( ~ r2_hidden('#skF_5'('#skF_11',k1_xboole_0,k10_relat_1('#skF_11','#skF_10'),D_146),A_147)
      | ~ r2_hidden(D_146,k10_relat_1('#skF_11','#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_415])).

tff(c_428,plain,(
    ! [D_142] : ~ r2_hidden(D_142,k10_relat_1('#skF_11','#skF_10')) ),
    inference(resolution,[status(thm)],[c_405,c_424])).

tff(c_5062,plain,
    ( r2_hidden('#skF_6'(k1_xboole_0,k10_relat_1('#skF_11','#skF_10')),k1_xboole_0)
    | k10_relat_1('#skF_11','#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4968,c_428])).

tff(c_5109,plain,(
    r2_hidden('#skF_6'(k1_xboole_0,k10_relat_1('#skF_11','#skF_10')),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_5062])).

tff(c_138,plain,(
    ! [C_90,B_91,A_92] :
      ( ~ r2_hidden(C_90,B_91)
      | ~ r2_hidden(C_90,A_92)
      | k3_xboole_0(A_92,B_91) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_94])).

tff(c_170,plain,(
    ! [A_95,B_96,A_97] :
      ( ~ r2_hidden('#skF_1'(A_95,B_96),A_97)
      | k3_xboole_0(A_97,B_96) != k1_xboole_0
      | r1_xboole_0(A_95,B_96) ) ),
    inference(resolution,[status(thm)],[c_8,c_138])).

tff(c_180,plain,(
    ! [B_100,A_101] :
      ( k3_xboole_0(B_100,B_100) != k1_xboole_0
      | r1_xboole_0(A_101,B_100) ) ),
    inference(resolution,[status(thm)],[c_8,c_170])).

tff(c_185,plain,(
    ! [A_102] : r1_xboole_0(A_102,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_180])).

tff(c_6,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_191,plain,(
    ! [C_7,A_102] :
      ( ~ r2_hidden(C_7,k1_xboole_0)
      | ~ r2_hidden(C_7,A_102) ) ),
    inference(resolution,[status(thm)],[c_185,c_6])).

tff(c_5126,plain,(
    ! [A_102] : ~ r2_hidden('#skF_6'(k1_xboole_0,k10_relat_1('#skF_11','#skF_10')),A_102) ),
    inference(resolution,[status(thm)],[c_5109,c_191])).

tff(c_5131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5126,c_5109])).

tff(c_5133,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_11'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_5195,plain,(
    k3_xboole_0('#skF_10',k2_relat_1('#skF_11')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5185,c_5133])).

tff(c_32,plain,(
    ! [A_51,C_66] :
      ( r2_hidden(k4_tarski('#skF_9'(A_51,k2_relat_1(A_51),C_66),C_66),A_51)
      | ~ r2_hidden(C_66,k2_relat_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_5209,plain,(
    ! [A_379,B_380] :
      ( k3_xboole_0(A_379,A_379) != k1_xboole_0
      | r1_xboole_0(A_379,B_380) ) ),
    inference(resolution,[status(thm)],[c_10,c_5176])).

tff(c_5214,plain,(
    ! [B_381] : r1_xboole_0(k1_xboole_0,B_381) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_5209])).

tff(c_5243,plain,(
    ! [C_385,B_386] :
      ( ~ r2_hidden(C_385,B_386)
      | ~ r2_hidden(C_385,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_5214,c_6])).

tff(c_5422,plain,(
    ! [A_424,C_425] :
      ( ~ r2_hidden(k4_tarski('#skF_9'(A_424,k2_relat_1(A_424),C_425),C_425),k1_xboole_0)
      | ~ r2_hidden(C_425,k2_relat_1(A_424)) ) ),
    inference(resolution,[status(thm)],[c_32,c_5243])).

tff(c_5426,plain,(
    ! [C_66] : ~ r2_hidden(C_66,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_32,c_5422])).

tff(c_5431,plain,(
    ! [C_66] : ~ r2_hidden(C_66,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_5426])).

tff(c_5132,plain,(
    k10_relat_1('#skF_11','#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_5299,plain,(
    ! [D_394,A_395,B_396,E_397] :
      ( r2_hidden(D_394,k10_relat_1(A_395,B_396))
      | ~ r2_hidden(E_397,B_396)
      | ~ r2_hidden(k4_tarski(D_394,E_397),A_395)
      | ~ v1_relat_1(A_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_7990,plain,(
    ! [D_569,A_570,A_571,B_572] :
      ( r2_hidden(D_569,k10_relat_1(A_570,A_571))
      | ~ r2_hidden(k4_tarski(D_569,'#skF_1'(A_571,B_572)),A_570)
      | ~ v1_relat_1(A_570)
      | r1_xboole_0(A_571,B_572) ) ),
    inference(resolution,[status(thm)],[c_10,c_5299])).

tff(c_28287,plain,(
    ! [A_1123,A_1124,B_1125] :
      ( r2_hidden('#skF_9'(A_1123,k2_relat_1(A_1123),'#skF_1'(A_1124,B_1125)),k10_relat_1(A_1123,A_1124))
      | ~ v1_relat_1(A_1123)
      | r1_xboole_0(A_1124,B_1125)
      | ~ r2_hidden('#skF_1'(A_1124,B_1125),k2_relat_1(A_1123)) ) ),
    inference(resolution,[status(thm)],[c_32,c_7990])).

tff(c_28465,plain,(
    ! [B_1125] :
      ( r2_hidden('#skF_9'('#skF_11',k2_relat_1('#skF_11'),'#skF_1'('#skF_10',B_1125)),k1_xboole_0)
      | ~ v1_relat_1('#skF_11')
      | r1_xboole_0('#skF_10',B_1125)
      | ~ r2_hidden('#skF_1'('#skF_10',B_1125),k2_relat_1('#skF_11')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5132,c_28287])).

tff(c_28496,plain,(
    ! [B_1125] :
      ( r2_hidden('#skF_9'('#skF_11',k2_relat_1('#skF_11'),'#skF_1'('#skF_10',B_1125)),k1_xboole_0)
      | r1_xboole_0('#skF_10',B_1125)
      | ~ r2_hidden('#skF_1'('#skF_10',B_1125),k2_relat_1('#skF_11')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_28465])).

tff(c_28499,plain,(
    ! [B_1126] :
      ( r1_xboole_0('#skF_10',B_1126)
      | ~ r2_hidden('#skF_1'('#skF_10',B_1126),k2_relat_1('#skF_11')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5431,c_28496])).

tff(c_28504,plain,(
    r1_xboole_0('#skF_10',k2_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_8,c_28499])).

tff(c_28509,plain,(
    k3_xboole_0('#skF_10',k2_relat_1('#skF_11')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28504,c_2])).

tff(c_28514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5195,c_28509])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:49:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.55/5.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.55/5.45  
% 12.55/5.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.55/5.46  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_4 > #skF_10 > #skF_2 > #skF_8 > #skF_9 > #skF_5 > #skF_3 > #skF_7 > #skF_1
% 12.55/5.46  
% 12.55/5.46  %Foreground sorts:
% 12.55/5.46  
% 12.55/5.46  
% 12.55/5.46  %Background operators:
% 12.55/5.46  
% 12.55/5.46  
% 12.55/5.46  %Foreground operators:
% 12.55/5.46  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 12.55/5.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.55/5.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.55/5.46  tff('#skF_11', type, '#skF_11': $i).
% 12.55/5.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 12.55/5.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.55/5.46  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 12.55/5.46  tff('#skF_10', type, '#skF_10': $i).
% 12.55/5.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.55/5.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.55/5.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.55/5.46  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 12.55/5.46  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 12.55/5.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.55/5.46  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 12.55/5.46  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 12.55/5.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.55/5.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 12.55/5.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.55/5.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.55/5.46  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 12.55/5.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.55/5.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.55/5.46  
% 12.55/5.47  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 12.55/5.47  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 12.55/5.47  tff(f_84, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 12.55/5.47  tff(f_77, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 12.55/5.47  tff(f_70, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 12.55/5.47  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 12.55/5.47  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 12.55/5.47  tff(f_49, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 12.55/5.47  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.55/5.47  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.55/5.47  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.55/5.47  tff(c_5147, plain, (![A_364, B_365, C_366]: (~r1_xboole_0(A_364, B_365) | ~r2_hidden(C_366, B_365) | ~r2_hidden(C_366, A_364))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.55/5.47  tff(c_5151, plain, (![C_367, B_368, A_369]: (~r2_hidden(C_367, B_368) | ~r2_hidden(C_367, A_369) | k3_xboole_0(A_369, B_368)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_5147])).
% 12.55/5.47  tff(c_5176, plain, (![A_372, B_373, A_374]: (~r2_hidden('#skF_1'(A_372, B_373), A_374) | k3_xboole_0(A_374, A_372)!=k1_xboole_0 | r1_xboole_0(A_372, B_373))), inference(resolution, [status(thm)], [c_10, c_5151])).
% 12.55/5.47  tff(c_5185, plain, (![B_375, A_376]: (k3_xboole_0(B_375, A_376)!=k1_xboole_0 | r1_xboole_0(A_376, B_375))), inference(resolution, [status(thm)], [c_8, c_5176])).
% 12.55/5.47  tff(c_58, plain, (k10_relat_1('#skF_11', '#skF_10')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_11'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.55/5.47  tff(c_80, plain, (r1_xboole_0(k2_relat_1('#skF_11'), '#skF_10')), inference(splitLeft, [status(thm)], [c_58])).
% 12.55/5.47  tff(c_52, plain, (~r1_xboole_0(k2_relat_1('#skF_11'), '#skF_10') | k10_relat_1('#skF_11', '#skF_10')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.55/5.47  tff(c_90, plain, (k10_relat_1('#skF_11', '#skF_10')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_80, c_52])).
% 12.55/5.47  tff(c_46, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 12.55/5.47  tff(c_466, plain, (![A_151, B_152]: (r2_hidden(k4_tarski('#skF_7'(A_151, B_152), '#skF_6'(A_151, B_152)), A_151) | r2_hidden('#skF_8'(A_151, B_152), B_152) | k2_relat_1(A_151)=B_152)), inference(cnfTransformation, [status(thm)], [f_70])).
% 12.55/5.47  tff(c_34, plain, (![C_66, A_51, D_69]: (r2_hidden(C_66, k2_relat_1(A_51)) | ~r2_hidden(k4_tarski(D_69, C_66), A_51))), inference(cnfTransformation, [status(thm)], [f_70])).
% 12.55/5.47  tff(c_2994, plain, (![A_284, B_285]: (r2_hidden('#skF_6'(A_284, B_285), k2_relat_1(A_284)) | r2_hidden('#skF_8'(A_284, B_285), B_285) | k2_relat_1(A_284)=B_285)), inference(resolution, [status(thm)], [c_466, c_34])).
% 12.55/5.47  tff(c_3112, plain, (![B_285]: (r2_hidden('#skF_6'(k1_xboole_0, B_285), k1_xboole_0) | r2_hidden('#skF_8'(k1_xboole_0, B_285), B_285) | k2_relat_1(k1_xboole_0)=B_285)), inference(superposition, [status(thm), theory('equality')], [c_46, c_2994])).
% 12.55/5.47  tff(c_4968, plain, (![B_356]: (r2_hidden('#skF_6'(k1_xboole_0, B_356), k1_xboole_0) | r2_hidden('#skF_8'(k1_xboole_0, B_356), B_356) | k1_xboole_0=B_356)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_3112])).
% 12.55/5.47  tff(c_50, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.55/5.47  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.55/5.47  tff(c_84, plain, (k3_xboole_0(k2_relat_1('#skF_11'), '#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_80, c_2])).
% 12.55/5.47  tff(c_112, plain, (![B_88, A_89]: (k10_relat_1(B_88, k3_xboole_0(k2_relat_1(B_88), A_89))=k10_relat_1(B_88, A_89) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_74])).
% 12.55/5.47  tff(c_121, plain, (k10_relat_1('#skF_11', k1_xboole_0)=k10_relat_1('#skF_11', '#skF_10') | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_84, c_112])).
% 12.55/5.47  tff(c_132, plain, (k10_relat_1('#skF_11', k1_xboole_0)=k10_relat_1('#skF_11', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_121])).
% 12.55/5.47  tff(c_379, plain, (![A_140, B_141, D_142]: (r2_hidden('#skF_5'(A_140, B_141, k10_relat_1(A_140, B_141), D_142), B_141) | ~r2_hidden(D_142, k10_relat_1(A_140, B_141)) | ~v1_relat_1(A_140))), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.55/5.47  tff(c_395, plain, (![D_142]: (r2_hidden('#skF_5'('#skF_11', k1_xboole_0, k10_relat_1('#skF_11', '#skF_10'), D_142), k1_xboole_0) | ~r2_hidden(D_142, k10_relat_1('#skF_11', k1_xboole_0)) | ~v1_relat_1('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_132, c_379])).
% 12.55/5.47  tff(c_405, plain, (![D_142]: (r2_hidden('#skF_5'('#skF_11', k1_xboole_0, k10_relat_1('#skF_11', '#skF_10'), D_142), k1_xboole_0) | ~r2_hidden(D_142, k10_relat_1('#skF_11', '#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_132, c_395])).
% 12.55/5.47  tff(c_12, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.55/5.47  tff(c_407, plain, (![D_145]: (r2_hidden('#skF_5'('#skF_11', k1_xboole_0, k10_relat_1('#skF_11', '#skF_10'), D_145), k1_xboole_0) | ~r2_hidden(D_145, k10_relat_1('#skF_11', '#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_132, c_395])).
% 12.55/5.47  tff(c_94, plain, (![A_84, B_85, C_86]: (~r1_xboole_0(A_84, B_85) | ~r2_hidden(C_86, B_85) | ~r2_hidden(C_86, A_84))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.55/5.47  tff(c_100, plain, (![C_86, B_2, A_1]: (~r2_hidden(C_86, B_2) | ~r2_hidden(C_86, A_1) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_94])).
% 12.55/5.47  tff(c_415, plain, (![D_145, A_1]: (~r2_hidden('#skF_5'('#skF_11', k1_xboole_0, k10_relat_1('#skF_11', '#skF_10'), D_145), A_1) | k3_xboole_0(A_1, k1_xboole_0)!=k1_xboole_0 | ~r2_hidden(D_145, k10_relat_1('#skF_11', '#skF_10')))), inference(resolution, [status(thm)], [c_407, c_100])).
% 12.55/5.47  tff(c_424, plain, (![D_146, A_147]: (~r2_hidden('#skF_5'('#skF_11', k1_xboole_0, k10_relat_1('#skF_11', '#skF_10'), D_146), A_147) | ~r2_hidden(D_146, k10_relat_1('#skF_11', '#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_415])).
% 12.55/5.47  tff(c_428, plain, (![D_142]: (~r2_hidden(D_142, k10_relat_1('#skF_11', '#skF_10')))), inference(resolution, [status(thm)], [c_405, c_424])).
% 12.55/5.47  tff(c_5062, plain, (r2_hidden('#skF_6'(k1_xboole_0, k10_relat_1('#skF_11', '#skF_10')), k1_xboole_0) | k10_relat_1('#skF_11', '#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_4968, c_428])).
% 12.55/5.47  tff(c_5109, plain, (r2_hidden('#skF_6'(k1_xboole_0, k10_relat_1('#skF_11', '#skF_10')), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_90, c_5062])).
% 12.55/5.47  tff(c_138, plain, (![C_90, B_91, A_92]: (~r2_hidden(C_90, B_91) | ~r2_hidden(C_90, A_92) | k3_xboole_0(A_92, B_91)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_94])).
% 12.55/5.47  tff(c_170, plain, (![A_95, B_96, A_97]: (~r2_hidden('#skF_1'(A_95, B_96), A_97) | k3_xboole_0(A_97, B_96)!=k1_xboole_0 | r1_xboole_0(A_95, B_96))), inference(resolution, [status(thm)], [c_8, c_138])).
% 12.55/5.47  tff(c_180, plain, (![B_100, A_101]: (k3_xboole_0(B_100, B_100)!=k1_xboole_0 | r1_xboole_0(A_101, B_100))), inference(resolution, [status(thm)], [c_8, c_170])).
% 12.55/5.47  tff(c_185, plain, (![A_102]: (r1_xboole_0(A_102, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_180])).
% 12.55/5.47  tff(c_6, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.55/5.47  tff(c_191, plain, (![C_7, A_102]: (~r2_hidden(C_7, k1_xboole_0) | ~r2_hidden(C_7, A_102))), inference(resolution, [status(thm)], [c_185, c_6])).
% 12.55/5.47  tff(c_5126, plain, (![A_102]: (~r2_hidden('#skF_6'(k1_xboole_0, k10_relat_1('#skF_11', '#skF_10')), A_102))), inference(resolution, [status(thm)], [c_5109, c_191])).
% 12.55/5.47  tff(c_5131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5126, c_5109])).
% 12.55/5.47  tff(c_5133, plain, (~r1_xboole_0(k2_relat_1('#skF_11'), '#skF_10')), inference(splitRight, [status(thm)], [c_58])).
% 12.55/5.47  tff(c_5195, plain, (k3_xboole_0('#skF_10', k2_relat_1('#skF_11'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_5185, c_5133])).
% 12.55/5.47  tff(c_32, plain, (![A_51, C_66]: (r2_hidden(k4_tarski('#skF_9'(A_51, k2_relat_1(A_51), C_66), C_66), A_51) | ~r2_hidden(C_66, k2_relat_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 12.55/5.47  tff(c_5209, plain, (![A_379, B_380]: (k3_xboole_0(A_379, A_379)!=k1_xboole_0 | r1_xboole_0(A_379, B_380))), inference(resolution, [status(thm)], [c_10, c_5176])).
% 12.55/5.47  tff(c_5214, plain, (![B_381]: (r1_xboole_0(k1_xboole_0, B_381))), inference(superposition, [status(thm), theory('equality')], [c_12, c_5209])).
% 12.55/5.47  tff(c_5243, plain, (![C_385, B_386]: (~r2_hidden(C_385, B_386) | ~r2_hidden(C_385, k1_xboole_0))), inference(resolution, [status(thm)], [c_5214, c_6])).
% 12.55/5.47  tff(c_5422, plain, (![A_424, C_425]: (~r2_hidden(k4_tarski('#skF_9'(A_424, k2_relat_1(A_424), C_425), C_425), k1_xboole_0) | ~r2_hidden(C_425, k2_relat_1(A_424)))), inference(resolution, [status(thm)], [c_32, c_5243])).
% 12.55/5.47  tff(c_5426, plain, (![C_66]: (~r2_hidden(C_66, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_32, c_5422])).
% 12.55/5.47  tff(c_5431, plain, (![C_66]: (~r2_hidden(C_66, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_5426])).
% 12.55/5.47  tff(c_5132, plain, (k10_relat_1('#skF_11', '#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 12.55/5.47  tff(c_5299, plain, (![D_394, A_395, B_396, E_397]: (r2_hidden(D_394, k10_relat_1(A_395, B_396)) | ~r2_hidden(E_397, B_396) | ~r2_hidden(k4_tarski(D_394, E_397), A_395) | ~v1_relat_1(A_395))), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.55/5.47  tff(c_7990, plain, (![D_569, A_570, A_571, B_572]: (r2_hidden(D_569, k10_relat_1(A_570, A_571)) | ~r2_hidden(k4_tarski(D_569, '#skF_1'(A_571, B_572)), A_570) | ~v1_relat_1(A_570) | r1_xboole_0(A_571, B_572))), inference(resolution, [status(thm)], [c_10, c_5299])).
% 12.55/5.47  tff(c_28287, plain, (![A_1123, A_1124, B_1125]: (r2_hidden('#skF_9'(A_1123, k2_relat_1(A_1123), '#skF_1'(A_1124, B_1125)), k10_relat_1(A_1123, A_1124)) | ~v1_relat_1(A_1123) | r1_xboole_0(A_1124, B_1125) | ~r2_hidden('#skF_1'(A_1124, B_1125), k2_relat_1(A_1123)))), inference(resolution, [status(thm)], [c_32, c_7990])).
% 12.55/5.47  tff(c_28465, plain, (![B_1125]: (r2_hidden('#skF_9'('#skF_11', k2_relat_1('#skF_11'), '#skF_1'('#skF_10', B_1125)), k1_xboole_0) | ~v1_relat_1('#skF_11') | r1_xboole_0('#skF_10', B_1125) | ~r2_hidden('#skF_1'('#skF_10', B_1125), k2_relat_1('#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_5132, c_28287])).
% 12.55/5.47  tff(c_28496, plain, (![B_1125]: (r2_hidden('#skF_9'('#skF_11', k2_relat_1('#skF_11'), '#skF_1'('#skF_10', B_1125)), k1_xboole_0) | r1_xboole_0('#skF_10', B_1125) | ~r2_hidden('#skF_1'('#skF_10', B_1125), k2_relat_1('#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_28465])).
% 12.55/5.47  tff(c_28499, plain, (![B_1126]: (r1_xboole_0('#skF_10', B_1126) | ~r2_hidden('#skF_1'('#skF_10', B_1126), k2_relat_1('#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_5431, c_28496])).
% 12.55/5.47  tff(c_28504, plain, (r1_xboole_0('#skF_10', k2_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_8, c_28499])).
% 12.55/5.47  tff(c_28509, plain, (k3_xboole_0('#skF_10', k2_relat_1('#skF_11'))=k1_xboole_0), inference(resolution, [status(thm)], [c_28504, c_2])).
% 12.55/5.47  tff(c_28514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5195, c_28509])).
% 12.55/5.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.55/5.47  
% 12.55/5.47  Inference rules
% 12.55/5.47  ----------------------
% 12.55/5.47  #Ref     : 0
% 12.55/5.47  #Sup     : 6994
% 12.55/5.47  #Fact    : 0
% 12.55/5.47  #Define  : 0
% 12.55/5.47  #Split   : 18
% 12.55/5.47  #Chain   : 0
% 12.55/5.47  #Close   : 0
% 12.55/5.47  
% 12.55/5.47  Ordering : KBO
% 12.55/5.47  
% 12.55/5.47  Simplification rules
% 12.55/5.47  ----------------------
% 12.55/5.47  #Subsume      : 2461
% 12.55/5.47  #Demod        : 2499
% 12.55/5.47  #Tautology    : 1975
% 12.55/5.47  #SimpNegUnit  : 237
% 12.55/5.47  #BackRed      : 1
% 12.55/5.47  
% 12.55/5.47  #Partial instantiations: 0
% 12.55/5.47  #Strategies tried      : 1
% 12.55/5.47  
% 12.55/5.47  Timing (in seconds)
% 12.55/5.47  ----------------------
% 12.55/5.48  Preprocessing        : 0.30
% 12.55/5.48  Parsing              : 0.16
% 12.55/5.48  CNF conversion       : 0.03
% 12.55/5.48  Main loop            : 4.41
% 12.55/5.48  Inferencing          : 0.96
% 12.55/5.48  Reduction            : 0.86
% 12.55/5.48  Demodulation         : 0.55
% 12.55/5.48  BG Simplification    : 0.09
% 12.55/5.48  Subsumption          : 2.27
% 12.55/5.48  Abstraction          : 0.13
% 12.55/5.48  MUC search           : 0.00
% 12.55/5.48  Cooper               : 0.00
% 12.55/5.48  Total                : 4.75
% 12.55/5.48  Index Insertion      : 0.00
% 12.55/5.48  Index Deletion       : 0.00
% 12.55/5.48  Index Matching       : 0.00
% 12.55/5.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
