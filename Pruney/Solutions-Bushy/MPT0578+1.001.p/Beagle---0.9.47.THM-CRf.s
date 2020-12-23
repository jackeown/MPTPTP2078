%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0578+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:32 EST 2020

% Result     : Theorem 42.11s
% Output     : CNFRefutation 42.11s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 149 expanded)
%              Number of leaves         :   30 (  67 expanded)
%              Depth                    :   14
%              Number of atoms          :  182 ( 488 expanded)
%              Number of equality atoms :   22 (  66 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k5_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k1_relat_1 > #skF_13 > #skF_6 > #skF_1 > #skF_15 > #skF_12 > #skF_16 > #skF_2 > #skF_11 > #skF_4 > #skF_14 > #skF_3 > #skF_9 > #skF_8 > #skF_7 > #skF_5 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_12',type,(
    '#skF_12': ( $i * $i * $i ) > $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': ( $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_37,axiom,(
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

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

tff(c_56,plain,(
    v1_relat_1('#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_54,plain,(
    v1_relat_1('#skF_16') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_50,plain,(
    ! [A_161,B_162] :
      ( v1_relat_1(k5_relat_1(A_161,B_162))
      | ~ v1_relat_1(B_162)
      | ~ v1_relat_1(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_77,plain,(
    ! [A_183,B_184] :
      ( r2_hidden(k4_tarski('#skF_5'(A_183,B_184),'#skF_6'(A_183,B_184)),A_183)
      | r2_hidden('#skF_7'(A_183,B_184),B_184)
      | k1_relat_1(A_183) = B_184 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [C_58,A_43,D_61] :
      ( r2_hidden(C_58,k1_relat_1(A_43))
      | ~ r2_hidden(k4_tarski(C_58,D_61),A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_84,plain,(
    ! [A_183,B_184] :
      ( r2_hidden('#skF_5'(A_183,B_184),k1_relat_1(A_183))
      | r2_hidden('#skF_7'(A_183,B_184),B_184)
      | k1_relat_1(A_183) = B_184 ) ),
    inference(resolution,[status(thm)],[c_77,c_22])).

tff(c_4,plain,(
    ! [A_1,B_24,D_39] :
      ( r2_hidden('#skF_4'(A_1,B_24,k10_relat_1(A_1,B_24),D_39),B_24)
      | ~ r2_hidden(D_39,k10_relat_1(A_1,B_24))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [D_39,A_1,B_24] :
      ( r2_hidden(k4_tarski(D_39,'#skF_4'(A_1,B_24,k10_relat_1(A_1,B_24),D_39)),A_1)
      | ~ r2_hidden(D_39,k10_relat_1(A_1,B_24))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [C_58,A_43] :
      ( r2_hidden(k4_tarski(C_58,'#skF_8'(A_43,k1_relat_1(A_43),C_58)),A_43)
      | ~ r2_hidden(C_58,k1_relat_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_336,plain,(
    ! [B_239,D_240,E_243,A_242,F_241] :
      ( r2_hidden(k4_tarski(D_240,E_243),k5_relat_1(A_242,B_239))
      | ~ r2_hidden(k4_tarski(F_241,E_243),B_239)
      | ~ r2_hidden(k4_tarski(D_240,F_241),A_242)
      | ~ v1_relat_1(k5_relat_1(A_242,B_239))
      | ~ v1_relat_1(B_239)
      | ~ v1_relat_1(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1645,plain,(
    ! [D_390,A_391,C_392,A_393] :
      ( r2_hidden(k4_tarski(D_390,'#skF_8'(A_391,k1_relat_1(A_391),C_392)),k5_relat_1(A_393,A_391))
      | ~ r2_hidden(k4_tarski(D_390,C_392),A_393)
      | ~ v1_relat_1(k5_relat_1(A_393,A_391))
      | ~ v1_relat_1(A_391)
      | ~ v1_relat_1(A_393)
      | ~ r2_hidden(C_392,k1_relat_1(A_391)) ) ),
    inference(resolution,[status(thm)],[c_20,c_336])).

tff(c_1672,plain,(
    ! [D_394,A_395,A_396,C_397] :
      ( r2_hidden(D_394,k1_relat_1(k5_relat_1(A_395,A_396)))
      | ~ r2_hidden(k4_tarski(D_394,C_397),A_395)
      | ~ v1_relat_1(k5_relat_1(A_395,A_396))
      | ~ v1_relat_1(A_396)
      | ~ v1_relat_1(A_395)
      | ~ r2_hidden(C_397,k1_relat_1(A_396)) ) ),
    inference(resolution,[status(thm)],[c_1645,c_22])).

tff(c_2880,plain,(
    ! [D_486,A_487,A_488,B_489] :
      ( r2_hidden(D_486,k1_relat_1(k5_relat_1(A_487,A_488)))
      | ~ v1_relat_1(k5_relat_1(A_487,A_488))
      | ~ v1_relat_1(A_488)
      | ~ r2_hidden('#skF_4'(A_487,B_489,k10_relat_1(A_487,B_489),D_486),k1_relat_1(A_488))
      | ~ r2_hidden(D_486,k10_relat_1(A_487,B_489))
      | ~ v1_relat_1(A_487) ) ),
    inference(resolution,[status(thm)],[c_6,c_1672])).

tff(c_2890,plain,(
    ! [D_490,A_491,A_492] :
      ( r2_hidden(D_490,k1_relat_1(k5_relat_1(A_491,A_492)))
      | ~ v1_relat_1(k5_relat_1(A_491,A_492))
      | ~ v1_relat_1(A_492)
      | ~ r2_hidden(D_490,k10_relat_1(A_491,k1_relat_1(A_492)))
      | ~ v1_relat_1(A_491) ) ),
    inference(resolution,[status(thm)],[c_4,c_2880])).

tff(c_18981,plain,(
    ! [A_1115,A_1116,A_1117] :
      ( r2_hidden('#skF_7'(A_1115,k10_relat_1(A_1116,k1_relat_1(A_1117))),k1_relat_1(k5_relat_1(A_1116,A_1117)))
      | ~ v1_relat_1(k5_relat_1(A_1116,A_1117))
      | ~ v1_relat_1(A_1117)
      | ~ v1_relat_1(A_1116)
      | r2_hidden('#skF_5'(A_1115,k10_relat_1(A_1116,k1_relat_1(A_1117))),k1_relat_1(A_1115))
      | k1_relat_1(A_1115) = k10_relat_1(A_1116,k1_relat_1(A_1117)) ) ),
    inference(resolution,[status(thm)],[c_84,c_2890])).

tff(c_150,plain,(
    ! [A_199,B_200,D_201] :
      ( r2_hidden(k4_tarski('#skF_5'(A_199,B_200),'#skF_6'(A_199,B_200)),A_199)
      | ~ r2_hidden(k4_tarski('#skF_7'(A_199,B_200),D_201),A_199)
      | k1_relat_1(A_199) = B_200 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_159,plain,(
    ! [A_202,B_203] :
      ( r2_hidden(k4_tarski('#skF_5'(A_202,B_203),'#skF_6'(A_202,B_203)),A_202)
      | k1_relat_1(A_202) = B_203
      | ~ r2_hidden('#skF_7'(A_202,B_203),k1_relat_1(A_202)) ) ),
    inference(resolution,[status(thm)],[c_20,c_150])).

tff(c_171,plain,(
    ! [A_202,B_203] :
      ( r2_hidden('#skF_5'(A_202,B_203),k1_relat_1(A_202))
      | k1_relat_1(A_202) = B_203
      | ~ r2_hidden('#skF_7'(A_202,B_203),k1_relat_1(A_202)) ) ),
    inference(resolution,[status(thm)],[c_159,c_22])).

tff(c_19067,plain,(
    ! [A_1116,A_1117] :
      ( ~ v1_relat_1(k5_relat_1(A_1116,A_1117))
      | ~ v1_relat_1(A_1117)
      | ~ v1_relat_1(A_1116)
      | r2_hidden('#skF_5'(k5_relat_1(A_1116,A_1117),k10_relat_1(A_1116,k1_relat_1(A_1117))),k1_relat_1(k5_relat_1(A_1116,A_1117)))
      | k10_relat_1(A_1116,k1_relat_1(A_1117)) = k1_relat_1(k5_relat_1(A_1116,A_1117)) ) ),
    inference(resolution,[status(thm)],[c_18981,c_171])).

tff(c_48,plain,(
    ! [D_153,B_114,A_62,E_154] :
      ( r2_hidden(k4_tarski(D_153,'#skF_9'(B_114,D_153,A_62,E_154,k5_relat_1(A_62,B_114))),A_62)
      | ~ r2_hidden(k4_tarski(D_153,E_154),k5_relat_1(A_62,B_114))
      | ~ v1_relat_1(k5_relat_1(A_62,B_114))
      | ~ v1_relat_1(B_114)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_416,plain,(
    ! [B_260,D_261,A_262,E_263] :
      ( r2_hidden(k4_tarski('#skF_9'(B_260,D_261,A_262,E_263,k5_relat_1(A_262,B_260)),E_263),B_260)
      | ~ r2_hidden(k4_tarski(D_261,E_263),k5_relat_1(A_262,B_260))
      | ~ v1_relat_1(k5_relat_1(A_262,B_260))
      | ~ v1_relat_1(B_260)
      | ~ v1_relat_1(A_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_756,plain,(
    ! [B_307,D_308,A_309,E_310] :
      ( r2_hidden('#skF_9'(B_307,D_308,A_309,E_310,k5_relat_1(A_309,B_307)),k1_relat_1(B_307))
      | ~ r2_hidden(k4_tarski(D_308,E_310),k5_relat_1(A_309,B_307))
      | ~ v1_relat_1(k5_relat_1(A_309,B_307))
      | ~ v1_relat_1(B_307)
      | ~ v1_relat_1(A_309) ) ),
    inference(resolution,[status(thm)],[c_416,c_22])).

tff(c_2,plain,(
    ! [D_39,A_1,B_24,E_42] :
      ( r2_hidden(D_39,k10_relat_1(A_1,B_24))
      | ~ r2_hidden(E_42,B_24)
      | ~ r2_hidden(k4_tarski(D_39,E_42),A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22280,plain,(
    ! [B_1205,E_1202,D_1203,A_1201,D_1200,A_1204] :
      ( r2_hidden(D_1203,k10_relat_1(A_1204,k1_relat_1(B_1205)))
      | ~ r2_hidden(k4_tarski(D_1203,'#skF_9'(B_1205,D_1200,A_1201,E_1202,k5_relat_1(A_1201,B_1205))),A_1204)
      | ~ v1_relat_1(A_1204)
      | ~ r2_hidden(k4_tarski(D_1200,E_1202),k5_relat_1(A_1201,B_1205))
      | ~ v1_relat_1(k5_relat_1(A_1201,B_1205))
      | ~ v1_relat_1(B_1205)
      | ~ v1_relat_1(A_1201) ) ),
    inference(resolution,[status(thm)],[c_756,c_2])).

tff(c_22324,plain,(
    ! [D_1206,A_1207,B_1208,E_1209] :
      ( r2_hidden(D_1206,k10_relat_1(A_1207,k1_relat_1(B_1208)))
      | ~ r2_hidden(k4_tarski(D_1206,E_1209),k5_relat_1(A_1207,B_1208))
      | ~ v1_relat_1(k5_relat_1(A_1207,B_1208))
      | ~ v1_relat_1(B_1208)
      | ~ v1_relat_1(A_1207) ) ),
    inference(resolution,[status(thm)],[c_48,c_22280])).

tff(c_22438,plain,(
    ! [C_58,A_1207,B_1208] :
      ( r2_hidden(C_58,k10_relat_1(A_1207,k1_relat_1(B_1208)))
      | ~ v1_relat_1(k5_relat_1(A_1207,B_1208))
      | ~ v1_relat_1(B_1208)
      | ~ v1_relat_1(A_1207)
      | ~ r2_hidden(C_58,k1_relat_1(k5_relat_1(A_1207,B_1208))) ) ),
    inference(resolution,[status(thm)],[c_20,c_22324])).

tff(c_28,plain,(
    ! [A_43,B_44] :
      ( ~ r2_hidden('#skF_5'(A_43,B_44),B_44)
      | r2_hidden('#skF_7'(A_43,B_44),B_44)
      | k1_relat_1(A_43) = B_44 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_82065,plain,(
    ! [A_2000,A_2001,A_2002] :
      ( r2_hidden('#skF_7'(A_2000,k10_relat_1(A_2001,k1_relat_1(A_2002))),k1_relat_1(k5_relat_1(A_2001,A_2002)))
      | ~ v1_relat_1(k5_relat_1(A_2001,A_2002))
      | ~ v1_relat_1(A_2002)
      | ~ v1_relat_1(A_2001)
      | ~ r2_hidden('#skF_5'(A_2000,k10_relat_1(A_2001,k1_relat_1(A_2002))),k10_relat_1(A_2001,k1_relat_1(A_2002)))
      | k1_relat_1(A_2000) = k10_relat_1(A_2001,k1_relat_1(A_2002)) ) ),
    inference(resolution,[status(thm)],[c_28,c_2890])).

tff(c_22468,plain,(
    ! [C_1215,A_1216,B_1217] :
      ( r2_hidden(C_1215,k10_relat_1(A_1216,k1_relat_1(B_1217)))
      | ~ v1_relat_1(k5_relat_1(A_1216,B_1217))
      | ~ v1_relat_1(B_1217)
      | ~ v1_relat_1(A_1216)
      | ~ r2_hidden(C_1215,k1_relat_1(k5_relat_1(A_1216,B_1217))) ) ),
    inference(resolution,[status(thm)],[c_20,c_22324])).

tff(c_24,plain,(
    ! [A_43,B_44,D_57] :
      ( ~ r2_hidden('#skF_5'(A_43,B_44),B_44)
      | ~ r2_hidden(k4_tarski('#skF_7'(A_43,B_44),D_57),A_43)
      | k1_relat_1(A_43) = B_44 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_53261,plain,(
    ! [A_1648,A_1649,B_1650,D_1651] :
      ( ~ r2_hidden(k4_tarski('#skF_7'(A_1648,k10_relat_1(A_1649,k1_relat_1(B_1650))),D_1651),A_1648)
      | k1_relat_1(A_1648) = k10_relat_1(A_1649,k1_relat_1(B_1650))
      | ~ v1_relat_1(k5_relat_1(A_1649,B_1650))
      | ~ v1_relat_1(B_1650)
      | ~ v1_relat_1(A_1649)
      | ~ r2_hidden('#skF_5'(A_1648,k10_relat_1(A_1649,k1_relat_1(B_1650))),k1_relat_1(k5_relat_1(A_1649,B_1650))) ) ),
    inference(resolution,[status(thm)],[c_22468,c_24])).

tff(c_53414,plain,(
    ! [A_1652,A_1653,B_1654] :
      ( k1_relat_1(A_1652) = k10_relat_1(A_1653,k1_relat_1(B_1654))
      | ~ v1_relat_1(k5_relat_1(A_1653,B_1654))
      | ~ v1_relat_1(B_1654)
      | ~ v1_relat_1(A_1653)
      | ~ r2_hidden('#skF_5'(A_1652,k10_relat_1(A_1653,k1_relat_1(B_1654))),k1_relat_1(k5_relat_1(A_1653,B_1654)))
      | ~ r2_hidden('#skF_7'(A_1652,k10_relat_1(A_1653,k1_relat_1(B_1654))),k1_relat_1(A_1652)) ) ),
    inference(resolution,[status(thm)],[c_20,c_53261])).

tff(c_53434,plain,(
    ! [A_1116,A_1117] :
      ( ~ r2_hidden('#skF_7'(k5_relat_1(A_1116,A_1117),k10_relat_1(A_1116,k1_relat_1(A_1117))),k1_relat_1(k5_relat_1(A_1116,A_1117)))
      | ~ v1_relat_1(k5_relat_1(A_1116,A_1117))
      | ~ v1_relat_1(A_1117)
      | ~ v1_relat_1(A_1116)
      | k10_relat_1(A_1116,k1_relat_1(A_1117)) = k1_relat_1(k5_relat_1(A_1116,A_1117)) ) ),
    inference(resolution,[status(thm)],[c_19067,c_53414])).

tff(c_82131,plain,(
    ! [A_2003,A_2004] :
      ( ~ v1_relat_1(k5_relat_1(A_2003,A_2004))
      | ~ v1_relat_1(A_2004)
      | ~ v1_relat_1(A_2003)
      | ~ r2_hidden('#skF_5'(k5_relat_1(A_2003,A_2004),k10_relat_1(A_2003,k1_relat_1(A_2004))),k10_relat_1(A_2003,k1_relat_1(A_2004)))
      | k10_relat_1(A_2003,k1_relat_1(A_2004)) = k1_relat_1(k5_relat_1(A_2003,A_2004)) ) ),
    inference(resolution,[status(thm)],[c_82065,c_53434])).

tff(c_82144,plain,(
    ! [A_2005,B_2006] :
      ( k10_relat_1(A_2005,k1_relat_1(B_2006)) = k1_relat_1(k5_relat_1(A_2005,B_2006))
      | ~ v1_relat_1(k5_relat_1(A_2005,B_2006))
      | ~ v1_relat_1(B_2006)
      | ~ v1_relat_1(A_2005)
      | ~ r2_hidden('#skF_5'(k5_relat_1(A_2005,B_2006),k10_relat_1(A_2005,k1_relat_1(B_2006))),k1_relat_1(k5_relat_1(A_2005,B_2006))) ) ),
    inference(resolution,[status(thm)],[c_22438,c_82131])).

tff(c_82264,plain,(
    ! [A_2013,A_2014] :
      ( ~ v1_relat_1(k5_relat_1(A_2013,A_2014))
      | ~ v1_relat_1(A_2014)
      | ~ v1_relat_1(A_2013)
      | k10_relat_1(A_2013,k1_relat_1(A_2014)) = k1_relat_1(k5_relat_1(A_2013,A_2014)) ) ),
    inference(resolution,[status(thm)],[c_19067,c_82144])).

tff(c_82269,plain,(
    ! [A_2015,B_2016] :
      ( k10_relat_1(A_2015,k1_relat_1(B_2016)) = k1_relat_1(k5_relat_1(A_2015,B_2016))
      | ~ v1_relat_1(B_2016)
      | ~ v1_relat_1(A_2015) ) ),
    inference(resolution,[status(thm)],[c_50,c_82264])).

tff(c_52,plain,(
    k10_relat_1('#skF_15',k1_relat_1('#skF_16')) != k1_relat_1(k5_relat_1('#skF_15','#skF_16')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_83596,plain,
    ( ~ v1_relat_1('#skF_16')
    | ~ v1_relat_1('#skF_15') ),
    inference(superposition,[status(thm),theory(equality)],[c_82269,c_52])).

tff(c_83604,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_83596])).

%------------------------------------------------------------------------------
