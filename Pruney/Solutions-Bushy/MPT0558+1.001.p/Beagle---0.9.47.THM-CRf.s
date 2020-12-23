%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0558+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:29 EST 2020

% Result     : Theorem 44.26s
% Output     : CNFRefutation 44.44s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 149 expanded)
%              Number of leaves         :   30 (  67 expanded)
%              Depth                    :   14
%              Number of atoms          :  187 ( 488 expanded)
%              Number of equality atoms :   23 (  66 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k9_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k2_relat_1 > #skF_13 > #skF_6 > #skF_1 > #skF_15 > #skF_12 > #skF_16 > #skF_2 > #skF_11 > #skF_4 > #skF_14 > #skF_3 > #skF_9 > #skF_8 > #skF_7 > #skF_5 > #skF_10

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

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
      ( r2_hidden(k4_tarski('#skF_6'(A_183,B_184),'#skF_5'(A_183,B_184)),A_183)
      | r2_hidden('#skF_7'(A_183,B_184),B_184)
      | k2_relat_1(A_183) = B_184 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [C_58,A_43,D_61] :
      ( r2_hidden(C_58,k2_relat_1(A_43))
      | ~ r2_hidden(k4_tarski(D_61,C_58),A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_84,plain,(
    ! [A_183,B_184] :
      ( r2_hidden('#skF_5'(A_183,B_184),k2_relat_1(A_183))
      | r2_hidden('#skF_7'(A_183,B_184),B_184)
      | k2_relat_1(A_183) = B_184 ) ),
    inference(resolution,[status(thm)],[c_77,c_22])).

tff(c_4,plain,(
    ! [A_1,B_24,D_39] :
      ( r2_hidden('#skF_4'(A_1,B_24,k9_relat_1(A_1,B_24),D_39),B_24)
      | ~ r2_hidden(D_39,k9_relat_1(A_1,B_24))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_43,C_58] :
      ( r2_hidden(k4_tarski('#skF_8'(A_43,k2_relat_1(A_43),C_58),C_58),A_43)
      | ~ r2_hidden(C_58,k2_relat_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_1,B_24,D_39] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1,B_24,k9_relat_1(A_1,B_24),D_39),D_39),A_1)
      | ~ r2_hidden(D_39,k9_relat_1(A_1,B_24))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_336,plain,(
    ! [B_239,D_240,E_243,A_242,F_241] :
      ( r2_hidden(k4_tarski(D_240,E_243),k5_relat_1(A_242,B_239))
      | ~ r2_hidden(k4_tarski(F_241,E_243),B_239)
      | ~ r2_hidden(k4_tarski(D_240,F_241),A_242)
      | ~ v1_relat_1(k5_relat_1(A_242,B_239))
      | ~ v1_relat_1(B_239)
      | ~ v1_relat_1(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2985,plain,(
    ! [D_507,B_508,A_511,D_510,A_509] :
      ( r2_hidden(k4_tarski(D_507,D_510),k5_relat_1(A_509,A_511))
      | ~ r2_hidden(k4_tarski(D_507,'#skF_4'(A_511,B_508,k9_relat_1(A_511,B_508),D_510)),A_509)
      | ~ v1_relat_1(k5_relat_1(A_509,A_511))
      | ~ v1_relat_1(A_509)
      | ~ r2_hidden(D_510,k9_relat_1(A_511,B_508))
      | ~ v1_relat_1(A_511) ) ),
    inference(resolution,[status(thm)],[c_6,c_336])).

tff(c_76094,plain,(
    ! [A_1998,A_1999,B_2000,D_2001] :
      ( r2_hidden(k4_tarski('#skF_8'(A_1998,k2_relat_1(A_1998),'#skF_4'(A_1999,B_2000,k9_relat_1(A_1999,B_2000),D_2001)),D_2001),k5_relat_1(A_1998,A_1999))
      | ~ v1_relat_1(k5_relat_1(A_1998,A_1999))
      | ~ v1_relat_1(A_1998)
      | ~ r2_hidden(D_2001,k9_relat_1(A_1999,B_2000))
      | ~ v1_relat_1(A_1999)
      | ~ r2_hidden('#skF_4'(A_1999,B_2000,k9_relat_1(A_1999,B_2000),D_2001),k2_relat_1(A_1998)) ) ),
    inference(resolution,[status(thm)],[c_20,c_2985])).

tff(c_76221,plain,(
    ! [D_2002,A_2003,A_2004,B_2005] :
      ( r2_hidden(D_2002,k2_relat_1(k5_relat_1(A_2003,A_2004)))
      | ~ v1_relat_1(k5_relat_1(A_2003,A_2004))
      | ~ v1_relat_1(A_2003)
      | ~ r2_hidden(D_2002,k9_relat_1(A_2004,B_2005))
      | ~ v1_relat_1(A_2004)
      | ~ r2_hidden('#skF_4'(A_2004,B_2005,k9_relat_1(A_2004,B_2005),D_2002),k2_relat_1(A_2003)) ) ),
    inference(resolution,[status(thm)],[c_76094,c_22])).

tff(c_76311,plain,(
    ! [D_2006,A_2007,A_2008] :
      ( r2_hidden(D_2006,k2_relat_1(k5_relat_1(A_2007,A_2008)))
      | ~ v1_relat_1(k5_relat_1(A_2007,A_2008))
      | ~ v1_relat_1(A_2007)
      | ~ r2_hidden(D_2006,k9_relat_1(A_2008,k2_relat_1(A_2007)))
      | ~ v1_relat_1(A_2008) ) ),
    inference(resolution,[status(thm)],[c_4,c_76221])).

tff(c_84874,plain,(
    ! [A_2102,A_2103,A_2104] :
      ( r2_hidden('#skF_7'(A_2102,k9_relat_1(A_2103,k2_relat_1(A_2104))),k2_relat_1(k5_relat_1(A_2104,A_2103)))
      | ~ v1_relat_1(k5_relat_1(A_2104,A_2103))
      | ~ v1_relat_1(A_2104)
      | ~ v1_relat_1(A_2103)
      | r2_hidden('#skF_5'(A_2102,k9_relat_1(A_2103,k2_relat_1(A_2104))),k2_relat_1(A_2102))
      | k9_relat_1(A_2103,k2_relat_1(A_2104)) = k2_relat_1(A_2102) ) ),
    inference(resolution,[status(thm)],[c_84,c_76311])).

tff(c_150,plain,(
    ! [A_199,B_200,D_201] :
      ( r2_hidden(k4_tarski('#skF_6'(A_199,B_200),'#skF_5'(A_199,B_200)),A_199)
      | ~ r2_hidden(k4_tarski(D_201,'#skF_7'(A_199,B_200)),A_199)
      | k2_relat_1(A_199) = B_200 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_159,plain,(
    ! [A_202,B_203] :
      ( r2_hidden(k4_tarski('#skF_6'(A_202,B_203),'#skF_5'(A_202,B_203)),A_202)
      | k2_relat_1(A_202) = B_203
      | ~ r2_hidden('#skF_7'(A_202,B_203),k2_relat_1(A_202)) ) ),
    inference(resolution,[status(thm)],[c_20,c_150])).

tff(c_171,plain,(
    ! [A_202,B_203] :
      ( r2_hidden('#skF_5'(A_202,B_203),k2_relat_1(A_202))
      | k2_relat_1(A_202) = B_203
      | ~ r2_hidden('#skF_7'(A_202,B_203),k2_relat_1(A_202)) ) ),
    inference(resolution,[status(thm)],[c_159,c_22])).

tff(c_85139,plain,(
    ! [A_2104,A_2103] :
      ( ~ v1_relat_1(k5_relat_1(A_2104,A_2103))
      | ~ v1_relat_1(A_2104)
      | ~ v1_relat_1(A_2103)
      | r2_hidden('#skF_5'(k5_relat_1(A_2104,A_2103),k9_relat_1(A_2103,k2_relat_1(A_2104))),k2_relat_1(k5_relat_1(A_2104,A_2103)))
      | k9_relat_1(A_2103,k2_relat_1(A_2104)) = k2_relat_1(k5_relat_1(A_2104,A_2103)) ) ),
    inference(resolution,[status(thm)],[c_84874,c_171])).

tff(c_46,plain,(
    ! [B_114,D_153,A_62,E_154] :
      ( r2_hidden(k4_tarski('#skF_9'(B_114,D_153,A_62,E_154,k5_relat_1(A_62,B_114)),E_154),B_114)
      | ~ r2_hidden(k4_tarski(D_153,E_154),k5_relat_1(A_62,B_114))
      | ~ v1_relat_1(k5_relat_1(A_62,B_114))
      | ~ v1_relat_1(B_114)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_643,plain,(
    ! [D_275,B_276,A_277,E_278] :
      ( r2_hidden(k4_tarski(D_275,'#skF_9'(B_276,D_275,A_277,E_278,k5_relat_1(A_277,B_276))),A_277)
      | ~ r2_hidden(k4_tarski(D_275,E_278),k5_relat_1(A_277,B_276))
      | ~ v1_relat_1(k5_relat_1(A_277,B_276))
      | ~ v1_relat_1(B_276)
      | ~ v1_relat_1(A_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_756,plain,(
    ! [B_307,D_308,A_309,E_310] :
      ( r2_hidden('#skF_9'(B_307,D_308,A_309,E_310,k5_relat_1(A_309,B_307)),k2_relat_1(A_309))
      | ~ r2_hidden(k4_tarski(D_308,E_310),k5_relat_1(A_309,B_307))
      | ~ v1_relat_1(k5_relat_1(A_309,B_307))
      | ~ v1_relat_1(B_307)
      | ~ v1_relat_1(A_309) ) ),
    inference(resolution,[status(thm)],[c_643,c_22])).

tff(c_2,plain,(
    ! [D_39,A_1,B_24,E_42] :
      ( r2_hidden(D_39,k9_relat_1(A_1,B_24))
      | ~ r2_hidden(E_42,B_24)
      | ~ r2_hidden(k4_tarski(E_42,D_39),A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_11013,plain,(
    ! [B_932,A_928,D_930,D_927,A_931,E_929] :
      ( r2_hidden(D_930,k9_relat_1(A_931,k2_relat_1(A_928)))
      | ~ r2_hidden(k4_tarski('#skF_9'(B_932,D_927,A_928,E_929,k5_relat_1(A_928,B_932)),D_930),A_931)
      | ~ v1_relat_1(A_931)
      | ~ r2_hidden(k4_tarski(D_927,E_929),k5_relat_1(A_928,B_932))
      | ~ v1_relat_1(k5_relat_1(A_928,B_932))
      | ~ v1_relat_1(B_932)
      | ~ v1_relat_1(A_928) ) ),
    inference(resolution,[status(thm)],[c_756,c_2])).

tff(c_11043,plain,(
    ! [E_933,B_934,A_935,D_936] :
      ( r2_hidden(E_933,k9_relat_1(B_934,k2_relat_1(A_935)))
      | ~ r2_hidden(k4_tarski(D_936,E_933),k5_relat_1(A_935,B_934))
      | ~ v1_relat_1(k5_relat_1(A_935,B_934))
      | ~ v1_relat_1(B_934)
      | ~ v1_relat_1(A_935) ) ),
    inference(resolution,[status(thm)],[c_46,c_11013])).

tff(c_11149,plain,(
    ! [C_58,B_934,A_935] :
      ( r2_hidden(C_58,k9_relat_1(B_934,k2_relat_1(A_935)))
      | ~ v1_relat_1(k5_relat_1(A_935,B_934))
      | ~ v1_relat_1(B_934)
      | ~ v1_relat_1(A_935)
      | ~ r2_hidden(C_58,k2_relat_1(k5_relat_1(A_935,B_934))) ) ),
    inference(resolution,[status(thm)],[c_20,c_11043])).

tff(c_28,plain,(
    ! [A_43,B_44] :
      ( ~ r2_hidden('#skF_5'(A_43,B_44),B_44)
      | r2_hidden('#skF_7'(A_43,B_44),B_44)
      | k2_relat_1(A_43) = B_44 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_76761,plain,(
    ! [A_43,A_2008,A_2007] :
      ( r2_hidden('#skF_7'(A_43,k9_relat_1(A_2008,k2_relat_1(A_2007))),k2_relat_1(k5_relat_1(A_2007,A_2008)))
      | ~ v1_relat_1(k5_relat_1(A_2007,A_2008))
      | ~ v1_relat_1(A_2007)
      | ~ v1_relat_1(A_2008)
      | ~ r2_hidden('#skF_5'(A_43,k9_relat_1(A_2008,k2_relat_1(A_2007))),k9_relat_1(A_2008,k2_relat_1(A_2007)))
      | k9_relat_1(A_2008,k2_relat_1(A_2007)) = k2_relat_1(A_43) ) ),
    inference(resolution,[status(thm)],[c_28,c_76311])).

tff(c_85193,plain,(
    ! [A_2105,A_2106] :
      ( ~ v1_relat_1(k5_relat_1(A_2105,A_2106))
      | ~ v1_relat_1(A_2105)
      | ~ v1_relat_1(A_2106)
      | r2_hidden('#skF_5'(k5_relat_1(A_2105,A_2106),k9_relat_1(A_2106,k2_relat_1(A_2105))),k2_relat_1(k5_relat_1(A_2105,A_2106)))
      | k9_relat_1(A_2106,k2_relat_1(A_2105)) = k2_relat_1(k5_relat_1(A_2105,A_2106)) ) ),
    inference(resolution,[status(thm)],[c_84874,c_171])).

tff(c_11150,plain,(
    ! [C_937,B_938,A_939] :
      ( r2_hidden(C_937,k9_relat_1(B_938,k2_relat_1(A_939)))
      | ~ v1_relat_1(k5_relat_1(A_939,B_938))
      | ~ v1_relat_1(B_938)
      | ~ v1_relat_1(A_939)
      | ~ r2_hidden(C_937,k2_relat_1(k5_relat_1(A_939,B_938))) ) ),
    inference(resolution,[status(thm)],[c_20,c_11043])).

tff(c_24,plain,(
    ! [A_43,B_44,D_57] :
      ( ~ r2_hidden('#skF_5'(A_43,B_44),B_44)
      | ~ r2_hidden(k4_tarski(D_57,'#skF_7'(A_43,B_44)),A_43)
      | k2_relat_1(A_43) = B_44 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_34739,plain,(
    ! [D_1321,A_1322,B_1323,A_1324] :
      ( ~ r2_hidden(k4_tarski(D_1321,'#skF_7'(A_1322,k9_relat_1(B_1323,k2_relat_1(A_1324)))),A_1322)
      | k9_relat_1(B_1323,k2_relat_1(A_1324)) = k2_relat_1(A_1322)
      | ~ v1_relat_1(k5_relat_1(A_1324,B_1323))
      | ~ v1_relat_1(B_1323)
      | ~ v1_relat_1(A_1324)
      | ~ r2_hidden('#skF_5'(A_1322,k9_relat_1(B_1323,k2_relat_1(A_1324))),k2_relat_1(k5_relat_1(A_1324,B_1323))) ) ),
    inference(resolution,[status(thm)],[c_11150,c_24])).

tff(c_34827,plain,(
    ! [B_1323,A_1324,A_43] :
      ( k9_relat_1(B_1323,k2_relat_1(A_1324)) = k2_relat_1(A_43)
      | ~ v1_relat_1(k5_relat_1(A_1324,B_1323))
      | ~ v1_relat_1(B_1323)
      | ~ v1_relat_1(A_1324)
      | ~ r2_hidden('#skF_5'(A_43,k9_relat_1(B_1323,k2_relat_1(A_1324))),k2_relat_1(k5_relat_1(A_1324,B_1323)))
      | ~ r2_hidden('#skF_7'(A_43,k9_relat_1(B_1323,k2_relat_1(A_1324))),k2_relat_1(A_43)) ) ),
    inference(resolution,[status(thm)],[c_20,c_34739])).

tff(c_87477,plain,(
    ! [A_2132,A_2133] :
      ( ~ r2_hidden('#skF_7'(k5_relat_1(A_2132,A_2133),k9_relat_1(A_2133,k2_relat_1(A_2132))),k2_relat_1(k5_relat_1(A_2132,A_2133)))
      | ~ v1_relat_1(k5_relat_1(A_2132,A_2133))
      | ~ v1_relat_1(A_2132)
      | ~ v1_relat_1(A_2133)
      | k9_relat_1(A_2133,k2_relat_1(A_2132)) = k2_relat_1(k5_relat_1(A_2132,A_2133)) ) ),
    inference(resolution,[status(thm)],[c_85193,c_34827])).

tff(c_87488,plain,(
    ! [A_2134,A_2135] :
      ( ~ v1_relat_1(k5_relat_1(A_2134,A_2135))
      | ~ v1_relat_1(A_2134)
      | ~ v1_relat_1(A_2135)
      | ~ r2_hidden('#skF_5'(k5_relat_1(A_2134,A_2135),k9_relat_1(A_2135,k2_relat_1(A_2134))),k9_relat_1(A_2135,k2_relat_1(A_2134)))
      | k9_relat_1(A_2135,k2_relat_1(A_2134)) = k2_relat_1(k5_relat_1(A_2134,A_2135)) ) ),
    inference(resolution,[status(thm)],[c_76761,c_87477])).

tff(c_87496,plain,(
    ! [B_2136,A_2137] :
      ( k9_relat_1(B_2136,k2_relat_1(A_2137)) = k2_relat_1(k5_relat_1(A_2137,B_2136))
      | ~ v1_relat_1(k5_relat_1(A_2137,B_2136))
      | ~ v1_relat_1(B_2136)
      | ~ v1_relat_1(A_2137)
      | ~ r2_hidden('#skF_5'(k5_relat_1(A_2137,B_2136),k9_relat_1(B_2136,k2_relat_1(A_2137))),k2_relat_1(k5_relat_1(A_2137,B_2136))) ) ),
    inference(resolution,[status(thm)],[c_11149,c_87488])).

tff(c_87524,plain,(
    ! [A_2138,A_2139] :
      ( ~ v1_relat_1(k5_relat_1(A_2138,A_2139))
      | ~ v1_relat_1(A_2138)
      | ~ v1_relat_1(A_2139)
      | k9_relat_1(A_2139,k2_relat_1(A_2138)) = k2_relat_1(k5_relat_1(A_2138,A_2139)) ) ),
    inference(resolution,[status(thm)],[c_85139,c_87496])).

tff(c_87626,plain,(
    ! [B_2146,A_2147] :
      ( k9_relat_1(B_2146,k2_relat_1(A_2147)) = k2_relat_1(k5_relat_1(A_2147,B_2146))
      | ~ v1_relat_1(B_2146)
      | ~ v1_relat_1(A_2147) ) ),
    inference(resolution,[status(thm)],[c_50,c_87524])).

tff(c_52,plain,(
    k9_relat_1('#skF_16',k2_relat_1('#skF_15')) != k2_relat_1(k5_relat_1('#skF_15','#skF_16')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_89188,plain,
    ( ~ v1_relat_1('#skF_16')
    | ~ v1_relat_1('#skF_15') ),
    inference(superposition,[status(thm),theory(equality)],[c_87626,c_52])).

tff(c_89196,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_89188])).

%------------------------------------------------------------------------------
