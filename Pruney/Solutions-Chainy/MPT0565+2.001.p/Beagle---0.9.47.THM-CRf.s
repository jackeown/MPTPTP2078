%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:14 EST 2020

% Result     : Theorem 42.16s
% Output     : CNFRefutation 42.25s
% Verified   : 
% Statistics : Number of formulae       :   62 (  93 expanded)
%              Number of leaves         :   26 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  119 ( 212 expanded)
%              Number of equality atoms :   25 (  46 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_1 > #skF_12 > #skF_13 > #skF_10 > #skF_2 > #skF_4 > #skF_3 > #skF_8 > #skF_7 > #skF_9 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

tff(c_46,plain,(
    v1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30,plain,(
    ! [A_43,B_44] :
      ( r2_hidden(k4_tarski('#skF_5'(A_43,B_44),'#skF_6'(A_43,B_44)),A_43)
      | r2_hidden('#skF_7'(A_43,B_44),B_44)
      | k1_relat_1(A_43) = B_44 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_96,plain,(
    ! [A_112,B_113] :
      ( r2_hidden(k4_tarski('#skF_5'(A_112,B_113),'#skF_6'(A_112,B_113)),A_112)
      | r2_hidden('#skF_7'(A_112,B_113),B_113)
      | k1_relat_1(A_112) = B_113 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    ! [C_77,A_62,D_80] :
      ( r2_hidden(C_77,k2_relat_1(A_62))
      | ~ r2_hidden(k4_tarski(D_80,C_77),A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_128,plain,(
    ! [A_118,B_119] :
      ( r2_hidden('#skF_6'(A_118,B_119),k2_relat_1(A_118))
      | r2_hidden('#skF_7'(A_118,B_119),B_119)
      | k1_relat_1(A_118) = B_119 ) ),
    inference(resolution,[status(thm)],[c_96,c_34])).

tff(c_2,plain,(
    ! [D_39,A_1,B_24,E_42] :
      ( r2_hidden(D_39,k10_relat_1(A_1,B_24))
      | ~ r2_hidden(E_42,B_24)
      | ~ r2_hidden(k4_tarski(D_39,E_42),A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_7215,plain,(
    ! [D_451,A_452,A_453,B_454] :
      ( r2_hidden(D_451,k10_relat_1(A_452,k2_relat_1(A_453)))
      | ~ r2_hidden(k4_tarski(D_451,'#skF_6'(A_453,B_454)),A_452)
      | ~ v1_relat_1(A_452)
      | r2_hidden('#skF_7'(A_453,B_454),B_454)
      | k1_relat_1(A_453) = B_454 ) ),
    inference(resolution,[status(thm)],[c_128,c_2])).

tff(c_7358,plain,(
    ! [A_455,B_456] :
      ( r2_hidden('#skF_5'(A_455,B_456),k10_relat_1(A_455,k2_relat_1(A_455)))
      | ~ v1_relat_1(A_455)
      | r2_hidden('#skF_7'(A_455,B_456),B_456)
      | k1_relat_1(A_455) = B_456 ) ),
    inference(resolution,[status(thm)],[c_30,c_7215])).

tff(c_151,plain,(
    ! [D_127,A_128,B_129] :
      ( r2_hidden(k4_tarski(D_127,'#skF_4'(A_128,B_129,k10_relat_1(A_128,B_129),D_127)),A_128)
      | ~ r2_hidden(D_127,k10_relat_1(A_128,B_129))
      | ~ v1_relat_1(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22,plain,(
    ! [C_58,A_43,D_61] :
      ( r2_hidden(C_58,k1_relat_1(A_43))
      | ~ r2_hidden(k4_tarski(C_58,D_61),A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_161,plain,(
    ! [D_127,A_128,B_129] :
      ( r2_hidden(D_127,k1_relat_1(A_128))
      | ~ r2_hidden(D_127,k10_relat_1(A_128,B_129))
      | ~ v1_relat_1(A_128) ) ),
    inference(resolution,[status(thm)],[c_151,c_22])).

tff(c_87236,plain,(
    ! [A_1729,A_1730,B_1731] :
      ( r2_hidden('#skF_7'(A_1729,k10_relat_1(A_1730,B_1731)),k1_relat_1(A_1730))
      | ~ v1_relat_1(A_1730)
      | r2_hidden('#skF_5'(A_1729,k10_relat_1(A_1730,B_1731)),k10_relat_1(A_1729,k2_relat_1(A_1729)))
      | ~ v1_relat_1(A_1729)
      | k1_relat_1(A_1729) = k10_relat_1(A_1730,B_1731) ) ),
    inference(resolution,[status(thm)],[c_7358,c_161])).

tff(c_28,plain,(
    ! [A_43,B_44] :
      ( ~ r2_hidden('#skF_5'(A_43,B_44),B_44)
      | r2_hidden('#skF_7'(A_43,B_44),B_44)
      | k1_relat_1(A_43) = B_44 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_163,plain,(
    ! [D_130,A_131,B_132] :
      ( r2_hidden(D_130,k1_relat_1(A_131))
      | ~ r2_hidden(D_130,k10_relat_1(A_131,B_132))
      | ~ v1_relat_1(A_131) ) ),
    inference(resolution,[status(thm)],[c_151,c_22])).

tff(c_220,plain,(
    ! [A_43,A_131,B_132] :
      ( r2_hidden('#skF_7'(A_43,k10_relat_1(A_131,B_132)),k1_relat_1(A_131))
      | ~ v1_relat_1(A_131)
      | ~ r2_hidden('#skF_5'(A_43,k10_relat_1(A_131,B_132)),k10_relat_1(A_131,B_132))
      | k1_relat_1(A_43) = k10_relat_1(A_131,B_132) ) ),
    inference(resolution,[status(thm)],[c_28,c_163])).

tff(c_87482,plain,(
    ! [A_1729] :
      ( r2_hidden('#skF_7'(A_1729,k10_relat_1(A_1729,k2_relat_1(A_1729))),k1_relat_1(A_1729))
      | ~ v1_relat_1(A_1729)
      | k10_relat_1(A_1729,k2_relat_1(A_1729)) = k1_relat_1(A_1729) ) ),
    inference(resolution,[status(thm)],[c_87236,c_220])).

tff(c_106,plain,(
    ! [A_112,B_113] :
      ( r2_hidden('#skF_5'(A_112,B_113),k1_relat_1(A_112))
      | r2_hidden('#skF_7'(A_112,B_113),B_113)
      | k1_relat_1(A_112) = B_113 ) ),
    inference(resolution,[status(thm)],[c_96,c_22])).

tff(c_7568,plain,(
    ! [A_461,A_462,B_463] :
      ( r2_hidden('#skF_7'(A_461,k10_relat_1(A_462,B_463)),k1_relat_1(A_462))
      | ~ v1_relat_1(A_462)
      | r2_hidden('#skF_5'(A_461,k10_relat_1(A_462,B_463)),k1_relat_1(A_461))
      | k1_relat_1(A_461) = k10_relat_1(A_462,B_463) ) ),
    inference(resolution,[status(thm)],[c_106,c_163])).

tff(c_20,plain,(
    ! [C_58,A_43] :
      ( r2_hidden(k4_tarski(C_58,'#skF_8'(A_43,k1_relat_1(A_43),C_58)),A_43)
      | ~ r2_hidden(C_58,k1_relat_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_305,plain,(
    ! [A_148,B_149,D_150] :
      ( r2_hidden(k4_tarski('#skF_5'(A_148,B_149),'#skF_6'(A_148,B_149)),A_148)
      | ~ r2_hidden(k4_tarski('#skF_7'(A_148,B_149),D_150),A_148)
      | k1_relat_1(A_148) = B_149 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_314,plain,(
    ! [A_151,B_152] :
      ( r2_hidden(k4_tarski('#skF_5'(A_151,B_152),'#skF_6'(A_151,B_152)),A_151)
      | k1_relat_1(A_151) = B_152
      | ~ r2_hidden('#skF_7'(A_151,B_152),k1_relat_1(A_151)) ) ),
    inference(resolution,[status(thm)],[c_20,c_305])).

tff(c_329,plain,(
    ! [A_151,B_152] :
      ( r2_hidden('#skF_5'(A_151,B_152),k1_relat_1(A_151))
      | k1_relat_1(A_151) = B_152
      | ~ r2_hidden('#skF_7'(A_151,B_152),k1_relat_1(A_151)) ) ),
    inference(resolution,[status(thm)],[c_314,c_22])).

tff(c_7600,plain,(
    ! [A_462,B_463] :
      ( ~ v1_relat_1(A_462)
      | r2_hidden('#skF_5'(A_462,k10_relat_1(A_462,B_463)),k1_relat_1(A_462))
      | k10_relat_1(A_462,B_463) = k1_relat_1(A_462) ) ),
    inference(resolution,[status(thm)],[c_7568,c_329])).

tff(c_60,plain,(
    ! [C_93,A_94] :
      ( r2_hidden(k4_tarski(C_93,'#skF_8'(A_94,k1_relat_1(A_94),C_93)),A_94)
      | ~ r2_hidden(C_93,k1_relat_1(A_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_68,plain,(
    ! [A_94,C_93] :
      ( r2_hidden('#skF_8'(A_94,k1_relat_1(A_94),C_93),k2_relat_1(A_94))
      | ~ r2_hidden(C_93,k1_relat_1(A_94)) ) ),
    inference(resolution,[status(thm)],[c_60,c_34])).

tff(c_71,plain,(
    ! [D_99,A_100,B_101,E_102] :
      ( r2_hidden(D_99,k10_relat_1(A_100,B_101))
      | ~ r2_hidden(E_102,B_101)
      | ~ r2_hidden(k4_tarski(D_99,E_102),A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_363,plain,(
    ! [D_160,A_161,A_162,C_163] :
      ( r2_hidden(D_160,k10_relat_1(A_161,k2_relat_1(A_162)))
      | ~ r2_hidden(k4_tarski(D_160,'#skF_8'(A_162,k1_relat_1(A_162),C_163)),A_161)
      | ~ v1_relat_1(A_161)
      | ~ r2_hidden(C_163,k1_relat_1(A_162)) ) ),
    inference(resolution,[status(thm)],[c_68,c_71])).

tff(c_374,plain,(
    ! [C_168,A_169] :
      ( r2_hidden(C_168,k10_relat_1(A_169,k2_relat_1(A_169)))
      | ~ v1_relat_1(A_169)
      | ~ r2_hidden(C_168,k1_relat_1(A_169)) ) ),
    inference(resolution,[status(thm)],[c_20,c_363])).

tff(c_24,plain,(
    ! [A_43,B_44,D_57] :
      ( ~ r2_hidden('#skF_5'(A_43,B_44),B_44)
      | ~ r2_hidden(k4_tarski('#skF_7'(A_43,B_44),D_57),A_43)
      | k1_relat_1(A_43) = B_44 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_90106,plain,(
    ! [A_1756,A_1757,D_1758] :
      ( ~ r2_hidden(k4_tarski('#skF_7'(A_1756,k10_relat_1(A_1757,k2_relat_1(A_1757))),D_1758),A_1756)
      | k1_relat_1(A_1756) = k10_relat_1(A_1757,k2_relat_1(A_1757))
      | ~ v1_relat_1(A_1757)
      | ~ r2_hidden('#skF_5'(A_1756,k10_relat_1(A_1757,k2_relat_1(A_1757))),k1_relat_1(A_1757)) ) ),
    inference(resolution,[status(thm)],[c_374,c_24])).

tff(c_90727,plain,(
    ! [A_1759,A_1760] :
      ( k1_relat_1(A_1759) = k10_relat_1(A_1760,k2_relat_1(A_1760))
      | ~ v1_relat_1(A_1760)
      | ~ r2_hidden('#skF_5'(A_1759,k10_relat_1(A_1760,k2_relat_1(A_1760))),k1_relat_1(A_1760))
      | ~ r2_hidden('#skF_7'(A_1759,k10_relat_1(A_1760,k2_relat_1(A_1760))),k1_relat_1(A_1759)) ) ),
    inference(resolution,[status(thm)],[c_20,c_90106])).

tff(c_91229,plain,(
    ! [A_1764] :
      ( ~ r2_hidden('#skF_7'(A_1764,k10_relat_1(A_1764,k2_relat_1(A_1764))),k1_relat_1(A_1764))
      | ~ v1_relat_1(A_1764)
      | k10_relat_1(A_1764,k2_relat_1(A_1764)) = k1_relat_1(A_1764) ) ),
    inference(resolution,[status(thm)],[c_7600,c_90727])).

tff(c_91598,plain,(
    ! [A_1765] :
      ( ~ v1_relat_1(A_1765)
      | k10_relat_1(A_1765,k2_relat_1(A_1765)) = k1_relat_1(A_1765) ) ),
    inference(resolution,[status(thm)],[c_87482,c_91229])).

tff(c_44,plain,(
    k10_relat_1('#skF_13',k2_relat_1('#skF_13')) != k1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_92953,plain,(
    ~ v1_relat_1('#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_91598,c_44])).

tff(c_92962,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_92953])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:35:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 42.16/28.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 42.16/28.59  
% 42.16/28.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 42.16/28.59  %$ r2_hidden > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_1 > #skF_12 > #skF_13 > #skF_10 > #skF_2 > #skF_4 > #skF_3 > #skF_8 > #skF_7 > #skF_9 > #skF_5
% 42.16/28.59  
% 42.16/28.59  %Foreground sorts:
% 42.16/28.59  
% 42.16/28.59  
% 42.16/28.59  %Background operators:
% 42.16/28.59  
% 42.16/28.59  
% 42.16/28.59  %Foreground operators:
% 42.16/28.59  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 42.16/28.59  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 42.16/28.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 42.16/28.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 42.16/28.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 42.16/28.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 42.16/28.59  tff('#skF_12', type, '#skF_12': ($i * $i * $i) > $i).
% 42.16/28.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 42.16/28.59  tff('#skF_13', type, '#skF_13': $i).
% 42.16/28.59  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 42.16/28.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 42.16/28.59  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 42.16/28.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 42.16/28.59  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 42.16/28.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 42.16/28.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 42.16/28.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 42.16/28.59  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 42.16/28.59  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 42.16/28.59  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 42.16/28.59  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 42.16/28.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 42.16/28.59  
% 42.25/28.60  tff(f_59, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 42.25/28.60  tff(f_46, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 42.25/28.60  tff(f_54, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 42.25/28.60  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 42.25/28.60  tff(c_46, plain, (v1_relat_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_59])).
% 42.25/28.60  tff(c_30, plain, (![A_43, B_44]: (r2_hidden(k4_tarski('#skF_5'(A_43, B_44), '#skF_6'(A_43, B_44)), A_43) | r2_hidden('#skF_7'(A_43, B_44), B_44) | k1_relat_1(A_43)=B_44)), inference(cnfTransformation, [status(thm)], [f_46])).
% 42.25/28.60  tff(c_96, plain, (![A_112, B_113]: (r2_hidden(k4_tarski('#skF_5'(A_112, B_113), '#skF_6'(A_112, B_113)), A_112) | r2_hidden('#skF_7'(A_112, B_113), B_113) | k1_relat_1(A_112)=B_113)), inference(cnfTransformation, [status(thm)], [f_46])).
% 42.25/28.60  tff(c_34, plain, (![C_77, A_62, D_80]: (r2_hidden(C_77, k2_relat_1(A_62)) | ~r2_hidden(k4_tarski(D_80, C_77), A_62))), inference(cnfTransformation, [status(thm)], [f_54])).
% 42.25/28.60  tff(c_128, plain, (![A_118, B_119]: (r2_hidden('#skF_6'(A_118, B_119), k2_relat_1(A_118)) | r2_hidden('#skF_7'(A_118, B_119), B_119) | k1_relat_1(A_118)=B_119)), inference(resolution, [status(thm)], [c_96, c_34])).
% 42.25/28.60  tff(c_2, plain, (![D_39, A_1, B_24, E_42]: (r2_hidden(D_39, k10_relat_1(A_1, B_24)) | ~r2_hidden(E_42, B_24) | ~r2_hidden(k4_tarski(D_39, E_42), A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 42.25/28.60  tff(c_7215, plain, (![D_451, A_452, A_453, B_454]: (r2_hidden(D_451, k10_relat_1(A_452, k2_relat_1(A_453))) | ~r2_hidden(k4_tarski(D_451, '#skF_6'(A_453, B_454)), A_452) | ~v1_relat_1(A_452) | r2_hidden('#skF_7'(A_453, B_454), B_454) | k1_relat_1(A_453)=B_454)), inference(resolution, [status(thm)], [c_128, c_2])).
% 42.25/28.60  tff(c_7358, plain, (![A_455, B_456]: (r2_hidden('#skF_5'(A_455, B_456), k10_relat_1(A_455, k2_relat_1(A_455))) | ~v1_relat_1(A_455) | r2_hidden('#skF_7'(A_455, B_456), B_456) | k1_relat_1(A_455)=B_456)), inference(resolution, [status(thm)], [c_30, c_7215])).
% 42.25/28.60  tff(c_151, plain, (![D_127, A_128, B_129]: (r2_hidden(k4_tarski(D_127, '#skF_4'(A_128, B_129, k10_relat_1(A_128, B_129), D_127)), A_128) | ~r2_hidden(D_127, k10_relat_1(A_128, B_129)) | ~v1_relat_1(A_128))), inference(cnfTransformation, [status(thm)], [f_38])).
% 42.25/28.60  tff(c_22, plain, (![C_58, A_43, D_61]: (r2_hidden(C_58, k1_relat_1(A_43)) | ~r2_hidden(k4_tarski(C_58, D_61), A_43))), inference(cnfTransformation, [status(thm)], [f_46])).
% 42.25/28.60  tff(c_161, plain, (![D_127, A_128, B_129]: (r2_hidden(D_127, k1_relat_1(A_128)) | ~r2_hidden(D_127, k10_relat_1(A_128, B_129)) | ~v1_relat_1(A_128))), inference(resolution, [status(thm)], [c_151, c_22])).
% 42.25/28.60  tff(c_87236, plain, (![A_1729, A_1730, B_1731]: (r2_hidden('#skF_7'(A_1729, k10_relat_1(A_1730, B_1731)), k1_relat_1(A_1730)) | ~v1_relat_1(A_1730) | r2_hidden('#skF_5'(A_1729, k10_relat_1(A_1730, B_1731)), k10_relat_1(A_1729, k2_relat_1(A_1729))) | ~v1_relat_1(A_1729) | k1_relat_1(A_1729)=k10_relat_1(A_1730, B_1731))), inference(resolution, [status(thm)], [c_7358, c_161])).
% 42.25/28.60  tff(c_28, plain, (![A_43, B_44]: (~r2_hidden('#skF_5'(A_43, B_44), B_44) | r2_hidden('#skF_7'(A_43, B_44), B_44) | k1_relat_1(A_43)=B_44)), inference(cnfTransformation, [status(thm)], [f_46])).
% 42.25/28.60  tff(c_163, plain, (![D_130, A_131, B_132]: (r2_hidden(D_130, k1_relat_1(A_131)) | ~r2_hidden(D_130, k10_relat_1(A_131, B_132)) | ~v1_relat_1(A_131))), inference(resolution, [status(thm)], [c_151, c_22])).
% 42.25/28.60  tff(c_220, plain, (![A_43, A_131, B_132]: (r2_hidden('#skF_7'(A_43, k10_relat_1(A_131, B_132)), k1_relat_1(A_131)) | ~v1_relat_1(A_131) | ~r2_hidden('#skF_5'(A_43, k10_relat_1(A_131, B_132)), k10_relat_1(A_131, B_132)) | k1_relat_1(A_43)=k10_relat_1(A_131, B_132))), inference(resolution, [status(thm)], [c_28, c_163])).
% 42.25/28.60  tff(c_87482, plain, (![A_1729]: (r2_hidden('#skF_7'(A_1729, k10_relat_1(A_1729, k2_relat_1(A_1729))), k1_relat_1(A_1729)) | ~v1_relat_1(A_1729) | k10_relat_1(A_1729, k2_relat_1(A_1729))=k1_relat_1(A_1729))), inference(resolution, [status(thm)], [c_87236, c_220])).
% 42.25/28.60  tff(c_106, plain, (![A_112, B_113]: (r2_hidden('#skF_5'(A_112, B_113), k1_relat_1(A_112)) | r2_hidden('#skF_7'(A_112, B_113), B_113) | k1_relat_1(A_112)=B_113)), inference(resolution, [status(thm)], [c_96, c_22])).
% 42.25/28.60  tff(c_7568, plain, (![A_461, A_462, B_463]: (r2_hidden('#skF_7'(A_461, k10_relat_1(A_462, B_463)), k1_relat_1(A_462)) | ~v1_relat_1(A_462) | r2_hidden('#skF_5'(A_461, k10_relat_1(A_462, B_463)), k1_relat_1(A_461)) | k1_relat_1(A_461)=k10_relat_1(A_462, B_463))), inference(resolution, [status(thm)], [c_106, c_163])).
% 42.25/28.60  tff(c_20, plain, (![C_58, A_43]: (r2_hidden(k4_tarski(C_58, '#skF_8'(A_43, k1_relat_1(A_43), C_58)), A_43) | ~r2_hidden(C_58, k1_relat_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 42.25/28.60  tff(c_305, plain, (![A_148, B_149, D_150]: (r2_hidden(k4_tarski('#skF_5'(A_148, B_149), '#skF_6'(A_148, B_149)), A_148) | ~r2_hidden(k4_tarski('#skF_7'(A_148, B_149), D_150), A_148) | k1_relat_1(A_148)=B_149)), inference(cnfTransformation, [status(thm)], [f_46])).
% 42.25/28.60  tff(c_314, plain, (![A_151, B_152]: (r2_hidden(k4_tarski('#skF_5'(A_151, B_152), '#skF_6'(A_151, B_152)), A_151) | k1_relat_1(A_151)=B_152 | ~r2_hidden('#skF_7'(A_151, B_152), k1_relat_1(A_151)))), inference(resolution, [status(thm)], [c_20, c_305])).
% 42.25/28.60  tff(c_329, plain, (![A_151, B_152]: (r2_hidden('#skF_5'(A_151, B_152), k1_relat_1(A_151)) | k1_relat_1(A_151)=B_152 | ~r2_hidden('#skF_7'(A_151, B_152), k1_relat_1(A_151)))), inference(resolution, [status(thm)], [c_314, c_22])).
% 42.25/28.60  tff(c_7600, plain, (![A_462, B_463]: (~v1_relat_1(A_462) | r2_hidden('#skF_5'(A_462, k10_relat_1(A_462, B_463)), k1_relat_1(A_462)) | k10_relat_1(A_462, B_463)=k1_relat_1(A_462))), inference(resolution, [status(thm)], [c_7568, c_329])).
% 42.25/28.60  tff(c_60, plain, (![C_93, A_94]: (r2_hidden(k4_tarski(C_93, '#skF_8'(A_94, k1_relat_1(A_94), C_93)), A_94) | ~r2_hidden(C_93, k1_relat_1(A_94)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 42.25/28.60  tff(c_68, plain, (![A_94, C_93]: (r2_hidden('#skF_8'(A_94, k1_relat_1(A_94), C_93), k2_relat_1(A_94)) | ~r2_hidden(C_93, k1_relat_1(A_94)))), inference(resolution, [status(thm)], [c_60, c_34])).
% 42.25/28.60  tff(c_71, plain, (![D_99, A_100, B_101, E_102]: (r2_hidden(D_99, k10_relat_1(A_100, B_101)) | ~r2_hidden(E_102, B_101) | ~r2_hidden(k4_tarski(D_99, E_102), A_100) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_38])).
% 42.25/28.60  tff(c_363, plain, (![D_160, A_161, A_162, C_163]: (r2_hidden(D_160, k10_relat_1(A_161, k2_relat_1(A_162))) | ~r2_hidden(k4_tarski(D_160, '#skF_8'(A_162, k1_relat_1(A_162), C_163)), A_161) | ~v1_relat_1(A_161) | ~r2_hidden(C_163, k1_relat_1(A_162)))), inference(resolution, [status(thm)], [c_68, c_71])).
% 42.25/28.60  tff(c_374, plain, (![C_168, A_169]: (r2_hidden(C_168, k10_relat_1(A_169, k2_relat_1(A_169))) | ~v1_relat_1(A_169) | ~r2_hidden(C_168, k1_relat_1(A_169)))), inference(resolution, [status(thm)], [c_20, c_363])).
% 42.25/28.60  tff(c_24, plain, (![A_43, B_44, D_57]: (~r2_hidden('#skF_5'(A_43, B_44), B_44) | ~r2_hidden(k4_tarski('#skF_7'(A_43, B_44), D_57), A_43) | k1_relat_1(A_43)=B_44)), inference(cnfTransformation, [status(thm)], [f_46])).
% 42.25/28.60  tff(c_90106, plain, (![A_1756, A_1757, D_1758]: (~r2_hidden(k4_tarski('#skF_7'(A_1756, k10_relat_1(A_1757, k2_relat_1(A_1757))), D_1758), A_1756) | k1_relat_1(A_1756)=k10_relat_1(A_1757, k2_relat_1(A_1757)) | ~v1_relat_1(A_1757) | ~r2_hidden('#skF_5'(A_1756, k10_relat_1(A_1757, k2_relat_1(A_1757))), k1_relat_1(A_1757)))), inference(resolution, [status(thm)], [c_374, c_24])).
% 42.25/28.60  tff(c_90727, plain, (![A_1759, A_1760]: (k1_relat_1(A_1759)=k10_relat_1(A_1760, k2_relat_1(A_1760)) | ~v1_relat_1(A_1760) | ~r2_hidden('#skF_5'(A_1759, k10_relat_1(A_1760, k2_relat_1(A_1760))), k1_relat_1(A_1760)) | ~r2_hidden('#skF_7'(A_1759, k10_relat_1(A_1760, k2_relat_1(A_1760))), k1_relat_1(A_1759)))), inference(resolution, [status(thm)], [c_20, c_90106])).
% 42.25/28.60  tff(c_91229, plain, (![A_1764]: (~r2_hidden('#skF_7'(A_1764, k10_relat_1(A_1764, k2_relat_1(A_1764))), k1_relat_1(A_1764)) | ~v1_relat_1(A_1764) | k10_relat_1(A_1764, k2_relat_1(A_1764))=k1_relat_1(A_1764))), inference(resolution, [status(thm)], [c_7600, c_90727])).
% 42.25/28.60  tff(c_91598, plain, (![A_1765]: (~v1_relat_1(A_1765) | k10_relat_1(A_1765, k2_relat_1(A_1765))=k1_relat_1(A_1765))), inference(resolution, [status(thm)], [c_87482, c_91229])).
% 42.25/28.60  tff(c_44, plain, (k10_relat_1('#skF_13', k2_relat_1('#skF_13'))!=k1_relat_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_59])).
% 42.25/28.60  tff(c_92953, plain, (~v1_relat_1('#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_91598, c_44])).
% 42.25/28.60  tff(c_92962, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_92953])).
% 42.25/28.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 42.25/28.60  
% 42.25/28.60  Inference rules
% 42.25/28.60  ----------------------
% 42.25/28.60  #Ref     : 0
% 42.25/28.60  #Sup     : 22205
% 42.25/28.60  #Fact    : 0
% 42.25/28.60  #Define  : 0
% 42.25/28.60  #Split   : 0
% 42.25/28.60  #Chain   : 0
% 42.25/28.60  #Close   : 0
% 42.25/28.60  
% 42.25/28.60  Ordering : KBO
% 42.25/28.60  
% 42.25/28.60  Simplification rules
% 42.25/28.60  ----------------------
% 42.25/28.60  #Subsume      : 659
% 42.25/28.60  #Demod        : 1
% 42.25/28.60  #Tautology    : 240
% 42.25/28.60  #SimpNegUnit  : 0
% 42.25/28.60  #BackRed      : 0
% 42.25/28.60  
% 42.25/28.60  #Partial instantiations: 0
% 42.25/28.60  #Strategies tried      : 1
% 42.25/28.60  
% 42.25/28.60  Timing (in seconds)
% 42.25/28.60  ----------------------
% 42.25/28.61  Preprocessing        : 0.32
% 42.25/28.61  Parsing              : 0.16
% 42.25/28.61  CNF conversion       : 0.03
% 42.25/28.61  Main loop            : 27.47
% 42.25/28.61  Inferencing          : 3.66
% 42.25/28.61  Reduction            : 2.69
% 42.25/28.61  Demodulation         : 1.68
% 42.25/28.61  BG Simplification    : 0.60
% 42.25/28.61  Subsumption          : 18.91
% 42.25/28.61  Abstraction          : 1.08
% 42.25/28.61  MUC search           : 0.00
% 42.25/28.61  Cooper               : 0.00
% 42.25/28.61  Total                : 27.82
% 42.25/28.61  Index Insertion      : 0.00
% 42.25/28.61  Index Deletion       : 0.00
% 42.25/28.61  Index Matching       : 0.00
% 42.25/28.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
