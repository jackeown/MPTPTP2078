%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:33 EST 2020

% Result     : Theorem 7.59s
% Output     : CNFRefutation 7.59s
% Verified   : 
% Statistics : Number of formulae       :   58 (  89 expanded)
%              Number of leaves         :   22 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  125 ( 220 expanded)
%              Number of equality atoms :   24 (  44 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_1 > #skF_2 > #skF_9 > #skF_4 > #skF_3 > #skF_8 > #skF_7 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_38,axiom,(
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

tff(c_38,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30,plain,(
    ! [A_43,B_44] :
      ( r2_hidden(k4_tarski('#skF_6'(A_43,B_44),'#skF_5'(A_43,B_44)),A_43)
      | r2_hidden('#skF_7'(A_43,B_44),B_44)
      | k2_relat_1(A_43) = B_44 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_67,plain,(
    ! [A_87,B_88] :
      ( r2_hidden(k4_tarski('#skF_6'(A_87,B_88),'#skF_5'(A_87,B_88)),A_87)
      | r2_hidden('#skF_7'(A_87,B_88),B_88)
      | k2_relat_1(A_87) = B_88 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    ! [A_62,C_64,B_63] :
      ( r2_hidden(A_62,k1_relat_1(C_64))
      | ~ r2_hidden(k4_tarski(A_62,B_63),C_64)
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_87,plain,(
    ! [A_91,B_92] :
      ( r2_hidden('#skF_6'(A_91,B_92),k1_relat_1(A_91))
      | ~ v1_relat_1(A_91)
      | r2_hidden('#skF_7'(A_91,B_92),B_92)
      | k2_relat_1(A_91) = B_92 ) ),
    inference(resolution,[status(thm)],[c_67,c_34])).

tff(c_2,plain,(
    ! [D_39,A_1,B_24,E_42] :
      ( r2_hidden(D_39,k9_relat_1(A_1,B_24))
      | ~ r2_hidden(E_42,B_24)
      | ~ r2_hidden(k4_tarski(E_42,D_39),A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2139,plain,(
    ! [D_277,A_278,A_279,B_280] :
      ( r2_hidden(D_277,k9_relat_1(A_278,k1_relat_1(A_279)))
      | ~ r2_hidden(k4_tarski('#skF_6'(A_279,B_280),D_277),A_278)
      | ~ v1_relat_1(A_278)
      | ~ v1_relat_1(A_279)
      | r2_hidden('#skF_7'(A_279,B_280),B_280)
      | k2_relat_1(A_279) = B_280 ) ),
    inference(resolution,[status(thm)],[c_87,c_2])).

tff(c_2174,plain,(
    ! [A_281,B_282] :
      ( r2_hidden('#skF_5'(A_281,B_282),k9_relat_1(A_281,k1_relat_1(A_281)))
      | ~ v1_relat_1(A_281)
      | r2_hidden('#skF_7'(A_281,B_282),B_282)
      | k2_relat_1(A_281) = B_282 ) ),
    inference(resolution,[status(thm)],[c_30,c_2139])).

tff(c_102,plain,(
    ! [A_99,B_100,D_101] :
      ( r2_hidden(k4_tarski('#skF_4'(A_99,B_100,k9_relat_1(A_99,B_100),D_101),D_101),A_99)
      | ~ r2_hidden(D_101,k9_relat_1(A_99,B_100))
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22,plain,(
    ! [C_58,A_43,D_61] :
      ( r2_hidden(C_58,k2_relat_1(A_43))
      | ~ r2_hidden(k4_tarski(D_61,C_58),A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_113,plain,(
    ! [D_101,A_99,B_100] :
      ( r2_hidden(D_101,k2_relat_1(A_99))
      | ~ r2_hidden(D_101,k9_relat_1(A_99,B_100))
      | ~ v1_relat_1(A_99) ) ),
    inference(resolution,[status(thm)],[c_102,c_22])).

tff(c_5211,plain,(
    ! [A_434,A_435,B_436] :
      ( r2_hidden('#skF_7'(A_434,k9_relat_1(A_435,B_436)),k2_relat_1(A_435))
      | ~ v1_relat_1(A_435)
      | r2_hidden('#skF_5'(A_434,k9_relat_1(A_435,B_436)),k9_relat_1(A_434,k1_relat_1(A_434)))
      | ~ v1_relat_1(A_434)
      | k9_relat_1(A_435,B_436) = k2_relat_1(A_434) ) ),
    inference(resolution,[status(thm)],[c_2174,c_113])).

tff(c_28,plain,(
    ! [A_43,B_44] :
      ( ~ r2_hidden('#skF_5'(A_43,B_44),B_44)
      | r2_hidden('#skF_7'(A_43,B_44),B_44)
      | k2_relat_1(A_43) = B_44 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_114,plain,(
    ! [D_102,A_103,B_104] :
      ( r2_hidden(D_102,k2_relat_1(A_103))
      | ~ r2_hidden(D_102,k9_relat_1(A_103,B_104))
      | ~ v1_relat_1(A_103) ) ),
    inference(resolution,[status(thm)],[c_102,c_22])).

tff(c_158,plain,(
    ! [A_43,A_103,B_104] :
      ( r2_hidden('#skF_7'(A_43,k9_relat_1(A_103,B_104)),k2_relat_1(A_103))
      | ~ v1_relat_1(A_103)
      | ~ r2_hidden('#skF_5'(A_43,k9_relat_1(A_103,B_104)),k9_relat_1(A_103,B_104))
      | k9_relat_1(A_103,B_104) = k2_relat_1(A_43) ) ),
    inference(resolution,[status(thm)],[c_28,c_114])).

tff(c_5295,plain,(
    ! [A_434] :
      ( r2_hidden('#skF_7'(A_434,k9_relat_1(A_434,k1_relat_1(A_434))),k2_relat_1(A_434))
      | ~ v1_relat_1(A_434)
      | k9_relat_1(A_434,k1_relat_1(A_434)) = k2_relat_1(A_434) ) ),
    inference(resolution,[status(thm)],[c_5211,c_158])).

tff(c_78,plain,(
    ! [A_87,B_88] :
      ( r2_hidden('#skF_5'(A_87,B_88),k2_relat_1(A_87))
      | r2_hidden('#skF_7'(A_87,B_88),B_88)
      | k2_relat_1(A_87) = B_88 ) ),
    inference(resolution,[status(thm)],[c_67,c_22])).

tff(c_394,plain,(
    ! [A_153,A_154,B_155] :
      ( r2_hidden('#skF_7'(A_153,k9_relat_1(A_154,B_155)),k2_relat_1(A_154))
      | ~ v1_relat_1(A_154)
      | r2_hidden('#skF_5'(A_153,k9_relat_1(A_154,B_155)),k2_relat_1(A_153))
      | k9_relat_1(A_154,B_155) = k2_relat_1(A_153) ) ),
    inference(resolution,[status(thm)],[c_78,c_114])).

tff(c_20,plain,(
    ! [A_43,C_58] :
      ( r2_hidden(k4_tarski('#skF_8'(A_43,k2_relat_1(A_43),C_58),C_58),A_43)
      | ~ r2_hidden(C_58,k2_relat_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_164,plain,(
    ! [A_108,B_109,D_110] :
      ( r2_hidden(k4_tarski('#skF_6'(A_108,B_109),'#skF_5'(A_108,B_109)),A_108)
      | ~ r2_hidden(k4_tarski(D_110,'#skF_7'(A_108,B_109)),A_108)
      | k2_relat_1(A_108) = B_109 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_182,plain,(
    ! [A_115,B_116] :
      ( r2_hidden(k4_tarski('#skF_6'(A_115,B_116),'#skF_5'(A_115,B_116)),A_115)
      | k2_relat_1(A_115) = B_116
      | ~ r2_hidden('#skF_7'(A_115,B_116),k2_relat_1(A_115)) ) ),
    inference(resolution,[status(thm)],[c_20,c_164])).

tff(c_198,plain,(
    ! [A_115,B_116] :
      ( r2_hidden('#skF_5'(A_115,B_116),k2_relat_1(A_115))
      | k2_relat_1(A_115) = B_116
      | ~ r2_hidden('#skF_7'(A_115,B_116),k2_relat_1(A_115)) ) ),
    inference(resolution,[status(thm)],[c_182,c_22])).

tff(c_412,plain,(
    ! [A_154,B_155] :
      ( ~ v1_relat_1(A_154)
      | r2_hidden('#skF_5'(A_154,k9_relat_1(A_154,B_155)),k2_relat_1(A_154))
      | k9_relat_1(A_154,B_155) = k2_relat_1(A_154) ) ),
    inference(resolution,[status(thm)],[c_394,c_198])).

tff(c_41,plain,(
    ! [A_71,C_72] :
      ( r2_hidden(k4_tarski('#skF_8'(A_71,k2_relat_1(A_71),C_72),C_72),A_71)
      | ~ r2_hidden(C_72,k2_relat_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_48,plain,(
    ! [A_71,C_72] :
      ( r2_hidden('#skF_8'(A_71,k2_relat_1(A_71),C_72),k1_relat_1(A_71))
      | ~ v1_relat_1(A_71)
      | ~ r2_hidden(C_72,k2_relat_1(A_71)) ) ),
    inference(resolution,[status(thm)],[c_41,c_34])).

tff(c_53,plain,(
    ! [D_80,A_81,B_82,E_83] :
      ( r2_hidden(D_80,k9_relat_1(A_81,B_82))
      | ~ r2_hidden(E_83,B_82)
      | ~ r2_hidden(k4_tarski(E_83,D_80),A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_439,plain,(
    ! [D_166,A_167,A_168,C_169] :
      ( r2_hidden(D_166,k9_relat_1(A_167,k1_relat_1(A_168)))
      | ~ r2_hidden(k4_tarski('#skF_8'(A_168,k2_relat_1(A_168),C_169),D_166),A_167)
      | ~ v1_relat_1(A_167)
      | ~ v1_relat_1(A_168)
      | ~ r2_hidden(C_169,k2_relat_1(A_168)) ) ),
    inference(resolution,[status(thm)],[c_48,c_53])).

tff(c_448,plain,(
    ! [C_170,A_171] :
      ( r2_hidden(C_170,k9_relat_1(A_171,k1_relat_1(A_171)))
      | ~ v1_relat_1(A_171)
      | ~ r2_hidden(C_170,k2_relat_1(A_171)) ) ),
    inference(resolution,[status(thm)],[c_20,c_439])).

tff(c_24,plain,(
    ! [A_43,B_44,D_57] :
      ( ~ r2_hidden('#skF_5'(A_43,B_44),B_44)
      | ~ r2_hidden(k4_tarski(D_57,'#skF_7'(A_43,B_44)),A_43)
      | k2_relat_1(A_43) = B_44 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_5517,plain,(
    ! [D_451,A_452,A_453] :
      ( ~ r2_hidden(k4_tarski(D_451,'#skF_7'(A_452,k9_relat_1(A_453,k1_relat_1(A_453)))),A_452)
      | k9_relat_1(A_453,k1_relat_1(A_453)) = k2_relat_1(A_452)
      | ~ v1_relat_1(A_453)
      | ~ r2_hidden('#skF_5'(A_452,k9_relat_1(A_453,k1_relat_1(A_453))),k2_relat_1(A_453)) ) ),
    inference(resolution,[status(thm)],[c_448,c_24])).

tff(c_5574,plain,(
    ! [A_454,A_455] :
      ( k9_relat_1(A_454,k1_relat_1(A_454)) = k2_relat_1(A_455)
      | ~ v1_relat_1(A_454)
      | ~ r2_hidden('#skF_5'(A_455,k9_relat_1(A_454,k1_relat_1(A_454))),k2_relat_1(A_454))
      | ~ r2_hidden('#skF_7'(A_455,k9_relat_1(A_454,k1_relat_1(A_454))),k2_relat_1(A_455)) ) ),
    inference(resolution,[status(thm)],[c_20,c_5517])).

tff(c_5618,plain,(
    ! [A_456] :
      ( ~ r2_hidden('#skF_7'(A_456,k9_relat_1(A_456,k1_relat_1(A_456))),k2_relat_1(A_456))
      | ~ v1_relat_1(A_456)
      | k9_relat_1(A_456,k1_relat_1(A_456)) = k2_relat_1(A_456) ) ),
    inference(resolution,[status(thm)],[c_412,c_5574])).

tff(c_5672,plain,(
    ! [A_457] :
      ( ~ v1_relat_1(A_457)
      | k9_relat_1(A_457,k1_relat_1(A_457)) = k2_relat_1(A_457) ) ),
    inference(resolution,[status(thm)],[c_5295,c_5618])).

tff(c_36,plain,(
    k9_relat_1('#skF_9',k1_relat_1('#skF_9')) != k2_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5945,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_5672,c_36])).

tff(c_5954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_5945])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:00:02 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.59/2.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.59/2.58  
% 7.59/2.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.59/2.58  %$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_1 > #skF_2 > #skF_9 > #skF_4 > #skF_3 > #skF_8 > #skF_7 > #skF_5
% 7.59/2.58  
% 7.59/2.58  %Foreground sorts:
% 7.59/2.58  
% 7.59/2.58  
% 7.59/2.58  %Background operators:
% 7.59/2.58  
% 7.59/2.58  
% 7.59/2.58  %Foreground operators:
% 7.59/2.58  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 7.59/2.58  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.59/2.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.59/2.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.59/2.58  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.59/2.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.59/2.58  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.59/2.58  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.59/2.58  tff('#skF_9', type, '#skF_9': $i).
% 7.59/2.58  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 7.59/2.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.59/2.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.59/2.58  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.59/2.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.59/2.58  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 7.59/2.58  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 7.59/2.58  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.59/2.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.59/2.58  
% 7.59/2.60  tff(f_59, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 7.59/2.60  tff(f_46, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 7.59/2.60  tff(f_54, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 7.59/2.60  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 7.59/2.60  tff(c_38, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.59/2.60  tff(c_30, plain, (![A_43, B_44]: (r2_hidden(k4_tarski('#skF_6'(A_43, B_44), '#skF_5'(A_43, B_44)), A_43) | r2_hidden('#skF_7'(A_43, B_44), B_44) | k2_relat_1(A_43)=B_44)), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.59/2.60  tff(c_67, plain, (![A_87, B_88]: (r2_hidden(k4_tarski('#skF_6'(A_87, B_88), '#skF_5'(A_87, B_88)), A_87) | r2_hidden('#skF_7'(A_87, B_88), B_88) | k2_relat_1(A_87)=B_88)), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.59/2.60  tff(c_34, plain, (![A_62, C_64, B_63]: (r2_hidden(A_62, k1_relat_1(C_64)) | ~r2_hidden(k4_tarski(A_62, B_63), C_64) | ~v1_relat_1(C_64))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.59/2.60  tff(c_87, plain, (![A_91, B_92]: (r2_hidden('#skF_6'(A_91, B_92), k1_relat_1(A_91)) | ~v1_relat_1(A_91) | r2_hidden('#skF_7'(A_91, B_92), B_92) | k2_relat_1(A_91)=B_92)), inference(resolution, [status(thm)], [c_67, c_34])).
% 7.59/2.60  tff(c_2, plain, (![D_39, A_1, B_24, E_42]: (r2_hidden(D_39, k9_relat_1(A_1, B_24)) | ~r2_hidden(E_42, B_24) | ~r2_hidden(k4_tarski(E_42, D_39), A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.59/2.60  tff(c_2139, plain, (![D_277, A_278, A_279, B_280]: (r2_hidden(D_277, k9_relat_1(A_278, k1_relat_1(A_279))) | ~r2_hidden(k4_tarski('#skF_6'(A_279, B_280), D_277), A_278) | ~v1_relat_1(A_278) | ~v1_relat_1(A_279) | r2_hidden('#skF_7'(A_279, B_280), B_280) | k2_relat_1(A_279)=B_280)), inference(resolution, [status(thm)], [c_87, c_2])).
% 7.59/2.60  tff(c_2174, plain, (![A_281, B_282]: (r2_hidden('#skF_5'(A_281, B_282), k9_relat_1(A_281, k1_relat_1(A_281))) | ~v1_relat_1(A_281) | r2_hidden('#skF_7'(A_281, B_282), B_282) | k2_relat_1(A_281)=B_282)), inference(resolution, [status(thm)], [c_30, c_2139])).
% 7.59/2.60  tff(c_102, plain, (![A_99, B_100, D_101]: (r2_hidden(k4_tarski('#skF_4'(A_99, B_100, k9_relat_1(A_99, B_100), D_101), D_101), A_99) | ~r2_hidden(D_101, k9_relat_1(A_99, B_100)) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.59/2.60  tff(c_22, plain, (![C_58, A_43, D_61]: (r2_hidden(C_58, k2_relat_1(A_43)) | ~r2_hidden(k4_tarski(D_61, C_58), A_43))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.59/2.60  tff(c_113, plain, (![D_101, A_99, B_100]: (r2_hidden(D_101, k2_relat_1(A_99)) | ~r2_hidden(D_101, k9_relat_1(A_99, B_100)) | ~v1_relat_1(A_99))), inference(resolution, [status(thm)], [c_102, c_22])).
% 7.59/2.60  tff(c_5211, plain, (![A_434, A_435, B_436]: (r2_hidden('#skF_7'(A_434, k9_relat_1(A_435, B_436)), k2_relat_1(A_435)) | ~v1_relat_1(A_435) | r2_hidden('#skF_5'(A_434, k9_relat_1(A_435, B_436)), k9_relat_1(A_434, k1_relat_1(A_434))) | ~v1_relat_1(A_434) | k9_relat_1(A_435, B_436)=k2_relat_1(A_434))), inference(resolution, [status(thm)], [c_2174, c_113])).
% 7.59/2.60  tff(c_28, plain, (![A_43, B_44]: (~r2_hidden('#skF_5'(A_43, B_44), B_44) | r2_hidden('#skF_7'(A_43, B_44), B_44) | k2_relat_1(A_43)=B_44)), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.59/2.60  tff(c_114, plain, (![D_102, A_103, B_104]: (r2_hidden(D_102, k2_relat_1(A_103)) | ~r2_hidden(D_102, k9_relat_1(A_103, B_104)) | ~v1_relat_1(A_103))), inference(resolution, [status(thm)], [c_102, c_22])).
% 7.59/2.60  tff(c_158, plain, (![A_43, A_103, B_104]: (r2_hidden('#skF_7'(A_43, k9_relat_1(A_103, B_104)), k2_relat_1(A_103)) | ~v1_relat_1(A_103) | ~r2_hidden('#skF_5'(A_43, k9_relat_1(A_103, B_104)), k9_relat_1(A_103, B_104)) | k9_relat_1(A_103, B_104)=k2_relat_1(A_43))), inference(resolution, [status(thm)], [c_28, c_114])).
% 7.59/2.60  tff(c_5295, plain, (![A_434]: (r2_hidden('#skF_7'(A_434, k9_relat_1(A_434, k1_relat_1(A_434))), k2_relat_1(A_434)) | ~v1_relat_1(A_434) | k9_relat_1(A_434, k1_relat_1(A_434))=k2_relat_1(A_434))), inference(resolution, [status(thm)], [c_5211, c_158])).
% 7.59/2.60  tff(c_78, plain, (![A_87, B_88]: (r2_hidden('#skF_5'(A_87, B_88), k2_relat_1(A_87)) | r2_hidden('#skF_7'(A_87, B_88), B_88) | k2_relat_1(A_87)=B_88)), inference(resolution, [status(thm)], [c_67, c_22])).
% 7.59/2.60  tff(c_394, plain, (![A_153, A_154, B_155]: (r2_hidden('#skF_7'(A_153, k9_relat_1(A_154, B_155)), k2_relat_1(A_154)) | ~v1_relat_1(A_154) | r2_hidden('#skF_5'(A_153, k9_relat_1(A_154, B_155)), k2_relat_1(A_153)) | k9_relat_1(A_154, B_155)=k2_relat_1(A_153))), inference(resolution, [status(thm)], [c_78, c_114])).
% 7.59/2.60  tff(c_20, plain, (![A_43, C_58]: (r2_hidden(k4_tarski('#skF_8'(A_43, k2_relat_1(A_43), C_58), C_58), A_43) | ~r2_hidden(C_58, k2_relat_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.59/2.60  tff(c_164, plain, (![A_108, B_109, D_110]: (r2_hidden(k4_tarski('#skF_6'(A_108, B_109), '#skF_5'(A_108, B_109)), A_108) | ~r2_hidden(k4_tarski(D_110, '#skF_7'(A_108, B_109)), A_108) | k2_relat_1(A_108)=B_109)), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.59/2.60  tff(c_182, plain, (![A_115, B_116]: (r2_hidden(k4_tarski('#skF_6'(A_115, B_116), '#skF_5'(A_115, B_116)), A_115) | k2_relat_1(A_115)=B_116 | ~r2_hidden('#skF_7'(A_115, B_116), k2_relat_1(A_115)))), inference(resolution, [status(thm)], [c_20, c_164])).
% 7.59/2.60  tff(c_198, plain, (![A_115, B_116]: (r2_hidden('#skF_5'(A_115, B_116), k2_relat_1(A_115)) | k2_relat_1(A_115)=B_116 | ~r2_hidden('#skF_7'(A_115, B_116), k2_relat_1(A_115)))), inference(resolution, [status(thm)], [c_182, c_22])).
% 7.59/2.60  tff(c_412, plain, (![A_154, B_155]: (~v1_relat_1(A_154) | r2_hidden('#skF_5'(A_154, k9_relat_1(A_154, B_155)), k2_relat_1(A_154)) | k9_relat_1(A_154, B_155)=k2_relat_1(A_154))), inference(resolution, [status(thm)], [c_394, c_198])).
% 7.59/2.60  tff(c_41, plain, (![A_71, C_72]: (r2_hidden(k4_tarski('#skF_8'(A_71, k2_relat_1(A_71), C_72), C_72), A_71) | ~r2_hidden(C_72, k2_relat_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.59/2.60  tff(c_48, plain, (![A_71, C_72]: (r2_hidden('#skF_8'(A_71, k2_relat_1(A_71), C_72), k1_relat_1(A_71)) | ~v1_relat_1(A_71) | ~r2_hidden(C_72, k2_relat_1(A_71)))), inference(resolution, [status(thm)], [c_41, c_34])).
% 7.59/2.60  tff(c_53, plain, (![D_80, A_81, B_82, E_83]: (r2_hidden(D_80, k9_relat_1(A_81, B_82)) | ~r2_hidden(E_83, B_82) | ~r2_hidden(k4_tarski(E_83, D_80), A_81) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.59/2.60  tff(c_439, plain, (![D_166, A_167, A_168, C_169]: (r2_hidden(D_166, k9_relat_1(A_167, k1_relat_1(A_168))) | ~r2_hidden(k4_tarski('#skF_8'(A_168, k2_relat_1(A_168), C_169), D_166), A_167) | ~v1_relat_1(A_167) | ~v1_relat_1(A_168) | ~r2_hidden(C_169, k2_relat_1(A_168)))), inference(resolution, [status(thm)], [c_48, c_53])).
% 7.59/2.60  tff(c_448, plain, (![C_170, A_171]: (r2_hidden(C_170, k9_relat_1(A_171, k1_relat_1(A_171))) | ~v1_relat_1(A_171) | ~r2_hidden(C_170, k2_relat_1(A_171)))), inference(resolution, [status(thm)], [c_20, c_439])).
% 7.59/2.60  tff(c_24, plain, (![A_43, B_44, D_57]: (~r2_hidden('#skF_5'(A_43, B_44), B_44) | ~r2_hidden(k4_tarski(D_57, '#skF_7'(A_43, B_44)), A_43) | k2_relat_1(A_43)=B_44)), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.59/2.60  tff(c_5517, plain, (![D_451, A_452, A_453]: (~r2_hidden(k4_tarski(D_451, '#skF_7'(A_452, k9_relat_1(A_453, k1_relat_1(A_453)))), A_452) | k9_relat_1(A_453, k1_relat_1(A_453))=k2_relat_1(A_452) | ~v1_relat_1(A_453) | ~r2_hidden('#skF_5'(A_452, k9_relat_1(A_453, k1_relat_1(A_453))), k2_relat_1(A_453)))), inference(resolution, [status(thm)], [c_448, c_24])).
% 7.59/2.60  tff(c_5574, plain, (![A_454, A_455]: (k9_relat_1(A_454, k1_relat_1(A_454))=k2_relat_1(A_455) | ~v1_relat_1(A_454) | ~r2_hidden('#skF_5'(A_455, k9_relat_1(A_454, k1_relat_1(A_454))), k2_relat_1(A_454)) | ~r2_hidden('#skF_7'(A_455, k9_relat_1(A_454, k1_relat_1(A_454))), k2_relat_1(A_455)))), inference(resolution, [status(thm)], [c_20, c_5517])).
% 7.59/2.60  tff(c_5618, plain, (![A_456]: (~r2_hidden('#skF_7'(A_456, k9_relat_1(A_456, k1_relat_1(A_456))), k2_relat_1(A_456)) | ~v1_relat_1(A_456) | k9_relat_1(A_456, k1_relat_1(A_456))=k2_relat_1(A_456))), inference(resolution, [status(thm)], [c_412, c_5574])).
% 7.59/2.60  tff(c_5672, plain, (![A_457]: (~v1_relat_1(A_457) | k9_relat_1(A_457, k1_relat_1(A_457))=k2_relat_1(A_457))), inference(resolution, [status(thm)], [c_5295, c_5618])).
% 7.59/2.60  tff(c_36, plain, (k9_relat_1('#skF_9', k1_relat_1('#skF_9'))!=k2_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.59/2.60  tff(c_5945, plain, (~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_5672, c_36])).
% 7.59/2.60  tff(c_5954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_5945])).
% 7.59/2.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.59/2.60  
% 7.59/2.60  Inference rules
% 7.59/2.60  ----------------------
% 7.59/2.60  #Ref     : 0
% 7.59/2.60  #Sup     : 1425
% 7.59/2.60  #Fact    : 0
% 7.59/2.60  #Define  : 0
% 7.59/2.60  #Split   : 0
% 7.59/2.60  #Chain   : 0
% 7.59/2.60  #Close   : 0
% 7.59/2.60  
% 7.59/2.60  Ordering : KBO
% 7.59/2.60  
% 7.59/2.60  Simplification rules
% 7.59/2.60  ----------------------
% 7.59/2.60  #Subsume      : 108
% 7.59/2.60  #Demod        : 1
% 7.59/2.60  #Tautology    : 30
% 7.59/2.60  #SimpNegUnit  : 0
% 7.59/2.60  #BackRed      : 0
% 7.59/2.60  
% 7.59/2.60  #Partial instantiations: 0
% 7.59/2.60  #Strategies tried      : 1
% 7.59/2.60  
% 7.59/2.60  Timing (in seconds)
% 7.59/2.60  ----------------------
% 7.59/2.60  Preprocessing        : 0.29
% 7.59/2.60  Parsing              : 0.16
% 7.59/2.60  CNF conversion       : 0.03
% 7.59/2.60  Main loop            : 1.54
% 7.59/2.60  Inferencing          : 0.51
% 7.59/2.60  Reduction            : 0.31
% 7.59/2.60  Demodulation         : 0.19
% 7.59/2.60  BG Simplification    : 0.07
% 7.59/2.60  Subsumption          : 0.51
% 7.59/2.60  Abstraction          : 0.10
% 7.59/2.60  MUC search           : 0.00
% 7.94/2.60  Cooper               : 0.00
% 7.94/2.60  Total                : 1.87
% 7.94/2.60  Index Insertion      : 0.00
% 7.94/2.60  Index Deletion       : 0.00
% 7.94/2.60  Index Matching       : 0.00
% 7.94/2.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
