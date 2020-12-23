%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:33 EST 2020

% Result     : Theorem 36.21s
% Output     : CNFRefutation 36.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 108 expanded)
%              Number of leaves         :   26 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :   99 ( 249 expanded)
%              Number of equality atoms :   21 (  53 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_1 > #skF_12 > #skF_13 > #skF_10 > #skF_2 > #skF_4 > #skF_3 > #skF_8 > #skF_7 > #skF_9 > #skF_5

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

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
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_46,plain,(
    v1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_108,plain,(
    ! [A_114,B_115] :
      ( r2_hidden(k4_tarski('#skF_10'(A_114,B_115),'#skF_9'(A_114,B_115)),A_114)
      | r2_hidden('#skF_11'(A_114,B_115),B_115)
      | k2_relat_1(A_114) = B_115 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_34,plain,(
    ! [C_77,A_62,D_80] :
      ( r2_hidden(C_77,k2_relat_1(A_62))
      | ~ r2_hidden(k4_tarski(D_80,C_77),A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_119,plain,(
    ! [A_114,B_115] :
      ( r2_hidden('#skF_9'(A_114,B_115),k2_relat_1(A_114))
      | r2_hidden('#skF_11'(A_114,B_115),B_115)
      | k2_relat_1(A_114) = B_115 ) ),
    inference(resolution,[status(thm)],[c_108,c_34])).

tff(c_151,plain,(
    ! [A_127,B_128,D_129] :
      ( r2_hidden(k4_tarski('#skF_4'(A_127,B_128,k9_relat_1(A_127,B_128),D_129),D_129),A_127)
      | ~ r2_hidden(D_129,k9_relat_1(A_127,B_128))
      | ~ v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_163,plain,(
    ! [D_130,A_131,B_132] :
      ( r2_hidden(D_130,k2_relat_1(A_131))
      | ~ r2_hidden(D_130,k9_relat_1(A_131,B_132))
      | ~ v1_relat_1(A_131) ) ),
    inference(resolution,[status(thm)],[c_151,c_34])).

tff(c_7002,plain,(
    ! [A_444,A_445,B_446] :
      ( r2_hidden('#skF_11'(A_444,k9_relat_1(A_445,B_446)),k2_relat_1(A_445))
      | ~ v1_relat_1(A_445)
      | r2_hidden('#skF_9'(A_444,k9_relat_1(A_445,B_446)),k2_relat_1(A_444))
      | k9_relat_1(A_445,B_446) = k2_relat_1(A_444) ) ),
    inference(resolution,[status(thm)],[c_119,c_163])).

tff(c_32,plain,(
    ! [A_62,C_77] :
      ( r2_hidden(k4_tarski('#skF_12'(A_62,k2_relat_1(A_62),C_77),C_77),A_62)
      | ~ r2_hidden(C_77,k2_relat_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_245,plain,(
    ! [A_139,B_140,D_141] :
      ( r2_hidden(k4_tarski('#skF_10'(A_139,B_140),'#skF_9'(A_139,B_140)),A_139)
      | ~ r2_hidden(k4_tarski(D_141,'#skF_11'(A_139,B_140)),A_139)
      | k2_relat_1(A_139) = B_140 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_254,plain,(
    ! [A_142,B_143] :
      ( r2_hidden(k4_tarski('#skF_10'(A_142,B_143),'#skF_9'(A_142,B_143)),A_142)
      | k2_relat_1(A_142) = B_143
      | ~ r2_hidden('#skF_11'(A_142,B_143),k2_relat_1(A_142)) ) ),
    inference(resolution,[status(thm)],[c_32,c_245])).

tff(c_270,plain,(
    ! [A_142,B_143] :
      ( r2_hidden('#skF_9'(A_142,B_143),k2_relat_1(A_142))
      | k2_relat_1(A_142) = B_143
      | ~ r2_hidden('#skF_11'(A_142,B_143),k2_relat_1(A_142)) ) ),
    inference(resolution,[status(thm)],[c_254,c_34])).

tff(c_7038,plain,(
    ! [A_445,B_446] :
      ( ~ v1_relat_1(A_445)
      | r2_hidden('#skF_9'(A_445,k9_relat_1(A_445,B_446)),k2_relat_1(A_445))
      | k9_relat_1(A_445,B_446) = k2_relat_1(A_445) ) ),
    inference(resolution,[status(thm)],[c_7002,c_270])).

tff(c_50,plain,(
    ! [A_89,C_90] :
      ( r2_hidden(k4_tarski('#skF_12'(A_89,k2_relat_1(A_89),C_90),C_90),A_89)
      | ~ r2_hidden(C_90,k2_relat_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_22,plain,(
    ! [C_58,A_43,D_61] :
      ( r2_hidden(C_58,k1_relat_1(A_43))
      | ~ r2_hidden(k4_tarski(C_58,D_61),A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_57,plain,(
    ! [A_89,C_90] :
      ( r2_hidden('#skF_12'(A_89,k2_relat_1(A_89),C_90),k1_relat_1(A_89))
      | ~ r2_hidden(C_90,k2_relat_1(A_89)) ) ),
    inference(resolution,[status(thm)],[c_50,c_22])).

tff(c_71,plain,(
    ! [D_99,A_100,B_101,E_102] :
      ( r2_hidden(D_99,k9_relat_1(A_100,B_101))
      | ~ r2_hidden(E_102,B_101)
      | ~ r2_hidden(k4_tarski(E_102,D_99),A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_370,plain,(
    ! [D_168,A_169,A_170,C_171] :
      ( r2_hidden(D_168,k9_relat_1(A_169,k1_relat_1(A_170)))
      | ~ r2_hidden(k4_tarski('#skF_12'(A_170,k2_relat_1(A_170),C_171),D_168),A_169)
      | ~ v1_relat_1(A_169)
      | ~ r2_hidden(C_171,k2_relat_1(A_170)) ) ),
    inference(resolution,[status(thm)],[c_57,c_71])).

tff(c_379,plain,(
    ! [C_77,A_62] :
      ( r2_hidden(C_77,k9_relat_1(A_62,k1_relat_1(A_62)))
      | ~ v1_relat_1(A_62)
      | ~ r2_hidden(C_77,k2_relat_1(A_62)) ) ),
    inference(resolution,[status(thm)],[c_32,c_370])).

tff(c_40,plain,(
    ! [A_62,B_63] :
      ( ~ r2_hidden('#skF_9'(A_62,B_63),B_63)
      | r2_hidden('#skF_11'(A_62,B_63),B_63)
      | k2_relat_1(A_62) = B_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18293,plain,(
    ! [A_722,A_723,B_724] :
      ( r2_hidden('#skF_11'(A_722,k9_relat_1(A_723,B_724)),k2_relat_1(A_723))
      | ~ v1_relat_1(A_723)
      | ~ r2_hidden('#skF_9'(A_722,k9_relat_1(A_723,B_724)),k9_relat_1(A_723,B_724))
      | k9_relat_1(A_723,B_724) = k2_relat_1(A_722) ) ),
    inference(resolution,[status(thm)],[c_40,c_163])).

tff(c_18302,plain,(
    ! [A_722,A_62] :
      ( r2_hidden('#skF_11'(A_722,k9_relat_1(A_62,k1_relat_1(A_62))),k2_relat_1(A_62))
      | k9_relat_1(A_62,k1_relat_1(A_62)) = k2_relat_1(A_722)
      | ~ v1_relat_1(A_62)
      | ~ r2_hidden('#skF_9'(A_722,k9_relat_1(A_62,k1_relat_1(A_62))),k2_relat_1(A_62)) ) ),
    inference(resolution,[status(thm)],[c_379,c_18293])).

tff(c_380,plain,(
    ! [C_172,A_173] :
      ( r2_hidden(C_172,k9_relat_1(A_173,k1_relat_1(A_173)))
      | ~ v1_relat_1(A_173)
      | ~ r2_hidden(C_172,k2_relat_1(A_173)) ) ),
    inference(resolution,[status(thm)],[c_32,c_370])).

tff(c_36,plain,(
    ! [A_62,B_63,D_76] :
      ( ~ r2_hidden('#skF_9'(A_62,B_63),B_63)
      | ~ r2_hidden(k4_tarski(D_76,'#skF_11'(A_62,B_63)),A_62)
      | k2_relat_1(A_62) = B_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_84753,plain,(
    ! [D_1708,A_1709,A_1710] :
      ( ~ r2_hidden(k4_tarski(D_1708,'#skF_11'(A_1709,k9_relat_1(A_1710,k1_relat_1(A_1710)))),A_1709)
      | k9_relat_1(A_1710,k1_relat_1(A_1710)) = k2_relat_1(A_1709)
      | ~ v1_relat_1(A_1710)
      | ~ r2_hidden('#skF_9'(A_1709,k9_relat_1(A_1710,k1_relat_1(A_1710))),k2_relat_1(A_1710)) ) ),
    inference(resolution,[status(thm)],[c_380,c_36])).

tff(c_85374,plain,(
    ! [A_1711,A_1712] :
      ( k9_relat_1(A_1711,k1_relat_1(A_1711)) = k2_relat_1(A_1712)
      | ~ v1_relat_1(A_1711)
      | ~ r2_hidden('#skF_9'(A_1712,k9_relat_1(A_1711,k1_relat_1(A_1711))),k2_relat_1(A_1711))
      | ~ r2_hidden('#skF_11'(A_1712,k9_relat_1(A_1711,k1_relat_1(A_1711))),k2_relat_1(A_1712)) ) ),
    inference(resolution,[status(thm)],[c_32,c_84753])).

tff(c_85671,plain,(
    ! [A_1713] :
      ( ~ r2_hidden('#skF_11'(A_1713,k9_relat_1(A_1713,k1_relat_1(A_1713))),k2_relat_1(A_1713))
      | ~ v1_relat_1(A_1713)
      | k9_relat_1(A_1713,k1_relat_1(A_1713)) = k2_relat_1(A_1713) ) ),
    inference(resolution,[status(thm)],[c_7038,c_85374])).

tff(c_86037,plain,(
    ! [A_1714] :
      ( k9_relat_1(A_1714,k1_relat_1(A_1714)) = k2_relat_1(A_1714)
      | ~ v1_relat_1(A_1714)
      | ~ r2_hidden('#skF_9'(A_1714,k9_relat_1(A_1714,k1_relat_1(A_1714))),k2_relat_1(A_1714)) ) ),
    inference(resolution,[status(thm)],[c_18302,c_85671])).

tff(c_86401,plain,(
    ! [A_1715] :
      ( ~ v1_relat_1(A_1715)
      | k9_relat_1(A_1715,k1_relat_1(A_1715)) = k2_relat_1(A_1715) ) ),
    inference(resolution,[status(thm)],[c_7038,c_86037])).

tff(c_44,plain,(
    k9_relat_1('#skF_13',k1_relat_1('#skF_13')) != k2_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_87705,plain,(
    ~ v1_relat_1('#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_86401,c_44])).

tff(c_87714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_87705])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:47:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 36.21/24.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.21/24.45  
% 36.21/24.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.21/24.45  %$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_1 > #skF_12 > #skF_13 > #skF_10 > #skF_2 > #skF_4 > #skF_3 > #skF_8 > #skF_7 > #skF_9 > #skF_5
% 36.21/24.45  
% 36.21/24.45  %Foreground sorts:
% 36.21/24.45  
% 36.21/24.45  
% 36.21/24.45  %Background operators:
% 36.21/24.45  
% 36.21/24.45  
% 36.21/24.45  %Foreground operators:
% 36.21/24.45  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 36.21/24.45  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 36.21/24.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 36.21/24.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 36.21/24.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 36.21/24.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 36.21/24.45  tff('#skF_12', type, '#skF_12': ($i * $i * $i) > $i).
% 36.21/24.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 36.21/24.45  tff('#skF_13', type, '#skF_13': $i).
% 36.21/24.45  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 36.21/24.45  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 36.21/24.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 36.21/24.45  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 36.21/24.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 36.21/24.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 36.21/24.45  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 36.21/24.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 36.21/24.45  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 36.21/24.45  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 36.21/24.45  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 36.21/24.45  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 36.21/24.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 36.21/24.45  
% 36.21/24.46  tff(f_59, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 36.21/24.46  tff(f_54, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 36.21/24.46  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 36.21/24.46  tff(f_46, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 36.21/24.46  tff(c_46, plain, (v1_relat_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_59])).
% 36.21/24.46  tff(c_108, plain, (![A_114, B_115]: (r2_hidden(k4_tarski('#skF_10'(A_114, B_115), '#skF_9'(A_114, B_115)), A_114) | r2_hidden('#skF_11'(A_114, B_115), B_115) | k2_relat_1(A_114)=B_115)), inference(cnfTransformation, [status(thm)], [f_54])).
% 36.21/24.46  tff(c_34, plain, (![C_77, A_62, D_80]: (r2_hidden(C_77, k2_relat_1(A_62)) | ~r2_hidden(k4_tarski(D_80, C_77), A_62))), inference(cnfTransformation, [status(thm)], [f_54])).
% 36.21/24.46  tff(c_119, plain, (![A_114, B_115]: (r2_hidden('#skF_9'(A_114, B_115), k2_relat_1(A_114)) | r2_hidden('#skF_11'(A_114, B_115), B_115) | k2_relat_1(A_114)=B_115)), inference(resolution, [status(thm)], [c_108, c_34])).
% 36.21/24.46  tff(c_151, plain, (![A_127, B_128, D_129]: (r2_hidden(k4_tarski('#skF_4'(A_127, B_128, k9_relat_1(A_127, B_128), D_129), D_129), A_127) | ~r2_hidden(D_129, k9_relat_1(A_127, B_128)) | ~v1_relat_1(A_127))), inference(cnfTransformation, [status(thm)], [f_38])).
% 36.21/24.46  tff(c_163, plain, (![D_130, A_131, B_132]: (r2_hidden(D_130, k2_relat_1(A_131)) | ~r2_hidden(D_130, k9_relat_1(A_131, B_132)) | ~v1_relat_1(A_131))), inference(resolution, [status(thm)], [c_151, c_34])).
% 36.21/24.46  tff(c_7002, plain, (![A_444, A_445, B_446]: (r2_hidden('#skF_11'(A_444, k9_relat_1(A_445, B_446)), k2_relat_1(A_445)) | ~v1_relat_1(A_445) | r2_hidden('#skF_9'(A_444, k9_relat_1(A_445, B_446)), k2_relat_1(A_444)) | k9_relat_1(A_445, B_446)=k2_relat_1(A_444))), inference(resolution, [status(thm)], [c_119, c_163])).
% 36.21/24.46  tff(c_32, plain, (![A_62, C_77]: (r2_hidden(k4_tarski('#skF_12'(A_62, k2_relat_1(A_62), C_77), C_77), A_62) | ~r2_hidden(C_77, k2_relat_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 36.21/24.46  tff(c_245, plain, (![A_139, B_140, D_141]: (r2_hidden(k4_tarski('#skF_10'(A_139, B_140), '#skF_9'(A_139, B_140)), A_139) | ~r2_hidden(k4_tarski(D_141, '#skF_11'(A_139, B_140)), A_139) | k2_relat_1(A_139)=B_140)), inference(cnfTransformation, [status(thm)], [f_54])).
% 36.21/24.46  tff(c_254, plain, (![A_142, B_143]: (r2_hidden(k4_tarski('#skF_10'(A_142, B_143), '#skF_9'(A_142, B_143)), A_142) | k2_relat_1(A_142)=B_143 | ~r2_hidden('#skF_11'(A_142, B_143), k2_relat_1(A_142)))), inference(resolution, [status(thm)], [c_32, c_245])).
% 36.21/24.46  tff(c_270, plain, (![A_142, B_143]: (r2_hidden('#skF_9'(A_142, B_143), k2_relat_1(A_142)) | k2_relat_1(A_142)=B_143 | ~r2_hidden('#skF_11'(A_142, B_143), k2_relat_1(A_142)))), inference(resolution, [status(thm)], [c_254, c_34])).
% 36.21/24.46  tff(c_7038, plain, (![A_445, B_446]: (~v1_relat_1(A_445) | r2_hidden('#skF_9'(A_445, k9_relat_1(A_445, B_446)), k2_relat_1(A_445)) | k9_relat_1(A_445, B_446)=k2_relat_1(A_445))), inference(resolution, [status(thm)], [c_7002, c_270])).
% 36.21/24.46  tff(c_50, plain, (![A_89, C_90]: (r2_hidden(k4_tarski('#skF_12'(A_89, k2_relat_1(A_89), C_90), C_90), A_89) | ~r2_hidden(C_90, k2_relat_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 36.21/24.46  tff(c_22, plain, (![C_58, A_43, D_61]: (r2_hidden(C_58, k1_relat_1(A_43)) | ~r2_hidden(k4_tarski(C_58, D_61), A_43))), inference(cnfTransformation, [status(thm)], [f_46])).
% 36.21/24.46  tff(c_57, plain, (![A_89, C_90]: (r2_hidden('#skF_12'(A_89, k2_relat_1(A_89), C_90), k1_relat_1(A_89)) | ~r2_hidden(C_90, k2_relat_1(A_89)))), inference(resolution, [status(thm)], [c_50, c_22])).
% 36.21/24.46  tff(c_71, plain, (![D_99, A_100, B_101, E_102]: (r2_hidden(D_99, k9_relat_1(A_100, B_101)) | ~r2_hidden(E_102, B_101) | ~r2_hidden(k4_tarski(E_102, D_99), A_100) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_38])).
% 36.21/24.46  tff(c_370, plain, (![D_168, A_169, A_170, C_171]: (r2_hidden(D_168, k9_relat_1(A_169, k1_relat_1(A_170))) | ~r2_hidden(k4_tarski('#skF_12'(A_170, k2_relat_1(A_170), C_171), D_168), A_169) | ~v1_relat_1(A_169) | ~r2_hidden(C_171, k2_relat_1(A_170)))), inference(resolution, [status(thm)], [c_57, c_71])).
% 36.21/24.46  tff(c_379, plain, (![C_77, A_62]: (r2_hidden(C_77, k9_relat_1(A_62, k1_relat_1(A_62))) | ~v1_relat_1(A_62) | ~r2_hidden(C_77, k2_relat_1(A_62)))), inference(resolution, [status(thm)], [c_32, c_370])).
% 36.21/24.46  tff(c_40, plain, (![A_62, B_63]: (~r2_hidden('#skF_9'(A_62, B_63), B_63) | r2_hidden('#skF_11'(A_62, B_63), B_63) | k2_relat_1(A_62)=B_63)), inference(cnfTransformation, [status(thm)], [f_54])).
% 36.21/24.46  tff(c_18293, plain, (![A_722, A_723, B_724]: (r2_hidden('#skF_11'(A_722, k9_relat_1(A_723, B_724)), k2_relat_1(A_723)) | ~v1_relat_1(A_723) | ~r2_hidden('#skF_9'(A_722, k9_relat_1(A_723, B_724)), k9_relat_1(A_723, B_724)) | k9_relat_1(A_723, B_724)=k2_relat_1(A_722))), inference(resolution, [status(thm)], [c_40, c_163])).
% 36.21/24.46  tff(c_18302, plain, (![A_722, A_62]: (r2_hidden('#skF_11'(A_722, k9_relat_1(A_62, k1_relat_1(A_62))), k2_relat_1(A_62)) | k9_relat_1(A_62, k1_relat_1(A_62))=k2_relat_1(A_722) | ~v1_relat_1(A_62) | ~r2_hidden('#skF_9'(A_722, k9_relat_1(A_62, k1_relat_1(A_62))), k2_relat_1(A_62)))), inference(resolution, [status(thm)], [c_379, c_18293])).
% 36.21/24.46  tff(c_380, plain, (![C_172, A_173]: (r2_hidden(C_172, k9_relat_1(A_173, k1_relat_1(A_173))) | ~v1_relat_1(A_173) | ~r2_hidden(C_172, k2_relat_1(A_173)))), inference(resolution, [status(thm)], [c_32, c_370])).
% 36.21/24.46  tff(c_36, plain, (![A_62, B_63, D_76]: (~r2_hidden('#skF_9'(A_62, B_63), B_63) | ~r2_hidden(k4_tarski(D_76, '#skF_11'(A_62, B_63)), A_62) | k2_relat_1(A_62)=B_63)), inference(cnfTransformation, [status(thm)], [f_54])).
% 36.21/24.46  tff(c_84753, plain, (![D_1708, A_1709, A_1710]: (~r2_hidden(k4_tarski(D_1708, '#skF_11'(A_1709, k9_relat_1(A_1710, k1_relat_1(A_1710)))), A_1709) | k9_relat_1(A_1710, k1_relat_1(A_1710))=k2_relat_1(A_1709) | ~v1_relat_1(A_1710) | ~r2_hidden('#skF_9'(A_1709, k9_relat_1(A_1710, k1_relat_1(A_1710))), k2_relat_1(A_1710)))), inference(resolution, [status(thm)], [c_380, c_36])).
% 36.21/24.46  tff(c_85374, plain, (![A_1711, A_1712]: (k9_relat_1(A_1711, k1_relat_1(A_1711))=k2_relat_1(A_1712) | ~v1_relat_1(A_1711) | ~r2_hidden('#skF_9'(A_1712, k9_relat_1(A_1711, k1_relat_1(A_1711))), k2_relat_1(A_1711)) | ~r2_hidden('#skF_11'(A_1712, k9_relat_1(A_1711, k1_relat_1(A_1711))), k2_relat_1(A_1712)))), inference(resolution, [status(thm)], [c_32, c_84753])).
% 36.21/24.46  tff(c_85671, plain, (![A_1713]: (~r2_hidden('#skF_11'(A_1713, k9_relat_1(A_1713, k1_relat_1(A_1713))), k2_relat_1(A_1713)) | ~v1_relat_1(A_1713) | k9_relat_1(A_1713, k1_relat_1(A_1713))=k2_relat_1(A_1713))), inference(resolution, [status(thm)], [c_7038, c_85374])).
% 36.21/24.46  tff(c_86037, plain, (![A_1714]: (k9_relat_1(A_1714, k1_relat_1(A_1714))=k2_relat_1(A_1714) | ~v1_relat_1(A_1714) | ~r2_hidden('#skF_9'(A_1714, k9_relat_1(A_1714, k1_relat_1(A_1714))), k2_relat_1(A_1714)))), inference(resolution, [status(thm)], [c_18302, c_85671])).
% 36.21/24.46  tff(c_86401, plain, (![A_1715]: (~v1_relat_1(A_1715) | k9_relat_1(A_1715, k1_relat_1(A_1715))=k2_relat_1(A_1715))), inference(resolution, [status(thm)], [c_7038, c_86037])).
% 36.21/24.46  tff(c_44, plain, (k9_relat_1('#skF_13', k1_relat_1('#skF_13'))!=k2_relat_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_59])).
% 36.21/24.46  tff(c_87705, plain, (~v1_relat_1('#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_86401, c_44])).
% 36.21/24.46  tff(c_87714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_87705])).
% 36.21/24.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.21/24.46  
% 36.21/24.46  Inference rules
% 36.21/24.46  ----------------------
% 36.21/24.46  #Ref     : 0
% 36.21/24.46  #Sup     : 20920
% 36.21/24.46  #Fact    : 0
% 36.21/24.46  #Define  : 0
% 36.21/24.46  #Split   : 0
% 36.21/24.46  #Chain   : 0
% 36.21/24.46  #Close   : 0
% 36.21/24.46  
% 36.21/24.46  Ordering : KBO
% 36.21/24.46  
% 36.21/24.46  Simplification rules
% 36.21/24.46  ----------------------
% 36.21/24.46  #Subsume      : 631
% 36.21/24.46  #Demod        : 1
% 36.21/24.46  #Tautology    : 239
% 36.21/24.46  #SimpNegUnit  : 0
% 36.21/24.46  #BackRed      : 0
% 36.21/24.46  
% 36.21/24.46  #Partial instantiations: 0
% 36.21/24.46  #Strategies tried      : 1
% 36.21/24.46  
% 36.21/24.46  Timing (in seconds)
% 36.21/24.46  ----------------------
% 36.21/24.47  Preprocessing        : 0.30
% 36.21/24.47  Parsing              : 0.15
% 36.21/24.47  CNF conversion       : 0.03
% 36.21/24.47  Main loop            : 23.39
% 36.21/24.47  Inferencing          : 3.08
% 36.21/24.47  Reduction            : 2.36
% 36.21/24.47  Demodulation         : 1.47
% 36.21/24.47  BG Simplification    : 0.52
% 36.21/24.47  Subsumption          : 15.96
% 36.21/24.47  Abstraction          : 0.94
% 36.21/24.47  MUC search           : 0.00
% 36.21/24.47  Cooper               : 0.00
% 36.21/24.47  Total                : 23.72
% 36.21/24.47  Index Insertion      : 0.00
% 36.21/24.47  Index Deletion       : 0.00
% 36.21/24.47  Index Matching       : 0.00
% 36.21/24.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
