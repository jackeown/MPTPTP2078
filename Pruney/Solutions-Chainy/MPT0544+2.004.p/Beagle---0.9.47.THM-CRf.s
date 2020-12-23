%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:33 EST 2020

% Result     : Theorem 36.27s
% Output     : CNFRefutation 36.40s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 117 expanded)
%              Number of leaves         :   23 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  105 ( 285 expanded)
%              Number of equality atoms :   20 (  52 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_4 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_105,plain,(
    ! [A_81,B_82] :
      ( r2_hidden(k4_tarski('#skF_6'(A_81,B_82),'#skF_5'(A_81,B_82)),A_81)
      | r2_hidden('#skF_7'(A_81,B_82),B_82)
      | k2_relat_1(A_81) = B_82 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [C_35,A_20,D_38] :
      ( r2_hidden(C_35,k2_relat_1(A_20))
      | ~ r2_hidden(k4_tarski(D_38,C_35),A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_119,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_5'(A_83,B_84),k2_relat_1(A_83))
      | r2_hidden('#skF_7'(A_83,B_84),B_84)
      | k2_relat_1(A_83) = B_84 ) ),
    inference(resolution,[status(thm)],[c_105,c_16])).

tff(c_64,plain,(
    ! [A_72,B_73,C_74] :
      ( r2_hidden(k4_tarski('#skF_9'(A_72,B_73,C_74),A_72),C_74)
      | ~ r2_hidden(A_72,k9_relat_1(C_74,B_73))
      | ~ v1_relat_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_71,plain,(
    ! [A_72,C_74,B_73] :
      ( r2_hidden(A_72,k2_relat_1(C_74))
      | ~ r2_hidden(A_72,k9_relat_1(C_74,B_73))
      | ~ v1_relat_1(C_74) ) ),
    inference(resolution,[status(thm)],[c_64,c_16])).

tff(c_638,plain,(
    ! [A_153,C_154,B_155] :
      ( r2_hidden('#skF_7'(A_153,k9_relat_1(C_154,B_155)),k2_relat_1(C_154))
      | ~ v1_relat_1(C_154)
      | r2_hidden('#skF_5'(A_153,k9_relat_1(C_154,B_155)),k2_relat_1(A_153))
      | k9_relat_1(C_154,B_155) = k2_relat_1(A_153) ) ),
    inference(resolution,[status(thm)],[c_119,c_71])).

tff(c_14,plain,(
    ! [A_20,C_35] :
      ( r2_hidden(k4_tarski('#skF_8'(A_20,k2_relat_1(A_20),C_35),C_35),A_20)
      | ~ r2_hidden(C_35,k2_relat_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_239,plain,(
    ! [A_102,B_103,D_104] :
      ( r2_hidden(k4_tarski('#skF_6'(A_102,B_103),'#skF_5'(A_102,B_103)),A_102)
      | ~ r2_hidden(k4_tarski(D_104,'#skF_7'(A_102,B_103)),A_102)
      | k2_relat_1(A_102) = B_103 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_286,plain,(
    ! [A_109,B_110] :
      ( r2_hidden(k4_tarski('#skF_6'(A_109,B_110),'#skF_5'(A_109,B_110)),A_109)
      | k2_relat_1(A_109) = B_110
      | ~ r2_hidden('#skF_7'(A_109,B_110),k2_relat_1(A_109)) ) ),
    inference(resolution,[status(thm)],[c_14,c_239])).

tff(c_301,plain,(
    ! [A_109,B_110] :
      ( r2_hidden('#skF_5'(A_109,B_110),k2_relat_1(A_109))
      | k2_relat_1(A_109) = B_110
      | ~ r2_hidden('#skF_7'(A_109,B_110),k2_relat_1(A_109)) ) ),
    inference(resolution,[status(thm)],[c_286,c_16])).

tff(c_656,plain,(
    ! [C_154,B_155] :
      ( ~ v1_relat_1(C_154)
      | r2_hidden('#skF_5'(C_154,k9_relat_1(C_154,B_155)),k2_relat_1(C_154))
      | k9_relat_1(C_154,B_155) = k2_relat_1(C_154) ) ),
    inference(resolution,[status(thm)],[c_638,c_301])).

tff(c_50,plain,(
    ! [A_57,C_58] :
      ( r2_hidden(k4_tarski('#skF_8'(A_57,k2_relat_1(A_57),C_58),C_58),A_57)
      | ~ r2_hidden(C_58,k2_relat_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [C_16,A_1,D_19] :
      ( r2_hidden(C_16,k1_relat_1(A_1))
      | ~ r2_hidden(k4_tarski(C_16,D_19),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_58,plain,(
    ! [A_57,C_58] :
      ( r2_hidden('#skF_8'(A_57,k2_relat_1(A_57),C_58),k1_relat_1(A_57))
      | ~ r2_hidden(C_58,k2_relat_1(A_57)) ) ),
    inference(resolution,[status(thm)],[c_50,c_4])).

tff(c_159,plain,(
    ! [A_93,C_94,B_95,D_96] :
      ( r2_hidden(A_93,k9_relat_1(C_94,B_95))
      | ~ r2_hidden(D_96,B_95)
      | ~ r2_hidden(k4_tarski(D_96,A_93),C_94)
      | ~ r2_hidden(D_96,k1_relat_1(C_94))
      | ~ v1_relat_1(C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_7245,plain,(
    ! [A_593,C_594,A_595,C_596] :
      ( r2_hidden(A_593,k9_relat_1(C_594,k1_relat_1(A_595)))
      | ~ r2_hidden(k4_tarski('#skF_8'(A_595,k2_relat_1(A_595),C_596),A_593),C_594)
      | ~ r2_hidden('#skF_8'(A_595,k2_relat_1(A_595),C_596),k1_relat_1(C_594))
      | ~ v1_relat_1(C_594)
      | ~ r2_hidden(C_596,k2_relat_1(A_595)) ) ),
    inference(resolution,[status(thm)],[c_58,c_159])).

tff(c_7309,plain,(
    ! [C_597,A_598] :
      ( r2_hidden(C_597,k9_relat_1(A_598,k1_relat_1(A_598)))
      | ~ r2_hidden('#skF_8'(A_598,k2_relat_1(A_598),C_597),k1_relat_1(A_598))
      | ~ v1_relat_1(A_598)
      | ~ r2_hidden(C_597,k2_relat_1(A_598)) ) ),
    inference(resolution,[status(thm)],[c_14,c_7245])).

tff(c_7329,plain,(
    ! [C_599,A_600] :
      ( r2_hidden(C_599,k9_relat_1(A_600,k1_relat_1(A_600)))
      | ~ v1_relat_1(A_600)
      | ~ r2_hidden(C_599,k2_relat_1(A_600)) ) ),
    inference(resolution,[status(thm)],[c_58,c_7309])).

tff(c_22,plain,(
    ! [A_20,B_21] :
      ( ~ r2_hidden('#skF_5'(A_20,B_21),B_21)
      | r2_hidden('#skF_7'(A_20,B_21),B_21)
      | k2_relat_1(A_20) = B_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_73,plain,(
    ! [A_75,C_76,B_77] :
      ( r2_hidden(A_75,k2_relat_1(C_76))
      | ~ r2_hidden(A_75,k9_relat_1(C_76,B_77))
      | ~ v1_relat_1(C_76) ) ),
    inference(resolution,[status(thm)],[c_64,c_16])).

tff(c_103,plain,(
    ! [A_20,C_76,B_77] :
      ( r2_hidden('#skF_7'(A_20,k9_relat_1(C_76,B_77)),k2_relat_1(C_76))
      | ~ v1_relat_1(C_76)
      | ~ r2_hidden('#skF_5'(A_20,k9_relat_1(C_76,B_77)),k9_relat_1(C_76,B_77))
      | k9_relat_1(C_76,B_77) = k2_relat_1(A_20) ) ),
    inference(resolution,[status(thm)],[c_22,c_73])).

tff(c_7471,plain,(
    ! [A_20,A_600] :
      ( r2_hidden('#skF_7'(A_20,k9_relat_1(A_600,k1_relat_1(A_600))),k2_relat_1(A_600))
      | k9_relat_1(A_600,k1_relat_1(A_600)) = k2_relat_1(A_20)
      | ~ v1_relat_1(A_600)
      | ~ r2_hidden('#skF_5'(A_20,k9_relat_1(A_600,k1_relat_1(A_600))),k2_relat_1(A_600)) ) ),
    inference(resolution,[status(thm)],[c_7329,c_103])).

tff(c_18,plain,(
    ! [A_20,B_21,D_34] :
      ( ~ r2_hidden('#skF_5'(A_20,B_21),B_21)
      | ~ r2_hidden(k4_tarski(D_34,'#skF_7'(A_20,B_21)),A_20)
      | k2_relat_1(A_20) = B_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_77492,plain,(
    ! [D_1770,A_1771,A_1772] :
      ( ~ r2_hidden(k4_tarski(D_1770,'#skF_7'(A_1771,k9_relat_1(A_1772,k1_relat_1(A_1772)))),A_1771)
      | k9_relat_1(A_1772,k1_relat_1(A_1772)) = k2_relat_1(A_1771)
      | ~ v1_relat_1(A_1772)
      | ~ r2_hidden('#skF_5'(A_1771,k9_relat_1(A_1772,k1_relat_1(A_1772))),k2_relat_1(A_1772)) ) ),
    inference(resolution,[status(thm)],[c_7329,c_18])).

tff(c_78101,plain,(
    ! [A_1773,A_1774] :
      ( k9_relat_1(A_1773,k1_relat_1(A_1773)) = k2_relat_1(A_1774)
      | ~ v1_relat_1(A_1773)
      | ~ r2_hidden('#skF_5'(A_1774,k9_relat_1(A_1773,k1_relat_1(A_1773))),k2_relat_1(A_1773))
      | ~ r2_hidden('#skF_7'(A_1774,k9_relat_1(A_1773,k1_relat_1(A_1773))),k2_relat_1(A_1774)) ) ),
    inference(resolution,[status(thm)],[c_14,c_77492])).

tff(c_78397,plain,(
    ! [C_1775] :
      ( ~ r2_hidden('#skF_7'(C_1775,k9_relat_1(C_1775,k1_relat_1(C_1775))),k2_relat_1(C_1775))
      | ~ v1_relat_1(C_1775)
      | k9_relat_1(C_1775,k1_relat_1(C_1775)) = k2_relat_1(C_1775) ) ),
    inference(resolution,[status(thm)],[c_656,c_78101])).

tff(c_78931,plain,(
    ! [A_1780] :
      ( k9_relat_1(A_1780,k1_relat_1(A_1780)) = k2_relat_1(A_1780)
      | ~ v1_relat_1(A_1780)
      | ~ r2_hidden('#skF_5'(A_1780,k9_relat_1(A_1780,k1_relat_1(A_1780))),k2_relat_1(A_1780)) ) ),
    inference(resolution,[status(thm)],[c_7471,c_78397])).

tff(c_79292,plain,(
    ! [C_1781] :
      ( ~ v1_relat_1(C_1781)
      | k9_relat_1(C_1781,k1_relat_1(C_1781)) = k2_relat_1(C_1781) ) ),
    inference(resolution,[status(thm)],[c_656,c_78931])).

tff(c_34,plain,(
    k9_relat_1('#skF_10',k1_relat_1('#skF_10')) != k2_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_80847,plain,(
    ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_79292,c_34])).

tff(c_80855,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_80847])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:18:42 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 36.27/24.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.27/24.98  
% 36.27/24.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.27/24.98  %$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_4 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5
% 36.27/24.98  
% 36.27/24.98  %Foreground sorts:
% 36.27/24.98  
% 36.27/24.98  
% 36.27/24.98  %Background operators:
% 36.27/24.98  
% 36.27/24.98  
% 36.27/24.98  %Foreground operators:
% 36.27/24.98  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 36.27/24.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 36.27/24.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 36.27/24.98  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 36.27/24.98  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 36.27/24.98  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 36.27/24.98  tff('#skF_10', type, '#skF_10': $i).
% 36.27/24.98  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 36.27/24.98  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 36.27/24.98  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 36.27/24.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 36.27/24.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 36.27/24.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 36.27/24.98  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 36.27/24.98  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 36.27/24.98  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 36.27/24.98  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 36.27/24.98  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 36.27/24.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 36.27/24.98  
% 36.40/24.99  tff(f_57, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 36.40/24.99  tff(f_41, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 36.40/24.99  tff(f_52, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 36.40/24.99  tff(f_33, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 36.40/24.99  tff(c_36, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_57])).
% 36.40/24.99  tff(c_105, plain, (![A_81, B_82]: (r2_hidden(k4_tarski('#skF_6'(A_81, B_82), '#skF_5'(A_81, B_82)), A_81) | r2_hidden('#skF_7'(A_81, B_82), B_82) | k2_relat_1(A_81)=B_82)), inference(cnfTransformation, [status(thm)], [f_41])).
% 36.40/24.99  tff(c_16, plain, (![C_35, A_20, D_38]: (r2_hidden(C_35, k2_relat_1(A_20)) | ~r2_hidden(k4_tarski(D_38, C_35), A_20))), inference(cnfTransformation, [status(thm)], [f_41])).
% 36.40/24.99  tff(c_119, plain, (![A_83, B_84]: (r2_hidden('#skF_5'(A_83, B_84), k2_relat_1(A_83)) | r2_hidden('#skF_7'(A_83, B_84), B_84) | k2_relat_1(A_83)=B_84)), inference(resolution, [status(thm)], [c_105, c_16])).
% 36.40/24.99  tff(c_64, plain, (![A_72, B_73, C_74]: (r2_hidden(k4_tarski('#skF_9'(A_72, B_73, C_74), A_72), C_74) | ~r2_hidden(A_72, k9_relat_1(C_74, B_73)) | ~v1_relat_1(C_74))), inference(cnfTransformation, [status(thm)], [f_52])).
% 36.40/24.99  tff(c_71, plain, (![A_72, C_74, B_73]: (r2_hidden(A_72, k2_relat_1(C_74)) | ~r2_hidden(A_72, k9_relat_1(C_74, B_73)) | ~v1_relat_1(C_74))), inference(resolution, [status(thm)], [c_64, c_16])).
% 36.40/24.99  tff(c_638, plain, (![A_153, C_154, B_155]: (r2_hidden('#skF_7'(A_153, k9_relat_1(C_154, B_155)), k2_relat_1(C_154)) | ~v1_relat_1(C_154) | r2_hidden('#skF_5'(A_153, k9_relat_1(C_154, B_155)), k2_relat_1(A_153)) | k9_relat_1(C_154, B_155)=k2_relat_1(A_153))), inference(resolution, [status(thm)], [c_119, c_71])).
% 36.40/24.99  tff(c_14, plain, (![A_20, C_35]: (r2_hidden(k4_tarski('#skF_8'(A_20, k2_relat_1(A_20), C_35), C_35), A_20) | ~r2_hidden(C_35, k2_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 36.40/24.99  tff(c_239, plain, (![A_102, B_103, D_104]: (r2_hidden(k4_tarski('#skF_6'(A_102, B_103), '#skF_5'(A_102, B_103)), A_102) | ~r2_hidden(k4_tarski(D_104, '#skF_7'(A_102, B_103)), A_102) | k2_relat_1(A_102)=B_103)), inference(cnfTransformation, [status(thm)], [f_41])).
% 36.40/24.99  tff(c_286, plain, (![A_109, B_110]: (r2_hidden(k4_tarski('#skF_6'(A_109, B_110), '#skF_5'(A_109, B_110)), A_109) | k2_relat_1(A_109)=B_110 | ~r2_hidden('#skF_7'(A_109, B_110), k2_relat_1(A_109)))), inference(resolution, [status(thm)], [c_14, c_239])).
% 36.40/24.99  tff(c_301, plain, (![A_109, B_110]: (r2_hidden('#skF_5'(A_109, B_110), k2_relat_1(A_109)) | k2_relat_1(A_109)=B_110 | ~r2_hidden('#skF_7'(A_109, B_110), k2_relat_1(A_109)))), inference(resolution, [status(thm)], [c_286, c_16])).
% 36.40/24.99  tff(c_656, plain, (![C_154, B_155]: (~v1_relat_1(C_154) | r2_hidden('#skF_5'(C_154, k9_relat_1(C_154, B_155)), k2_relat_1(C_154)) | k9_relat_1(C_154, B_155)=k2_relat_1(C_154))), inference(resolution, [status(thm)], [c_638, c_301])).
% 36.40/24.99  tff(c_50, plain, (![A_57, C_58]: (r2_hidden(k4_tarski('#skF_8'(A_57, k2_relat_1(A_57), C_58), C_58), A_57) | ~r2_hidden(C_58, k2_relat_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 36.40/24.99  tff(c_4, plain, (![C_16, A_1, D_19]: (r2_hidden(C_16, k1_relat_1(A_1)) | ~r2_hidden(k4_tarski(C_16, D_19), A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 36.40/24.99  tff(c_58, plain, (![A_57, C_58]: (r2_hidden('#skF_8'(A_57, k2_relat_1(A_57), C_58), k1_relat_1(A_57)) | ~r2_hidden(C_58, k2_relat_1(A_57)))), inference(resolution, [status(thm)], [c_50, c_4])).
% 36.40/24.99  tff(c_159, plain, (![A_93, C_94, B_95, D_96]: (r2_hidden(A_93, k9_relat_1(C_94, B_95)) | ~r2_hidden(D_96, B_95) | ~r2_hidden(k4_tarski(D_96, A_93), C_94) | ~r2_hidden(D_96, k1_relat_1(C_94)) | ~v1_relat_1(C_94))), inference(cnfTransformation, [status(thm)], [f_52])).
% 36.40/24.99  tff(c_7245, plain, (![A_593, C_594, A_595, C_596]: (r2_hidden(A_593, k9_relat_1(C_594, k1_relat_1(A_595))) | ~r2_hidden(k4_tarski('#skF_8'(A_595, k2_relat_1(A_595), C_596), A_593), C_594) | ~r2_hidden('#skF_8'(A_595, k2_relat_1(A_595), C_596), k1_relat_1(C_594)) | ~v1_relat_1(C_594) | ~r2_hidden(C_596, k2_relat_1(A_595)))), inference(resolution, [status(thm)], [c_58, c_159])).
% 36.40/24.99  tff(c_7309, plain, (![C_597, A_598]: (r2_hidden(C_597, k9_relat_1(A_598, k1_relat_1(A_598))) | ~r2_hidden('#skF_8'(A_598, k2_relat_1(A_598), C_597), k1_relat_1(A_598)) | ~v1_relat_1(A_598) | ~r2_hidden(C_597, k2_relat_1(A_598)))), inference(resolution, [status(thm)], [c_14, c_7245])).
% 36.40/24.99  tff(c_7329, plain, (![C_599, A_600]: (r2_hidden(C_599, k9_relat_1(A_600, k1_relat_1(A_600))) | ~v1_relat_1(A_600) | ~r2_hidden(C_599, k2_relat_1(A_600)))), inference(resolution, [status(thm)], [c_58, c_7309])).
% 36.40/24.99  tff(c_22, plain, (![A_20, B_21]: (~r2_hidden('#skF_5'(A_20, B_21), B_21) | r2_hidden('#skF_7'(A_20, B_21), B_21) | k2_relat_1(A_20)=B_21)), inference(cnfTransformation, [status(thm)], [f_41])).
% 36.40/24.99  tff(c_73, plain, (![A_75, C_76, B_77]: (r2_hidden(A_75, k2_relat_1(C_76)) | ~r2_hidden(A_75, k9_relat_1(C_76, B_77)) | ~v1_relat_1(C_76))), inference(resolution, [status(thm)], [c_64, c_16])).
% 36.40/24.99  tff(c_103, plain, (![A_20, C_76, B_77]: (r2_hidden('#skF_7'(A_20, k9_relat_1(C_76, B_77)), k2_relat_1(C_76)) | ~v1_relat_1(C_76) | ~r2_hidden('#skF_5'(A_20, k9_relat_1(C_76, B_77)), k9_relat_1(C_76, B_77)) | k9_relat_1(C_76, B_77)=k2_relat_1(A_20))), inference(resolution, [status(thm)], [c_22, c_73])).
% 36.40/24.99  tff(c_7471, plain, (![A_20, A_600]: (r2_hidden('#skF_7'(A_20, k9_relat_1(A_600, k1_relat_1(A_600))), k2_relat_1(A_600)) | k9_relat_1(A_600, k1_relat_1(A_600))=k2_relat_1(A_20) | ~v1_relat_1(A_600) | ~r2_hidden('#skF_5'(A_20, k9_relat_1(A_600, k1_relat_1(A_600))), k2_relat_1(A_600)))), inference(resolution, [status(thm)], [c_7329, c_103])).
% 36.40/24.99  tff(c_18, plain, (![A_20, B_21, D_34]: (~r2_hidden('#skF_5'(A_20, B_21), B_21) | ~r2_hidden(k4_tarski(D_34, '#skF_7'(A_20, B_21)), A_20) | k2_relat_1(A_20)=B_21)), inference(cnfTransformation, [status(thm)], [f_41])).
% 36.40/24.99  tff(c_77492, plain, (![D_1770, A_1771, A_1772]: (~r2_hidden(k4_tarski(D_1770, '#skF_7'(A_1771, k9_relat_1(A_1772, k1_relat_1(A_1772)))), A_1771) | k9_relat_1(A_1772, k1_relat_1(A_1772))=k2_relat_1(A_1771) | ~v1_relat_1(A_1772) | ~r2_hidden('#skF_5'(A_1771, k9_relat_1(A_1772, k1_relat_1(A_1772))), k2_relat_1(A_1772)))), inference(resolution, [status(thm)], [c_7329, c_18])).
% 36.40/24.99  tff(c_78101, plain, (![A_1773, A_1774]: (k9_relat_1(A_1773, k1_relat_1(A_1773))=k2_relat_1(A_1774) | ~v1_relat_1(A_1773) | ~r2_hidden('#skF_5'(A_1774, k9_relat_1(A_1773, k1_relat_1(A_1773))), k2_relat_1(A_1773)) | ~r2_hidden('#skF_7'(A_1774, k9_relat_1(A_1773, k1_relat_1(A_1773))), k2_relat_1(A_1774)))), inference(resolution, [status(thm)], [c_14, c_77492])).
% 36.40/24.99  tff(c_78397, plain, (![C_1775]: (~r2_hidden('#skF_7'(C_1775, k9_relat_1(C_1775, k1_relat_1(C_1775))), k2_relat_1(C_1775)) | ~v1_relat_1(C_1775) | k9_relat_1(C_1775, k1_relat_1(C_1775))=k2_relat_1(C_1775))), inference(resolution, [status(thm)], [c_656, c_78101])).
% 36.40/24.99  tff(c_78931, plain, (![A_1780]: (k9_relat_1(A_1780, k1_relat_1(A_1780))=k2_relat_1(A_1780) | ~v1_relat_1(A_1780) | ~r2_hidden('#skF_5'(A_1780, k9_relat_1(A_1780, k1_relat_1(A_1780))), k2_relat_1(A_1780)))), inference(resolution, [status(thm)], [c_7471, c_78397])).
% 36.40/24.99  tff(c_79292, plain, (![C_1781]: (~v1_relat_1(C_1781) | k9_relat_1(C_1781, k1_relat_1(C_1781))=k2_relat_1(C_1781))), inference(resolution, [status(thm)], [c_656, c_78931])).
% 36.40/24.99  tff(c_34, plain, (k9_relat_1('#skF_10', k1_relat_1('#skF_10'))!=k2_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_57])).
% 36.40/24.99  tff(c_80847, plain, (~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_79292, c_34])).
% 36.40/24.99  tff(c_80855, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_80847])).
% 36.40/24.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.40/24.99  
% 36.40/24.99  Inference rules
% 36.40/24.99  ----------------------
% 36.40/24.99  #Ref     : 0
% 36.40/24.99  #Sup     : 19277
% 36.40/24.99  #Fact    : 0
% 36.40/24.99  #Define  : 0
% 36.40/24.99  #Split   : 0
% 36.40/24.99  #Chain   : 0
% 36.40/24.99  #Close   : 0
% 36.40/24.99  
% 36.40/24.99  Ordering : KBO
% 36.40/24.99  
% 36.40/24.99  Simplification rules
% 36.40/25.00  ----------------------
% 36.40/25.00  #Subsume      : 833
% 36.40/25.00  #Demod        : 1
% 36.40/25.00  #Tautology    : 241
% 36.40/25.00  #SimpNegUnit  : 0
% 36.40/25.00  #BackRed      : 0
% 36.40/25.00  
% 36.40/25.00  #Partial instantiations: 0
% 36.40/25.00  #Strategies tried      : 1
% 36.40/25.00  
% 36.40/25.00  Timing (in seconds)
% 36.40/25.00  ----------------------
% 36.40/25.00  Preprocessing        : 0.28
% 36.40/25.00  Parsing              : 0.15
% 36.40/25.00  CNF conversion       : 0.03
% 36.40/25.00  Main loop            : 23.96
% 36.40/25.00  Inferencing          : 3.33
% 36.40/25.00  Reduction            : 2.39
% 36.40/25.00  Demodulation         : 1.50
% 36.40/25.00  BG Simplification    : 0.49
% 36.40/25.00  Subsumption          : 16.38
% 36.40/25.00  Abstraction          : 0.93
% 36.40/25.00  MUC search           : 0.00
% 36.40/25.00  Cooper               : 0.00
% 36.40/25.00  Total                : 24.27
% 36.40/25.00  Index Insertion      : 0.00
% 36.40/25.00  Index Deletion       : 0.00
% 36.40/25.00  Index Matching       : 0.00
% 36.40/25.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
