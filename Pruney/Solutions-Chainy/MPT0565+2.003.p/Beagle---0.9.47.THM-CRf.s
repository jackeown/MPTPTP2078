%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:14 EST 2020

% Result     : Theorem 37.89s
% Output     : CNFRefutation 37.89s
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
%$ r2_hidden > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_4 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5

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

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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
       => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_132,plain,(
    ! [A_87,B_88] :
      ( r2_hidden(k4_tarski('#skF_1'(A_87,B_88),'#skF_2'(A_87,B_88)),A_87)
      | r2_hidden('#skF_3'(A_87,B_88),B_88)
      | k1_relat_1(A_87) = B_88 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [C_16,A_1,D_19] :
      ( r2_hidden(C_16,k1_relat_1(A_1))
      | ~ r2_hidden(k4_tarski(C_16,D_19),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_152,plain,(
    ! [A_91,B_92] :
      ( r2_hidden('#skF_1'(A_91,B_92),k1_relat_1(A_91))
      | r2_hidden('#skF_3'(A_91,B_92),B_92)
      | k1_relat_1(A_91) = B_92 ) ),
    inference(resolution,[status(thm)],[c_132,c_4])).

tff(c_64,plain,(
    ! [A_72,B_73,C_74] :
      ( r2_hidden(k4_tarski(A_72,'#skF_9'(A_72,B_73,C_74)),C_74)
      | ~ r2_hidden(A_72,k10_relat_1(C_74,B_73))
      | ~ v1_relat_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_72,plain,(
    ! [A_72,C_74,B_73] :
      ( r2_hidden(A_72,k1_relat_1(C_74))
      | ~ r2_hidden(A_72,k10_relat_1(C_74,B_73))
      | ~ v1_relat_1(C_74) ) ),
    inference(resolution,[status(thm)],[c_64,c_4])).

tff(c_585,plain,(
    ! [A_144,C_145,B_146] :
      ( r2_hidden('#skF_3'(A_144,k10_relat_1(C_145,B_146)),k1_relat_1(C_145))
      | ~ v1_relat_1(C_145)
      | r2_hidden('#skF_1'(A_144,k10_relat_1(C_145,B_146)),k1_relat_1(A_144))
      | k1_relat_1(A_144) = k10_relat_1(C_145,B_146) ) ),
    inference(resolution,[status(thm)],[c_152,c_72])).

tff(c_2,plain,(
    ! [C_16,A_1] :
      ( r2_hidden(k4_tarski(C_16,'#skF_4'(A_1,k1_relat_1(A_1),C_16)),A_1)
      | ~ r2_hidden(C_16,k1_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_217,plain,(
    ! [A_97,B_98,D_99] :
      ( r2_hidden(k4_tarski('#skF_1'(A_97,B_98),'#skF_2'(A_97,B_98)),A_97)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_97,B_98),D_99),A_97)
      | k1_relat_1(A_97) = B_98 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_226,plain,(
    ! [A_100,B_101] :
      ( r2_hidden(k4_tarski('#skF_1'(A_100,B_101),'#skF_2'(A_100,B_101)),A_100)
      | k1_relat_1(A_100) = B_101
      | ~ r2_hidden('#skF_3'(A_100,B_101),k1_relat_1(A_100)) ) ),
    inference(resolution,[status(thm)],[c_2,c_217])).

tff(c_242,plain,(
    ! [A_100,B_101] :
      ( r2_hidden('#skF_1'(A_100,B_101),k1_relat_1(A_100))
      | k1_relat_1(A_100) = B_101
      | ~ r2_hidden('#skF_3'(A_100,B_101),k1_relat_1(A_100)) ) ),
    inference(resolution,[status(thm)],[c_226,c_4])).

tff(c_607,plain,(
    ! [C_145,B_146] :
      ( ~ v1_relat_1(C_145)
      | r2_hidden('#skF_1'(C_145,k10_relat_1(C_145,B_146)),k1_relat_1(C_145))
      | k10_relat_1(C_145,B_146) = k1_relat_1(C_145) ) ),
    inference(resolution,[status(thm)],[c_585,c_242])).

tff(c_40,plain,(
    ! [C_53,A_54] :
      ( r2_hidden(k4_tarski(C_53,'#skF_4'(A_54,k1_relat_1(A_54),C_53)),A_54)
      | ~ r2_hidden(C_53,k1_relat_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [C_35,A_20,D_38] :
      ( r2_hidden(C_35,k2_relat_1(A_20))
      | ~ r2_hidden(k4_tarski(D_38,C_35),A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_47,plain,(
    ! [A_54,C_53] :
      ( r2_hidden('#skF_4'(A_54,k1_relat_1(A_54),C_53),k2_relat_1(A_54))
      | ~ r2_hidden(C_53,k1_relat_1(A_54)) ) ),
    inference(resolution,[status(thm)],[c_40,c_16])).

tff(c_159,plain,(
    ! [A_93,C_94,B_95,D_96] :
      ( r2_hidden(A_93,k10_relat_1(C_94,B_95))
      | ~ r2_hidden(D_96,B_95)
      | ~ r2_hidden(k4_tarski(A_93,D_96),C_94)
      | ~ r2_hidden(D_96,k2_relat_1(C_94))
      | ~ v1_relat_1(C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_7641,plain,(
    ! [A_604,C_605,A_606,C_607] :
      ( r2_hidden(A_604,k10_relat_1(C_605,k2_relat_1(A_606)))
      | ~ r2_hidden(k4_tarski(A_604,'#skF_4'(A_606,k1_relat_1(A_606),C_607)),C_605)
      | ~ r2_hidden('#skF_4'(A_606,k1_relat_1(A_606),C_607),k2_relat_1(C_605))
      | ~ v1_relat_1(C_605)
      | ~ r2_hidden(C_607,k1_relat_1(A_606)) ) ),
    inference(resolution,[status(thm)],[c_47,c_159])).

tff(c_7705,plain,(
    ! [C_608,A_609] :
      ( r2_hidden(C_608,k10_relat_1(A_609,k2_relat_1(A_609)))
      | ~ r2_hidden('#skF_4'(A_609,k1_relat_1(A_609),C_608),k2_relat_1(A_609))
      | ~ v1_relat_1(A_609)
      | ~ r2_hidden(C_608,k1_relat_1(A_609)) ) ),
    inference(resolution,[status(thm)],[c_2,c_7641])).

tff(c_7725,plain,(
    ! [C_610,A_611] :
      ( r2_hidden(C_610,k10_relat_1(A_611,k2_relat_1(A_611)))
      | ~ v1_relat_1(A_611)
      | ~ r2_hidden(C_610,k1_relat_1(A_611)) ) ),
    inference(resolution,[status(thm)],[c_47,c_7705])).

tff(c_10,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_3'(A_1,B_2),B_2)
      | k1_relat_1(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_73,plain,(
    ! [A_75,C_76,B_77] :
      ( r2_hidden(A_75,k1_relat_1(C_76))
      | ~ r2_hidden(A_75,k10_relat_1(C_76,B_77))
      | ~ v1_relat_1(C_76) ) ),
    inference(resolution,[status(thm)],[c_64,c_4])).

tff(c_100,plain,(
    ! [A_1,C_76,B_77] :
      ( r2_hidden('#skF_3'(A_1,k10_relat_1(C_76,B_77)),k1_relat_1(C_76))
      | ~ v1_relat_1(C_76)
      | ~ r2_hidden('#skF_1'(A_1,k10_relat_1(C_76,B_77)),k10_relat_1(C_76,B_77))
      | k1_relat_1(A_1) = k10_relat_1(C_76,B_77) ) ),
    inference(resolution,[status(thm)],[c_10,c_73])).

tff(c_7872,plain,(
    ! [A_1,A_611] :
      ( r2_hidden('#skF_3'(A_1,k10_relat_1(A_611,k2_relat_1(A_611))),k1_relat_1(A_611))
      | k1_relat_1(A_1) = k10_relat_1(A_611,k2_relat_1(A_611))
      | ~ v1_relat_1(A_611)
      | ~ r2_hidden('#skF_1'(A_1,k10_relat_1(A_611,k2_relat_1(A_611))),k1_relat_1(A_611)) ) ),
    inference(resolution,[status(thm)],[c_7725,c_100])).

tff(c_6,plain,(
    ! [A_1,B_2,D_15] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_1,B_2),D_15),A_1)
      | k1_relat_1(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_79363,plain,(
    ! [A_1779,A_1780,D_1781] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_1779,k10_relat_1(A_1780,k2_relat_1(A_1780))),D_1781),A_1779)
      | k1_relat_1(A_1779) = k10_relat_1(A_1780,k2_relat_1(A_1780))
      | ~ v1_relat_1(A_1780)
      | ~ r2_hidden('#skF_1'(A_1779,k10_relat_1(A_1780,k2_relat_1(A_1780))),k1_relat_1(A_1780)) ) ),
    inference(resolution,[status(thm)],[c_7725,c_6])).

tff(c_79972,plain,(
    ! [A_1782,A_1783] :
      ( k1_relat_1(A_1782) = k10_relat_1(A_1783,k2_relat_1(A_1783))
      | ~ v1_relat_1(A_1783)
      | ~ r2_hidden('#skF_1'(A_1782,k10_relat_1(A_1783,k2_relat_1(A_1783))),k1_relat_1(A_1783))
      | ~ r2_hidden('#skF_3'(A_1782,k10_relat_1(A_1783,k2_relat_1(A_1783))),k1_relat_1(A_1782)) ) ),
    inference(resolution,[status(thm)],[c_2,c_79363])).

tff(c_80444,plain,(
    ! [C_1788] :
      ( ~ r2_hidden('#skF_3'(C_1788,k10_relat_1(C_1788,k2_relat_1(C_1788))),k1_relat_1(C_1788))
      | ~ v1_relat_1(C_1788)
      | k10_relat_1(C_1788,k2_relat_1(C_1788)) = k1_relat_1(C_1788) ) ),
    inference(resolution,[status(thm)],[c_607,c_79972])).

tff(c_80805,plain,(
    ! [A_1789] :
      ( k10_relat_1(A_1789,k2_relat_1(A_1789)) = k1_relat_1(A_1789)
      | ~ v1_relat_1(A_1789)
      | ~ r2_hidden('#skF_1'(A_1789,k10_relat_1(A_1789,k2_relat_1(A_1789))),k1_relat_1(A_1789)) ) ),
    inference(resolution,[status(thm)],[c_7872,c_80444])).

tff(c_81166,plain,(
    ! [C_1790] :
      ( ~ v1_relat_1(C_1790)
      | k10_relat_1(C_1790,k2_relat_1(C_1790)) = k1_relat_1(C_1790) ) ),
    inference(resolution,[status(thm)],[c_607,c_80805])).

tff(c_34,plain,(
    k10_relat_1('#skF_10',k2_relat_1('#skF_10')) != k1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_82736,plain,(
    ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_81166,c_34])).

tff(c_82744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_82736])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:30:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 37.89/25.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 37.89/25.98  
% 37.89/25.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 37.89/25.99  %$ r2_hidden > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_4 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5
% 37.89/25.99  
% 37.89/25.99  %Foreground sorts:
% 37.89/25.99  
% 37.89/25.99  
% 37.89/25.99  %Background operators:
% 37.89/25.99  
% 37.89/25.99  
% 37.89/25.99  %Foreground operators:
% 37.89/25.99  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 37.89/25.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 37.89/25.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 37.89/25.99  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 37.89/25.99  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 37.89/25.99  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 37.89/25.99  tff('#skF_10', type, '#skF_10': $i).
% 37.89/25.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 37.89/25.99  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 37.89/25.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 37.89/25.99  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 37.89/25.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 37.89/25.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 37.89/25.99  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 37.89/25.99  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 37.89/25.99  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 37.89/25.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 37.89/25.99  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 37.89/25.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 37.89/25.99  
% 37.89/26.00  tff(f_57, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 37.89/26.00  tff(f_33, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 37.89/26.00  tff(f_52, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 37.89/26.00  tff(f_41, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 37.89/26.00  tff(c_36, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_57])).
% 37.89/26.00  tff(c_132, plain, (![A_87, B_88]: (r2_hidden(k4_tarski('#skF_1'(A_87, B_88), '#skF_2'(A_87, B_88)), A_87) | r2_hidden('#skF_3'(A_87, B_88), B_88) | k1_relat_1(A_87)=B_88)), inference(cnfTransformation, [status(thm)], [f_33])).
% 37.89/26.00  tff(c_4, plain, (![C_16, A_1, D_19]: (r2_hidden(C_16, k1_relat_1(A_1)) | ~r2_hidden(k4_tarski(C_16, D_19), A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 37.89/26.00  tff(c_152, plain, (![A_91, B_92]: (r2_hidden('#skF_1'(A_91, B_92), k1_relat_1(A_91)) | r2_hidden('#skF_3'(A_91, B_92), B_92) | k1_relat_1(A_91)=B_92)), inference(resolution, [status(thm)], [c_132, c_4])).
% 37.89/26.00  tff(c_64, plain, (![A_72, B_73, C_74]: (r2_hidden(k4_tarski(A_72, '#skF_9'(A_72, B_73, C_74)), C_74) | ~r2_hidden(A_72, k10_relat_1(C_74, B_73)) | ~v1_relat_1(C_74))), inference(cnfTransformation, [status(thm)], [f_52])).
% 37.89/26.00  tff(c_72, plain, (![A_72, C_74, B_73]: (r2_hidden(A_72, k1_relat_1(C_74)) | ~r2_hidden(A_72, k10_relat_1(C_74, B_73)) | ~v1_relat_1(C_74))), inference(resolution, [status(thm)], [c_64, c_4])).
% 37.89/26.00  tff(c_585, plain, (![A_144, C_145, B_146]: (r2_hidden('#skF_3'(A_144, k10_relat_1(C_145, B_146)), k1_relat_1(C_145)) | ~v1_relat_1(C_145) | r2_hidden('#skF_1'(A_144, k10_relat_1(C_145, B_146)), k1_relat_1(A_144)) | k1_relat_1(A_144)=k10_relat_1(C_145, B_146))), inference(resolution, [status(thm)], [c_152, c_72])).
% 37.89/26.00  tff(c_2, plain, (![C_16, A_1]: (r2_hidden(k4_tarski(C_16, '#skF_4'(A_1, k1_relat_1(A_1), C_16)), A_1) | ~r2_hidden(C_16, k1_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 37.89/26.00  tff(c_217, plain, (![A_97, B_98, D_99]: (r2_hidden(k4_tarski('#skF_1'(A_97, B_98), '#skF_2'(A_97, B_98)), A_97) | ~r2_hidden(k4_tarski('#skF_3'(A_97, B_98), D_99), A_97) | k1_relat_1(A_97)=B_98)), inference(cnfTransformation, [status(thm)], [f_33])).
% 37.89/26.00  tff(c_226, plain, (![A_100, B_101]: (r2_hidden(k4_tarski('#skF_1'(A_100, B_101), '#skF_2'(A_100, B_101)), A_100) | k1_relat_1(A_100)=B_101 | ~r2_hidden('#skF_3'(A_100, B_101), k1_relat_1(A_100)))), inference(resolution, [status(thm)], [c_2, c_217])).
% 37.89/26.00  tff(c_242, plain, (![A_100, B_101]: (r2_hidden('#skF_1'(A_100, B_101), k1_relat_1(A_100)) | k1_relat_1(A_100)=B_101 | ~r2_hidden('#skF_3'(A_100, B_101), k1_relat_1(A_100)))), inference(resolution, [status(thm)], [c_226, c_4])).
% 37.89/26.00  tff(c_607, plain, (![C_145, B_146]: (~v1_relat_1(C_145) | r2_hidden('#skF_1'(C_145, k10_relat_1(C_145, B_146)), k1_relat_1(C_145)) | k10_relat_1(C_145, B_146)=k1_relat_1(C_145))), inference(resolution, [status(thm)], [c_585, c_242])).
% 37.89/26.00  tff(c_40, plain, (![C_53, A_54]: (r2_hidden(k4_tarski(C_53, '#skF_4'(A_54, k1_relat_1(A_54), C_53)), A_54) | ~r2_hidden(C_53, k1_relat_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 37.89/26.00  tff(c_16, plain, (![C_35, A_20, D_38]: (r2_hidden(C_35, k2_relat_1(A_20)) | ~r2_hidden(k4_tarski(D_38, C_35), A_20))), inference(cnfTransformation, [status(thm)], [f_41])).
% 37.89/26.00  tff(c_47, plain, (![A_54, C_53]: (r2_hidden('#skF_4'(A_54, k1_relat_1(A_54), C_53), k2_relat_1(A_54)) | ~r2_hidden(C_53, k1_relat_1(A_54)))), inference(resolution, [status(thm)], [c_40, c_16])).
% 37.89/26.00  tff(c_159, plain, (![A_93, C_94, B_95, D_96]: (r2_hidden(A_93, k10_relat_1(C_94, B_95)) | ~r2_hidden(D_96, B_95) | ~r2_hidden(k4_tarski(A_93, D_96), C_94) | ~r2_hidden(D_96, k2_relat_1(C_94)) | ~v1_relat_1(C_94))), inference(cnfTransformation, [status(thm)], [f_52])).
% 37.89/26.00  tff(c_7641, plain, (![A_604, C_605, A_606, C_607]: (r2_hidden(A_604, k10_relat_1(C_605, k2_relat_1(A_606))) | ~r2_hidden(k4_tarski(A_604, '#skF_4'(A_606, k1_relat_1(A_606), C_607)), C_605) | ~r2_hidden('#skF_4'(A_606, k1_relat_1(A_606), C_607), k2_relat_1(C_605)) | ~v1_relat_1(C_605) | ~r2_hidden(C_607, k1_relat_1(A_606)))), inference(resolution, [status(thm)], [c_47, c_159])).
% 37.89/26.00  tff(c_7705, plain, (![C_608, A_609]: (r2_hidden(C_608, k10_relat_1(A_609, k2_relat_1(A_609))) | ~r2_hidden('#skF_4'(A_609, k1_relat_1(A_609), C_608), k2_relat_1(A_609)) | ~v1_relat_1(A_609) | ~r2_hidden(C_608, k1_relat_1(A_609)))), inference(resolution, [status(thm)], [c_2, c_7641])).
% 37.89/26.00  tff(c_7725, plain, (![C_610, A_611]: (r2_hidden(C_610, k10_relat_1(A_611, k2_relat_1(A_611))) | ~v1_relat_1(A_611) | ~r2_hidden(C_610, k1_relat_1(A_611)))), inference(resolution, [status(thm)], [c_47, c_7705])).
% 37.89/26.00  tff(c_10, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_3'(A_1, B_2), B_2) | k1_relat_1(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_33])).
% 37.89/26.00  tff(c_73, plain, (![A_75, C_76, B_77]: (r2_hidden(A_75, k1_relat_1(C_76)) | ~r2_hidden(A_75, k10_relat_1(C_76, B_77)) | ~v1_relat_1(C_76))), inference(resolution, [status(thm)], [c_64, c_4])).
% 37.89/26.00  tff(c_100, plain, (![A_1, C_76, B_77]: (r2_hidden('#skF_3'(A_1, k10_relat_1(C_76, B_77)), k1_relat_1(C_76)) | ~v1_relat_1(C_76) | ~r2_hidden('#skF_1'(A_1, k10_relat_1(C_76, B_77)), k10_relat_1(C_76, B_77)) | k1_relat_1(A_1)=k10_relat_1(C_76, B_77))), inference(resolution, [status(thm)], [c_10, c_73])).
% 37.89/26.00  tff(c_7872, plain, (![A_1, A_611]: (r2_hidden('#skF_3'(A_1, k10_relat_1(A_611, k2_relat_1(A_611))), k1_relat_1(A_611)) | k1_relat_1(A_1)=k10_relat_1(A_611, k2_relat_1(A_611)) | ~v1_relat_1(A_611) | ~r2_hidden('#skF_1'(A_1, k10_relat_1(A_611, k2_relat_1(A_611))), k1_relat_1(A_611)))), inference(resolution, [status(thm)], [c_7725, c_100])).
% 37.89/26.00  tff(c_6, plain, (![A_1, B_2, D_15]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | ~r2_hidden(k4_tarski('#skF_3'(A_1, B_2), D_15), A_1) | k1_relat_1(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_33])).
% 37.89/26.00  tff(c_79363, plain, (![A_1779, A_1780, D_1781]: (~r2_hidden(k4_tarski('#skF_3'(A_1779, k10_relat_1(A_1780, k2_relat_1(A_1780))), D_1781), A_1779) | k1_relat_1(A_1779)=k10_relat_1(A_1780, k2_relat_1(A_1780)) | ~v1_relat_1(A_1780) | ~r2_hidden('#skF_1'(A_1779, k10_relat_1(A_1780, k2_relat_1(A_1780))), k1_relat_1(A_1780)))), inference(resolution, [status(thm)], [c_7725, c_6])).
% 37.89/26.00  tff(c_79972, plain, (![A_1782, A_1783]: (k1_relat_1(A_1782)=k10_relat_1(A_1783, k2_relat_1(A_1783)) | ~v1_relat_1(A_1783) | ~r2_hidden('#skF_1'(A_1782, k10_relat_1(A_1783, k2_relat_1(A_1783))), k1_relat_1(A_1783)) | ~r2_hidden('#skF_3'(A_1782, k10_relat_1(A_1783, k2_relat_1(A_1783))), k1_relat_1(A_1782)))), inference(resolution, [status(thm)], [c_2, c_79363])).
% 37.89/26.00  tff(c_80444, plain, (![C_1788]: (~r2_hidden('#skF_3'(C_1788, k10_relat_1(C_1788, k2_relat_1(C_1788))), k1_relat_1(C_1788)) | ~v1_relat_1(C_1788) | k10_relat_1(C_1788, k2_relat_1(C_1788))=k1_relat_1(C_1788))), inference(resolution, [status(thm)], [c_607, c_79972])).
% 37.89/26.00  tff(c_80805, plain, (![A_1789]: (k10_relat_1(A_1789, k2_relat_1(A_1789))=k1_relat_1(A_1789) | ~v1_relat_1(A_1789) | ~r2_hidden('#skF_1'(A_1789, k10_relat_1(A_1789, k2_relat_1(A_1789))), k1_relat_1(A_1789)))), inference(resolution, [status(thm)], [c_7872, c_80444])).
% 37.89/26.00  tff(c_81166, plain, (![C_1790]: (~v1_relat_1(C_1790) | k10_relat_1(C_1790, k2_relat_1(C_1790))=k1_relat_1(C_1790))), inference(resolution, [status(thm)], [c_607, c_80805])).
% 37.89/26.00  tff(c_34, plain, (k10_relat_1('#skF_10', k2_relat_1('#skF_10'))!=k1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_57])).
% 37.89/26.00  tff(c_82736, plain, (~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_81166, c_34])).
% 37.89/26.00  tff(c_82744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_82736])).
% 37.89/26.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 37.89/26.00  
% 37.89/26.00  Inference rules
% 37.89/26.00  ----------------------
% 37.89/26.00  #Ref     : 0
% 37.89/26.00  #Sup     : 19696
% 37.89/26.00  #Fact    : 0
% 37.89/26.00  #Define  : 0
% 37.89/26.00  #Split   : 0
% 37.89/26.00  #Chain   : 0
% 37.89/26.00  #Close   : 0
% 37.89/26.00  
% 37.89/26.00  Ordering : KBO
% 37.89/26.00  
% 37.89/26.00  Simplification rules
% 37.89/26.00  ----------------------
% 37.89/26.00  #Subsume      : 813
% 37.89/26.00  #Demod        : 1
% 37.89/26.00  #Tautology    : 244
% 37.89/26.00  #SimpNegUnit  : 0
% 37.89/26.00  #BackRed      : 0
% 37.89/26.00  
% 37.89/26.00  #Partial instantiations: 0
% 37.89/26.00  #Strategies tried      : 1
% 37.89/26.00  
% 37.89/26.00  Timing (in seconds)
% 37.89/26.00  ----------------------
% 37.89/26.00  Preprocessing        : 0.29
% 37.89/26.00  Parsing              : 0.15
% 37.89/26.00  CNF conversion       : 0.03
% 37.89/26.00  Main loop            : 24.95
% 37.89/26.00  Inferencing          : 3.37
% 37.89/26.00  Reduction            : 2.44
% 38.01/26.00  Demodulation         : 1.54
% 38.01/26.00  BG Simplification    : 0.50
% 38.01/26.00  Subsumption          : 17.30
% 38.01/26.00  Abstraction          : 0.88
% 38.01/26.00  MUC search           : 0.00
% 38.01/26.01  Cooper               : 0.00
% 38.01/26.01  Total                : 25.28
% 38.01/26.01  Index Insertion      : 0.00
% 38.01/26.01  Index Deletion       : 0.00
% 38.01/26.01  Index Matching       : 0.00
% 38.01/26.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
