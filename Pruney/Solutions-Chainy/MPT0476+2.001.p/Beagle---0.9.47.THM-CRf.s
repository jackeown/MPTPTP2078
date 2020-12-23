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
% DateTime   : Thu Dec  3 09:59:30 EST 2020

% Result     : Theorem 47.98s
% Output     : CNFRefutation 48.12s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 217 expanded)
%              Number of leaves         :   28 (  86 expanded)
%              Depth                    :   14
%              Number of atoms          :  110 ( 461 expanded)
%              Number of equality atoms :   44 ( 156 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_12 > #skF_3 > #skF_14 > #skF_13 > #skF_10 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_54,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k6_relat_1(A)
      <=> ! [C,D] :
            ( r2_hidden(k4_tarski(C,D),B)
          <=> ( r2_hidden(C,A)
              & C = D ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( k1_relat_1(k6_relat_1(A)) = A
        & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_87161,plain,(
    ! [A_1083,B_1084] :
      ( r2_hidden(k4_tarski('#skF_5'(A_1083,B_1084),'#skF_6'(A_1083,B_1084)),A_1083)
      | r2_hidden('#skF_7'(A_1083,B_1084),B_1084)
      | k1_relat_1(A_1083) = B_1084 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_44,plain,(
    ! [A_47] : v1_relat_1(k6_relat_1(A_47)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    ! [C_7,A_1,D_8] :
      ( r2_hidden(C_7,A_1)
      | ~ r2_hidden(k4_tarski(C_7,D_8),k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_48,plain,(
    ! [C_7,A_1,D_8] :
      ( r2_hidden(C_7,A_1)
      | ~ r2_hidden(k4_tarski(C_7,D_8),k6_relat_1(A_1)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_18])).

tff(c_87215,plain,(
    ! [A_1,B_1084] :
      ( r2_hidden('#skF_5'(k6_relat_1(A_1),B_1084),A_1)
      | r2_hidden('#skF_7'(k6_relat_1(A_1),B_1084),B_1084)
      | k1_relat_1(k6_relat_1(A_1)) = B_1084 ) ),
    inference(resolution,[status(thm)],[c_87161,c_48])).

tff(c_14,plain,(
    ! [D_8,A_1] :
      ( r2_hidden(k4_tarski(D_8,D_8),k6_relat_1(A_1))
      | ~ r2_hidden(D_8,A_1)
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_52,plain,(
    ! [D_8,A_1] :
      ( r2_hidden(k4_tarski(D_8,D_8),k6_relat_1(A_1))
      | ~ r2_hidden(D_8,A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_14])).

tff(c_88500,plain,(
    ! [A_1125,B_1126,D_1127] :
      ( r2_hidden(k4_tarski('#skF_5'(A_1125,B_1126),'#skF_6'(A_1125,B_1126)),A_1125)
      | ~ r2_hidden(k4_tarski('#skF_7'(A_1125,B_1126),D_1127),A_1125)
      | k1_relat_1(A_1125) = B_1126 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_125498,plain,(
    ! [A_1592,B_1593] :
      ( r2_hidden(k4_tarski('#skF_5'(k6_relat_1(A_1592),B_1593),'#skF_6'(k6_relat_1(A_1592),B_1593)),k6_relat_1(A_1592))
      | k1_relat_1(k6_relat_1(A_1592)) = B_1593
      | ~ r2_hidden('#skF_7'(k6_relat_1(A_1592),B_1593),A_1592) ) ),
    inference(resolution,[status(thm)],[c_52,c_88500])).

tff(c_141035,plain,(
    ! [A_1711,B_1712] :
      ( r2_hidden('#skF_5'(k6_relat_1(A_1711),B_1712),A_1711)
      | k1_relat_1(k6_relat_1(A_1711)) = B_1712
      | ~ r2_hidden('#skF_7'(k6_relat_1(A_1711),B_1712),A_1711) ) ),
    inference(resolution,[status(thm)],[c_125498,c_48])).

tff(c_141715,plain,(
    ! [B_1084] :
      ( r2_hidden('#skF_5'(k6_relat_1(B_1084),B_1084),B_1084)
      | k1_relat_1(k6_relat_1(B_1084)) = B_1084 ) ),
    inference(resolution,[status(thm)],[c_87215,c_141035])).

tff(c_28,plain,(
    ! [A_9,B_10] :
      ( ~ r2_hidden('#skF_5'(A_9,B_10),B_10)
      | r2_hidden('#skF_7'(A_9,B_10),B_10)
      | k1_relat_1(A_9) = B_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_141779,plain,(
    ! [B_1713] :
      ( r2_hidden('#skF_5'(k6_relat_1(B_1713),B_1713),B_1713)
      | k1_relat_1(k6_relat_1(B_1713)) = B_1713 ) ),
    inference(resolution,[status(thm)],[c_87215,c_141035])).

tff(c_24,plain,(
    ! [A_9,B_10,D_23] :
      ( ~ r2_hidden('#skF_5'(A_9,B_10),B_10)
      | ~ r2_hidden(k4_tarski('#skF_7'(A_9,B_10),D_23),A_9)
      | k1_relat_1(A_9) = B_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_141806,plain,(
    ! [B_1714,D_1715] :
      ( ~ r2_hidden(k4_tarski('#skF_7'(k6_relat_1(B_1714),B_1714),D_1715),k6_relat_1(B_1714))
      | k1_relat_1(k6_relat_1(B_1714)) = B_1714 ) ),
    inference(resolution,[status(thm)],[c_141779,c_24])).

tff(c_141822,plain,(
    ! [A_1716] :
      ( k1_relat_1(k6_relat_1(A_1716)) = A_1716
      | ~ r2_hidden('#skF_7'(k6_relat_1(A_1716),A_1716),A_1716) ) ),
    inference(resolution,[status(thm)],[c_52,c_141806])).

tff(c_142586,plain,(
    ! [B_1718] :
      ( ~ r2_hidden('#skF_5'(k6_relat_1(B_1718),B_1718),B_1718)
      | k1_relat_1(k6_relat_1(B_1718)) = B_1718 ) ),
    inference(resolution,[status(thm)],[c_28,c_141822])).

tff(c_143168,plain,(
    ! [B_1084] : k1_relat_1(k6_relat_1(B_1084)) = B_1084 ),
    inference(resolution,[status(thm)],[c_141715,c_142586])).

tff(c_46,plain,
    ( k1_relat_1(k6_relat_1('#skF_14')) != '#skF_14'
    | k2_relat_1(k6_relat_1('#skF_13')) != '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_54,plain,(
    k2_relat_1(k6_relat_1('#skF_13')) != '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_1176,plain,(
    ! [A_147,B_148] :
      ( r2_hidden(k4_tarski('#skF_10'(A_147,B_148),'#skF_9'(A_147,B_148)),A_147)
      | r2_hidden('#skF_11'(A_147,B_148),B_148)
      | k2_relat_1(A_147) = B_148 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [D_8,C_7,A_1] :
      ( D_8 = C_7
      | ~ r2_hidden(k4_tarski(C_7,D_8),k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_50,plain,(
    ! [D_8,C_7,A_1] :
      ( D_8 = C_7
      | ~ r2_hidden(k4_tarski(C_7,D_8),k6_relat_1(A_1)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_16])).

tff(c_1223,plain,(
    ! [A_1,B_148] :
      ( '#skF_10'(k6_relat_1(A_1),B_148) = '#skF_9'(k6_relat_1(A_1),B_148)
      | r2_hidden('#skF_11'(k6_relat_1(A_1),B_148),B_148)
      | k2_relat_1(k6_relat_1(A_1)) = B_148 ) ),
    inference(resolution,[status(thm)],[c_1176,c_50])).

tff(c_1852,plain,(
    ! [A_170,B_171,D_172] :
      ( r2_hidden(k4_tarski('#skF_10'(A_170,B_171),'#skF_9'(A_170,B_171)),A_170)
      | ~ r2_hidden(k4_tarski(D_172,'#skF_11'(A_170,B_171)),A_170)
      | k2_relat_1(A_170) = B_171 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_50892,plain,(
    ! [A_720,B_721] :
      ( r2_hidden(k4_tarski('#skF_10'(k6_relat_1(A_720),B_721),'#skF_9'(k6_relat_1(A_720),B_721)),k6_relat_1(A_720))
      | k2_relat_1(k6_relat_1(A_720)) = B_721
      | ~ r2_hidden('#skF_11'(k6_relat_1(A_720),B_721),A_720) ) ),
    inference(resolution,[status(thm)],[c_52,c_1852])).

tff(c_84506,plain,(
    ! [A_950,B_951] :
      ( '#skF_10'(k6_relat_1(A_950),B_951) = '#skF_9'(k6_relat_1(A_950),B_951)
      | k2_relat_1(k6_relat_1(A_950)) = B_951
      | ~ r2_hidden('#skF_11'(k6_relat_1(A_950),B_951),A_950) ) ),
    inference(resolution,[status(thm)],[c_50892,c_50])).

tff(c_84801,plain,(
    ! [B_952] :
      ( '#skF_10'(k6_relat_1(B_952),B_952) = '#skF_9'(k6_relat_1(B_952),B_952)
      | k2_relat_1(k6_relat_1(B_952)) = B_952 ) ),
    inference(resolution,[status(thm)],[c_1223,c_84506])).

tff(c_85052,plain,(
    '#skF_10'(k6_relat_1('#skF_13'),'#skF_13') = '#skF_9'(k6_relat_1('#skF_13'),'#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_84801,c_54])).

tff(c_1221,plain,(
    ! [A_1,B_148] :
      ( r2_hidden('#skF_10'(k6_relat_1(A_1),B_148),A_1)
      | r2_hidden('#skF_11'(k6_relat_1(A_1),B_148),B_148)
      | k2_relat_1(k6_relat_1(A_1)) = B_148 ) ),
    inference(resolution,[status(thm)],[c_1176,c_48])).

tff(c_75072,plain,(
    ! [A_868,B_869] :
      ( r2_hidden('#skF_10'(k6_relat_1(A_868),B_869),A_868)
      | k2_relat_1(k6_relat_1(A_868)) = B_869
      | ~ r2_hidden('#skF_11'(k6_relat_1(A_868),B_869),A_868) ) ),
    inference(resolution,[status(thm)],[c_50892,c_48])).

tff(c_75963,plain,(
    ! [B_148] :
      ( r2_hidden('#skF_10'(k6_relat_1(B_148),B_148),B_148)
      | k2_relat_1(k6_relat_1(B_148)) = B_148 ) ),
    inference(resolution,[status(thm)],[c_1221,c_75072])).

tff(c_85059,plain,
    ( r2_hidden('#skF_9'(k6_relat_1('#skF_13'),'#skF_13'),'#skF_13')
    | k2_relat_1(k6_relat_1('#skF_13')) = '#skF_13' ),
    inference(superposition,[status(thm),theory(equality)],[c_85052,c_75963])).

tff(c_85076,plain,(
    r2_hidden('#skF_9'(k6_relat_1('#skF_13'),'#skF_13'),'#skF_13') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_85059])).

tff(c_40,plain,(
    ! [A_28,B_29] :
      ( ~ r2_hidden('#skF_9'(A_28,B_29),B_29)
      | r2_hidden('#skF_11'(A_28,B_29),B_29)
      | k2_relat_1(A_28) = B_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_36,plain,(
    ! [A_28,B_29,D_42] :
      ( ~ r2_hidden('#skF_9'(A_28,B_29),B_29)
      | ~ r2_hidden(k4_tarski(D_42,'#skF_11'(A_28,B_29)),A_28)
      | k2_relat_1(A_28) = B_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_85084,plain,(
    ! [D_42] :
      ( ~ r2_hidden(k4_tarski(D_42,'#skF_11'(k6_relat_1('#skF_13'),'#skF_13')),k6_relat_1('#skF_13'))
      | k2_relat_1(k6_relat_1('#skF_13')) = '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_85076,c_36])).

tff(c_85088,plain,(
    ! [D_953] : ~ r2_hidden(k4_tarski(D_953,'#skF_11'(k6_relat_1('#skF_13'),'#skF_13')),k6_relat_1('#skF_13')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_85084])).

tff(c_85103,plain,(
    ~ r2_hidden('#skF_11'(k6_relat_1('#skF_13'),'#skF_13'),'#skF_13') ),
    inference(resolution,[status(thm)],[c_52,c_85088])).

tff(c_85114,plain,
    ( ~ r2_hidden('#skF_9'(k6_relat_1('#skF_13'),'#skF_13'),'#skF_13')
    | k2_relat_1(k6_relat_1('#skF_13')) = '#skF_13' ),
    inference(resolution,[status(thm)],[c_40,c_85103])).

tff(c_85123,plain,(
    k2_relat_1(k6_relat_1('#skF_13')) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85076,c_85114])).

tff(c_85125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_85123])).

tff(c_85126,plain,(
    k1_relat_1(k6_relat_1('#skF_14')) != '#skF_14' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_143531,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_143168,c_85126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:59:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 47.98/29.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.98/29.83  
% 47.98/29.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.98/29.83  %$ r2_hidden > v1_relat_1 > k4_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_12 > #skF_3 > #skF_14 > #skF_13 > #skF_10 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_4
% 47.98/29.83  
% 47.98/29.83  %Foreground sorts:
% 47.98/29.83  
% 47.98/29.83  
% 47.98/29.83  %Background operators:
% 47.98/29.83  
% 47.98/29.83  
% 47.98/29.83  %Foreground operators:
% 47.98/29.83  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 47.98/29.83  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 47.98/29.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 47.98/29.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 47.98/29.83  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 47.98/29.83  tff('#skF_12', type, '#skF_12': ($i * $i * $i) > $i).
% 47.98/29.83  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 47.98/29.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 47.98/29.83  tff('#skF_14', type, '#skF_14': $i).
% 47.98/29.83  tff('#skF_13', type, '#skF_13': $i).
% 47.98/29.83  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 47.98/29.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 47.98/29.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 47.98/29.83  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 47.98/29.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 47.98/29.83  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 47.98/29.83  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 47.98/29.83  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 47.98/29.83  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 47.98/29.83  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 47.98/29.83  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 47.98/29.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 47.98/29.83  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 47.98/29.83  
% 48.12/29.84  tff(f_44, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 48.12/29.84  tff(f_54, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 48.12/29.84  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => ((B = k6_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> (r2_hidden(C, A) & (C = D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_relat_1)).
% 48.12/29.84  tff(f_59, negated_conjecture, ~(![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 48.12/29.84  tff(f_52, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 48.12/29.84  tff(c_87161, plain, (![A_1083, B_1084]: (r2_hidden(k4_tarski('#skF_5'(A_1083, B_1084), '#skF_6'(A_1083, B_1084)), A_1083) | r2_hidden('#skF_7'(A_1083, B_1084), B_1084) | k1_relat_1(A_1083)=B_1084)), inference(cnfTransformation, [status(thm)], [f_44])).
% 48.12/29.84  tff(c_44, plain, (![A_47]: (v1_relat_1(k6_relat_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 48.12/29.84  tff(c_18, plain, (![C_7, A_1, D_8]: (r2_hidden(C_7, A_1) | ~r2_hidden(k4_tarski(C_7, D_8), k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 48.12/29.84  tff(c_48, plain, (![C_7, A_1, D_8]: (r2_hidden(C_7, A_1) | ~r2_hidden(k4_tarski(C_7, D_8), k6_relat_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_18])).
% 48.12/29.84  tff(c_87215, plain, (![A_1, B_1084]: (r2_hidden('#skF_5'(k6_relat_1(A_1), B_1084), A_1) | r2_hidden('#skF_7'(k6_relat_1(A_1), B_1084), B_1084) | k1_relat_1(k6_relat_1(A_1))=B_1084)), inference(resolution, [status(thm)], [c_87161, c_48])).
% 48.12/29.84  tff(c_14, plain, (![D_8, A_1]: (r2_hidden(k4_tarski(D_8, D_8), k6_relat_1(A_1)) | ~r2_hidden(D_8, A_1) | ~v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 48.12/29.84  tff(c_52, plain, (![D_8, A_1]: (r2_hidden(k4_tarski(D_8, D_8), k6_relat_1(A_1)) | ~r2_hidden(D_8, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_14])).
% 48.12/29.84  tff(c_88500, plain, (![A_1125, B_1126, D_1127]: (r2_hidden(k4_tarski('#skF_5'(A_1125, B_1126), '#skF_6'(A_1125, B_1126)), A_1125) | ~r2_hidden(k4_tarski('#skF_7'(A_1125, B_1126), D_1127), A_1125) | k1_relat_1(A_1125)=B_1126)), inference(cnfTransformation, [status(thm)], [f_44])).
% 48.12/29.84  tff(c_125498, plain, (![A_1592, B_1593]: (r2_hidden(k4_tarski('#skF_5'(k6_relat_1(A_1592), B_1593), '#skF_6'(k6_relat_1(A_1592), B_1593)), k6_relat_1(A_1592)) | k1_relat_1(k6_relat_1(A_1592))=B_1593 | ~r2_hidden('#skF_7'(k6_relat_1(A_1592), B_1593), A_1592))), inference(resolution, [status(thm)], [c_52, c_88500])).
% 48.12/29.84  tff(c_141035, plain, (![A_1711, B_1712]: (r2_hidden('#skF_5'(k6_relat_1(A_1711), B_1712), A_1711) | k1_relat_1(k6_relat_1(A_1711))=B_1712 | ~r2_hidden('#skF_7'(k6_relat_1(A_1711), B_1712), A_1711))), inference(resolution, [status(thm)], [c_125498, c_48])).
% 48.12/29.84  tff(c_141715, plain, (![B_1084]: (r2_hidden('#skF_5'(k6_relat_1(B_1084), B_1084), B_1084) | k1_relat_1(k6_relat_1(B_1084))=B_1084)), inference(resolution, [status(thm)], [c_87215, c_141035])).
% 48.12/29.84  tff(c_28, plain, (![A_9, B_10]: (~r2_hidden('#skF_5'(A_9, B_10), B_10) | r2_hidden('#skF_7'(A_9, B_10), B_10) | k1_relat_1(A_9)=B_10)), inference(cnfTransformation, [status(thm)], [f_44])).
% 48.12/29.84  tff(c_141779, plain, (![B_1713]: (r2_hidden('#skF_5'(k6_relat_1(B_1713), B_1713), B_1713) | k1_relat_1(k6_relat_1(B_1713))=B_1713)), inference(resolution, [status(thm)], [c_87215, c_141035])).
% 48.12/29.84  tff(c_24, plain, (![A_9, B_10, D_23]: (~r2_hidden('#skF_5'(A_9, B_10), B_10) | ~r2_hidden(k4_tarski('#skF_7'(A_9, B_10), D_23), A_9) | k1_relat_1(A_9)=B_10)), inference(cnfTransformation, [status(thm)], [f_44])).
% 48.12/29.84  tff(c_141806, plain, (![B_1714, D_1715]: (~r2_hidden(k4_tarski('#skF_7'(k6_relat_1(B_1714), B_1714), D_1715), k6_relat_1(B_1714)) | k1_relat_1(k6_relat_1(B_1714))=B_1714)), inference(resolution, [status(thm)], [c_141779, c_24])).
% 48.12/29.84  tff(c_141822, plain, (![A_1716]: (k1_relat_1(k6_relat_1(A_1716))=A_1716 | ~r2_hidden('#skF_7'(k6_relat_1(A_1716), A_1716), A_1716))), inference(resolution, [status(thm)], [c_52, c_141806])).
% 48.12/29.84  tff(c_142586, plain, (![B_1718]: (~r2_hidden('#skF_5'(k6_relat_1(B_1718), B_1718), B_1718) | k1_relat_1(k6_relat_1(B_1718))=B_1718)), inference(resolution, [status(thm)], [c_28, c_141822])).
% 48.12/29.84  tff(c_143168, plain, (![B_1084]: (k1_relat_1(k6_relat_1(B_1084))=B_1084)), inference(resolution, [status(thm)], [c_141715, c_142586])).
% 48.12/29.84  tff(c_46, plain, (k1_relat_1(k6_relat_1('#skF_14'))!='#skF_14' | k2_relat_1(k6_relat_1('#skF_13'))!='#skF_13'), inference(cnfTransformation, [status(thm)], [f_59])).
% 48.12/29.84  tff(c_54, plain, (k2_relat_1(k6_relat_1('#skF_13'))!='#skF_13'), inference(splitLeft, [status(thm)], [c_46])).
% 48.12/29.84  tff(c_1176, plain, (![A_147, B_148]: (r2_hidden(k4_tarski('#skF_10'(A_147, B_148), '#skF_9'(A_147, B_148)), A_147) | r2_hidden('#skF_11'(A_147, B_148), B_148) | k2_relat_1(A_147)=B_148)), inference(cnfTransformation, [status(thm)], [f_52])).
% 48.12/29.84  tff(c_16, plain, (![D_8, C_7, A_1]: (D_8=C_7 | ~r2_hidden(k4_tarski(C_7, D_8), k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 48.12/29.84  tff(c_50, plain, (![D_8, C_7, A_1]: (D_8=C_7 | ~r2_hidden(k4_tarski(C_7, D_8), k6_relat_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_16])).
% 48.12/29.84  tff(c_1223, plain, (![A_1, B_148]: ('#skF_10'(k6_relat_1(A_1), B_148)='#skF_9'(k6_relat_1(A_1), B_148) | r2_hidden('#skF_11'(k6_relat_1(A_1), B_148), B_148) | k2_relat_1(k6_relat_1(A_1))=B_148)), inference(resolution, [status(thm)], [c_1176, c_50])).
% 48.12/29.84  tff(c_1852, plain, (![A_170, B_171, D_172]: (r2_hidden(k4_tarski('#skF_10'(A_170, B_171), '#skF_9'(A_170, B_171)), A_170) | ~r2_hidden(k4_tarski(D_172, '#skF_11'(A_170, B_171)), A_170) | k2_relat_1(A_170)=B_171)), inference(cnfTransformation, [status(thm)], [f_52])).
% 48.12/29.84  tff(c_50892, plain, (![A_720, B_721]: (r2_hidden(k4_tarski('#skF_10'(k6_relat_1(A_720), B_721), '#skF_9'(k6_relat_1(A_720), B_721)), k6_relat_1(A_720)) | k2_relat_1(k6_relat_1(A_720))=B_721 | ~r2_hidden('#skF_11'(k6_relat_1(A_720), B_721), A_720))), inference(resolution, [status(thm)], [c_52, c_1852])).
% 48.12/29.84  tff(c_84506, plain, (![A_950, B_951]: ('#skF_10'(k6_relat_1(A_950), B_951)='#skF_9'(k6_relat_1(A_950), B_951) | k2_relat_1(k6_relat_1(A_950))=B_951 | ~r2_hidden('#skF_11'(k6_relat_1(A_950), B_951), A_950))), inference(resolution, [status(thm)], [c_50892, c_50])).
% 48.12/29.84  tff(c_84801, plain, (![B_952]: ('#skF_10'(k6_relat_1(B_952), B_952)='#skF_9'(k6_relat_1(B_952), B_952) | k2_relat_1(k6_relat_1(B_952))=B_952)), inference(resolution, [status(thm)], [c_1223, c_84506])).
% 48.12/29.84  tff(c_85052, plain, ('#skF_10'(k6_relat_1('#skF_13'), '#skF_13')='#skF_9'(k6_relat_1('#skF_13'), '#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_84801, c_54])).
% 48.12/29.84  tff(c_1221, plain, (![A_1, B_148]: (r2_hidden('#skF_10'(k6_relat_1(A_1), B_148), A_1) | r2_hidden('#skF_11'(k6_relat_1(A_1), B_148), B_148) | k2_relat_1(k6_relat_1(A_1))=B_148)), inference(resolution, [status(thm)], [c_1176, c_48])).
% 48.12/29.84  tff(c_75072, plain, (![A_868, B_869]: (r2_hidden('#skF_10'(k6_relat_1(A_868), B_869), A_868) | k2_relat_1(k6_relat_1(A_868))=B_869 | ~r2_hidden('#skF_11'(k6_relat_1(A_868), B_869), A_868))), inference(resolution, [status(thm)], [c_50892, c_48])).
% 48.12/29.84  tff(c_75963, plain, (![B_148]: (r2_hidden('#skF_10'(k6_relat_1(B_148), B_148), B_148) | k2_relat_1(k6_relat_1(B_148))=B_148)), inference(resolution, [status(thm)], [c_1221, c_75072])).
% 48.12/29.84  tff(c_85059, plain, (r2_hidden('#skF_9'(k6_relat_1('#skF_13'), '#skF_13'), '#skF_13') | k2_relat_1(k6_relat_1('#skF_13'))='#skF_13'), inference(superposition, [status(thm), theory('equality')], [c_85052, c_75963])).
% 48.12/29.84  tff(c_85076, plain, (r2_hidden('#skF_9'(k6_relat_1('#skF_13'), '#skF_13'), '#skF_13')), inference(negUnitSimplification, [status(thm)], [c_54, c_85059])).
% 48.12/29.84  tff(c_40, plain, (![A_28, B_29]: (~r2_hidden('#skF_9'(A_28, B_29), B_29) | r2_hidden('#skF_11'(A_28, B_29), B_29) | k2_relat_1(A_28)=B_29)), inference(cnfTransformation, [status(thm)], [f_52])).
% 48.12/29.84  tff(c_36, plain, (![A_28, B_29, D_42]: (~r2_hidden('#skF_9'(A_28, B_29), B_29) | ~r2_hidden(k4_tarski(D_42, '#skF_11'(A_28, B_29)), A_28) | k2_relat_1(A_28)=B_29)), inference(cnfTransformation, [status(thm)], [f_52])).
% 48.12/29.84  tff(c_85084, plain, (![D_42]: (~r2_hidden(k4_tarski(D_42, '#skF_11'(k6_relat_1('#skF_13'), '#skF_13')), k6_relat_1('#skF_13')) | k2_relat_1(k6_relat_1('#skF_13'))='#skF_13')), inference(resolution, [status(thm)], [c_85076, c_36])).
% 48.12/29.84  tff(c_85088, plain, (![D_953]: (~r2_hidden(k4_tarski(D_953, '#skF_11'(k6_relat_1('#skF_13'), '#skF_13')), k6_relat_1('#skF_13')))), inference(negUnitSimplification, [status(thm)], [c_54, c_85084])).
% 48.12/29.84  tff(c_85103, plain, (~r2_hidden('#skF_11'(k6_relat_1('#skF_13'), '#skF_13'), '#skF_13')), inference(resolution, [status(thm)], [c_52, c_85088])).
% 48.12/29.84  tff(c_85114, plain, (~r2_hidden('#skF_9'(k6_relat_1('#skF_13'), '#skF_13'), '#skF_13') | k2_relat_1(k6_relat_1('#skF_13'))='#skF_13'), inference(resolution, [status(thm)], [c_40, c_85103])).
% 48.12/29.84  tff(c_85123, plain, (k2_relat_1(k6_relat_1('#skF_13'))='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_85076, c_85114])).
% 48.12/29.84  tff(c_85125, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_85123])).
% 48.12/29.84  tff(c_85126, plain, (k1_relat_1(k6_relat_1('#skF_14'))!='#skF_14'), inference(splitRight, [status(thm)], [c_46])).
% 48.12/29.84  tff(c_143531, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_143168, c_85126])).
% 48.12/29.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 48.12/29.84  
% 48.12/29.84  Inference rules
% 48.12/29.84  ----------------------
% 48.12/29.84  #Ref     : 0
% 48.12/29.84  #Sup     : 34683
% 48.12/29.84  #Fact    : 0
% 48.12/29.84  #Define  : 0
% 48.12/29.84  #Split   : 3
% 48.12/29.84  #Chain   : 0
% 48.15/29.84  #Close   : 0
% 48.15/29.84  
% 48.15/29.84  Ordering : KBO
% 48.15/29.84  
% 48.15/29.84  Simplification rules
% 48.15/29.84  ----------------------
% 48.15/29.84  #Subsume      : 783
% 48.15/29.84  #Demod        : 876
% 48.15/29.84  #Tautology    : 238
% 48.15/29.84  #SimpNegUnit  : 9
% 48.15/29.84  #BackRed      : 375
% 48.15/29.84  
% 48.15/29.84  #Partial instantiations: 0
% 48.15/29.84  #Strategies tried      : 1
% 48.15/29.84  
% 48.15/29.84  Timing (in seconds)
% 48.15/29.84  ----------------------
% 48.15/29.85  Preprocessing        : 0.29
% 48.15/29.85  Parsing              : 0.14
% 48.15/29.85  CNF conversion       : 0.02
% 48.15/29.85  Main loop            : 28.79
% 48.15/29.85  Inferencing          : 2.89
% 48.15/29.85  Reduction            : 3.06
% 48.15/29.85  Demodulation         : 1.95
% 48.15/29.85  BG Simplification    : 0.70
% 48.15/29.85  Subsumption          : 20.32
% 48.15/29.85  Abstraction          : 0.98
% 48.15/29.85  MUC search           : 0.00
% 48.15/29.85  Cooper               : 0.00
% 48.15/29.85  Total                : 29.11
% 48.15/29.85  Index Insertion      : 0.00
% 48.15/29.85  Index Deletion       : 0.00
% 48.15/29.85  Index Matching       : 0.00
% 48.15/29.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
