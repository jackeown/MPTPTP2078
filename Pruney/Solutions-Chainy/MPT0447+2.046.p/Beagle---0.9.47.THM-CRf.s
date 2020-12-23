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
% DateTime   : Thu Dec  3 09:58:34 EST 2020

% Result     : Theorem 4.76s
% Output     : CNFRefutation 5.10s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 180 expanded)
%              Number of leaves         :   31 (  76 expanded)
%              Depth                    :    8
%              Number of atoms          :  117 ( 398 expanded)
%              Number of equality atoms :    4 (  16 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_11 > #skF_3 > #skF_10 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_4

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

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_46,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    ! [C_65,B_66,A_67] :
      ( r2_hidden(C_65,B_66)
      | ~ r2_hidden(C_65,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_79,plain,(
    ! [A_1,B_2,B_66] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_66)
      | ~ r1_tarski(A_1,B_66)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_76])).

tff(c_87,plain,(
    ! [A_80,C_81] :
      ( r2_hidden(k4_tarski('#skF_9'(A_80,k2_relat_1(A_80),C_81),C_81),A_80)
      | ~ r2_hidden(C_81,k2_relat_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_38,plain,(
    ! [B_51,C_52,A_50] :
      ( r2_hidden(B_51,k3_relat_1(C_52))
      | ~ r2_hidden(k4_tarski(A_50,B_51),C_52)
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_107,plain,(
    ! [C_82,A_83] :
      ( r2_hidden(C_82,k3_relat_1(A_83))
      | ~ v1_relat_1(A_83)
      | ~ r2_hidden(C_82,k2_relat_1(A_83)) ) ),
    inference(resolution,[status(thm)],[c_87,c_38])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_435,plain,(
    ! [A_128,A_129] :
      ( r1_tarski(A_128,k3_relat_1(A_129))
      | ~ v1_relat_1(A_129)
      | ~ r2_hidden('#skF_1'(A_128,k3_relat_1(A_129)),k2_relat_1(A_129)) ) ),
    inference(resolution,[status(thm)],[c_107,c_4])).

tff(c_454,plain,(
    ! [A_129,A_1] :
      ( ~ v1_relat_1(A_129)
      | ~ r1_tarski(A_1,k2_relat_1(A_129))
      | r1_tarski(A_1,k3_relat_1(A_129)) ) ),
    inference(resolution,[status(thm)],[c_79,c_435])).

tff(c_161,plain,(
    ! [C_93,A_94] :
      ( r2_hidden(k4_tarski(C_93,'#skF_5'(A_94,k1_relat_1(A_94),C_93)),A_94)
      | ~ r2_hidden(C_93,k1_relat_1(A_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_40,plain,(
    ! [A_50,C_52,B_51] :
      ( r2_hidden(A_50,k3_relat_1(C_52))
      | ~ r2_hidden(k4_tarski(A_50,B_51),C_52)
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_181,plain,(
    ! [C_95,A_96] :
      ( r2_hidden(C_95,k3_relat_1(A_96))
      | ~ v1_relat_1(A_96)
      | ~ r2_hidden(C_95,k1_relat_1(A_96)) ) ),
    inference(resolution,[status(thm)],[c_161,c_40])).

tff(c_292,plain,(
    ! [A_107,A_108] :
      ( r1_tarski(A_107,k3_relat_1(A_108))
      | ~ v1_relat_1(A_108)
      | ~ r2_hidden('#skF_1'(A_107,k3_relat_1(A_108)),k1_relat_1(A_108)) ) ),
    inference(resolution,[status(thm)],[c_181,c_4])).

tff(c_301,plain,(
    ! [A_108,A_1] :
      ( ~ v1_relat_1(A_108)
      | ~ r1_tarski(A_1,k1_relat_1(A_108))
      | r1_tarski(A_1,k3_relat_1(A_108)) ) ),
    inference(resolution,[status(thm)],[c_79,c_292])).

tff(c_48,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    ! [A_49] :
      ( k2_xboole_0(k1_relat_1(A_49),k2_relat_1(A_49)) = k3_relat_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_82,plain,(
    ! [A_74,C_75,B_76] :
      ( r1_tarski(k2_xboole_0(A_74,C_75),B_76)
      | ~ r1_tarski(C_75,B_76)
      | ~ r1_tarski(A_74,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_760,plain,(
    ! [A_155,B_156] :
      ( r1_tarski(k3_relat_1(A_155),B_156)
      | ~ r1_tarski(k2_relat_1(A_155),B_156)
      | ~ r1_tarski(k1_relat_1(A_155),B_156)
      | ~ v1_relat_1(A_155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_82])).

tff(c_42,plain,(
    ~ r1_tarski(k3_relat_1('#skF_10'),k3_relat_1('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_773,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_10'),k3_relat_1('#skF_11'))
    | ~ r1_tarski(k1_relat_1('#skF_10'),k3_relat_1('#skF_11'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_760,c_42])).

tff(c_784,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_10'),k3_relat_1('#skF_11'))
    | ~ r1_tarski(k1_relat_1('#skF_10'),k3_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_773])).

tff(c_785,plain,(
    ~ r1_tarski(k1_relat_1('#skF_10'),k3_relat_1('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_784])).

tff(c_791,plain,
    ( ~ v1_relat_1('#skF_11')
    | ~ r1_tarski(k1_relat_1('#skF_10'),k1_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_301,c_785])).

tff(c_797,plain,(
    ~ r1_tarski(k1_relat_1('#skF_10'),k1_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_791])).

tff(c_44,plain,(
    r1_tarski('#skF_10','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2087,plain,(
    ! [C_227,A_228,B_229] :
      ( r2_hidden(k4_tarski(C_227,'#skF_5'(A_228,k1_relat_1(A_228),C_227)),B_229)
      | ~ r1_tarski(A_228,B_229)
      | ~ r2_hidden(C_227,k1_relat_1(A_228)) ) ),
    inference(resolution,[status(thm)],[c_161,c_2])).

tff(c_14,plain,(
    ! [C_26,A_11,D_29] :
      ( r2_hidden(C_26,k1_relat_1(A_11))
      | ~ r2_hidden(k4_tarski(C_26,D_29),A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2165,plain,(
    ! [C_230,B_231,A_232] :
      ( r2_hidden(C_230,k1_relat_1(B_231))
      | ~ r1_tarski(A_232,B_231)
      | ~ r2_hidden(C_230,k1_relat_1(A_232)) ) ),
    inference(resolution,[status(thm)],[c_2087,c_14])).

tff(c_2205,plain,(
    ! [C_233] :
      ( r2_hidden(C_233,k1_relat_1('#skF_11'))
      | ~ r2_hidden(C_233,k1_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_44,c_2165])).

tff(c_2497,plain,(
    ! [A_240] :
      ( r1_tarski(A_240,k1_relat_1('#skF_11'))
      | ~ r2_hidden('#skF_1'(A_240,k1_relat_1('#skF_11')),k1_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_2205,c_4])).

tff(c_2509,plain,(
    r1_tarski(k1_relat_1('#skF_10'),k1_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_6,c_2497])).

tff(c_2515,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_797,c_797,c_2509])).

tff(c_2516,plain,(
    ~ r1_tarski(k2_relat_1('#skF_10'),k3_relat_1('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_784])).

tff(c_2520,plain,
    ( ~ v1_relat_1('#skF_11')
    | ~ r1_tarski(k2_relat_1('#skF_10'),k2_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_454,c_2516])).

tff(c_2526,plain,(
    ~ r1_tarski(k2_relat_1('#skF_10'),k2_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2520])).

tff(c_2923,plain,(
    ! [A_280,C_281,B_282] :
      ( r2_hidden(k4_tarski('#skF_9'(A_280,k2_relat_1(A_280),C_281),C_281),B_282)
      | ~ r1_tarski(A_280,B_282)
      | ~ r2_hidden(C_281,k2_relat_1(A_280)) ) ),
    inference(resolution,[status(thm)],[c_87,c_2])).

tff(c_26,plain,(
    ! [C_45,A_30,D_48] :
      ( r2_hidden(C_45,k2_relat_1(A_30))
      | ~ r2_hidden(k4_tarski(D_48,C_45),A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2977,plain,(
    ! [C_283,B_284,A_285] :
      ( r2_hidden(C_283,k2_relat_1(B_284))
      | ~ r1_tarski(A_285,B_284)
      | ~ r2_hidden(C_283,k2_relat_1(A_285)) ) ),
    inference(resolution,[status(thm)],[c_2923,c_26])).

tff(c_3011,plain,(
    ! [C_286] :
      ( r2_hidden(C_286,k2_relat_1('#skF_11'))
      | ~ r2_hidden(C_286,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_44,c_2977])).

tff(c_3267,plain,(
    ! [A_291] :
      ( r1_tarski(A_291,k2_relat_1('#skF_11'))
      | ~ r2_hidden('#skF_1'(A_291,k2_relat_1('#skF_11')),k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_3011,c_4])).

tff(c_3279,plain,(
    r1_tarski(k2_relat_1('#skF_10'),k2_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_6,c_3267])).

tff(c_3285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2526,c_2526,c_3279])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:06:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.76/1.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.76/1.91  
% 4.76/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.76/1.91  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_11 > #skF_3 > #skF_10 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_4
% 4.76/1.91  
% 4.76/1.91  %Foreground sorts:
% 4.76/1.91  
% 4.76/1.91  
% 4.76/1.91  %Background operators:
% 4.76/1.91  
% 4.76/1.91  
% 4.76/1.91  %Foreground operators:
% 4.76/1.91  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.76/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.76/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.76/1.91  tff('#skF_11', type, '#skF_11': $i).
% 4.76/1.91  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.76/1.91  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 4.76/1.91  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.76/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.76/1.91  tff('#skF_10', type, '#skF_10': $i).
% 4.76/1.91  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.76/1.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.76/1.91  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.76/1.91  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 4.76/1.91  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 4.76/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.76/1.91  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.76/1.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.76/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.76/1.91  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.76/1.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.76/1.91  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 4.76/1.91  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.76/1.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.76/1.91  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.76/1.91  
% 5.10/1.93  tff(f_78, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 5.10/1.93  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.10/1.93  tff(f_56, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 5.10/1.93  tff(f_68, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relat_1)).
% 5.10/1.93  tff(f_48, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 5.10/1.93  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 5.10/1.93  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 5.10/1.93  tff(c_46, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.10/1.93  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.10/1.93  tff(c_76, plain, (![C_65, B_66, A_67]: (r2_hidden(C_65, B_66) | ~r2_hidden(C_65, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.10/1.93  tff(c_79, plain, (![A_1, B_2, B_66]: (r2_hidden('#skF_1'(A_1, B_2), B_66) | ~r1_tarski(A_1, B_66) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_76])).
% 5.10/1.93  tff(c_87, plain, (![A_80, C_81]: (r2_hidden(k4_tarski('#skF_9'(A_80, k2_relat_1(A_80), C_81), C_81), A_80) | ~r2_hidden(C_81, k2_relat_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.10/1.93  tff(c_38, plain, (![B_51, C_52, A_50]: (r2_hidden(B_51, k3_relat_1(C_52)) | ~r2_hidden(k4_tarski(A_50, B_51), C_52) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.10/1.93  tff(c_107, plain, (![C_82, A_83]: (r2_hidden(C_82, k3_relat_1(A_83)) | ~v1_relat_1(A_83) | ~r2_hidden(C_82, k2_relat_1(A_83)))), inference(resolution, [status(thm)], [c_87, c_38])).
% 5.10/1.93  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.10/1.93  tff(c_435, plain, (![A_128, A_129]: (r1_tarski(A_128, k3_relat_1(A_129)) | ~v1_relat_1(A_129) | ~r2_hidden('#skF_1'(A_128, k3_relat_1(A_129)), k2_relat_1(A_129)))), inference(resolution, [status(thm)], [c_107, c_4])).
% 5.10/1.93  tff(c_454, plain, (![A_129, A_1]: (~v1_relat_1(A_129) | ~r1_tarski(A_1, k2_relat_1(A_129)) | r1_tarski(A_1, k3_relat_1(A_129)))), inference(resolution, [status(thm)], [c_79, c_435])).
% 5.10/1.93  tff(c_161, plain, (![C_93, A_94]: (r2_hidden(k4_tarski(C_93, '#skF_5'(A_94, k1_relat_1(A_94), C_93)), A_94) | ~r2_hidden(C_93, k1_relat_1(A_94)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.10/1.93  tff(c_40, plain, (![A_50, C_52, B_51]: (r2_hidden(A_50, k3_relat_1(C_52)) | ~r2_hidden(k4_tarski(A_50, B_51), C_52) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.10/1.93  tff(c_181, plain, (![C_95, A_96]: (r2_hidden(C_95, k3_relat_1(A_96)) | ~v1_relat_1(A_96) | ~r2_hidden(C_95, k1_relat_1(A_96)))), inference(resolution, [status(thm)], [c_161, c_40])).
% 5.10/1.93  tff(c_292, plain, (![A_107, A_108]: (r1_tarski(A_107, k3_relat_1(A_108)) | ~v1_relat_1(A_108) | ~r2_hidden('#skF_1'(A_107, k3_relat_1(A_108)), k1_relat_1(A_108)))), inference(resolution, [status(thm)], [c_181, c_4])).
% 5.10/1.93  tff(c_301, plain, (![A_108, A_1]: (~v1_relat_1(A_108) | ~r1_tarski(A_1, k1_relat_1(A_108)) | r1_tarski(A_1, k3_relat_1(A_108)))), inference(resolution, [status(thm)], [c_79, c_292])).
% 5.10/1.93  tff(c_48, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.10/1.93  tff(c_36, plain, (![A_49]: (k2_xboole_0(k1_relat_1(A_49), k2_relat_1(A_49))=k3_relat_1(A_49) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.10/1.93  tff(c_82, plain, (![A_74, C_75, B_76]: (r1_tarski(k2_xboole_0(A_74, C_75), B_76) | ~r1_tarski(C_75, B_76) | ~r1_tarski(A_74, B_76))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.10/1.93  tff(c_760, plain, (![A_155, B_156]: (r1_tarski(k3_relat_1(A_155), B_156) | ~r1_tarski(k2_relat_1(A_155), B_156) | ~r1_tarski(k1_relat_1(A_155), B_156) | ~v1_relat_1(A_155))), inference(superposition, [status(thm), theory('equality')], [c_36, c_82])).
% 5.10/1.93  tff(c_42, plain, (~r1_tarski(k3_relat_1('#skF_10'), k3_relat_1('#skF_11'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.10/1.93  tff(c_773, plain, (~r1_tarski(k2_relat_1('#skF_10'), k3_relat_1('#skF_11')) | ~r1_tarski(k1_relat_1('#skF_10'), k3_relat_1('#skF_11')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_760, c_42])).
% 5.10/1.93  tff(c_784, plain, (~r1_tarski(k2_relat_1('#skF_10'), k3_relat_1('#skF_11')) | ~r1_tarski(k1_relat_1('#skF_10'), k3_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_773])).
% 5.10/1.93  tff(c_785, plain, (~r1_tarski(k1_relat_1('#skF_10'), k3_relat_1('#skF_11'))), inference(splitLeft, [status(thm)], [c_784])).
% 5.10/1.93  tff(c_791, plain, (~v1_relat_1('#skF_11') | ~r1_tarski(k1_relat_1('#skF_10'), k1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_301, c_785])).
% 5.10/1.93  tff(c_797, plain, (~r1_tarski(k1_relat_1('#skF_10'), k1_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_791])).
% 5.10/1.93  tff(c_44, plain, (r1_tarski('#skF_10', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.10/1.93  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.10/1.93  tff(c_2087, plain, (![C_227, A_228, B_229]: (r2_hidden(k4_tarski(C_227, '#skF_5'(A_228, k1_relat_1(A_228), C_227)), B_229) | ~r1_tarski(A_228, B_229) | ~r2_hidden(C_227, k1_relat_1(A_228)))), inference(resolution, [status(thm)], [c_161, c_2])).
% 5.10/1.93  tff(c_14, plain, (![C_26, A_11, D_29]: (r2_hidden(C_26, k1_relat_1(A_11)) | ~r2_hidden(k4_tarski(C_26, D_29), A_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.10/1.93  tff(c_2165, plain, (![C_230, B_231, A_232]: (r2_hidden(C_230, k1_relat_1(B_231)) | ~r1_tarski(A_232, B_231) | ~r2_hidden(C_230, k1_relat_1(A_232)))), inference(resolution, [status(thm)], [c_2087, c_14])).
% 5.10/1.93  tff(c_2205, plain, (![C_233]: (r2_hidden(C_233, k1_relat_1('#skF_11')) | ~r2_hidden(C_233, k1_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_44, c_2165])).
% 5.10/1.93  tff(c_2497, plain, (![A_240]: (r1_tarski(A_240, k1_relat_1('#skF_11')) | ~r2_hidden('#skF_1'(A_240, k1_relat_1('#skF_11')), k1_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_2205, c_4])).
% 5.10/1.93  tff(c_2509, plain, (r1_tarski(k1_relat_1('#skF_10'), k1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_6, c_2497])).
% 5.10/1.93  tff(c_2515, plain, $false, inference(negUnitSimplification, [status(thm)], [c_797, c_797, c_2509])).
% 5.10/1.93  tff(c_2516, plain, (~r1_tarski(k2_relat_1('#skF_10'), k3_relat_1('#skF_11'))), inference(splitRight, [status(thm)], [c_784])).
% 5.10/1.93  tff(c_2520, plain, (~v1_relat_1('#skF_11') | ~r1_tarski(k2_relat_1('#skF_10'), k2_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_454, c_2516])).
% 5.10/1.93  tff(c_2526, plain, (~r1_tarski(k2_relat_1('#skF_10'), k2_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2520])).
% 5.10/1.93  tff(c_2923, plain, (![A_280, C_281, B_282]: (r2_hidden(k4_tarski('#skF_9'(A_280, k2_relat_1(A_280), C_281), C_281), B_282) | ~r1_tarski(A_280, B_282) | ~r2_hidden(C_281, k2_relat_1(A_280)))), inference(resolution, [status(thm)], [c_87, c_2])).
% 5.10/1.93  tff(c_26, plain, (![C_45, A_30, D_48]: (r2_hidden(C_45, k2_relat_1(A_30)) | ~r2_hidden(k4_tarski(D_48, C_45), A_30))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.10/1.93  tff(c_2977, plain, (![C_283, B_284, A_285]: (r2_hidden(C_283, k2_relat_1(B_284)) | ~r1_tarski(A_285, B_284) | ~r2_hidden(C_283, k2_relat_1(A_285)))), inference(resolution, [status(thm)], [c_2923, c_26])).
% 5.10/1.93  tff(c_3011, plain, (![C_286]: (r2_hidden(C_286, k2_relat_1('#skF_11')) | ~r2_hidden(C_286, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_44, c_2977])).
% 5.10/1.93  tff(c_3267, plain, (![A_291]: (r1_tarski(A_291, k2_relat_1('#skF_11')) | ~r2_hidden('#skF_1'(A_291, k2_relat_1('#skF_11')), k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_3011, c_4])).
% 5.10/1.93  tff(c_3279, plain, (r1_tarski(k2_relat_1('#skF_10'), k2_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_6, c_3267])).
% 5.10/1.93  tff(c_3285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2526, c_2526, c_3279])).
% 5.10/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.10/1.93  
% 5.10/1.93  Inference rules
% 5.10/1.93  ----------------------
% 5.10/1.93  #Ref     : 0
% 5.10/1.93  #Sup     : 718
% 5.10/1.93  #Fact    : 0
% 5.10/1.93  #Define  : 0
% 5.10/1.93  #Split   : 8
% 5.10/1.93  #Chain   : 0
% 5.10/1.93  #Close   : 0
% 5.10/1.93  
% 5.10/1.93  Ordering : KBO
% 5.10/1.93  
% 5.10/1.93  Simplification rules
% 5.10/1.93  ----------------------
% 5.10/1.93  #Subsume      : 62
% 5.10/1.93  #Demod        : 29
% 5.10/1.93  #Tautology    : 13
% 5.10/1.93  #SimpNegUnit  : 2
% 5.10/1.93  #BackRed      : 0
% 5.10/1.93  
% 5.10/1.93  #Partial instantiations: 0
% 5.10/1.93  #Strategies tried      : 1
% 5.10/1.93  
% 5.10/1.93  Timing (in seconds)
% 5.10/1.93  ----------------------
% 5.10/1.93  Preprocessing        : 0.29
% 5.10/1.93  Parsing              : 0.16
% 5.10/1.93  CNF conversion       : 0.03
% 5.10/1.93  Main loop            : 0.87
% 5.10/1.93  Inferencing          : 0.30
% 5.10/1.93  Reduction            : 0.21
% 5.10/1.93  Demodulation         : 0.13
% 5.10/1.93  BG Simplification    : 0.04
% 5.10/1.93  Subsumption          : 0.24
% 5.10/1.93  Abstraction          : 0.04
% 5.10/1.93  MUC search           : 0.00
% 5.10/1.93  Cooper               : 0.00
% 5.10/1.93  Total                : 1.19
% 5.10/1.93  Index Insertion      : 0.00
% 5.10/1.93  Index Deletion       : 0.00
% 5.10/1.93  Index Matching       : 0.00
% 5.10/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
