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
% DateTime   : Thu Dec  3 10:01:41 EST 2020

% Result     : Theorem 36.72s
% Output     : CNFRefutation 36.72s
% Verified   : 
% Statistics : Number of formulae       :   66 (  88 expanded)
%              Number of leaves         :   29 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  112 ( 174 expanded)
%              Number of equality atoms :   12 (  26 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_43,axiom,(
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

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_69,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_67,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_42,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_7'),'#skF_6')
    | k10_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_59,plain,(
    k10_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_12,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_40,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_30,plain,(
    ! [A_22,B_23,C_24] :
      ( r2_hidden('#skF_5'(A_22,B_23,C_24),B_23)
      | ~ r2_hidden(A_22,k10_relat_1(C_24,B_23))
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_967,plain,(
    ! [A_121,B_122,C_123] :
      ( r2_hidden('#skF_5'(A_121,B_122,C_123),k2_relat_1(C_123))
      | ~ r2_hidden(A_121,k10_relat_1(C_123,B_122))
      | ~ v1_relat_1(C_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_48,plain,
    ( k10_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_60,plain,(
    r1_xboole_0(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_48])).

tff(c_194,plain,(
    ! [A_53,B_54,C_55] :
      ( ~ r1_xboole_0(A_53,B_54)
      | ~ r2_hidden(C_55,B_54)
      | ~ r2_hidden(C_55,A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_208,plain,(
    ! [C_55] :
      ( ~ r2_hidden(C_55,'#skF_6')
      | ~ r2_hidden(C_55,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_60,c_194])).

tff(c_971,plain,(
    ! [A_121,B_122] :
      ( ~ r2_hidden('#skF_5'(A_121,B_122,'#skF_7'),'#skF_6')
      | ~ r2_hidden(A_121,k10_relat_1('#skF_7',B_122))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_967,c_208])).

tff(c_992,plain,(
    ! [A_126,B_127] :
      ( ~ r2_hidden('#skF_5'(A_126,B_127,'#skF_7'),'#skF_6')
      | ~ r2_hidden(A_126,k10_relat_1('#skF_7',B_127)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_971])).

tff(c_996,plain,(
    ! [A_22] :
      ( ~ r2_hidden(A_22,k10_relat_1('#skF_7','#skF_6'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_30,c_992])).

tff(c_1000,plain,(
    ! [A_128] : ~ r2_hidden(A_128,k10_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_996])).

tff(c_1020,plain,(
    k10_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_1000])).

tff(c_1028,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_1020])).

tff(c_1029,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    ! [A_21] :
      ( k9_relat_1(A_21,k1_relat_1(A_21)) = k2_relat_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_16,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_14,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1044,plain,(
    ! [A_129,B_130,C_131] :
      ( ~ r1_xboole_0(A_129,B_130)
      | ~ r2_hidden(C_131,k3_xboole_0(A_129,B_130)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1055,plain,(
    ! [A_13,C_131] :
      ( ~ r1_xboole_0(A_13,k1_xboole_0)
      | ~ r2_hidden(C_131,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1044])).

tff(c_1059,plain,(
    ! [C_131] : ~ r2_hidden(C_131,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1055])).

tff(c_1030,plain,(
    k10_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_22,plain,(
    ! [A_15,B_16,C_17] :
      ( r2_hidden(k4_tarski('#skF_4'(A_15,B_16,C_17),A_15),C_17)
      | ~ r2_hidden(A_15,k9_relat_1(C_17,B_16))
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2110,plain,(
    ! [A_232,C_233,B_234,D_235] :
      ( r2_hidden(A_232,k10_relat_1(C_233,B_234))
      | ~ r2_hidden(D_235,B_234)
      | ~ r2_hidden(k4_tarski(A_232,D_235),C_233)
      | ~ r2_hidden(D_235,k2_relat_1(C_233))
      | ~ v1_relat_1(C_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_7671,plain,(
    ! [A_455,C_456,B_457,A_458] :
      ( r2_hidden(A_455,k10_relat_1(C_456,B_457))
      | ~ r2_hidden(k4_tarski(A_455,'#skF_1'(A_458,B_457)),C_456)
      | ~ r2_hidden('#skF_1'(A_458,B_457),k2_relat_1(C_456))
      | ~ v1_relat_1(C_456)
      | r1_xboole_0(A_458,B_457) ) ),
    inference(resolution,[status(thm)],[c_4,c_2110])).

tff(c_75288,plain,(
    ! [A_1576,B_1577,B_1578,C_1579] :
      ( r2_hidden('#skF_4'('#skF_1'(A_1576,B_1577),B_1578,C_1579),k10_relat_1(C_1579,B_1577))
      | ~ r2_hidden('#skF_1'(A_1576,B_1577),k2_relat_1(C_1579))
      | r1_xboole_0(A_1576,B_1577)
      | ~ r2_hidden('#skF_1'(A_1576,B_1577),k9_relat_1(C_1579,B_1578))
      | ~ v1_relat_1(C_1579) ) ),
    inference(resolution,[status(thm)],[c_22,c_7671])).

tff(c_75427,plain,(
    ! [A_1576,B_1578] :
      ( r2_hidden('#skF_4'('#skF_1'(A_1576,'#skF_6'),B_1578,'#skF_7'),k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_1576,'#skF_6'),k2_relat_1('#skF_7'))
      | r1_xboole_0(A_1576,'#skF_6')
      | ~ r2_hidden('#skF_1'(A_1576,'#skF_6'),k9_relat_1('#skF_7',B_1578))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1030,c_75288])).

tff(c_75471,plain,(
    ! [A_1576,B_1578] :
      ( r2_hidden('#skF_4'('#skF_1'(A_1576,'#skF_6'),B_1578,'#skF_7'),k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_1576,'#skF_6'),k2_relat_1('#skF_7'))
      | r1_xboole_0(A_1576,'#skF_6')
      | ~ r2_hidden('#skF_1'(A_1576,'#skF_6'),k9_relat_1('#skF_7',B_1578)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_75427])).

tff(c_75473,plain,(
    ! [A_1580,B_1581] :
      ( ~ r2_hidden('#skF_1'(A_1580,'#skF_6'),k2_relat_1('#skF_7'))
      | r1_xboole_0(A_1580,'#skF_6')
      | ~ r2_hidden('#skF_1'(A_1580,'#skF_6'),k9_relat_1('#skF_7',B_1581)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1059,c_75471])).

tff(c_75535,plain,(
    ! [A_1580] :
      ( ~ r2_hidden('#skF_1'(A_1580,'#skF_6'),k2_relat_1('#skF_7'))
      | r1_xboole_0(A_1580,'#skF_6')
      | ~ r2_hidden('#skF_1'(A_1580,'#skF_6'),k2_relat_1('#skF_7'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_75473])).

tff(c_75573,plain,(
    ! [A_1582] :
      ( r1_xboole_0(A_1582,'#skF_6')
      | ~ r2_hidden('#skF_1'(A_1582,'#skF_6'),k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_75535])).

tff(c_75585,plain,(
    r1_xboole_0(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_75573])).

tff(c_75596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1029,c_1029,c_75585])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:43:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 36.72/28.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.72/28.39  
% 36.72/28.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.72/28.39  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_3 > #skF_2 > #skF_1
% 36.72/28.39  
% 36.72/28.39  %Foreground sorts:
% 36.72/28.39  
% 36.72/28.39  
% 36.72/28.39  %Background operators:
% 36.72/28.39  
% 36.72/28.39  
% 36.72/28.39  %Foreground operators:
% 36.72/28.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 36.72/28.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 36.72/28.39  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 36.72/28.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 36.72/28.39  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 36.72/28.39  tff('#skF_7', type, '#skF_7': $i).
% 36.72/28.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 36.72/28.39  tff('#skF_6', type, '#skF_6': $i).
% 36.72/28.39  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 36.72/28.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 36.72/28.39  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 36.72/28.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 36.72/28.39  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 36.72/28.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 36.72/28.39  tff('#skF_3', type, '#skF_3': $i > $i).
% 36.72/28.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 36.72/28.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 36.72/28.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 36.72/28.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 36.72/28.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 36.72/28.39  
% 36.72/28.41  tff(f_110, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 36.72/28.41  tff(f_65, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 36.72/28.41  tff(f_95, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 36.72/28.41  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 36.72/28.41  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 36.72/28.41  tff(f_69, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 36.72/28.41  tff(f_67, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 36.72/28.41  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 36.72/28.41  tff(f_80, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 36.72/28.41  tff(c_42, plain, (~r1_xboole_0(k2_relat_1('#skF_7'), '#skF_6') | k10_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_110])).
% 36.72/28.41  tff(c_59, plain, (k10_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 36.72/28.41  tff(c_12, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_65])).
% 36.72/28.41  tff(c_40, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_110])).
% 36.72/28.41  tff(c_30, plain, (![A_22, B_23, C_24]: (r2_hidden('#skF_5'(A_22, B_23, C_24), B_23) | ~r2_hidden(A_22, k10_relat_1(C_24, B_23)) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_95])).
% 36.72/28.41  tff(c_967, plain, (![A_121, B_122, C_123]: (r2_hidden('#skF_5'(A_121, B_122, C_123), k2_relat_1(C_123)) | ~r2_hidden(A_121, k10_relat_1(C_123, B_122)) | ~v1_relat_1(C_123))), inference(cnfTransformation, [status(thm)], [f_95])).
% 36.72/28.41  tff(c_48, plain, (k10_relat_1('#skF_7', '#skF_6')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_110])).
% 36.72/28.41  tff(c_60, plain, (r1_xboole_0(k2_relat_1('#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_59, c_48])).
% 36.72/28.41  tff(c_194, plain, (![A_53, B_54, C_55]: (~r1_xboole_0(A_53, B_54) | ~r2_hidden(C_55, B_54) | ~r2_hidden(C_55, A_53))), inference(cnfTransformation, [status(thm)], [f_43])).
% 36.72/28.41  tff(c_208, plain, (![C_55]: (~r2_hidden(C_55, '#skF_6') | ~r2_hidden(C_55, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_60, c_194])).
% 36.72/28.41  tff(c_971, plain, (![A_121, B_122]: (~r2_hidden('#skF_5'(A_121, B_122, '#skF_7'), '#skF_6') | ~r2_hidden(A_121, k10_relat_1('#skF_7', B_122)) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_967, c_208])).
% 36.72/28.41  tff(c_992, plain, (![A_126, B_127]: (~r2_hidden('#skF_5'(A_126, B_127, '#skF_7'), '#skF_6') | ~r2_hidden(A_126, k10_relat_1('#skF_7', B_127)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_971])).
% 36.72/28.41  tff(c_996, plain, (![A_22]: (~r2_hidden(A_22, k10_relat_1('#skF_7', '#skF_6')) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_30, c_992])).
% 36.72/28.41  tff(c_1000, plain, (![A_128]: (~r2_hidden(A_128, k10_relat_1('#skF_7', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_996])).
% 36.72/28.41  tff(c_1020, plain, (k10_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_1000])).
% 36.72/28.41  tff(c_1028, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_1020])).
% 36.72/28.41  tff(c_1029, plain, (~r1_xboole_0(k2_relat_1('#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_42])).
% 36.72/28.41  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 36.72/28.41  tff(c_26, plain, (![A_21]: (k9_relat_1(A_21, k1_relat_1(A_21))=k2_relat_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_84])).
% 36.72/28.41  tff(c_16, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_69])).
% 36.72/28.41  tff(c_14, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 36.72/28.41  tff(c_1044, plain, (![A_129, B_130, C_131]: (~r1_xboole_0(A_129, B_130) | ~r2_hidden(C_131, k3_xboole_0(A_129, B_130)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 36.72/28.41  tff(c_1055, plain, (![A_13, C_131]: (~r1_xboole_0(A_13, k1_xboole_0) | ~r2_hidden(C_131, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1044])).
% 36.72/28.41  tff(c_1059, plain, (![C_131]: (~r2_hidden(C_131, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1055])).
% 36.72/28.41  tff(c_1030, plain, (k10_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 36.72/28.41  tff(c_22, plain, (![A_15, B_16, C_17]: (r2_hidden(k4_tarski('#skF_4'(A_15, B_16, C_17), A_15), C_17) | ~r2_hidden(A_15, k9_relat_1(C_17, B_16)) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_80])).
% 36.72/28.41  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 36.72/28.41  tff(c_2110, plain, (![A_232, C_233, B_234, D_235]: (r2_hidden(A_232, k10_relat_1(C_233, B_234)) | ~r2_hidden(D_235, B_234) | ~r2_hidden(k4_tarski(A_232, D_235), C_233) | ~r2_hidden(D_235, k2_relat_1(C_233)) | ~v1_relat_1(C_233))), inference(cnfTransformation, [status(thm)], [f_95])).
% 36.72/28.41  tff(c_7671, plain, (![A_455, C_456, B_457, A_458]: (r2_hidden(A_455, k10_relat_1(C_456, B_457)) | ~r2_hidden(k4_tarski(A_455, '#skF_1'(A_458, B_457)), C_456) | ~r2_hidden('#skF_1'(A_458, B_457), k2_relat_1(C_456)) | ~v1_relat_1(C_456) | r1_xboole_0(A_458, B_457))), inference(resolution, [status(thm)], [c_4, c_2110])).
% 36.72/28.41  tff(c_75288, plain, (![A_1576, B_1577, B_1578, C_1579]: (r2_hidden('#skF_4'('#skF_1'(A_1576, B_1577), B_1578, C_1579), k10_relat_1(C_1579, B_1577)) | ~r2_hidden('#skF_1'(A_1576, B_1577), k2_relat_1(C_1579)) | r1_xboole_0(A_1576, B_1577) | ~r2_hidden('#skF_1'(A_1576, B_1577), k9_relat_1(C_1579, B_1578)) | ~v1_relat_1(C_1579))), inference(resolution, [status(thm)], [c_22, c_7671])).
% 36.72/28.41  tff(c_75427, plain, (![A_1576, B_1578]: (r2_hidden('#skF_4'('#skF_1'(A_1576, '#skF_6'), B_1578, '#skF_7'), k1_xboole_0) | ~r2_hidden('#skF_1'(A_1576, '#skF_6'), k2_relat_1('#skF_7')) | r1_xboole_0(A_1576, '#skF_6') | ~r2_hidden('#skF_1'(A_1576, '#skF_6'), k9_relat_1('#skF_7', B_1578)) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1030, c_75288])).
% 36.72/28.41  tff(c_75471, plain, (![A_1576, B_1578]: (r2_hidden('#skF_4'('#skF_1'(A_1576, '#skF_6'), B_1578, '#skF_7'), k1_xboole_0) | ~r2_hidden('#skF_1'(A_1576, '#skF_6'), k2_relat_1('#skF_7')) | r1_xboole_0(A_1576, '#skF_6') | ~r2_hidden('#skF_1'(A_1576, '#skF_6'), k9_relat_1('#skF_7', B_1578)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_75427])).
% 36.72/28.41  tff(c_75473, plain, (![A_1580, B_1581]: (~r2_hidden('#skF_1'(A_1580, '#skF_6'), k2_relat_1('#skF_7')) | r1_xboole_0(A_1580, '#skF_6') | ~r2_hidden('#skF_1'(A_1580, '#skF_6'), k9_relat_1('#skF_7', B_1581)))), inference(negUnitSimplification, [status(thm)], [c_1059, c_75471])).
% 36.72/28.41  tff(c_75535, plain, (![A_1580]: (~r2_hidden('#skF_1'(A_1580, '#skF_6'), k2_relat_1('#skF_7')) | r1_xboole_0(A_1580, '#skF_6') | ~r2_hidden('#skF_1'(A_1580, '#skF_6'), k2_relat_1('#skF_7')) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_75473])).
% 36.72/28.41  tff(c_75573, plain, (![A_1582]: (r1_xboole_0(A_1582, '#skF_6') | ~r2_hidden('#skF_1'(A_1582, '#skF_6'), k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_75535])).
% 36.72/28.41  tff(c_75585, plain, (r1_xboole_0(k2_relat_1('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_6, c_75573])).
% 36.72/28.41  tff(c_75596, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1029, c_1029, c_75585])).
% 36.72/28.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.72/28.41  
% 36.72/28.41  Inference rules
% 36.72/28.41  ----------------------
% 36.72/28.41  #Ref     : 0
% 36.72/28.41  #Sup     : 20676
% 36.72/28.41  #Fact    : 0
% 36.72/28.41  #Define  : 0
% 36.72/28.41  #Split   : 19
% 36.72/28.41  #Chain   : 0
% 36.72/28.41  #Close   : 0
% 36.72/28.41  
% 36.72/28.41  Ordering : KBO
% 36.72/28.41  
% 36.72/28.41  Simplification rules
% 36.72/28.41  ----------------------
% 36.72/28.41  #Subsume      : 7635
% 36.72/28.41  #Demod        : 2478
% 36.72/28.41  #Tautology    : 6567
% 36.72/28.41  #SimpNegUnit  : 157
% 36.72/28.41  #BackRed      : 0
% 36.72/28.41  
% 36.72/28.41  #Partial instantiations: 0
% 36.72/28.41  #Strategies tried      : 1
% 36.72/28.41  
% 36.72/28.41  Timing (in seconds)
% 36.72/28.41  ----------------------
% 36.72/28.41  Preprocessing        : 0.32
% 36.72/28.41  Parsing              : 0.17
% 36.72/28.41  CNF conversion       : 0.03
% 36.72/28.41  Main loop            : 27.31
% 36.72/28.41  Inferencing          : 2.08
% 36.72/28.41  Reduction            : 1.92
% 36.72/28.41  Demodulation         : 1.31
% 36.72/28.41  BG Simplification    : 0.20
% 36.72/28.41  Subsumption          : 22.65
% 36.72/28.41  Abstraction          : 0.26
% 36.72/28.41  MUC search           : 0.00
% 36.72/28.41  Cooper               : 0.00
% 36.72/28.41  Total                : 27.66
% 36.72/28.41  Index Insertion      : 0.00
% 36.72/28.41  Index Deletion       : 0.00
% 36.72/28.41  Index Matching       : 0.00
% 36.72/28.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
