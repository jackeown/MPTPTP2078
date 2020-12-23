%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:41 EST 2020

% Result     : Theorem 38.51s
% Output     : CNFRefutation 38.63s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 103 expanded)
%              Number of leaves         :   29 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :  120 ( 203 expanded)
%              Number of equality atoms :   12 (  30 expanded)
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

tff(f_112,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_47,axiom,(
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

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_71,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_82,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_60,plain,(
    k10_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_14,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_3'(A_13),A_13)
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_40,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_30,plain,(
    ! [A_23,B_24,C_25] :
      ( r2_hidden('#skF_5'(A_23,B_24,C_25),B_24)
      | ~ r2_hidden(A_23,k10_relat_1(C_25,B_24))
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1066,plain,(
    ! [A_131,B_132,C_133] :
      ( r2_hidden('#skF_5'(A_131,B_132,C_133),k2_relat_1(C_133))
      | ~ r2_hidden(A_131,k10_relat_1(C_133,B_132))
      | ~ v1_relat_1(C_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_48,plain,
    ( k10_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_61,plain,(
    r1_xboole_0(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_48])).

tff(c_125,plain,(
    ! [A_48,B_49,C_50] :
      ( ~ r1_xboole_0(A_48,B_49)
      | ~ r2_hidden(C_50,B_49)
      | ~ r2_hidden(C_50,A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_135,plain,(
    ! [C_50] :
      ( ~ r2_hidden(C_50,'#skF_6')
      | ~ r2_hidden(C_50,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_61,c_125])).

tff(c_1070,plain,(
    ! [A_131,B_132] :
      ( ~ r2_hidden('#skF_5'(A_131,B_132,'#skF_7'),'#skF_6')
      | ~ r2_hidden(A_131,k10_relat_1('#skF_7',B_132))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1066,c_135])).

tff(c_1074,plain,(
    ! [A_134,B_135] :
      ( ~ r2_hidden('#skF_5'(A_134,B_135,'#skF_7'),'#skF_6')
      | ~ r2_hidden(A_134,k10_relat_1('#skF_7',B_135)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1070])).

tff(c_1078,plain,(
    ! [A_23] :
      ( ~ r2_hidden(A_23,k10_relat_1('#skF_7','#skF_6'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_30,c_1074])).

tff(c_1082,plain,(
    ! [A_136] : ~ r2_hidden(A_136,k10_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1078])).

tff(c_1102,plain,(
    k10_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_1082])).

tff(c_1110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1102])).

tff(c_1111,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_22] :
      ( k9_relat_1(A_22,k1_relat_1(A_22)) = k2_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_16,plain,(
    ! [A_15] : r1_xboole_0(A_15,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_51,plain,(
    ! [B_34,A_35] :
      ( r1_xboole_0(B_34,A_35)
      | ~ r1_xboole_0(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    ! [A_15] : r1_xboole_0(k1_xboole_0,A_15) ),
    inference(resolution,[status(thm)],[c_16,c_51])).

tff(c_1120,plain,(
    ! [A_139,B_140,C_141] :
      ( ~ r1_xboole_0(A_139,B_140)
      | ~ r2_hidden(C_141,k3_xboole_0(A_139,B_140)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1131,plain,(
    ! [A_142,B_143] :
      ( ~ r1_xboole_0(A_142,B_143)
      | k3_xboole_0(A_142,B_143) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_1120])).

tff(c_1140,plain,(
    ! [A_144] : k3_xboole_0(k1_xboole_0,A_144) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_1131])).

tff(c_12,plain,(
    ! [A_8,B_9,C_12] :
      ( ~ r1_xboole_0(A_8,B_9)
      | ~ r2_hidden(C_12,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1145,plain,(
    ! [A_144,C_12] :
      ( ~ r1_xboole_0(k1_xboole_0,A_144)
      | ~ r2_hidden(C_12,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1140,c_12])).

tff(c_1150,plain,(
    ! [C_12] : ~ r2_hidden(C_12,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1145])).

tff(c_1113,plain,(
    k10_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1111,c_48])).

tff(c_22,plain,(
    ! [A_16,B_17,C_18] :
      ( r2_hidden(k4_tarski('#skF_4'(A_16,B_17,C_18),A_16),C_18)
      | ~ r2_hidden(A_16,k9_relat_1(C_18,B_17))
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2102,plain,(
    ! [A_233,C_234,B_235,D_236] :
      ( r2_hidden(A_233,k10_relat_1(C_234,B_235))
      | ~ r2_hidden(D_236,B_235)
      | ~ r2_hidden(k4_tarski(A_233,D_236),C_234)
      | ~ r2_hidden(D_236,k2_relat_1(C_234))
      | ~ v1_relat_1(C_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_9534,plain,(
    ! [A_501,C_502,B_503,A_504] :
      ( r2_hidden(A_501,k10_relat_1(C_502,B_503))
      | ~ r2_hidden(k4_tarski(A_501,'#skF_1'(A_504,B_503)),C_502)
      | ~ r2_hidden('#skF_1'(A_504,B_503),k2_relat_1(C_502))
      | ~ v1_relat_1(C_502)
      | r1_xboole_0(A_504,B_503) ) ),
    inference(resolution,[status(thm)],[c_6,c_2102])).

tff(c_81077,plain,(
    ! [A_1526,B_1527,B_1528,C_1529] :
      ( r2_hidden('#skF_4'('#skF_1'(A_1526,B_1527),B_1528,C_1529),k10_relat_1(C_1529,B_1527))
      | ~ r2_hidden('#skF_1'(A_1526,B_1527),k2_relat_1(C_1529))
      | r1_xboole_0(A_1526,B_1527)
      | ~ r2_hidden('#skF_1'(A_1526,B_1527),k9_relat_1(C_1529,B_1528))
      | ~ v1_relat_1(C_1529) ) ),
    inference(resolution,[status(thm)],[c_22,c_9534])).

tff(c_81233,plain,(
    ! [A_1526,B_1528] :
      ( r2_hidden('#skF_4'('#skF_1'(A_1526,'#skF_6'),B_1528,'#skF_7'),k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_1526,'#skF_6'),k2_relat_1('#skF_7'))
      | r1_xboole_0(A_1526,'#skF_6')
      | ~ r2_hidden('#skF_1'(A_1526,'#skF_6'),k9_relat_1('#skF_7',B_1528))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1113,c_81077])).

tff(c_81282,plain,(
    ! [A_1526,B_1528] :
      ( r2_hidden('#skF_4'('#skF_1'(A_1526,'#skF_6'),B_1528,'#skF_7'),k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_1526,'#skF_6'),k2_relat_1('#skF_7'))
      | r1_xboole_0(A_1526,'#skF_6')
      | ~ r2_hidden('#skF_1'(A_1526,'#skF_6'),k9_relat_1('#skF_7',B_1528)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81233])).

tff(c_81284,plain,(
    ! [A_1530,B_1531] :
      ( ~ r2_hidden('#skF_1'(A_1530,'#skF_6'),k2_relat_1('#skF_7'))
      | r1_xboole_0(A_1530,'#skF_6')
      | ~ r2_hidden('#skF_1'(A_1530,'#skF_6'),k9_relat_1('#skF_7',B_1531)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1150,c_81282])).

tff(c_81366,plain,(
    ! [A_1530] :
      ( ~ r2_hidden('#skF_1'(A_1530,'#skF_6'),k2_relat_1('#skF_7'))
      | r1_xboole_0(A_1530,'#skF_6')
      | ~ r2_hidden('#skF_1'(A_1530,'#skF_6'),k2_relat_1('#skF_7'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_81284])).

tff(c_81410,plain,(
    ! [A_1532] :
      ( r1_xboole_0(A_1532,'#skF_6')
      | ~ r2_hidden('#skF_1'(A_1532,'#skF_6'),k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81366])).

tff(c_81422,plain,(
    r1_xboole_0(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_81410])).

tff(c_81433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1111,c_1111,c_81422])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:44:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 38.51/31.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 38.51/31.19  
% 38.51/31.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 38.51/31.19  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_3 > #skF_2 > #skF_1
% 38.51/31.19  
% 38.51/31.19  %Foreground sorts:
% 38.51/31.19  
% 38.51/31.19  
% 38.51/31.19  %Background operators:
% 38.51/31.19  
% 38.51/31.19  
% 38.51/31.19  %Foreground operators:
% 38.51/31.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 38.51/31.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 38.51/31.19  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 38.51/31.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 38.51/31.19  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 38.51/31.19  tff('#skF_7', type, '#skF_7': $i).
% 38.51/31.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 38.51/31.19  tff('#skF_6', type, '#skF_6': $i).
% 38.51/31.19  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 38.51/31.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 38.51/31.19  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 38.51/31.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 38.51/31.19  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 38.51/31.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 38.51/31.19  tff('#skF_3', type, '#skF_3': $i > $i).
% 38.51/31.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 38.51/31.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 38.51/31.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 38.51/31.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 38.51/31.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 38.51/31.19  
% 38.63/31.21  tff(f_112, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 38.63/31.21  tff(f_69, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 38.63/31.21  tff(f_97, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 38.63/31.21  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 38.63/31.21  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 38.63/31.21  tff(f_71, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 38.63/31.21  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 38.63/31.21  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 38.63/31.21  tff(f_82, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 38.63/31.21  tff(c_42, plain, (~r1_xboole_0(k2_relat_1('#skF_7'), '#skF_6') | k10_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_112])).
% 38.63/31.21  tff(c_60, plain, (k10_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 38.63/31.21  tff(c_14, plain, (![A_13]: (r2_hidden('#skF_3'(A_13), A_13) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_69])).
% 38.63/31.21  tff(c_40, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_112])).
% 38.63/31.21  tff(c_30, plain, (![A_23, B_24, C_25]: (r2_hidden('#skF_5'(A_23, B_24, C_25), B_24) | ~r2_hidden(A_23, k10_relat_1(C_25, B_24)) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_97])).
% 38.63/31.21  tff(c_1066, plain, (![A_131, B_132, C_133]: (r2_hidden('#skF_5'(A_131, B_132, C_133), k2_relat_1(C_133)) | ~r2_hidden(A_131, k10_relat_1(C_133, B_132)) | ~v1_relat_1(C_133))), inference(cnfTransformation, [status(thm)], [f_97])).
% 38.63/31.21  tff(c_48, plain, (k10_relat_1('#skF_7', '#skF_6')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_112])).
% 38.63/31.21  tff(c_61, plain, (r1_xboole_0(k2_relat_1('#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_60, c_48])).
% 38.63/31.21  tff(c_125, plain, (![A_48, B_49, C_50]: (~r1_xboole_0(A_48, B_49) | ~r2_hidden(C_50, B_49) | ~r2_hidden(C_50, A_48))), inference(cnfTransformation, [status(thm)], [f_47])).
% 38.63/31.21  tff(c_135, plain, (![C_50]: (~r2_hidden(C_50, '#skF_6') | ~r2_hidden(C_50, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_61, c_125])).
% 38.63/31.21  tff(c_1070, plain, (![A_131, B_132]: (~r2_hidden('#skF_5'(A_131, B_132, '#skF_7'), '#skF_6') | ~r2_hidden(A_131, k10_relat_1('#skF_7', B_132)) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_1066, c_135])).
% 38.63/31.21  tff(c_1074, plain, (![A_134, B_135]: (~r2_hidden('#skF_5'(A_134, B_135, '#skF_7'), '#skF_6') | ~r2_hidden(A_134, k10_relat_1('#skF_7', B_135)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1070])).
% 38.63/31.21  tff(c_1078, plain, (![A_23]: (~r2_hidden(A_23, k10_relat_1('#skF_7', '#skF_6')) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_30, c_1074])).
% 38.63/31.21  tff(c_1082, plain, (![A_136]: (~r2_hidden(A_136, k10_relat_1('#skF_7', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1078])).
% 38.63/31.21  tff(c_1102, plain, (k10_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_1082])).
% 38.63/31.21  tff(c_1110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1102])).
% 38.63/31.21  tff(c_1111, plain, (~r1_xboole_0(k2_relat_1('#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_42])).
% 38.63/31.21  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 38.63/31.21  tff(c_26, plain, (![A_22]: (k9_relat_1(A_22, k1_relat_1(A_22))=k2_relat_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_86])).
% 38.63/31.21  tff(c_16, plain, (![A_15]: (r1_xboole_0(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_71])).
% 38.63/31.21  tff(c_51, plain, (![B_34, A_35]: (r1_xboole_0(B_34, A_35) | ~r1_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_29])).
% 38.63/31.21  tff(c_54, plain, (![A_15]: (r1_xboole_0(k1_xboole_0, A_15))), inference(resolution, [status(thm)], [c_16, c_51])).
% 38.63/31.21  tff(c_1120, plain, (![A_139, B_140, C_141]: (~r1_xboole_0(A_139, B_140) | ~r2_hidden(C_141, k3_xboole_0(A_139, B_140)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 38.63/31.21  tff(c_1131, plain, (![A_142, B_143]: (~r1_xboole_0(A_142, B_143) | k3_xboole_0(A_142, B_143)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_1120])).
% 38.63/31.21  tff(c_1140, plain, (![A_144]: (k3_xboole_0(k1_xboole_0, A_144)=k1_xboole_0)), inference(resolution, [status(thm)], [c_54, c_1131])).
% 38.63/31.21  tff(c_12, plain, (![A_8, B_9, C_12]: (~r1_xboole_0(A_8, B_9) | ~r2_hidden(C_12, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 38.63/31.21  tff(c_1145, plain, (![A_144, C_12]: (~r1_xboole_0(k1_xboole_0, A_144) | ~r2_hidden(C_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1140, c_12])).
% 38.63/31.21  tff(c_1150, plain, (![C_12]: (~r2_hidden(C_12, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1145])).
% 38.63/31.21  tff(c_1113, plain, (k10_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1111, c_48])).
% 38.63/31.21  tff(c_22, plain, (![A_16, B_17, C_18]: (r2_hidden(k4_tarski('#skF_4'(A_16, B_17, C_18), A_16), C_18) | ~r2_hidden(A_16, k9_relat_1(C_18, B_17)) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_82])).
% 38.63/31.21  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 38.63/31.21  tff(c_2102, plain, (![A_233, C_234, B_235, D_236]: (r2_hidden(A_233, k10_relat_1(C_234, B_235)) | ~r2_hidden(D_236, B_235) | ~r2_hidden(k4_tarski(A_233, D_236), C_234) | ~r2_hidden(D_236, k2_relat_1(C_234)) | ~v1_relat_1(C_234))), inference(cnfTransformation, [status(thm)], [f_97])).
% 38.63/31.21  tff(c_9534, plain, (![A_501, C_502, B_503, A_504]: (r2_hidden(A_501, k10_relat_1(C_502, B_503)) | ~r2_hidden(k4_tarski(A_501, '#skF_1'(A_504, B_503)), C_502) | ~r2_hidden('#skF_1'(A_504, B_503), k2_relat_1(C_502)) | ~v1_relat_1(C_502) | r1_xboole_0(A_504, B_503))), inference(resolution, [status(thm)], [c_6, c_2102])).
% 38.63/31.21  tff(c_81077, plain, (![A_1526, B_1527, B_1528, C_1529]: (r2_hidden('#skF_4'('#skF_1'(A_1526, B_1527), B_1528, C_1529), k10_relat_1(C_1529, B_1527)) | ~r2_hidden('#skF_1'(A_1526, B_1527), k2_relat_1(C_1529)) | r1_xboole_0(A_1526, B_1527) | ~r2_hidden('#skF_1'(A_1526, B_1527), k9_relat_1(C_1529, B_1528)) | ~v1_relat_1(C_1529))), inference(resolution, [status(thm)], [c_22, c_9534])).
% 38.63/31.21  tff(c_81233, plain, (![A_1526, B_1528]: (r2_hidden('#skF_4'('#skF_1'(A_1526, '#skF_6'), B_1528, '#skF_7'), k1_xboole_0) | ~r2_hidden('#skF_1'(A_1526, '#skF_6'), k2_relat_1('#skF_7')) | r1_xboole_0(A_1526, '#skF_6') | ~r2_hidden('#skF_1'(A_1526, '#skF_6'), k9_relat_1('#skF_7', B_1528)) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1113, c_81077])).
% 38.63/31.21  tff(c_81282, plain, (![A_1526, B_1528]: (r2_hidden('#skF_4'('#skF_1'(A_1526, '#skF_6'), B_1528, '#skF_7'), k1_xboole_0) | ~r2_hidden('#skF_1'(A_1526, '#skF_6'), k2_relat_1('#skF_7')) | r1_xboole_0(A_1526, '#skF_6') | ~r2_hidden('#skF_1'(A_1526, '#skF_6'), k9_relat_1('#skF_7', B_1528)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_81233])).
% 38.63/31.21  tff(c_81284, plain, (![A_1530, B_1531]: (~r2_hidden('#skF_1'(A_1530, '#skF_6'), k2_relat_1('#skF_7')) | r1_xboole_0(A_1530, '#skF_6') | ~r2_hidden('#skF_1'(A_1530, '#skF_6'), k9_relat_1('#skF_7', B_1531)))), inference(negUnitSimplification, [status(thm)], [c_1150, c_81282])).
% 38.63/31.21  tff(c_81366, plain, (![A_1530]: (~r2_hidden('#skF_1'(A_1530, '#skF_6'), k2_relat_1('#skF_7')) | r1_xboole_0(A_1530, '#skF_6') | ~r2_hidden('#skF_1'(A_1530, '#skF_6'), k2_relat_1('#skF_7')) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_81284])).
% 38.63/31.21  tff(c_81410, plain, (![A_1532]: (r1_xboole_0(A_1532, '#skF_6') | ~r2_hidden('#skF_1'(A_1532, '#skF_6'), k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_81366])).
% 38.63/31.21  tff(c_81422, plain, (r1_xboole_0(k2_relat_1('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_8, c_81410])).
% 38.63/31.21  tff(c_81433, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1111, c_1111, c_81422])).
% 38.63/31.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 38.63/31.21  
% 38.63/31.21  Inference rules
% 38.63/31.21  ----------------------
% 38.63/31.21  #Ref     : 0
% 38.63/31.21  #Sup     : 22453
% 38.63/31.21  #Fact    : 0
% 38.63/31.21  #Define  : 0
% 38.63/31.21  #Split   : 12
% 38.63/31.21  #Chain   : 0
% 38.63/31.21  #Close   : 0
% 38.63/31.21  
% 38.63/31.21  Ordering : KBO
% 38.63/31.21  
% 38.63/31.21  Simplification rules
% 38.63/31.21  ----------------------
% 38.63/31.21  #Subsume      : 7941
% 38.63/31.21  #Demod        : 2512
% 38.63/31.21  #Tautology    : 7212
% 38.63/31.21  #SimpNegUnit  : 179
% 38.63/31.21  #BackRed      : 0
% 38.63/31.21  
% 38.63/31.21  #Partial instantiations: 0
% 38.63/31.21  #Strategies tried      : 1
% 38.63/31.21  
% 38.63/31.21  Timing (in seconds)
% 38.63/31.21  ----------------------
% 38.63/31.21  Preprocessing        : 0.29
% 38.63/31.21  Parsing              : 0.16
% 38.63/31.21  CNF conversion       : 0.02
% 38.63/31.21  Main loop            : 30.15
% 38.63/31.21  Inferencing          : 2.11
% 38.63/31.21  Reduction            : 1.94
% 38.63/31.22  Demodulation         : 1.31
% 38.63/31.22  BG Simplification    : 0.21
% 38.63/31.22  Subsumption          : 25.45
% 38.63/31.22  Abstraction          : 0.25
% 38.63/31.22  MUC search           : 0.00
% 38.63/31.22  Cooper               : 0.00
% 38.63/31.22  Total                : 30.48
% 38.63/31.22  Index Insertion      : 0.00
% 38.63/31.22  Index Deletion       : 0.00
% 38.63/31.22  Index Matching       : 0.00
% 38.63/31.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
