%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:22 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 147 expanded)
%              Number of leaves         :   24 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  101 ( 301 expanded)
%              Number of equality atoms :   19 (  82 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_62,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_32,plain,
    ( k11_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_48,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_38,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_7'))
    | k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_49,plain,(
    k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_38])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_455,plain,(
    ! [A_105,B_106] :
      ( r2_hidden(k4_tarski('#skF_2'(A_105,B_106),'#skF_3'(A_105,B_106)),A_105)
      | r2_hidden('#skF_4'(A_105,B_106),B_106)
      | k1_relat_1(A_105) = B_106 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [C_22,A_7,D_25] :
      ( r2_hidden(C_22,k1_relat_1(A_7))
      | ~ r2_hidden(k4_tarski(C_22,D_25),A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_492,plain,(
    ! [A_107,B_108] :
      ( r2_hidden('#skF_2'(A_107,B_108),k1_relat_1(A_107))
      | r2_hidden('#skF_4'(A_107,B_108),B_108)
      | k1_relat_1(A_107) = B_108 ) ),
    inference(resolution,[status(thm)],[c_455,c_12])).

tff(c_531,plain,(
    ! [B_108] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_108),k1_xboole_0)
      | r2_hidden('#skF_4'(k1_xboole_0,B_108),B_108)
      | k1_relat_1(k1_xboole_0) = B_108 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_492])).

tff(c_542,plain,(
    ! [B_108] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_108),k1_xboole_0)
      | r2_hidden('#skF_4'(k1_xboole_0,B_108),B_108)
      | k1_xboole_0 = B_108 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_531])).

tff(c_543,plain,(
    ! [B_109] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_109),k1_xboole_0)
      | r2_hidden('#skF_4'(k1_xboole_0,B_109),B_109)
      | k1_xboole_0 = B_109 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_531])).

tff(c_8,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_53,plain,(
    ! [A_37,B_38,C_39] :
      ( ~ r1_xboole_0(A_37,B_38)
      | ~ r2_hidden(C_39,B_38)
      | ~ r2_hidden(C_39,A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_56,plain,(
    ! [C_39,A_6] :
      ( ~ r2_hidden(C_39,k1_xboole_0)
      | ~ r2_hidden(C_39,A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_53])).

tff(c_586,plain,(
    ! [B_110,A_111] :
      ( ~ r2_hidden('#skF_2'(k1_xboole_0,B_110),A_111)
      | r2_hidden('#skF_4'(k1_xboole_0,B_110),B_110)
      | k1_xboole_0 = B_110 ) ),
    inference(resolution,[status(thm)],[c_543,c_56])).

tff(c_604,plain,(
    ! [B_108] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_108),B_108)
      | k1_xboole_0 = B_108 ) ),
    inference(resolution,[status(thm)],[c_542,c_586])).

tff(c_671,plain,(
    ! [B_114] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_114),B_114)
      | k1_xboole_0 = B_114 ) ),
    inference(resolution,[status(thm)],[c_542,c_586])).

tff(c_30,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_84,plain,(
    ! [A_45,B_46,C_47] :
      ( r2_hidden(k4_tarski(A_45,B_46),C_47)
      | ~ r2_hidden(B_46,k11_relat_1(C_47,A_45))
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_93,plain,(
    ! [A_48,C_49,B_50] :
      ( r2_hidden(A_48,k1_relat_1(C_49))
      | ~ r2_hidden(B_50,k11_relat_1(C_49,A_48))
      | ~ v1_relat_1(C_49) ) ),
    inference(resolution,[status(thm)],[c_84,c_12])).

tff(c_106,plain,(
    ! [A_51,C_52,A_53] :
      ( r2_hidden(A_51,k1_relat_1(C_52))
      | ~ v1_relat_1(C_52)
      | r1_xboole_0(A_53,k11_relat_1(C_52,A_51)) ) ),
    inference(resolution,[status(thm)],[c_4,c_93])).

tff(c_113,plain,(
    ! [A_53] :
      ( ~ v1_relat_1('#skF_7')
      | r1_xboole_0(A_53,k11_relat_1('#skF_7','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_106,c_48])).

tff(c_124,plain,(
    ! [A_54] : r1_xboole_0(A_54,k11_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_113])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_127,plain,(
    ! [C_5,A_54] :
      ( ~ r2_hidden(C_5,k11_relat_1('#skF_7','#skF_6'))
      | ~ r2_hidden(C_5,A_54) ) ),
    inference(resolution,[status(thm)],[c_124,c_2])).

tff(c_686,plain,(
    ! [A_54] :
      ( ~ r2_hidden('#skF_4'(k1_xboole_0,k11_relat_1('#skF_7','#skF_6')),A_54)
      | k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_671,c_127])).

tff(c_705,plain,(
    ! [A_115] : ~ r2_hidden('#skF_4'(k1_xboole_0,k11_relat_1('#skF_7','#skF_6')),A_115) ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_686])).

tff(c_709,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_604,c_705])).

tff(c_731,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_709])).

tff(c_733,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_732,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_861,plain,(
    ! [C_148,A_149] :
      ( r2_hidden(k4_tarski(C_148,'#skF_5'(A_149,k1_relat_1(A_149),C_148)),A_149)
      | ~ r2_hidden(C_148,k1_relat_1(A_149)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [B_27,C_28,A_26] :
      ( r2_hidden(B_27,k11_relat_1(C_28,A_26))
      | ~ r2_hidden(k4_tarski(A_26,B_27),C_28)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1199,plain,(
    ! [A_187,C_188] :
      ( r2_hidden('#skF_5'(A_187,k1_relat_1(A_187),C_188),k11_relat_1(A_187,C_188))
      | ~ v1_relat_1(A_187)
      | ~ r2_hidden(C_188,k1_relat_1(A_187)) ) ),
    inference(resolution,[status(thm)],[c_861,c_24])).

tff(c_1204,plain,
    ( r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0)
    | ~ v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_732,c_1199])).

tff(c_1210,plain,(
    r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_733,c_30,c_1204])).

tff(c_742,plain,(
    ! [A_120,B_121,C_122] :
      ( ~ r1_xboole_0(A_120,B_121)
      | ~ r2_hidden(C_122,B_121)
      | ~ r2_hidden(C_122,A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_745,plain,(
    ! [C_122,A_6] :
      ( ~ r2_hidden(C_122,k1_xboole_0)
      | ~ r2_hidden(C_122,A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_742])).

tff(c_1214,plain,(
    ! [A_6] : ~ r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),A_6) ),
    inference(resolution,[status(thm)],[c_1210,c_745])).

tff(c_1216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1214,c_1210])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.52  
% 3.18/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.53  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 3.32/1.53  
% 3.32/1.53  %Foreground sorts:
% 3.32/1.53  
% 3.32/1.53  
% 3.32/1.53  %Background operators:
% 3.32/1.53  
% 3.32/1.53  
% 3.32/1.53  %Foreground operators:
% 3.32/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.53  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.32/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.32/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.32/1.53  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.32/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.32/1.53  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.32/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.32/1.53  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.32/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.32/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.32/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.32/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.32/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.32/1.53  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.32/1.53  
% 3.35/1.55  tff(f_70, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 3.35/1.55  tff(f_62, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.35/1.55  tff(f_53, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.35/1.55  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.35/1.55  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.35/1.55  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 3.35/1.55  tff(c_32, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0 | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.35/1.55  tff(c_48, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_32])).
% 3.35/1.55  tff(c_38, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7')) | k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.35/1.55  tff(c_49, plain, (k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_48, c_38])).
% 3.35/1.55  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.35/1.55  tff(c_455, plain, (![A_105, B_106]: (r2_hidden(k4_tarski('#skF_2'(A_105, B_106), '#skF_3'(A_105, B_106)), A_105) | r2_hidden('#skF_4'(A_105, B_106), B_106) | k1_relat_1(A_105)=B_106)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.35/1.55  tff(c_12, plain, (![C_22, A_7, D_25]: (r2_hidden(C_22, k1_relat_1(A_7)) | ~r2_hidden(k4_tarski(C_22, D_25), A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.35/1.55  tff(c_492, plain, (![A_107, B_108]: (r2_hidden('#skF_2'(A_107, B_108), k1_relat_1(A_107)) | r2_hidden('#skF_4'(A_107, B_108), B_108) | k1_relat_1(A_107)=B_108)), inference(resolution, [status(thm)], [c_455, c_12])).
% 3.35/1.55  tff(c_531, plain, (![B_108]: (r2_hidden('#skF_2'(k1_xboole_0, B_108), k1_xboole_0) | r2_hidden('#skF_4'(k1_xboole_0, B_108), B_108) | k1_relat_1(k1_xboole_0)=B_108)), inference(superposition, [status(thm), theory('equality')], [c_28, c_492])).
% 3.35/1.55  tff(c_542, plain, (![B_108]: (r2_hidden('#skF_2'(k1_xboole_0, B_108), k1_xboole_0) | r2_hidden('#skF_4'(k1_xboole_0, B_108), B_108) | k1_xboole_0=B_108)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_531])).
% 3.35/1.55  tff(c_543, plain, (![B_109]: (r2_hidden('#skF_2'(k1_xboole_0, B_109), k1_xboole_0) | r2_hidden('#skF_4'(k1_xboole_0, B_109), B_109) | k1_xboole_0=B_109)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_531])).
% 3.35/1.55  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.35/1.55  tff(c_53, plain, (![A_37, B_38, C_39]: (~r1_xboole_0(A_37, B_38) | ~r2_hidden(C_39, B_38) | ~r2_hidden(C_39, A_37))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.35/1.55  tff(c_56, plain, (![C_39, A_6]: (~r2_hidden(C_39, k1_xboole_0) | ~r2_hidden(C_39, A_6))), inference(resolution, [status(thm)], [c_8, c_53])).
% 3.35/1.55  tff(c_586, plain, (![B_110, A_111]: (~r2_hidden('#skF_2'(k1_xboole_0, B_110), A_111) | r2_hidden('#skF_4'(k1_xboole_0, B_110), B_110) | k1_xboole_0=B_110)), inference(resolution, [status(thm)], [c_543, c_56])).
% 3.35/1.55  tff(c_604, plain, (![B_108]: (r2_hidden('#skF_4'(k1_xboole_0, B_108), B_108) | k1_xboole_0=B_108)), inference(resolution, [status(thm)], [c_542, c_586])).
% 3.35/1.55  tff(c_671, plain, (![B_114]: (r2_hidden('#skF_4'(k1_xboole_0, B_114), B_114) | k1_xboole_0=B_114)), inference(resolution, [status(thm)], [c_542, c_586])).
% 3.35/1.55  tff(c_30, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.35/1.55  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.35/1.55  tff(c_84, plain, (![A_45, B_46, C_47]: (r2_hidden(k4_tarski(A_45, B_46), C_47) | ~r2_hidden(B_46, k11_relat_1(C_47, A_45)) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.35/1.55  tff(c_93, plain, (![A_48, C_49, B_50]: (r2_hidden(A_48, k1_relat_1(C_49)) | ~r2_hidden(B_50, k11_relat_1(C_49, A_48)) | ~v1_relat_1(C_49))), inference(resolution, [status(thm)], [c_84, c_12])).
% 3.35/1.55  tff(c_106, plain, (![A_51, C_52, A_53]: (r2_hidden(A_51, k1_relat_1(C_52)) | ~v1_relat_1(C_52) | r1_xboole_0(A_53, k11_relat_1(C_52, A_51)))), inference(resolution, [status(thm)], [c_4, c_93])).
% 3.35/1.55  tff(c_113, plain, (![A_53]: (~v1_relat_1('#skF_7') | r1_xboole_0(A_53, k11_relat_1('#skF_7', '#skF_6')))), inference(resolution, [status(thm)], [c_106, c_48])).
% 3.35/1.55  tff(c_124, plain, (![A_54]: (r1_xboole_0(A_54, k11_relat_1('#skF_7', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_113])).
% 3.35/1.55  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.35/1.55  tff(c_127, plain, (![C_5, A_54]: (~r2_hidden(C_5, k11_relat_1('#skF_7', '#skF_6')) | ~r2_hidden(C_5, A_54))), inference(resolution, [status(thm)], [c_124, c_2])).
% 3.35/1.55  tff(c_686, plain, (![A_54]: (~r2_hidden('#skF_4'(k1_xboole_0, k11_relat_1('#skF_7', '#skF_6')), A_54) | k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0)), inference(resolution, [status(thm)], [c_671, c_127])).
% 3.35/1.55  tff(c_705, plain, (![A_115]: (~r2_hidden('#skF_4'(k1_xboole_0, k11_relat_1('#skF_7', '#skF_6')), A_115))), inference(negUnitSimplification, [status(thm)], [c_49, c_686])).
% 3.35/1.55  tff(c_709, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_604, c_705])).
% 3.35/1.55  tff(c_731, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_709])).
% 3.35/1.55  tff(c_733, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_32])).
% 3.35/1.55  tff(c_732, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 3.35/1.55  tff(c_861, plain, (![C_148, A_149]: (r2_hidden(k4_tarski(C_148, '#skF_5'(A_149, k1_relat_1(A_149), C_148)), A_149) | ~r2_hidden(C_148, k1_relat_1(A_149)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.35/1.55  tff(c_24, plain, (![B_27, C_28, A_26]: (r2_hidden(B_27, k11_relat_1(C_28, A_26)) | ~r2_hidden(k4_tarski(A_26, B_27), C_28) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.35/1.55  tff(c_1199, plain, (![A_187, C_188]: (r2_hidden('#skF_5'(A_187, k1_relat_1(A_187), C_188), k11_relat_1(A_187, C_188)) | ~v1_relat_1(A_187) | ~r2_hidden(C_188, k1_relat_1(A_187)))), inference(resolution, [status(thm)], [c_861, c_24])).
% 3.35/1.55  tff(c_1204, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0) | ~v1_relat_1('#skF_7') | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_732, c_1199])).
% 3.35/1.55  tff(c_1210, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_733, c_30, c_1204])).
% 3.35/1.55  tff(c_742, plain, (![A_120, B_121, C_122]: (~r1_xboole_0(A_120, B_121) | ~r2_hidden(C_122, B_121) | ~r2_hidden(C_122, A_120))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.35/1.55  tff(c_745, plain, (![C_122, A_6]: (~r2_hidden(C_122, k1_xboole_0) | ~r2_hidden(C_122, A_6))), inference(resolution, [status(thm)], [c_8, c_742])).
% 3.35/1.55  tff(c_1214, plain, (![A_6]: (~r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), A_6))), inference(resolution, [status(thm)], [c_1210, c_745])).
% 3.35/1.55  tff(c_1216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1214, c_1210])).
% 3.35/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.55  
% 3.35/1.55  Inference rules
% 3.35/1.55  ----------------------
% 3.35/1.55  #Ref     : 0
% 3.35/1.55  #Sup     : 244
% 3.35/1.55  #Fact    : 0
% 3.35/1.55  #Define  : 0
% 3.35/1.55  #Split   : 6
% 3.35/1.55  #Chain   : 0
% 3.35/1.55  #Close   : 0
% 3.35/1.55  
% 3.35/1.55  Ordering : KBO
% 3.35/1.55  
% 3.35/1.55  Simplification rules
% 3.35/1.55  ----------------------
% 3.35/1.55  #Subsume      : 36
% 3.35/1.55  #Demod        : 70
% 3.35/1.55  #Tautology    : 42
% 3.35/1.55  #SimpNegUnit  : 7
% 3.35/1.55  #BackRed      : 1
% 3.35/1.55  
% 3.35/1.55  #Partial instantiations: 0
% 3.35/1.55  #Strategies tried      : 1
% 3.35/1.55  
% 3.35/1.55  Timing (in seconds)
% 3.35/1.55  ----------------------
% 3.35/1.55  Preprocessing        : 0.29
% 3.35/1.55  Parsing              : 0.15
% 3.35/1.55  CNF conversion       : 0.02
% 3.35/1.56  Main loop            : 0.49
% 3.35/1.56  Inferencing          : 0.20
% 3.35/1.56  Reduction            : 0.12
% 3.35/1.56  Demodulation         : 0.07
% 3.35/1.56  BG Simplification    : 0.02
% 3.35/1.56  Subsumption          : 0.11
% 3.35/1.56  Abstraction          : 0.02
% 3.35/1.56  MUC search           : 0.00
% 3.35/1.56  Cooper               : 0.00
% 3.35/1.56  Total                : 0.82
% 3.35/1.56  Index Insertion      : 0.00
% 3.35/1.56  Index Deletion       : 0.00
% 3.35/1.56  Index Matching       : 0.00
% 3.35/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
