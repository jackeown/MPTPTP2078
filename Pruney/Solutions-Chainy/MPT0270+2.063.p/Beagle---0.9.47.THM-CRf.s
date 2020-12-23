%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:00 EST 2020

% Result     : Theorem 18.20s
% Output     : CNFRefutation 18.44s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 135 expanded)
%              Number of leaves         :   24 (  57 expanded)
%              Depth                    :   11
%              Number of atoms          :   80 ( 280 expanded)
%              Number of equality atoms :   36 ( 104 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_48,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_tarski('#skF_5')
    | r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_86,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_tarski('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_50,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_74,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_196,plain,(
    ! [A_65,B_66,C_67] :
      ( ~ r2_hidden('#skF_1'(A_65,B_66,C_67),C_67)
      | r2_hidden('#skF_2'(A_65,B_66,C_67),C_67)
      | k4_xboole_0(A_65,B_66) = C_67 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_205,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2,A_1),A_1)
      | k4_xboole_0(A_1,B_2) = A_1 ) ),
    inference(resolution,[status(thm)],[c_18,c_196])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1294,plain,(
    ! [A_130,B_131,C_132] :
      ( ~ r2_hidden('#skF_1'(A_130,B_131,C_132),C_132)
      | r2_hidden('#skF_2'(A_130,B_131,C_132),B_131)
      | ~ r2_hidden('#skF_2'(A_130,B_131,C_132),A_130)
      | k4_xboole_0(A_130,B_131) = C_132 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1451,plain,(
    ! [A_138,B_139] :
      ( r2_hidden('#skF_2'(A_138,B_139,A_138),B_139)
      | ~ r2_hidden('#skF_2'(A_138,B_139,A_138),A_138)
      | k4_xboole_0(A_138,B_139) = A_138 ) ),
    inference(resolution,[status(thm)],[c_12,c_1294])).

tff(c_1474,plain,(
    ! [A_140,B_141] :
      ( r2_hidden('#skF_2'(A_140,B_141,A_140),B_141)
      | k4_xboole_0(A_140,B_141) = A_140 ) ),
    inference(resolution,[status(thm)],[c_205,c_1451])).

tff(c_40,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_105,plain,(
    ! [D_44,B_45,A_46] :
      ( D_44 = B_45
      | D_44 = A_46
      | ~ r2_hidden(D_44,k2_tarski(A_46,B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_114,plain,(
    ! [D_44,A_15] :
      ( D_44 = A_15
      | D_44 = A_15
      | ~ r2_hidden(D_44,k1_tarski(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_105])).

tff(c_12819,plain,(
    ! [A_306,A_307] :
      ( '#skF_2'(A_306,k1_tarski(A_307),A_306) = A_307
      | k4_xboole_0(A_306,k1_tarski(A_307)) = A_306 ) ),
    inference(resolution,[status(thm)],[c_1474,c_114])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1954,plain,(
    ! [A_147,A_148,B_149] :
      ( ~ r2_hidden('#skF_2'(A_147,k4_xboole_0(A_148,B_149),A_147),B_149)
      | k4_xboole_0(A_147,k4_xboole_0(A_148,B_149)) = A_147 ) ),
    inference(resolution,[status(thm)],[c_1474,c_4])).

tff(c_2014,plain,(
    ! [A_1,A_148] : k4_xboole_0(A_1,k4_xboole_0(A_148,A_1)) = A_1 ),
    inference(resolution,[status(thm)],[c_205,c_1954])).

tff(c_45301,plain,(
    ! [A_5622,A_5623] :
      ( k4_xboole_0(k1_tarski(A_5622),A_5623) = k1_tarski(A_5622)
      | '#skF_2'(A_5623,k1_tarski(A_5622),A_5623) = A_5622 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12819,c_2014])).

tff(c_45872,plain,(
    '#skF_2'('#skF_6',k1_tarski('#skF_5'),'#skF_6') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_45301,c_86])).

tff(c_45909,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_45872,c_205])).

tff(c_45920,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_45909])).

tff(c_46169,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_45920,c_2014])).

tff(c_46267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_46169])).

tff(c_46268,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_64,plain,(
    ! [D_26,A_27] : r2_hidden(D_26,k2_tarski(A_27,D_26)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_67,plain,(
    ! [A_15] : r2_hidden(A_15,k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_64])).

tff(c_46269,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_52,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_tarski('#skF_5')
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_46305,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46269,c_52])).

tff(c_46316,plain,(
    ! [D_5729] :
      ( ~ r2_hidden(D_5729,'#skF_8')
      | ~ r2_hidden(D_5729,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46305,c_4])).

tff(c_46320,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_67,c_46316])).

tff(c_46324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46268,c_46320])).

tff(c_46325,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_46326,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_54,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_46348,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46326,c_54])).

tff(c_46359,plain,(
    ! [D_5740] :
      ( ~ r2_hidden(D_5740,'#skF_8')
      | ~ r2_hidden(D_5740,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46348,c_4])).

tff(c_46363,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_67,c_46359])).

tff(c_46367,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46325,c_46363])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:28:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.20/7.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.44/7.62  
% 18.44/7.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.44/7.63  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3
% 18.44/7.63  
% 18.44/7.63  %Foreground sorts:
% 18.44/7.63  
% 18.44/7.63  
% 18.44/7.63  %Background operators:
% 18.44/7.63  
% 18.44/7.63  
% 18.44/7.63  %Foreground operators:
% 18.44/7.63  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 18.44/7.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.44/7.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.44/7.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 18.44/7.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.44/7.63  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 18.44/7.63  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 18.44/7.63  tff('#skF_7', type, '#skF_7': $i).
% 18.44/7.63  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 18.44/7.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 18.44/7.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.44/7.63  tff('#skF_5', type, '#skF_5': $i).
% 18.44/7.63  tff('#skF_6', type, '#skF_6': $i).
% 18.44/7.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 18.44/7.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 18.44/7.63  tff('#skF_8', type, '#skF_8': $i).
% 18.44/7.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.44/7.63  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 18.44/7.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.44/7.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.44/7.63  
% 18.44/7.64  tff(f_60, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 18.44/7.64  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 18.44/7.64  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 18.44/7.64  tff(f_46, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 18.44/7.64  tff(c_48, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_tarski('#skF_5') | r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_60])).
% 18.44/7.64  tff(c_86, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_tarski('#skF_5')), inference(splitLeft, [status(thm)], [c_48])).
% 18.44/7.64  tff(c_50, plain, (~r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_60])).
% 18.44/7.64  tff(c_74, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_50])).
% 18.44/7.64  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 18.44/7.64  tff(c_196, plain, (![A_65, B_66, C_67]: (~r2_hidden('#skF_1'(A_65, B_66, C_67), C_67) | r2_hidden('#skF_2'(A_65, B_66, C_67), C_67) | k4_xboole_0(A_65, B_66)=C_67)), inference(cnfTransformation, [status(thm)], [f_35])).
% 18.44/7.64  tff(c_205, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2, A_1), A_1) | k4_xboole_0(A_1, B_2)=A_1)), inference(resolution, [status(thm)], [c_18, c_196])).
% 18.44/7.64  tff(c_12, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 18.44/7.64  tff(c_1294, plain, (![A_130, B_131, C_132]: (~r2_hidden('#skF_1'(A_130, B_131, C_132), C_132) | r2_hidden('#skF_2'(A_130, B_131, C_132), B_131) | ~r2_hidden('#skF_2'(A_130, B_131, C_132), A_130) | k4_xboole_0(A_130, B_131)=C_132)), inference(cnfTransformation, [status(thm)], [f_35])).
% 18.44/7.64  tff(c_1451, plain, (![A_138, B_139]: (r2_hidden('#skF_2'(A_138, B_139, A_138), B_139) | ~r2_hidden('#skF_2'(A_138, B_139, A_138), A_138) | k4_xboole_0(A_138, B_139)=A_138)), inference(resolution, [status(thm)], [c_12, c_1294])).
% 18.44/7.64  tff(c_1474, plain, (![A_140, B_141]: (r2_hidden('#skF_2'(A_140, B_141, A_140), B_141) | k4_xboole_0(A_140, B_141)=A_140)), inference(resolution, [status(thm)], [c_205, c_1451])).
% 18.44/7.64  tff(c_40, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 18.44/7.64  tff(c_105, plain, (![D_44, B_45, A_46]: (D_44=B_45 | D_44=A_46 | ~r2_hidden(D_44, k2_tarski(A_46, B_45)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 18.44/7.64  tff(c_114, plain, (![D_44, A_15]: (D_44=A_15 | D_44=A_15 | ~r2_hidden(D_44, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_105])).
% 18.44/7.64  tff(c_12819, plain, (![A_306, A_307]: ('#skF_2'(A_306, k1_tarski(A_307), A_306)=A_307 | k4_xboole_0(A_306, k1_tarski(A_307))=A_306)), inference(resolution, [status(thm)], [c_1474, c_114])).
% 18.44/7.64  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 18.44/7.64  tff(c_1954, plain, (![A_147, A_148, B_149]: (~r2_hidden('#skF_2'(A_147, k4_xboole_0(A_148, B_149), A_147), B_149) | k4_xboole_0(A_147, k4_xboole_0(A_148, B_149))=A_147)), inference(resolution, [status(thm)], [c_1474, c_4])).
% 18.44/7.64  tff(c_2014, plain, (![A_1, A_148]: (k4_xboole_0(A_1, k4_xboole_0(A_148, A_1))=A_1)), inference(resolution, [status(thm)], [c_205, c_1954])).
% 18.44/7.64  tff(c_45301, plain, (![A_5622, A_5623]: (k4_xboole_0(k1_tarski(A_5622), A_5623)=k1_tarski(A_5622) | '#skF_2'(A_5623, k1_tarski(A_5622), A_5623)=A_5622)), inference(superposition, [status(thm), theory('equality')], [c_12819, c_2014])).
% 18.44/7.64  tff(c_45872, plain, ('#skF_2'('#skF_6', k1_tarski('#skF_5'), '#skF_6')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_45301, c_86])).
% 18.44/7.64  tff(c_45909, plain, (r2_hidden('#skF_5', '#skF_6') | k4_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_45872, c_205])).
% 18.44/7.64  tff(c_45920, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_74, c_45909])).
% 18.44/7.64  tff(c_46169, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_45920, c_2014])).
% 18.44/7.64  tff(c_46267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_46169])).
% 18.44/7.64  tff(c_46268, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_48])).
% 18.44/7.64  tff(c_64, plain, (![D_26, A_27]: (r2_hidden(D_26, k2_tarski(A_27, D_26)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 18.44/7.64  tff(c_67, plain, (![A_15]: (r2_hidden(A_15, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_64])).
% 18.44/7.64  tff(c_46269, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_48])).
% 18.44/7.64  tff(c_52, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_tarski('#skF_5') | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_60])).
% 18.44/7.64  tff(c_46305, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_tarski('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_46269, c_52])).
% 18.44/7.64  tff(c_46316, plain, (![D_5729]: (~r2_hidden(D_5729, '#skF_8') | ~r2_hidden(D_5729, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_46305, c_4])).
% 18.44/7.64  tff(c_46320, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_67, c_46316])).
% 18.44/7.64  tff(c_46324, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46268, c_46320])).
% 18.44/7.64  tff(c_46325, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_50])).
% 18.44/7.64  tff(c_46326, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_50])).
% 18.44/7.64  tff(c_54, plain, (~r2_hidden('#skF_5', '#skF_6') | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_60])).
% 18.44/7.64  tff(c_46348, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_tarski('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_46326, c_54])).
% 18.44/7.64  tff(c_46359, plain, (![D_5740]: (~r2_hidden(D_5740, '#skF_8') | ~r2_hidden(D_5740, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_46348, c_4])).
% 18.44/7.64  tff(c_46363, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_67, c_46359])).
% 18.44/7.64  tff(c_46367, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46325, c_46363])).
% 18.44/7.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.44/7.64  
% 18.44/7.64  Inference rules
% 18.44/7.64  ----------------------
% 18.44/7.64  #Ref     : 0
% 18.44/7.64  #Sup     : 10891
% 18.44/7.64  #Fact    : 8
% 18.44/7.64  #Define  : 0
% 18.44/7.64  #Split   : 3
% 18.44/7.64  #Chain   : 0
% 18.44/7.64  #Close   : 0
% 18.44/7.64  
% 18.44/7.64  Ordering : KBO
% 18.44/7.64  
% 18.44/7.64  Simplification rules
% 18.44/7.64  ----------------------
% 18.44/7.64  #Subsume      : 4393
% 18.44/7.64  #Demod        : 4358
% 18.44/7.64  #Tautology    : 1837
% 18.44/7.64  #SimpNegUnit  : 441
% 18.44/7.64  #BackRed      : 1
% 18.44/7.64  
% 18.44/7.64  #Partial instantiations: 2496
% 18.44/7.64  #Strategies tried      : 1
% 18.44/7.64  
% 18.44/7.64  Timing (in seconds)
% 18.44/7.64  ----------------------
% 18.44/7.64  Preprocessing        : 0.31
% 18.44/7.64  Parsing              : 0.16
% 18.44/7.64  CNF conversion       : 0.02
% 18.44/7.64  Main loop            : 6.57
% 18.44/7.64  Inferencing          : 1.41
% 18.44/7.64  Reduction            : 3.04
% 18.44/7.64  Demodulation         : 2.52
% 18.44/7.64  BG Simplification    : 0.17
% 18.44/7.64  Subsumption          : 1.60
% 18.44/7.64  Abstraction          : 0.30
% 18.44/7.64  MUC search           : 0.00
% 18.44/7.64  Cooper               : 0.00
% 18.44/7.64  Total                : 6.91
% 18.44/7.64  Index Insertion      : 0.00
% 18.44/7.64  Index Deletion       : 0.00
% 18.44/7.64  Index Matching       : 0.00
% 18.44/7.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
