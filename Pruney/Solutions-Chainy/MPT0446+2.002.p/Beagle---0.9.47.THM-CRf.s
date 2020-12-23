%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:26 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   71 (  85 expanded)
%              Number of leaves         :   42 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :   60 (  95 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_11 > #skF_3 > #skF_10 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_12 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r2_hidden(k4_tarski(A,B),C)
         => ( r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_54,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_64,plain,
    ( ~ r2_hidden('#skF_11',k3_relat_1('#skF_12'))
    | ~ r2_hidden('#skF_10',k3_relat_1('#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_144,plain,(
    ~ r2_hidden('#skF_10',k3_relat_1('#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_68,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_277,plain,(
    ! [A_121] :
      ( k2_xboole_0(k1_relat_1(A_121),k2_relat_1(A_121)) = k3_relat_1(A_121)
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_286,plain,(
    ! [A_121] :
      ( r1_tarski(k1_relat_1(A_121),k3_relat_1(A_121))
      | ~ v1_relat_1(A_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_8])).

tff(c_66,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_304,plain,(
    ! [C_128,A_129,D_130] :
      ( r2_hidden(C_128,k1_relat_1(A_129))
      | ~ r2_hidden(k4_tarski(C_128,D_130),A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_317,plain,(
    r2_hidden('#skF_10',k1_relat_1('#skF_12')) ),
    inference(resolution,[status(thm)],[c_66,c_304])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_342,plain,(
    ! [B_135] :
      ( r2_hidden('#skF_10',B_135)
      | ~ r1_tarski(k1_relat_1('#skF_12'),B_135) ) ),
    inference(resolution,[status(thm)],[c_317,c_2])).

tff(c_346,plain,
    ( r2_hidden('#skF_10',k3_relat_1('#skF_12'))
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_286,c_342])).

tff(c_365,plain,(
    r2_hidden('#skF_10',k3_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_346])).

tff(c_367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_365])).

tff(c_368,plain,(
    ~ r2_hidden('#skF_11',k3_relat_1('#skF_12')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_492,plain,(
    ! [A_158] :
      ( k2_xboole_0(k1_relat_1(A_158),k2_relat_1(A_158)) = k3_relat_1(A_158)
      | ~ v1_relat_1(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_10,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_126,plain,(
    ! [A_96,B_97] : k3_tarski(k2_tarski(A_96,B_97)) = k2_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_377,plain,(
    ! [B_142,A_143] : k3_tarski(k2_tarski(B_142,A_143)) = k2_xboole_0(A_143,B_142) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_126])).

tff(c_26,plain,(
    ! [A_39,B_40] : k3_tarski(k2_tarski(A_39,B_40)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_404,plain,(
    ! [B_146,A_147] : k2_xboole_0(B_146,A_147) = k2_xboole_0(A_147,B_146) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_26])).

tff(c_419,plain,(
    ! [A_147,B_146] : r1_tarski(A_147,k2_xboole_0(B_146,A_147)) ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_8])).

tff(c_498,plain,(
    ! [A_158] :
      ( r1_tarski(k2_relat_1(A_158),k3_relat_1(A_158))
      | ~ v1_relat_1(A_158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_419])).

tff(c_569,plain,(
    ! [C_169,A_170,D_171] :
      ( r2_hidden(C_169,k2_relat_1(A_170))
      | ~ r2_hidden(k4_tarski(D_171,C_169),A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_578,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_12')) ),
    inference(resolution,[status(thm)],[c_66,c_569])).

tff(c_687,plain,(
    ! [B_181] :
      ( r2_hidden('#skF_11',B_181)
      | ~ r1_tarski(k2_relat_1('#skF_12'),B_181) ) ),
    inference(resolution,[status(thm)],[c_578,c_2])).

tff(c_691,plain,
    ( r2_hidden('#skF_11',k3_relat_1('#skF_12'))
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_498,c_687])).

tff(c_710,plain,(
    r2_hidden('#skF_11',k3_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_691])).

tff(c_712,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_368,c_710])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:52:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.37  
% 2.77/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.37  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_11 > #skF_3 > #skF_10 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_12 > #skF_4
% 2.77/1.37  
% 2.77/1.37  %Foreground sorts:
% 2.77/1.37  
% 2.77/1.37  
% 2.77/1.37  %Background operators:
% 2.77/1.37  
% 2.77/1.37  
% 2.77/1.37  %Foreground operators:
% 2.77/1.37  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.77/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.37  tff('#skF_11', type, '#skF_11': $i).
% 2.77/1.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.77/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.77/1.37  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.77/1.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.77/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.77/1.37  tff('#skF_10', type, '#skF_10': $i).
% 2.77/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.77/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.77/1.37  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.77/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.77/1.37  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 2.77/1.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.77/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.77/1.37  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 2.77/1.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.77/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.37  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.77/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.77/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.77/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.77/1.37  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.77/1.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.77/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.77/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.77/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.77/1.37  tff('#skF_12', type, '#skF_12': $i).
% 2.77/1.37  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.77/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.37  
% 2.77/1.38  tff(f_98, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relat_1)).
% 2.77/1.38  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 2.77/1.38  tff(f_34, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.77/1.38  tff(f_77, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.77/1.38  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.77/1.38  tff(f_36, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.77/1.38  tff(f_54, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.77/1.38  tff(f_85, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 2.77/1.38  tff(c_64, plain, (~r2_hidden('#skF_11', k3_relat_1('#skF_12')) | ~r2_hidden('#skF_10', k3_relat_1('#skF_12'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.77/1.38  tff(c_144, plain, (~r2_hidden('#skF_10', k3_relat_1('#skF_12'))), inference(splitLeft, [status(thm)], [c_64])).
% 2.77/1.38  tff(c_68, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.77/1.38  tff(c_277, plain, (![A_121]: (k2_xboole_0(k1_relat_1(A_121), k2_relat_1(A_121))=k3_relat_1(A_121) | ~v1_relat_1(A_121))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.77/1.38  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.77/1.38  tff(c_286, plain, (![A_121]: (r1_tarski(k1_relat_1(A_121), k3_relat_1(A_121)) | ~v1_relat_1(A_121))), inference(superposition, [status(thm), theory('equality')], [c_277, c_8])).
% 2.77/1.38  tff(c_66, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_12')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.77/1.38  tff(c_304, plain, (![C_128, A_129, D_130]: (r2_hidden(C_128, k1_relat_1(A_129)) | ~r2_hidden(k4_tarski(C_128, D_130), A_129))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.77/1.38  tff(c_317, plain, (r2_hidden('#skF_10', k1_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_66, c_304])).
% 2.77/1.38  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.77/1.38  tff(c_342, plain, (![B_135]: (r2_hidden('#skF_10', B_135) | ~r1_tarski(k1_relat_1('#skF_12'), B_135))), inference(resolution, [status(thm)], [c_317, c_2])).
% 2.77/1.38  tff(c_346, plain, (r2_hidden('#skF_10', k3_relat_1('#skF_12')) | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_286, c_342])).
% 2.77/1.38  tff(c_365, plain, (r2_hidden('#skF_10', k3_relat_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_346])).
% 2.77/1.38  tff(c_367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_365])).
% 2.77/1.38  tff(c_368, plain, (~r2_hidden('#skF_11', k3_relat_1('#skF_12'))), inference(splitRight, [status(thm)], [c_64])).
% 2.77/1.38  tff(c_492, plain, (![A_158]: (k2_xboole_0(k1_relat_1(A_158), k2_relat_1(A_158))=k3_relat_1(A_158) | ~v1_relat_1(A_158))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.77/1.38  tff(c_10, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.77/1.38  tff(c_126, plain, (![A_96, B_97]: (k3_tarski(k2_tarski(A_96, B_97))=k2_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.77/1.38  tff(c_377, plain, (![B_142, A_143]: (k3_tarski(k2_tarski(B_142, A_143))=k2_xboole_0(A_143, B_142))), inference(superposition, [status(thm), theory('equality')], [c_10, c_126])).
% 2.77/1.38  tff(c_26, plain, (![A_39, B_40]: (k3_tarski(k2_tarski(A_39, B_40))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.77/1.38  tff(c_404, plain, (![B_146, A_147]: (k2_xboole_0(B_146, A_147)=k2_xboole_0(A_147, B_146))), inference(superposition, [status(thm), theory('equality')], [c_377, c_26])).
% 2.77/1.38  tff(c_419, plain, (![A_147, B_146]: (r1_tarski(A_147, k2_xboole_0(B_146, A_147)))), inference(superposition, [status(thm), theory('equality')], [c_404, c_8])).
% 2.77/1.38  tff(c_498, plain, (![A_158]: (r1_tarski(k2_relat_1(A_158), k3_relat_1(A_158)) | ~v1_relat_1(A_158))), inference(superposition, [status(thm), theory('equality')], [c_492, c_419])).
% 2.77/1.38  tff(c_569, plain, (![C_169, A_170, D_171]: (r2_hidden(C_169, k2_relat_1(A_170)) | ~r2_hidden(k4_tarski(D_171, C_169), A_170))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.77/1.38  tff(c_578, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_66, c_569])).
% 2.77/1.38  tff(c_687, plain, (![B_181]: (r2_hidden('#skF_11', B_181) | ~r1_tarski(k2_relat_1('#skF_12'), B_181))), inference(resolution, [status(thm)], [c_578, c_2])).
% 2.77/1.38  tff(c_691, plain, (r2_hidden('#skF_11', k3_relat_1('#skF_12')) | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_498, c_687])).
% 2.77/1.38  tff(c_710, plain, (r2_hidden('#skF_11', k3_relat_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_691])).
% 2.77/1.38  tff(c_712, plain, $false, inference(negUnitSimplification, [status(thm)], [c_368, c_710])).
% 2.77/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.38  
% 2.77/1.38  Inference rules
% 2.77/1.38  ----------------------
% 2.77/1.38  #Ref     : 0
% 2.77/1.38  #Sup     : 142
% 2.77/1.38  #Fact    : 0
% 2.77/1.38  #Define  : 0
% 2.77/1.38  #Split   : 3
% 2.77/1.38  #Chain   : 0
% 2.77/1.38  #Close   : 0
% 2.77/1.38  
% 2.77/1.38  Ordering : KBO
% 2.77/1.38  
% 2.77/1.38  Simplification rules
% 2.77/1.38  ----------------------
% 2.77/1.39  #Subsume      : 4
% 2.77/1.39  #Demod        : 28
% 2.77/1.39  #Tautology    : 70
% 2.77/1.39  #SimpNegUnit  : 4
% 2.77/1.39  #BackRed      : 0
% 2.77/1.39  
% 2.77/1.39  #Partial instantiations: 0
% 2.77/1.39  #Strategies tried      : 1
% 2.77/1.39  
% 2.77/1.39  Timing (in seconds)
% 2.77/1.39  ----------------------
% 2.77/1.39  Preprocessing        : 0.34
% 2.77/1.39  Parsing              : 0.18
% 2.77/1.39  CNF conversion       : 0.03
% 2.77/1.39  Main loop            : 0.30
% 2.77/1.39  Inferencing          : 0.11
% 2.77/1.39  Reduction            : 0.09
% 2.77/1.39  Demodulation         : 0.07
% 2.77/1.39  BG Simplification    : 0.02
% 2.77/1.39  Subsumption          : 0.05
% 2.77/1.39  Abstraction          : 0.02
% 2.77/1.39  MUC search           : 0.00
% 2.77/1.39  Cooper               : 0.00
% 2.77/1.39  Total                : 0.67
% 2.77/1.39  Index Insertion      : 0.00
% 2.77/1.39  Index Deletion       : 0.00
% 2.77/1.39  Index Matching       : 0.00
% 2.77/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
