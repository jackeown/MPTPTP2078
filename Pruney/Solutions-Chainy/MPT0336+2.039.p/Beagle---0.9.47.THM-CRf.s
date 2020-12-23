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
% DateTime   : Thu Dec  3 09:55:05 EST 2020

% Result     : Theorem 6.29s
% Output     : CNFRefutation 6.29s
% Verified   : 
% Statistics : Number of formulae       :   68 (  94 expanded)
%              Number of leaves         :   31 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :   78 ( 133 expanded)
%              Number of equality atoms :   34 (  55 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_57,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_53,axiom,(
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

tff(c_54,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_318,plain,(
    ! [B_65,A_66] :
      ( k1_tarski(B_65) = A_66
      | k1_xboole_0 = A_66
      | ~ r1_tarski(A_66,k1_tarski(B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_328,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_7')
    | k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_318])).

tff(c_477,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_328])).

tff(c_132,plain,(
    ! [A_48,B_49] :
      ( r1_xboole_0(A_48,B_49)
      | k3_xboole_0(A_48,B_49) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_138,plain,(
    ! [B_49,A_48] :
      ( r1_xboole_0(B_49,A_48)
      | k3_xboole_0(A_48,B_49) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_132,c_8])).

tff(c_50,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_141,plain,(
    ! [A_50,B_51] :
      ( k3_xboole_0(A_50,B_51) = k1_xboole_0
      | ~ r1_xboole_0(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_160,plain,(
    k3_xboole_0('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_141])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_873,plain,(
    ! [A_90,B_91,C_92] :
      ( k3_xboole_0(A_90,k2_xboole_0(B_91,C_92)) = k3_xboole_0(A_90,C_92)
      | ~ r1_xboole_0(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_48,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_137,plain,(
    k3_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_132,c_48])).

tff(c_140,plain,(
    k3_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_6')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_137])).

tff(c_912,plain,
    ( k3_xboole_0('#skF_5','#skF_6') != k1_xboole_0
    | ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_873,c_140])).

tff(c_952,plain,(
    ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_2,c_912])).

tff(c_959,plain,(
    k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_138,c_952])).

tff(c_966,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_959])).

tff(c_967,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_328])).

tff(c_18,plain,(
    ! [A_15] : r1_xboole_0(A_15,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_74,plain,(
    ! [B_41,A_42] :
      ( r1_xboole_0(B_41,A_42)
      | ~ r1_xboole_0(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_80,plain,(
    ! [A_15] : r1_xboole_0(k1_xboole_0,A_15) ),
    inference(resolution,[status(thm)],[c_18,c_74])).

tff(c_158,plain,(
    ! [A_15] : k3_xboole_0(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80,c_141])).

tff(c_361,plain,(
    ! [A_73,B_74,C_75] : k3_xboole_0(k3_xboole_0(A_73,B_74),C_75) = k3_xboole_0(A_73,k3_xboole_0(B_74,C_75)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_401,plain,(
    ! [C_75] : k3_xboole_0('#skF_6',k3_xboole_0('#skF_5',C_75)) = k3_xboole_0(k1_xboole_0,C_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_361])).

tff(c_448,plain,(
    ! [C_79] : k3_xboole_0('#skF_6',k3_xboole_0('#skF_5',C_79)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_401])).

tff(c_1035,plain,(
    ! [B_94] : k3_xboole_0('#skF_6',k3_xboole_0(B_94,'#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_448])).

tff(c_1049,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_7')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_967,c_1035])).

tff(c_24,plain,(
    ! [C_23] : r2_hidden(C_23,k1_tarski(C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_52,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_342,plain,(
    ! [A_70,B_71,C_72] :
      ( ~ r1_xboole_0(A_70,B_71)
      | ~ r2_hidden(C_72,B_71)
      | ~ r2_hidden(C_72,A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6915,plain,(
    ! [C_169,B_170,A_171] :
      ( ~ r2_hidden(C_169,B_170)
      | ~ r2_hidden(C_169,A_171)
      | k3_xboole_0(A_171,B_170) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_342])).

tff(c_6934,plain,(
    ! [A_172] :
      ( ~ r2_hidden('#skF_7',A_172)
      | k3_xboole_0(A_172,'#skF_6') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_6915])).

tff(c_6938,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),'#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_6934])).

tff(c_6945,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1049,c_2,c_6938])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:14:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.29/2.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.29/2.32  
% 6.29/2.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.29/2.33  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 6.29/2.33  
% 6.29/2.33  %Foreground sorts:
% 6.29/2.33  
% 6.29/2.33  
% 6.29/2.33  %Background operators:
% 6.29/2.33  
% 6.29/2.33  
% 6.29/2.33  %Foreground operators:
% 6.29/2.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.29/2.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.29/2.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.29/2.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.29/2.33  tff('#skF_7', type, '#skF_7': $i).
% 6.29/2.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.29/2.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.29/2.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.29/2.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.29/2.33  tff('#skF_5', type, '#skF_5': $i).
% 6.29/2.33  tff('#skF_6', type, '#skF_6': $i).
% 6.29/2.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.29/2.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.29/2.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.29/2.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.29/2.33  tff('#skF_4', type, '#skF_4': $i).
% 6.29/2.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.29/2.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.29/2.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.29/2.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.29/2.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.29/2.33  
% 6.29/2.34  tff(f_91, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 6.29/2.34  tff(f_80, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 6.29/2.34  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.29/2.34  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 6.29/2.34  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.29/2.34  tff(f_61, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 6.29/2.34  tff(f_57, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 6.29/2.34  tff(f_55, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 6.29/2.34  tff(f_68, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 6.29/2.34  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.29/2.34  tff(c_54, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.29/2.34  tff(c_318, plain, (![B_65, A_66]: (k1_tarski(B_65)=A_66 | k1_xboole_0=A_66 | ~r1_tarski(A_66, k1_tarski(B_65)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.29/2.34  tff(c_328, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_7') | k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_318])).
% 6.29/2.34  tff(c_477, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_328])).
% 6.29/2.34  tff(c_132, plain, (![A_48, B_49]: (r1_xboole_0(A_48, B_49) | k3_xboole_0(A_48, B_49)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.29/2.34  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.29/2.34  tff(c_138, plain, (![B_49, A_48]: (r1_xboole_0(B_49, A_48) | k3_xboole_0(A_48, B_49)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_132, c_8])).
% 6.29/2.34  tff(c_50, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.29/2.34  tff(c_141, plain, (![A_50, B_51]: (k3_xboole_0(A_50, B_51)=k1_xboole_0 | ~r1_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.29/2.34  tff(c_160, plain, (k3_xboole_0('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_141])).
% 6.29/2.34  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.29/2.34  tff(c_873, plain, (![A_90, B_91, C_92]: (k3_xboole_0(A_90, k2_xboole_0(B_91, C_92))=k3_xboole_0(A_90, C_92) | ~r1_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.29/2.34  tff(c_48, plain, (~r1_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.29/2.34  tff(c_137, plain, (k3_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_132, c_48])).
% 6.29/2.34  tff(c_140, plain, (k3_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_6'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_137])).
% 6.29/2.34  tff(c_912, plain, (k3_xboole_0('#skF_5', '#skF_6')!=k1_xboole_0 | ~r1_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_873, c_140])).
% 6.29/2.34  tff(c_952, plain, (~r1_xboole_0('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_2, c_912])).
% 6.29/2.34  tff(c_959, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_138, c_952])).
% 6.29/2.34  tff(c_966, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_477, c_959])).
% 6.29/2.34  tff(c_967, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_328])).
% 6.29/2.34  tff(c_18, plain, (![A_15]: (r1_xboole_0(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.29/2.34  tff(c_74, plain, (![B_41, A_42]: (r1_xboole_0(B_41, A_42) | ~r1_xboole_0(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.29/2.34  tff(c_80, plain, (![A_15]: (r1_xboole_0(k1_xboole_0, A_15))), inference(resolution, [status(thm)], [c_18, c_74])).
% 6.29/2.34  tff(c_158, plain, (![A_15]: (k3_xboole_0(k1_xboole_0, A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_80, c_141])).
% 6.29/2.34  tff(c_361, plain, (![A_73, B_74, C_75]: (k3_xboole_0(k3_xboole_0(A_73, B_74), C_75)=k3_xboole_0(A_73, k3_xboole_0(B_74, C_75)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.29/2.34  tff(c_401, plain, (![C_75]: (k3_xboole_0('#skF_6', k3_xboole_0('#skF_5', C_75))=k3_xboole_0(k1_xboole_0, C_75))), inference(superposition, [status(thm), theory('equality')], [c_160, c_361])).
% 6.29/2.34  tff(c_448, plain, (![C_79]: (k3_xboole_0('#skF_6', k3_xboole_0('#skF_5', C_79))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_158, c_401])).
% 6.29/2.34  tff(c_1035, plain, (![B_94]: (k3_xboole_0('#skF_6', k3_xboole_0(B_94, '#skF_5'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_448])).
% 6.29/2.34  tff(c_1049, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_7'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_967, c_1035])).
% 6.29/2.34  tff(c_24, plain, (![C_23]: (r2_hidden(C_23, k1_tarski(C_23)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.29/2.34  tff(c_52, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.29/2.34  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.29/2.34  tff(c_342, plain, (![A_70, B_71, C_72]: (~r1_xboole_0(A_70, B_71) | ~r2_hidden(C_72, B_71) | ~r2_hidden(C_72, A_70))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.29/2.34  tff(c_6915, plain, (![C_169, B_170, A_171]: (~r2_hidden(C_169, B_170) | ~r2_hidden(C_169, A_171) | k3_xboole_0(A_171, B_170)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_342])).
% 6.29/2.34  tff(c_6934, plain, (![A_172]: (~r2_hidden('#skF_7', A_172) | k3_xboole_0(A_172, '#skF_6')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_6915])).
% 6.29/2.34  tff(c_6938, plain, (k3_xboole_0(k1_tarski('#skF_7'), '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_6934])).
% 6.29/2.34  tff(c_6945, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1049, c_2, c_6938])).
% 6.29/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.29/2.34  
% 6.29/2.34  Inference rules
% 6.29/2.34  ----------------------
% 6.29/2.34  #Ref     : 0
% 6.29/2.34  #Sup     : 1752
% 6.29/2.34  #Fact    : 0
% 6.29/2.34  #Define  : 0
% 6.29/2.34  #Split   : 1
% 6.29/2.34  #Chain   : 0
% 6.29/2.34  #Close   : 0
% 6.29/2.34  
% 6.29/2.34  Ordering : KBO
% 6.29/2.34  
% 6.29/2.34  Simplification rules
% 6.29/2.34  ----------------------
% 6.29/2.34  #Subsume      : 23
% 6.29/2.34  #Demod        : 1889
% 6.29/2.34  #Tautology    : 1322
% 6.29/2.34  #SimpNegUnit  : 0
% 6.29/2.34  #BackRed      : 5
% 6.29/2.34  
% 6.29/2.34  #Partial instantiations: 0
% 6.29/2.34  #Strategies tried      : 1
% 6.29/2.34  
% 6.29/2.34  Timing (in seconds)
% 6.29/2.34  ----------------------
% 6.29/2.34  Preprocessing        : 0.33
% 6.29/2.34  Parsing              : 0.17
% 6.29/2.34  CNF conversion       : 0.02
% 6.29/2.34  Main loop            : 1.25
% 6.29/2.34  Inferencing          : 0.34
% 6.29/2.34  Reduction            : 0.66
% 6.29/2.34  Demodulation         : 0.57
% 6.29/2.34  BG Simplification    : 0.04
% 6.29/2.34  Subsumption          : 0.16
% 6.29/2.34  Abstraction          : 0.05
% 6.29/2.34  MUC search           : 0.00
% 6.29/2.34  Cooper               : 0.00
% 6.29/2.34  Total                : 1.61
% 6.29/2.34  Index Insertion      : 0.00
% 6.29/2.34  Index Deletion       : 0.00
% 6.29/2.34  Index Matching       : 0.00
% 6.29/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
