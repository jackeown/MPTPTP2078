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
% DateTime   : Thu Dec  3 09:52:56 EST 2020

% Result     : Theorem 21.19s
% Output     : CNFRefutation 21.19s
% Verified   : 
% Statistics : Number of formulae       :   69 (  96 expanded)
%              Number of leaves         :   27 (  45 expanded)
%              Depth                    :    6
%              Number of atoms          :   86 ( 157 expanded)
%              Number of equality atoms :   31 (  57 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_68,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_70,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_72,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_93,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_599,plain,(
    ! [A_107,B_108,C_109] :
      ( r2_hidden('#skF_1'(A_107,B_108,C_109),A_107)
      | r2_hidden('#skF_2'(A_107,B_108,C_109),C_109)
      | k4_xboole_0(A_107,B_108) = C_109 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_651,plain,(
    ! [A_107,B_108] :
      ( r2_hidden('#skF_2'(A_107,B_108,A_107),A_107)
      | k4_xboole_0(A_107,B_108) = A_107 ) ),
    inference(resolution,[status(thm)],[c_599,c_16])).

tff(c_1677,plain,(
    ! [A_168,B_169,C_170] :
      ( r2_hidden('#skF_1'(A_168,B_169,C_170),A_168)
      | r2_hidden('#skF_2'(A_168,B_169,C_170),B_169)
      | ~ r2_hidden('#skF_2'(A_168,B_169,C_170),A_168)
      | k4_xboole_0(A_168,B_169) = C_170 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18625,plain,(
    ! [A_5920,B_5921] :
      ( r2_hidden('#skF_2'(A_5920,B_5921,A_5920),B_5921)
      | ~ r2_hidden('#skF_2'(A_5920,B_5921,A_5920),A_5920)
      | k4_xboole_0(A_5920,B_5921) = A_5920 ) ),
    inference(resolution,[status(thm)],[c_1677,c_10])).

tff(c_18653,plain,(
    ! [A_107,B_108] :
      ( r2_hidden('#skF_2'(A_107,B_108,A_107),B_108)
      | k4_xboole_0(A_107,B_108) = A_107 ) ),
    inference(resolution,[status(thm)],[c_651,c_18625])).

tff(c_2056,plain,(
    ! [A_182,B_183] :
      ( r2_hidden('#skF_2'(A_182,B_183,A_182),A_182)
      | k4_xboole_0(A_182,B_183) = A_182 ) ),
    inference(resolution,[status(thm)],[c_599,c_16])).

tff(c_216,plain,(
    ! [A_72,B_73] :
      ( k4_xboole_0(A_72,k1_tarski(B_73)) = A_72
      | r2_hidden(B_73,A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_225,plain,(
    ! [D_8,B_73,A_72] :
      ( ~ r2_hidden(D_8,k1_tarski(B_73))
      | ~ r2_hidden(D_8,A_72)
      | r2_hidden(B_73,A_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_6])).

tff(c_132841,plain,(
    ! [B_35259,B_35260,A_35261] :
      ( ~ r2_hidden('#skF_2'(k1_tarski(B_35259),B_35260,k1_tarski(B_35259)),A_35261)
      | r2_hidden(B_35259,A_35261)
      | k4_xboole_0(k1_tarski(B_35259),B_35260) = k1_tarski(B_35259) ) ),
    inference(resolution,[status(thm)],[c_2056,c_225])).

tff(c_138422,plain,(
    ! [B_35321,B_35322] :
      ( r2_hidden(B_35321,B_35322)
      | k4_xboole_0(k1_tarski(B_35321),B_35322) = k1_tarski(B_35321) ) ),
    inference(resolution,[status(thm)],[c_18653,c_132841])).

tff(c_70,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_tarski('#skF_5')
    | r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_94,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_tarski('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_138629,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_138422,c_94])).

tff(c_138694,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_138629])).

tff(c_138695,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_60,plain,(
    ! [A_25] : k2_tarski(A_25,A_25) = k1_tarski(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_138738,plain,(
    ! [A_35325,B_35326] : k1_enumset1(A_35325,A_35325,B_35326) = k2_tarski(A_35325,B_35326) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_38,plain,(
    ! [E_24,A_18,B_19] : r2_hidden(E_24,k1_enumset1(A_18,B_19,E_24)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_138756,plain,(
    ! [B_35327,A_35328] : r2_hidden(B_35327,k2_tarski(A_35328,B_35327)) ),
    inference(superposition,[status(thm),theory(equality)],[c_138738,c_38])).

tff(c_138759,plain,(
    ! [A_25] : r2_hidden(A_25,k1_tarski(A_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_138756])).

tff(c_138696,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_74,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_tarski('#skF_5')
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_138800,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138696,c_74])).

tff(c_138837,plain,(
    ! [D_35342,B_35343,A_35344] :
      ( ~ r2_hidden(D_35342,B_35343)
      | ~ r2_hidden(D_35342,k4_xboole_0(A_35344,B_35343)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_138847,plain,(
    ! [D_35345] :
      ( ~ r2_hidden(D_35345,'#skF_8')
      | ~ r2_hidden(D_35345,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138800,c_138837])).

tff(c_138851,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_138759,c_138847])).

tff(c_138855,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138695,c_138851])).

tff(c_138856,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_138891,plain,(
    ! [A_35348,B_35349] : k1_enumset1(A_35348,A_35348,B_35349) = k2_tarski(A_35348,B_35349) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_138910,plain,(
    ! [B_35350,A_35351] : r2_hidden(B_35350,k2_tarski(A_35351,B_35350)) ),
    inference(superposition,[status(thm),theory(equality)],[c_138891,c_38])).

tff(c_138913,plain,(
    ! [A_25] : r2_hidden(A_25,k1_tarski(A_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_138910])).

tff(c_138857,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_76,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_138956,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138857,c_76])).

tff(c_138994,plain,(
    ! [D_35368] :
      ( ~ r2_hidden(D_35368,'#skF_8')
      | ~ r2_hidden(D_35368,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138956,c_6])).

tff(c_138998,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_138913,c_138994])).

tff(c_139002,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138856,c_138998])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:38:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.19/10.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.19/10.66  
% 21.19/10.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.19/10.67  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 21.19/10.67  
% 21.19/10.67  %Foreground sorts:
% 21.19/10.67  
% 21.19/10.67  
% 21.19/10.67  %Background operators:
% 21.19/10.67  
% 21.19/10.67  
% 21.19/10.67  %Foreground operators:
% 21.19/10.67  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 21.19/10.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.19/10.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 21.19/10.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 21.19/10.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 21.19/10.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 21.19/10.67  tff('#skF_7', type, '#skF_7': $i).
% 21.19/10.67  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 21.19/10.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.19/10.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 21.19/10.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 21.19/10.67  tff('#skF_5', type, '#skF_5': $i).
% 21.19/10.67  tff('#skF_6', type, '#skF_6': $i).
% 21.19/10.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 21.19/10.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 21.19/10.67  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 21.19/10.67  tff('#skF_8', type, '#skF_8': $i).
% 21.19/10.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.19/10.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.19/10.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 21.19/10.67  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 21.19/10.67  
% 21.19/10.68  tff(f_83, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 21.19/10.68  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 21.19/10.68  tff(f_77, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 21.19/10.68  tff(f_68, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 21.19/10.68  tff(f_70, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 21.19/10.68  tff(f_66, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 21.19/10.68  tff(c_72, plain, (~r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_83])).
% 21.19/10.68  tff(c_93, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_72])).
% 21.19/10.68  tff(c_599, plain, (![A_107, B_108, C_109]: (r2_hidden('#skF_1'(A_107, B_108, C_109), A_107) | r2_hidden('#skF_2'(A_107, B_108, C_109), C_109) | k4_xboole_0(A_107, B_108)=C_109)), inference(cnfTransformation, [status(thm)], [f_37])).
% 21.19/10.68  tff(c_16, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 21.19/10.68  tff(c_651, plain, (![A_107, B_108]: (r2_hidden('#skF_2'(A_107, B_108, A_107), A_107) | k4_xboole_0(A_107, B_108)=A_107)), inference(resolution, [status(thm)], [c_599, c_16])).
% 21.19/10.68  tff(c_1677, plain, (![A_168, B_169, C_170]: (r2_hidden('#skF_1'(A_168, B_169, C_170), A_168) | r2_hidden('#skF_2'(A_168, B_169, C_170), B_169) | ~r2_hidden('#skF_2'(A_168, B_169, C_170), A_168) | k4_xboole_0(A_168, B_169)=C_170)), inference(cnfTransformation, [status(thm)], [f_37])).
% 21.19/10.68  tff(c_10, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 21.19/10.68  tff(c_18625, plain, (![A_5920, B_5921]: (r2_hidden('#skF_2'(A_5920, B_5921, A_5920), B_5921) | ~r2_hidden('#skF_2'(A_5920, B_5921, A_5920), A_5920) | k4_xboole_0(A_5920, B_5921)=A_5920)), inference(resolution, [status(thm)], [c_1677, c_10])).
% 21.19/10.68  tff(c_18653, plain, (![A_107, B_108]: (r2_hidden('#skF_2'(A_107, B_108, A_107), B_108) | k4_xboole_0(A_107, B_108)=A_107)), inference(resolution, [status(thm)], [c_651, c_18625])).
% 21.19/10.68  tff(c_2056, plain, (![A_182, B_183]: (r2_hidden('#skF_2'(A_182, B_183, A_182), A_182) | k4_xboole_0(A_182, B_183)=A_182)), inference(resolution, [status(thm)], [c_599, c_16])).
% 21.19/10.68  tff(c_216, plain, (![A_72, B_73]: (k4_xboole_0(A_72, k1_tarski(B_73))=A_72 | r2_hidden(B_73, A_72))), inference(cnfTransformation, [status(thm)], [f_77])).
% 21.19/10.68  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 21.19/10.68  tff(c_225, plain, (![D_8, B_73, A_72]: (~r2_hidden(D_8, k1_tarski(B_73)) | ~r2_hidden(D_8, A_72) | r2_hidden(B_73, A_72))), inference(superposition, [status(thm), theory('equality')], [c_216, c_6])).
% 21.19/10.68  tff(c_132841, plain, (![B_35259, B_35260, A_35261]: (~r2_hidden('#skF_2'(k1_tarski(B_35259), B_35260, k1_tarski(B_35259)), A_35261) | r2_hidden(B_35259, A_35261) | k4_xboole_0(k1_tarski(B_35259), B_35260)=k1_tarski(B_35259))), inference(resolution, [status(thm)], [c_2056, c_225])).
% 21.19/10.68  tff(c_138422, plain, (![B_35321, B_35322]: (r2_hidden(B_35321, B_35322) | k4_xboole_0(k1_tarski(B_35321), B_35322)=k1_tarski(B_35321))), inference(resolution, [status(thm)], [c_18653, c_132841])).
% 21.19/10.68  tff(c_70, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_tarski('#skF_5') | r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_83])).
% 21.19/10.68  tff(c_94, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_tarski('#skF_5')), inference(splitLeft, [status(thm)], [c_70])).
% 21.19/10.68  tff(c_138629, plain, (r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_138422, c_94])).
% 21.19/10.68  tff(c_138694, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_138629])).
% 21.19/10.68  tff(c_138695, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_70])).
% 21.19/10.68  tff(c_60, plain, (![A_25]: (k2_tarski(A_25, A_25)=k1_tarski(A_25))), inference(cnfTransformation, [status(thm)], [f_68])).
% 21.19/10.68  tff(c_138738, plain, (![A_35325, B_35326]: (k1_enumset1(A_35325, A_35325, B_35326)=k2_tarski(A_35325, B_35326))), inference(cnfTransformation, [status(thm)], [f_70])).
% 21.19/10.68  tff(c_38, plain, (![E_24, A_18, B_19]: (r2_hidden(E_24, k1_enumset1(A_18, B_19, E_24)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 21.19/10.68  tff(c_138756, plain, (![B_35327, A_35328]: (r2_hidden(B_35327, k2_tarski(A_35328, B_35327)))), inference(superposition, [status(thm), theory('equality')], [c_138738, c_38])).
% 21.19/10.68  tff(c_138759, plain, (![A_25]: (r2_hidden(A_25, k1_tarski(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_138756])).
% 21.19/10.68  tff(c_138696, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_70])).
% 21.19/10.68  tff(c_74, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_tarski('#skF_5') | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_83])).
% 21.19/10.68  tff(c_138800, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_tarski('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_138696, c_74])).
% 21.19/10.68  tff(c_138837, plain, (![D_35342, B_35343, A_35344]: (~r2_hidden(D_35342, B_35343) | ~r2_hidden(D_35342, k4_xboole_0(A_35344, B_35343)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 21.19/10.68  tff(c_138847, plain, (![D_35345]: (~r2_hidden(D_35345, '#skF_8') | ~r2_hidden(D_35345, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_138800, c_138837])).
% 21.19/10.68  tff(c_138851, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_138759, c_138847])).
% 21.19/10.68  tff(c_138855, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138695, c_138851])).
% 21.19/10.68  tff(c_138856, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_72])).
% 21.19/10.68  tff(c_138891, plain, (![A_35348, B_35349]: (k1_enumset1(A_35348, A_35348, B_35349)=k2_tarski(A_35348, B_35349))), inference(cnfTransformation, [status(thm)], [f_70])).
% 21.19/10.68  tff(c_138910, plain, (![B_35350, A_35351]: (r2_hidden(B_35350, k2_tarski(A_35351, B_35350)))), inference(superposition, [status(thm), theory('equality')], [c_138891, c_38])).
% 21.19/10.68  tff(c_138913, plain, (![A_25]: (r2_hidden(A_25, k1_tarski(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_138910])).
% 21.19/10.68  tff(c_138857, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_72])).
% 21.19/10.68  tff(c_76, plain, (~r2_hidden('#skF_5', '#skF_6') | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_83])).
% 21.19/10.68  tff(c_138956, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_tarski('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_138857, c_76])).
% 21.19/10.68  tff(c_138994, plain, (![D_35368]: (~r2_hidden(D_35368, '#skF_8') | ~r2_hidden(D_35368, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_138956, c_6])).
% 21.19/10.68  tff(c_138998, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_138913, c_138994])).
% 21.19/10.68  tff(c_139002, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138856, c_138998])).
% 21.19/10.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.19/10.68  
% 21.19/10.68  Inference rules
% 21.19/10.68  ----------------------
% 21.19/10.68  #Ref     : 1
% 21.19/10.68  #Sup     : 22167
% 21.19/10.68  #Fact    : 22
% 21.19/10.68  #Define  : 0
% 21.19/10.68  #Split   : 7
% 21.19/10.68  #Chain   : 0
% 21.19/10.68  #Close   : 0
% 21.19/10.68  
% 21.19/10.68  Ordering : KBO
% 21.19/10.68  
% 21.19/10.68  Simplification rules
% 21.19/10.68  ----------------------
% 21.19/10.68  #Subsume      : 5973
% 21.19/10.68  #Demod        : 15325
% 21.19/10.68  #Tautology    : 4799
% 21.19/10.68  #SimpNegUnit  : 650
% 21.19/10.68  #BackRed      : 63
% 21.19/10.68  
% 21.19/10.68  #Partial instantiations: 18464
% 21.19/10.68  #Strategies tried      : 1
% 21.19/10.68  
% 21.19/10.68  Timing (in seconds)
% 21.19/10.68  ----------------------
% 21.19/10.68  Preprocessing        : 0.32
% 21.19/10.68  Parsing              : 0.16
% 21.19/10.68  CNF conversion       : 0.03
% 21.19/10.68  Main loop            : 9.56
% 21.19/10.68  Inferencing          : 2.22
% 21.19/10.68  Reduction            : 3.89
% 21.19/10.68  Demodulation         : 3.11
% 21.19/10.68  BG Simplification    : 0.34
% 21.19/10.68  Subsumption          : 2.33
% 21.19/10.68  Abstraction          : 0.57
% 21.19/10.68  MUC search           : 0.00
% 21.19/10.68  Cooper               : 0.00
% 21.19/10.68  Total                : 9.90
% 21.19/10.68  Index Insertion      : 0.00
% 21.19/10.68  Index Deletion       : 0.00
% 21.19/10.68  Index Matching       : 0.00
% 21.19/10.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
