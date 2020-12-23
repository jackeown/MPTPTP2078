%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:00 EST 2020

% Result     : Theorem 45.75s
% Output     : CNFRefutation 45.75s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 137 expanded)
%              Number of leaves         :   32 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :   93 ( 189 expanded)
%              Number of equality atoms :   30 (  61 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_94,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_51,axiom,(
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

tff(c_54,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_141,plain,(
    ! [B_52,A_53] :
      ( r1_xboole_0(B_52,A_53)
      | ~ r1_xboole_0(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_150,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_141])).

tff(c_182,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(A_61,B_62) = A_61
      | ~ r1_xboole_0(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_206,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_150,c_182])).

tff(c_2237,plain,(
    ! [A_158,B_159,C_160] : k4_xboole_0(k4_xboole_0(A_158,B_159),C_160) = k4_xboole_0(A_158,k2_xboole_0(B_159,C_160)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2337,plain,(
    ! [C_160] : k4_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_160)) = k4_xboole_0('#skF_3',C_160) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_2237])).

tff(c_174,plain,(
    ! [A_59,B_60] :
      ( r1_xboole_0(A_59,B_60)
      | k4_xboole_0(A_59,B_60) != A_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_560,plain,(
    ! [B_87,A_88] :
      ( r1_xboole_0(B_87,A_88)
      | k4_xboole_0(A_88,B_87) != A_88 ) ),
    inference(resolution,[status(thm)],[c_174,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_52,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_61,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_4','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_52])).

tff(c_571,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_2')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_560,c_61])).

tff(c_11669,plain,(
    k4_xboole_0('#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2337,c_571])).

tff(c_210,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_54,c_182])).

tff(c_50,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(A_39,k1_tarski(B_40)) = A_39
      | r2_hidden(B_40,A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_60,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_58])).

tff(c_346,plain,(
    ! [A_67,B_68] :
      ( k2_xboole_0(A_67,B_68) = B_68
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_356,plain,(
    k2_xboole_0(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_346])).

tff(c_30,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k4_xboole_0(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_572,plain,(
    ! [A_89,B_90] : k4_xboole_0(A_89,k4_xboole_0(A_89,B_90)) = k3_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_9004,plain,(
    ! [A_274,B_275] : k4_xboole_0(A_274,k3_xboole_0(A_274,B_275)) = k3_xboole_0(A_274,k4_xboole_0(A_274,B_275)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_572])).

tff(c_26,plain,(
    ! [A_19,B_20] : r1_tarski(k4_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2297,plain,(
    ! [A_158,B_159,C_160] : r1_tarski(k4_xboole_0(A_158,k2_xboole_0(B_159,C_160)),k4_xboole_0(A_158,B_159)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2237,c_26])).

tff(c_191839,plain,(
    ! [A_1351,B_1352,C_1353] : r1_tarski(k4_xboole_0(A_1351,k2_xboole_0(k3_xboole_0(A_1351,B_1352),C_1353)),k3_xboole_0(A_1351,k4_xboole_0(A_1351,B_1352))) ),
    inference(superposition,[status(thm),theory(equality)],[c_9004,c_2297])).

tff(c_192652,plain,(
    r1_tarski(k4_xboole_0('#skF_3',k1_tarski('#skF_5')),k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_191839])).

tff(c_1494,plain,(
    ! [A_125,B_126,C_127] :
      ( r1_tarski(A_125,B_126)
      | ~ r1_tarski(A_125,k4_xboole_0(B_126,C_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3863,plain,(
    ! [A_188,A_189,B_190] :
      ( r1_tarski(A_188,A_189)
      | ~ r1_tarski(A_188,k3_xboole_0(A_189,B_190)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1494])).

tff(c_3902,plain,(
    ! [A_188,A_3,B_4] :
      ( r1_tarski(A_188,A_3)
      | ~ r1_tarski(A_188,k3_xboole_0(B_4,A_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3863])).

tff(c_193635,plain,(
    r1_tarski(k4_xboole_0('#skF_3',k1_tarski('#skF_5')),k4_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_192652,c_3902])).

tff(c_20,plain,(
    ! [A_14,C_16,B_15] :
      ( r1_xboole_0(A_14,C_16)
      | ~ r1_tarski(A_14,k4_xboole_0(B_15,C_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_193697,plain,(
    r1_xboole_0(k4_xboole_0('#skF_3',k1_tarski('#skF_5')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_193635,c_20])).

tff(c_193720,plain,
    ( r1_xboole_0('#skF_3','#skF_2')
    | r2_hidden('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_193697])).

tff(c_193750,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_193720])).

tff(c_56,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_180,plain,(
    ! [B_60,A_59] :
      ( r1_xboole_0(B_60,A_59)
      | k4_xboole_0(A_59,B_60) != A_59 ) ),
    inference(resolution,[status(thm)],[c_174,c_6])).

tff(c_2023,plain,(
    ! [A_150,B_151,C_152] :
      ( ~ r1_xboole_0(A_150,B_151)
      | ~ r2_hidden(C_152,B_151)
      | ~ r2_hidden(C_152,A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_48250,plain,(
    ! [C_699,A_700,B_701] :
      ( ~ r2_hidden(C_699,A_700)
      | ~ r2_hidden(C_699,B_701)
      | k4_xboole_0(A_700,B_701) != A_700 ) ),
    inference(resolution,[status(thm)],[c_180,c_2023])).

tff(c_48262,plain,(
    ! [B_701] :
      ( ~ r2_hidden('#skF_5',B_701)
      | k4_xboole_0('#skF_4',B_701) != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_56,c_48250])).

tff(c_193767,plain,(
    k4_xboole_0('#skF_4','#skF_3') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_193750,c_48262])).

tff(c_193788,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_193767])).

tff(c_193789,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_193720])).

tff(c_36,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = A_29
      | ~ r1_xboole_0(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_193795,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_193789,c_36])).

tff(c_193802,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11669,c_193795])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:55:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 45.75/35.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 45.75/35.95  
% 45.75/35.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 45.75/35.96  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 45.75/35.96  
% 45.75/35.96  %Foreground sorts:
% 45.75/35.96  
% 45.75/35.96  
% 45.75/35.96  %Background operators:
% 45.75/35.96  
% 45.75/35.96  
% 45.75/35.96  %Foreground operators:
% 45.75/35.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 45.75/35.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 45.75/35.96  tff(k1_tarski, type, k1_tarski: $i > $i).
% 45.75/35.96  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 45.75/35.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 45.75/35.96  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 45.75/35.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 45.75/35.96  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 45.75/35.96  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 45.75/35.96  tff('#skF_5', type, '#skF_5': $i).
% 45.75/35.96  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 45.75/35.96  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 45.75/35.96  tff('#skF_2', type, '#skF_2': $i).
% 45.75/35.96  tff('#skF_3', type, '#skF_3': $i).
% 45.75/35.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 45.75/35.96  tff('#skF_4', type, '#skF_4': $i).
% 45.75/35.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 45.75/35.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 45.75/35.96  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 45.75/35.96  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 45.75/35.96  
% 45.75/35.97  tff(f_103, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 45.75/35.97  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 45.75/35.97  tff(f_81, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 45.75/35.97  tff(f_71, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 45.75/35.97  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 45.75/35.97  tff(f_94, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 45.75/35.97  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 45.75/35.97  tff(f_67, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 45.75/35.97  tff(f_73, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 45.75/35.97  tff(f_69, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 45.75/35.97  tff(f_63, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 45.75/35.97  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 45.75/35.97  tff(c_54, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 45.75/35.97  tff(c_141, plain, (![B_52, A_53]: (r1_xboole_0(B_52, A_53) | ~r1_xboole_0(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_33])).
% 45.75/35.97  tff(c_150, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_141])).
% 45.75/35.97  tff(c_182, plain, (![A_61, B_62]: (k4_xboole_0(A_61, B_62)=A_61 | ~r1_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_81])).
% 45.75/35.97  tff(c_206, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_150, c_182])).
% 45.75/35.97  tff(c_2237, plain, (![A_158, B_159, C_160]: (k4_xboole_0(k4_xboole_0(A_158, B_159), C_160)=k4_xboole_0(A_158, k2_xboole_0(B_159, C_160)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 45.75/35.97  tff(c_2337, plain, (![C_160]: (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_160))=k4_xboole_0('#skF_3', C_160))), inference(superposition, [status(thm), theory('equality')], [c_206, c_2237])).
% 45.75/35.97  tff(c_174, plain, (![A_59, B_60]: (r1_xboole_0(A_59, B_60) | k4_xboole_0(A_59, B_60)!=A_59)), inference(cnfTransformation, [status(thm)], [f_81])).
% 45.75/35.97  tff(c_6, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 45.75/35.97  tff(c_560, plain, (![B_87, A_88]: (r1_xboole_0(B_87, A_88) | k4_xboole_0(A_88, B_87)!=A_88)), inference(resolution, [status(thm)], [c_174, c_6])).
% 45.75/35.97  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 45.75/35.97  tff(c_52, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 45.75/35.97  tff(c_61, plain, (~r1_xboole_0(k2_xboole_0('#skF_4', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_52])).
% 45.75/35.97  tff(c_571, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_2'))!='#skF_3'), inference(resolution, [status(thm)], [c_560, c_61])).
% 45.75/35.97  tff(c_11669, plain, (k4_xboole_0('#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2337, c_571])).
% 45.75/35.97  tff(c_210, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_54, c_182])).
% 45.75/35.97  tff(c_50, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k1_tarski(B_40))=A_39 | r2_hidden(B_40, A_39))), inference(cnfTransformation, [status(thm)], [f_94])).
% 45.75/35.97  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 45.75/35.97  tff(c_58, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 45.75/35.97  tff(c_60, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_58])).
% 45.75/35.97  tff(c_346, plain, (![A_67, B_68]: (k2_xboole_0(A_67, B_68)=B_68 | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_67])).
% 45.75/35.97  tff(c_356, plain, (k2_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_60, c_346])).
% 45.75/35.97  tff(c_30, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k4_xboole_0(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_73])).
% 45.75/35.97  tff(c_572, plain, (![A_89, B_90]: (k4_xboole_0(A_89, k4_xboole_0(A_89, B_90))=k3_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_73])).
% 45.75/35.97  tff(c_9004, plain, (![A_274, B_275]: (k4_xboole_0(A_274, k3_xboole_0(A_274, B_275))=k3_xboole_0(A_274, k4_xboole_0(A_274, B_275)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_572])).
% 45.75/35.97  tff(c_26, plain, (![A_19, B_20]: (r1_tarski(k4_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 45.75/35.97  tff(c_2297, plain, (![A_158, B_159, C_160]: (r1_tarski(k4_xboole_0(A_158, k2_xboole_0(B_159, C_160)), k4_xboole_0(A_158, B_159)))), inference(superposition, [status(thm), theory('equality')], [c_2237, c_26])).
% 45.75/35.97  tff(c_191839, plain, (![A_1351, B_1352, C_1353]: (r1_tarski(k4_xboole_0(A_1351, k2_xboole_0(k3_xboole_0(A_1351, B_1352), C_1353)), k3_xboole_0(A_1351, k4_xboole_0(A_1351, B_1352))))), inference(superposition, [status(thm), theory('equality')], [c_9004, c_2297])).
% 45.75/35.97  tff(c_192652, plain, (r1_tarski(k4_xboole_0('#skF_3', k1_tarski('#skF_5')), k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_356, c_191839])).
% 45.75/35.97  tff(c_1494, plain, (![A_125, B_126, C_127]: (r1_tarski(A_125, B_126) | ~r1_tarski(A_125, k4_xboole_0(B_126, C_127)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 45.75/35.97  tff(c_3863, plain, (![A_188, A_189, B_190]: (r1_tarski(A_188, A_189) | ~r1_tarski(A_188, k3_xboole_0(A_189, B_190)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1494])).
% 45.75/35.97  tff(c_3902, plain, (![A_188, A_3, B_4]: (r1_tarski(A_188, A_3) | ~r1_tarski(A_188, k3_xboole_0(B_4, A_3)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_3863])).
% 45.75/35.97  tff(c_193635, plain, (r1_tarski(k4_xboole_0('#skF_3', k1_tarski('#skF_5')), k4_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_192652, c_3902])).
% 45.75/35.97  tff(c_20, plain, (![A_14, C_16, B_15]: (r1_xboole_0(A_14, C_16) | ~r1_tarski(A_14, k4_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 45.75/35.97  tff(c_193697, plain, (r1_xboole_0(k4_xboole_0('#skF_3', k1_tarski('#skF_5')), '#skF_2')), inference(resolution, [status(thm)], [c_193635, c_20])).
% 45.75/35.97  tff(c_193720, plain, (r1_xboole_0('#skF_3', '#skF_2') | r2_hidden('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_50, c_193697])).
% 45.75/35.97  tff(c_193750, plain, (r2_hidden('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_193720])).
% 45.75/35.97  tff(c_56, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 45.75/35.97  tff(c_180, plain, (![B_60, A_59]: (r1_xboole_0(B_60, A_59) | k4_xboole_0(A_59, B_60)!=A_59)), inference(resolution, [status(thm)], [c_174, c_6])).
% 45.75/35.97  tff(c_2023, plain, (![A_150, B_151, C_152]: (~r1_xboole_0(A_150, B_151) | ~r2_hidden(C_152, B_151) | ~r2_hidden(C_152, A_150))), inference(cnfTransformation, [status(thm)], [f_51])).
% 45.75/35.97  tff(c_48250, plain, (![C_699, A_700, B_701]: (~r2_hidden(C_699, A_700) | ~r2_hidden(C_699, B_701) | k4_xboole_0(A_700, B_701)!=A_700)), inference(resolution, [status(thm)], [c_180, c_2023])).
% 45.75/35.97  tff(c_48262, plain, (![B_701]: (~r2_hidden('#skF_5', B_701) | k4_xboole_0('#skF_4', B_701)!='#skF_4')), inference(resolution, [status(thm)], [c_56, c_48250])).
% 45.75/35.97  tff(c_193767, plain, (k4_xboole_0('#skF_4', '#skF_3')!='#skF_4'), inference(resolution, [status(thm)], [c_193750, c_48262])).
% 45.75/35.97  tff(c_193788, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_210, c_193767])).
% 45.75/35.97  tff(c_193789, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_193720])).
% 45.75/35.97  tff(c_36, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=A_29 | ~r1_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_81])).
% 45.75/35.97  tff(c_193795, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_193789, c_36])).
% 45.75/35.97  tff(c_193802, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11669, c_193795])).
% 45.75/35.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 45.75/35.97  
% 45.75/35.97  Inference rules
% 45.75/35.97  ----------------------
% 45.75/35.97  #Ref     : 1
% 45.75/35.97  #Sup     : 48917
% 45.75/35.97  #Fact    : 0
% 45.75/35.97  #Define  : 0
% 45.75/35.97  #Split   : 6
% 45.75/35.97  #Chain   : 0
% 45.75/35.97  #Close   : 0
% 45.75/35.97  
% 45.75/35.97  Ordering : KBO
% 45.75/35.97  
% 45.75/35.97  Simplification rules
% 45.75/35.97  ----------------------
% 45.75/35.97  #Subsume      : 6319
% 45.75/35.97  #Demod        : 47981
% 45.75/35.97  #Tautology    : 30016
% 45.75/35.97  #SimpNegUnit  : 360
% 45.75/35.97  #BackRed      : 7
% 45.75/35.97  
% 45.75/35.97  #Partial instantiations: 0
% 45.75/35.97  #Strategies tried      : 1
% 45.75/35.97  
% 45.75/35.97  Timing (in seconds)
% 45.75/35.97  ----------------------
% 45.75/35.97  Preprocessing        : 0.52
% 45.75/35.97  Parsing              : 0.26
% 45.75/35.97  CNF conversion       : 0.04
% 45.75/35.97  Main loop            : 34.54
% 45.75/35.97  Inferencing          : 2.63
% 45.75/35.97  Reduction            : 23.00
% 45.75/35.97  Demodulation         : 20.81
% 45.75/35.97  BG Simplification    : 0.28
% 45.75/35.97  Subsumption          : 7.52
% 45.75/35.98  Abstraction          : 0.47
% 45.75/35.98  MUC search           : 0.00
% 45.75/35.98  Cooper               : 0.00
% 45.75/35.98  Total                : 35.09
% 45.75/35.98  Index Insertion      : 0.00
% 45.75/35.98  Index Deletion       : 0.00
% 45.75/35.98  Index Matching       : 0.00
% 45.75/35.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
