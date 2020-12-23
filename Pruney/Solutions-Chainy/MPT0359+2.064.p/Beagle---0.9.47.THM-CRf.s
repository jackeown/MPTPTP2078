%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:17 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 163 expanded)
%              Number of leaves         :   32 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :   88 ( 230 expanded)
%              Number of equality atoms :   35 ( 110 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_62,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_66,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_78,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_80,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_58,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_64,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_50,axiom,(
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

tff(c_24,plain,(
    ! [A_19] : k2_subset_1(A_19) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,
    ( k2_subset_1('#skF_4') != '#skF_5'
    | ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_44,plain,
    ( '#skF_5' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_36])).

tff(c_76,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_18,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    ! [A_18] : k1_subset_1(A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    ! [A_24] : k3_subset_1(A_24,k1_subset_1(A_24)) = k2_subset_1(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_45,plain,(
    ! [A_24] : k3_subset_1(A_24,k1_subset_1(A_24)) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_30])).

tff(c_46,plain,(
    ! [A_24] : k3_subset_1(A_24,k1_xboole_0) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_45])).

tff(c_32,plain,(
    ! [A_25] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_150,plain,(
    ! [A_56,B_57] :
      ( k3_subset_1(A_56,k3_subset_1(A_56,B_57)) = B_57
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_154,plain,(
    ! [A_25] : k3_subset_1(A_25,k3_subset_1(A_25,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_150])).

tff(c_157,plain,(
    ! [A_25] : k3_subset_1(A_25,A_25) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_154])).

tff(c_42,plain,
    ( r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_5')
    | k2_subset_1('#skF_4') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_43,plain,
    ( r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_42])).

tff(c_77,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_43])).

tff(c_83,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_77,c_76])).

tff(c_158,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_83])).

tff(c_161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_158])).

tff(c_162,plain,(
    r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_43])).

tff(c_164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_162])).

tff(c_165,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_167,plain,(
    r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_43])).

tff(c_14,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_188,plain,(
    ! [C_69,B_70,A_71] :
      ( r2_hidden(C_69,B_70)
      | ~ r2_hidden(C_69,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_200,plain,(
    ! [A_11,B_70] :
      ( r2_hidden('#skF_3'(A_11),B_70)
      | ~ r1_tarski(A_11,B_70)
      | k1_xboole_0 = A_11 ) ),
    inference(resolution,[status(thm)],[c_14,c_188])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_205,plain,(
    ! [A_75,B_76] :
      ( k4_xboole_0(A_75,B_76) = k3_subset_1(A_75,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_214,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_205])).

tff(c_20,plain,(
    ! [A_16,B_17] : r1_xboole_0(k4_xboole_0(A_16,B_17),B_17) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_201,plain,(
    ! [A_72,B_73,C_74] :
      ( ~ r1_xboole_0(A_72,B_73)
      | ~ r2_hidden(C_74,B_73)
      | ~ r2_hidden(C_74,A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_290,plain,(
    ! [C_84,B_85,A_86] :
      ( ~ r2_hidden(C_84,B_85)
      | ~ r2_hidden(C_84,k4_xboole_0(A_86,B_85)) ) ),
    inference(resolution,[status(thm)],[c_20,c_201])).

tff(c_317,plain,(
    ! [C_87] :
      ( ~ r2_hidden(C_87,'#skF_5')
      | ~ r2_hidden(C_87,k3_subset_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_290])).

tff(c_337,plain,
    ( ~ r2_hidden('#skF_3'(k3_subset_1('#skF_4','#skF_5')),'#skF_5')
    | k3_subset_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_317])).

tff(c_413,plain,(
    ~ r2_hidden('#skF_3'(k3_subset_1('#skF_4','#skF_5')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_337])).

tff(c_416,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_5')
    | k3_subset_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_200,c_413])).

tff(c_419,plain,(
    k3_subset_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_416])).

tff(c_261,plain,(
    ! [A_81,B_82] :
      ( k3_subset_1(A_81,k3_subset_1(A_81,B_82)) = B_82
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_268,plain,(
    k3_subset_1('#skF_4',k3_subset_1('#skF_4','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_34,c_261])).

tff(c_422,plain,(
    k3_subset_1('#skF_4',k1_xboole_0) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_268])).

tff(c_426,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_422])).

tff(c_428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_426])).

tff(c_429,plain,(
    k3_subset_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_337])).

tff(c_432,plain,(
    k3_subset_1('#skF_4',k1_xboole_0) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_268])).

tff(c_436,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_432])).

tff(c_438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_436])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:02:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.36  
% 2.37/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.36  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.37/1.36  
% 2.37/1.36  %Foreground sorts:
% 2.37/1.36  
% 2.37/1.36  
% 2.37/1.36  %Background operators:
% 2.37/1.36  
% 2.37/1.36  
% 2.37/1.36  %Foreground operators:
% 2.37/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.37/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.37/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.37/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.36  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.37/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.37/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.37/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.36  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.37/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.37/1.36  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.37/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.37/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.37/1.36  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.37/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.36  
% 2.37/1.38  tff(f_68, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.37/1.38  tff(f_87, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 2.37/1.38  tff(f_62, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.37/1.38  tff(f_66, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.37/1.38  tff(f_78, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 2.37/1.38  tff(f_80, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.37/1.38  tff(f_76, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.37/1.38  tff(f_58, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.37/1.38  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.37/1.38  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.37/1.38  tff(f_64, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.37/1.38  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.37/1.38  tff(c_24, plain, (![A_19]: (k2_subset_1(A_19)=A_19)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.37/1.38  tff(c_36, plain, (k2_subset_1('#skF_4')!='#skF_5' | ~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.37/1.38  tff(c_44, plain, ('#skF_5'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_36])).
% 2.37/1.38  tff(c_76, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_44])).
% 2.37/1.38  tff(c_18, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.37/1.38  tff(c_22, plain, (![A_18]: (k1_subset_1(A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.37/1.38  tff(c_30, plain, (![A_24]: (k3_subset_1(A_24, k1_subset_1(A_24))=k2_subset_1(A_24))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.37/1.38  tff(c_45, plain, (![A_24]: (k3_subset_1(A_24, k1_subset_1(A_24))=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_30])).
% 2.37/1.38  tff(c_46, plain, (![A_24]: (k3_subset_1(A_24, k1_xboole_0)=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_45])).
% 2.37/1.38  tff(c_32, plain, (![A_25]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.37/1.38  tff(c_150, plain, (![A_56, B_57]: (k3_subset_1(A_56, k3_subset_1(A_56, B_57))=B_57 | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.37/1.38  tff(c_154, plain, (![A_25]: (k3_subset_1(A_25, k3_subset_1(A_25, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_150])).
% 2.37/1.38  tff(c_157, plain, (![A_25]: (k3_subset_1(A_25, A_25)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_154])).
% 2.37/1.38  tff(c_42, plain, (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_5') | k2_subset_1('#skF_4')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.37/1.38  tff(c_43, plain, (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_5') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_42])).
% 2.37/1.38  tff(c_77, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_43])).
% 2.37/1.38  tff(c_83, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_77, c_76])).
% 2.37/1.38  tff(c_158, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_83])).
% 2.37/1.38  tff(c_161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_158])).
% 2.37/1.38  tff(c_162, plain, (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_43])).
% 2.37/1.38  tff(c_164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_162])).
% 2.37/1.38  tff(c_165, plain, ('#skF_5'!='#skF_4'), inference(splitRight, [status(thm)], [c_44])).
% 2.37/1.38  tff(c_167, plain, (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_165, c_43])).
% 2.37/1.38  tff(c_14, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.37/1.38  tff(c_188, plain, (![C_69, B_70, A_71]: (r2_hidden(C_69, B_70) | ~r2_hidden(C_69, A_71) | ~r1_tarski(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.37/1.38  tff(c_200, plain, (![A_11, B_70]: (r2_hidden('#skF_3'(A_11), B_70) | ~r1_tarski(A_11, B_70) | k1_xboole_0=A_11)), inference(resolution, [status(thm)], [c_14, c_188])).
% 2.37/1.38  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.37/1.38  tff(c_205, plain, (![A_75, B_76]: (k4_xboole_0(A_75, B_76)=k3_subset_1(A_75, B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.37/1.38  tff(c_214, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_34, c_205])).
% 2.37/1.38  tff(c_20, plain, (![A_16, B_17]: (r1_xboole_0(k4_xboole_0(A_16, B_17), B_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.37/1.38  tff(c_201, plain, (![A_72, B_73, C_74]: (~r1_xboole_0(A_72, B_73) | ~r2_hidden(C_74, B_73) | ~r2_hidden(C_74, A_72))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.37/1.38  tff(c_290, plain, (![C_84, B_85, A_86]: (~r2_hidden(C_84, B_85) | ~r2_hidden(C_84, k4_xboole_0(A_86, B_85)))), inference(resolution, [status(thm)], [c_20, c_201])).
% 2.37/1.38  tff(c_317, plain, (![C_87]: (~r2_hidden(C_87, '#skF_5') | ~r2_hidden(C_87, k3_subset_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_214, c_290])).
% 2.37/1.38  tff(c_337, plain, (~r2_hidden('#skF_3'(k3_subset_1('#skF_4', '#skF_5')), '#skF_5') | k3_subset_1('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_317])).
% 2.37/1.38  tff(c_413, plain, (~r2_hidden('#skF_3'(k3_subset_1('#skF_4', '#skF_5')), '#skF_5')), inference(splitLeft, [status(thm)], [c_337])).
% 2.37/1.38  tff(c_416, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_5') | k3_subset_1('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_200, c_413])).
% 2.37/1.38  tff(c_419, plain, (k3_subset_1('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_167, c_416])).
% 2.37/1.38  tff(c_261, plain, (![A_81, B_82]: (k3_subset_1(A_81, k3_subset_1(A_81, B_82))=B_82 | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.37/1.38  tff(c_268, plain, (k3_subset_1('#skF_4', k3_subset_1('#skF_4', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_34, c_261])).
% 2.37/1.38  tff(c_422, plain, (k3_subset_1('#skF_4', k1_xboole_0)='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_419, c_268])).
% 2.37/1.38  tff(c_426, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_422])).
% 2.37/1.38  tff(c_428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_165, c_426])).
% 2.37/1.38  tff(c_429, plain, (k3_subset_1('#skF_4', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_337])).
% 2.37/1.38  tff(c_432, plain, (k3_subset_1('#skF_4', k1_xboole_0)='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_429, c_268])).
% 2.37/1.38  tff(c_436, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_432])).
% 2.37/1.38  tff(c_438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_165, c_436])).
% 2.37/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.38  
% 2.37/1.38  Inference rules
% 2.37/1.38  ----------------------
% 2.37/1.38  #Ref     : 0
% 2.37/1.38  #Sup     : 80
% 2.37/1.38  #Fact    : 0
% 2.37/1.38  #Define  : 0
% 2.37/1.38  #Split   : 3
% 2.37/1.38  #Chain   : 0
% 2.37/1.38  #Close   : 0
% 2.37/1.38  
% 2.37/1.38  Ordering : KBO
% 2.37/1.38  
% 2.37/1.38  Simplification rules
% 2.37/1.38  ----------------------
% 2.37/1.38  #Subsume      : 7
% 2.37/1.38  #Demod        : 31
% 2.37/1.38  #Tautology    : 32
% 2.37/1.38  #SimpNegUnit  : 4
% 2.37/1.38  #BackRed      : 13
% 2.37/1.38  
% 2.37/1.38  #Partial instantiations: 0
% 2.37/1.38  #Strategies tried      : 1
% 2.37/1.38  
% 2.37/1.38  Timing (in seconds)
% 2.37/1.38  ----------------------
% 2.37/1.38  Preprocessing        : 0.34
% 2.37/1.38  Parsing              : 0.18
% 2.37/1.38  CNF conversion       : 0.02
% 2.37/1.38  Main loop            : 0.23
% 2.37/1.38  Inferencing          : 0.09
% 2.37/1.38  Reduction            : 0.07
% 2.37/1.38  Demodulation         : 0.05
% 2.37/1.38  BG Simplification    : 0.02
% 2.37/1.38  Subsumption          : 0.04
% 2.37/1.38  Abstraction          : 0.01
% 2.37/1.38  MUC search           : 0.00
% 2.37/1.38  Cooper               : 0.00
% 2.37/1.38  Total                : 0.60
% 2.37/1.38  Index Insertion      : 0.00
% 2.37/1.38  Index Deletion       : 0.00
% 2.37/1.38  Index Matching       : 0.00
% 2.37/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
