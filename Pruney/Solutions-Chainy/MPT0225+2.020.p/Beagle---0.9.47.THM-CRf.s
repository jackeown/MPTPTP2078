%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:33 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 120 expanded)
%              Number of leaves         :   29 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :   89 ( 198 expanded)
%              Number of equality atoms :   30 (  69 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

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

tff(c_484,plain,(
    ! [A_119,B_120] :
      ( r1_xboole_0(A_119,B_120)
      | k4_xboole_0(A_119,B_120) != A_119 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_42,plain,(
    ! [B_30] : ~ r1_xboole_0(k1_tarski(B_30),k1_tarski(B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_488,plain,(
    ! [B_30] : k4_xboole_0(k1_tarski(B_30),k1_tarski(B_30)) != k1_tarski(B_30) ),
    inference(resolution,[status(thm)],[c_484,c_42])).

tff(c_64,plain,(
    ! [A_34,B_35] :
      ( r1_xboole_0(A_34,B_35)
      | k4_xboole_0(A_34,B_35) != A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_68,plain,(
    ! [B_30] : k4_xboole_0(k1_tarski(B_30),k1_tarski(B_30)) != k1_tarski(B_30) ),
    inference(resolution,[status(thm)],[c_64,c_42])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_40,plain,(
    ! [A_27,B_28] :
      ( r1_xboole_0(k1_tarski(A_27),B_28)
      | r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_92,plain,(
    ! [A_45,B_46] :
      ( k4_xboole_0(A_45,B_46) = A_45
      | ~ r1_xboole_0(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_146,plain,(
    ! [A_62,B_63] :
      ( k4_xboole_0(k1_tarski(A_62),B_63) = k1_tarski(A_62)
      | r2_hidden(A_62,B_63) ) ),
    inference(resolution,[status(thm)],[c_40,c_92])).

tff(c_44,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) != k1_tarski('#skF_4')
    | '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_85,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) != k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_163,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_85])).

tff(c_30,plain,(
    ! [C_26,A_22] :
      ( r2_hidden(C_26,k1_zfmisc_1(A_22))
      | ~ r1_tarski(C_26,A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_130,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r2_hidden(C_58,B_57)
      | ~ r2_hidden(C_58,A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_178,plain,(
    ! [C_70,B_71,A_72] :
      ( ~ r2_hidden(C_70,B_71)
      | ~ r2_hidden(C_70,k1_tarski(A_72))
      | r2_hidden(A_72,B_71) ) ),
    inference(resolution,[status(thm)],[c_40,c_130])).

tff(c_297,plain,(
    ! [C_88,A_89,A_90] :
      ( ~ r2_hidden(C_88,k1_tarski(A_89))
      | r2_hidden(A_89,k1_zfmisc_1(A_90))
      | ~ r1_tarski(C_88,A_90) ) ),
    inference(resolution,[status(thm)],[c_30,c_178])).

tff(c_319,plain,(
    ! [A_91] :
      ( r2_hidden('#skF_5',k1_zfmisc_1(A_91))
      | ~ r1_tarski('#skF_4',A_91) ) ),
    inference(resolution,[status(thm)],[c_163,c_297])).

tff(c_28,plain,(
    ! [C_26,A_22] :
      ( r1_tarski(C_26,A_22)
      | ~ r2_hidden(C_26,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_329,plain,(
    ! [A_91] :
      ( r1_tarski('#skF_5',A_91)
      | ~ r1_tarski('#skF_4',A_91) ) ),
    inference(resolution,[status(thm)],[c_319,c_28])).

tff(c_46,plain,
    ( '#skF_5' != '#skF_4'
    | '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_53,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_79,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(k1_tarski(A_40),B_41)
      | r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_84,plain,(
    ! [A_40] : r2_hidden(A_40,k1_tarski(A_40)) ),
    inference(resolution,[status(thm)],[c_79,c_42])).

tff(c_194,plain,(
    ! [A_73,A_74] :
      ( ~ r2_hidden(A_73,k1_tarski(A_74))
      | r2_hidden(A_74,k1_tarski(A_73)) ) ),
    inference(resolution,[status(thm)],[c_84,c_178])).

tff(c_205,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_163,c_194])).

tff(c_334,plain,(
    ! [A_93] :
      ( r2_hidden('#skF_4',k1_zfmisc_1(A_93))
      | ~ r1_tarski('#skF_5',A_93) ) ),
    inference(resolution,[status(thm)],[c_205,c_297])).

tff(c_345,plain,(
    ! [A_94] :
      ( r1_tarski('#skF_4',A_94)
      | ~ r1_tarski('#skF_5',A_94) ) ),
    inference(resolution,[status(thm)],[c_334,c_28])).

tff(c_354,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_345])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_356,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_354,c_8])).

tff(c_359,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_356])).

tff(c_362,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_329,c_359])).

tff(c_366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_362])).

tff(c_367,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_368,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_48,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) != k1_tarski('#skF_4')
    | k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_462,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_368,c_48])).

tff(c_463,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_462])).

tff(c_464,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_465,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_50,plain,
    ( '#skF_5' != '#skF_4'
    | k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_567,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_465,c_50])).

tff(c_568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_488,c_567])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:22:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.38  
% 2.53/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.39  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 2.53/1.39  
% 2.53/1.39  %Foreground sorts:
% 2.53/1.39  
% 2.53/1.39  
% 2.53/1.39  %Background operators:
% 2.53/1.39  
% 2.53/1.39  
% 2.53/1.39  %Foreground operators:
% 2.53/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.53/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.53/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.53/1.39  tff('#skF_7', type, '#skF_7': $i).
% 2.53/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.53/1.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.53/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.53/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.53/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.53/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.53/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.53/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.53/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.53/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.53/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.53/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.53/1.39  
% 2.53/1.40  tff(f_55, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.53/1.40  tff(f_80, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.53/1.40  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.53/1.40  tff(f_75, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.53/1.40  tff(f_86, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.53/1.40  tff(f_70, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.53/1.40  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.53/1.40  tff(c_484, plain, (![A_119, B_120]: (r1_xboole_0(A_119, B_120) | k4_xboole_0(A_119, B_120)!=A_119)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.53/1.40  tff(c_42, plain, (![B_30]: (~r1_xboole_0(k1_tarski(B_30), k1_tarski(B_30)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.53/1.40  tff(c_488, plain, (![B_30]: (k4_xboole_0(k1_tarski(B_30), k1_tarski(B_30))!=k1_tarski(B_30))), inference(resolution, [status(thm)], [c_484, c_42])).
% 2.53/1.40  tff(c_64, plain, (![A_34, B_35]: (r1_xboole_0(A_34, B_35) | k4_xboole_0(A_34, B_35)!=A_34)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.53/1.40  tff(c_68, plain, (![B_30]: (k4_xboole_0(k1_tarski(B_30), k1_tarski(B_30))!=k1_tarski(B_30))), inference(resolution, [status(thm)], [c_64, c_42])).
% 2.53/1.40  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.53/1.40  tff(c_40, plain, (![A_27, B_28]: (r1_xboole_0(k1_tarski(A_27), B_28) | r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.53/1.40  tff(c_92, plain, (![A_45, B_46]: (k4_xboole_0(A_45, B_46)=A_45 | ~r1_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.53/1.40  tff(c_146, plain, (![A_62, B_63]: (k4_xboole_0(k1_tarski(A_62), B_63)=k1_tarski(A_62) | r2_hidden(A_62, B_63))), inference(resolution, [status(thm)], [c_40, c_92])).
% 2.53/1.40  tff(c_44, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))!=k1_tarski('#skF_4') | '#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.53/1.40  tff(c_85, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))!=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_44])).
% 2.53/1.40  tff(c_163, plain, (r2_hidden('#skF_4', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_146, c_85])).
% 2.53/1.40  tff(c_30, plain, (![C_26, A_22]: (r2_hidden(C_26, k1_zfmisc_1(A_22)) | ~r1_tarski(C_26, A_22))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.53/1.40  tff(c_130, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | ~r2_hidden(C_58, B_57) | ~r2_hidden(C_58, A_56))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.53/1.40  tff(c_178, plain, (![C_70, B_71, A_72]: (~r2_hidden(C_70, B_71) | ~r2_hidden(C_70, k1_tarski(A_72)) | r2_hidden(A_72, B_71))), inference(resolution, [status(thm)], [c_40, c_130])).
% 2.53/1.40  tff(c_297, plain, (![C_88, A_89, A_90]: (~r2_hidden(C_88, k1_tarski(A_89)) | r2_hidden(A_89, k1_zfmisc_1(A_90)) | ~r1_tarski(C_88, A_90))), inference(resolution, [status(thm)], [c_30, c_178])).
% 2.53/1.40  tff(c_319, plain, (![A_91]: (r2_hidden('#skF_5', k1_zfmisc_1(A_91)) | ~r1_tarski('#skF_4', A_91))), inference(resolution, [status(thm)], [c_163, c_297])).
% 2.53/1.40  tff(c_28, plain, (![C_26, A_22]: (r1_tarski(C_26, A_22) | ~r2_hidden(C_26, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.53/1.40  tff(c_329, plain, (![A_91]: (r1_tarski('#skF_5', A_91) | ~r1_tarski('#skF_4', A_91))), inference(resolution, [status(thm)], [c_319, c_28])).
% 2.53/1.40  tff(c_46, plain, ('#skF_5'!='#skF_4' | '#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.53/1.40  tff(c_53, plain, ('#skF_5'!='#skF_4'), inference(splitLeft, [status(thm)], [c_46])).
% 2.53/1.40  tff(c_79, plain, (![A_40, B_41]: (r1_xboole_0(k1_tarski(A_40), B_41) | r2_hidden(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.53/1.40  tff(c_84, plain, (![A_40]: (r2_hidden(A_40, k1_tarski(A_40)))), inference(resolution, [status(thm)], [c_79, c_42])).
% 2.53/1.40  tff(c_194, plain, (![A_73, A_74]: (~r2_hidden(A_73, k1_tarski(A_74)) | r2_hidden(A_74, k1_tarski(A_73)))), inference(resolution, [status(thm)], [c_84, c_178])).
% 2.53/1.40  tff(c_205, plain, (r2_hidden('#skF_5', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_163, c_194])).
% 2.53/1.40  tff(c_334, plain, (![A_93]: (r2_hidden('#skF_4', k1_zfmisc_1(A_93)) | ~r1_tarski('#skF_5', A_93))), inference(resolution, [status(thm)], [c_205, c_297])).
% 2.53/1.40  tff(c_345, plain, (![A_94]: (r1_tarski('#skF_4', A_94) | ~r1_tarski('#skF_5', A_94))), inference(resolution, [status(thm)], [c_334, c_28])).
% 2.53/1.40  tff(c_354, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_12, c_345])).
% 2.53/1.40  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.53/1.40  tff(c_356, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_354, c_8])).
% 2.53/1.40  tff(c_359, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_53, c_356])).
% 2.53/1.40  tff(c_362, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_329, c_359])).
% 2.53/1.40  tff(c_366, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_362])).
% 2.53/1.40  tff(c_367, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_44])).
% 2.53/1.40  tff(c_368, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_44])).
% 2.53/1.40  tff(c_48, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))!=k1_tarski('#skF_4') | k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.53/1.40  tff(c_462, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_367, c_368, c_48])).
% 2.53/1.40  tff(c_463, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_462])).
% 2.53/1.40  tff(c_464, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_46])).
% 2.53/1.40  tff(c_465, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_46])).
% 2.53/1.40  tff(c_50, plain, ('#skF_5'!='#skF_4' | k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.53/1.40  tff(c_567, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_464, c_465, c_50])).
% 2.53/1.40  tff(c_568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_488, c_567])).
% 2.53/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.40  
% 2.53/1.40  Inference rules
% 2.53/1.40  ----------------------
% 2.53/1.40  #Ref     : 0
% 2.53/1.40  #Sup     : 115
% 2.53/1.40  #Fact    : 0
% 2.53/1.40  #Define  : 0
% 2.53/1.40  #Split   : 2
% 2.53/1.40  #Chain   : 0
% 2.53/1.40  #Close   : 0
% 2.53/1.40  
% 2.53/1.40  Ordering : KBO
% 2.53/1.40  
% 2.53/1.40  Simplification rules
% 2.53/1.40  ----------------------
% 2.53/1.40  #Subsume      : 7
% 2.53/1.40  #Demod        : 20
% 2.53/1.40  #Tautology    : 56
% 2.53/1.40  #SimpNegUnit  : 3
% 2.53/1.40  #BackRed      : 0
% 2.53/1.40  
% 2.53/1.40  #Partial instantiations: 0
% 2.53/1.40  #Strategies tried      : 1
% 2.53/1.40  
% 2.53/1.40  Timing (in seconds)
% 2.53/1.40  ----------------------
% 2.53/1.40  Preprocessing        : 0.32
% 2.53/1.40  Parsing              : 0.16
% 2.53/1.40  CNF conversion       : 0.02
% 2.53/1.40  Main loop            : 0.30
% 2.53/1.40  Inferencing          : 0.11
% 2.53/1.41  Reduction            : 0.08
% 2.53/1.41  Demodulation         : 0.05
% 2.53/1.41  BG Simplification    : 0.02
% 2.53/1.41  Subsumption          : 0.06
% 2.53/1.41  Abstraction          : 0.01
% 2.53/1.41  MUC search           : 0.00
% 2.53/1.41  Cooper               : 0.00
% 2.53/1.41  Total                : 0.65
% 2.53/1.41  Index Insertion      : 0.00
% 2.53/1.41  Index Deletion       : 0.00
% 2.53/1.41  Index Matching       : 0.00
% 2.53/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
