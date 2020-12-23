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
% DateTime   : Thu Dec  3 09:48:44 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   57 (  60 expanded)
%              Number of leaves         :   34 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   47 (  54 expanded)
%              Number of equality atoms :   20 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_49,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_52,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_50,plain,(
    ! [A_57,B_58] :
      ( r1_xboole_0(k1_tarski(A_57),B_58)
      | r2_hidden(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24,plain,(
    ! [C_23] : r2_hidden(C_23,k1_tarski(C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_98,plain,(
    ! [B_64,A_65] :
      ( ~ r2_hidden(B_64,A_65)
      | ~ v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,(
    ! [C_23] : ~ v1_xboole_0(k1_tarski(C_23)) ),
    inference(resolution,[status(thm)],[c_24,c_98])).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_209,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k3_xboole_0(A_85,B_86)) = k4_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_218,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = k4_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_209])).

tff(c_221,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_218])).

tff(c_54,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_188,plain,(
    ! [A_83,B_84] : k4_xboole_0(A_83,k4_xboole_0(A_83,B_84)) = k3_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_206,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k4_xboole_0(k1_tarski('#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_188])).

tff(c_318,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_206])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_163,plain,(
    ! [A_77,B_78,C_79] :
      ( ~ r1_xboole_0(A_77,B_78)
      | ~ r2_hidden(C_79,k3_xboole_0(A_77,B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_171,plain,(
    ! [A_77,B_78] :
      ( ~ r1_xboole_0(A_77,B_78)
      | v1_xboole_0(k3_xboole_0(A_77,B_78)) ) ),
    inference(resolution,[status(thm)],[c_4,c_163])).

tff(c_325,plain,
    ( ~ r1_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6'))
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_171])).

tff(c_332,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_325])).

tff(c_337,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_50,c_332])).

tff(c_22,plain,(
    ! [C_23,A_19] :
      ( C_23 = A_19
      | ~ r2_hidden(C_23,k1_tarski(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_340,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_337,c_22])).

tff(c_347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_340])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.38  
% 2.33/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.38  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 2.33/1.38  
% 2.33/1.38  %Foreground sorts:
% 2.33/1.38  
% 2.33/1.38  
% 2.33/1.38  %Background operators:
% 2.33/1.38  
% 2.33/1.38  
% 2.33/1.38  %Foreground operators:
% 2.33/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.33/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.33/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.33/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.33/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.33/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.33/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.33/1.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.33/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.33/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.33/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.33/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.33/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.33/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.33/1.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.33/1.38  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.33/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.33/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.33/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.33/1.38  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.33/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.33/1.38  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.33/1.38  
% 2.33/1.40  tff(f_90, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.33/1.40  tff(f_85, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.33/1.40  tff(f_64, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.33/1.40  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.33/1.40  tff(f_53, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.33/1.40  tff(f_49, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.33/1.40  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.33/1.40  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.33/1.40  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.33/1.40  tff(c_52, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.33/1.40  tff(c_50, plain, (![A_57, B_58]: (r1_xboole_0(k1_tarski(A_57), B_58) | r2_hidden(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.33/1.40  tff(c_24, plain, (![C_23]: (r2_hidden(C_23, k1_tarski(C_23)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.33/1.40  tff(c_98, plain, (![B_64, A_65]: (~r2_hidden(B_64, A_65) | ~v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.33/1.40  tff(c_102, plain, (![C_23]: (~v1_xboole_0(k1_tarski(C_23)))), inference(resolution, [status(thm)], [c_24, c_98])).
% 2.33/1.40  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.33/1.40  tff(c_12, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.33/1.40  tff(c_209, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k3_xboole_0(A_85, B_86))=k4_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.33/1.40  tff(c_218, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=k4_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_209])).
% 2.33/1.40  tff(c_221, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_218])).
% 2.33/1.40  tff(c_54, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.33/1.40  tff(c_188, plain, (![A_83, B_84]: (k4_xboole_0(A_83, k4_xboole_0(A_83, B_84))=k3_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.33/1.40  tff(c_206, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k4_xboole_0(k1_tarski('#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_54, c_188])).
% 2.33/1.40  tff(c_318, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_221, c_206])).
% 2.33/1.40  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.33/1.40  tff(c_163, plain, (![A_77, B_78, C_79]: (~r1_xboole_0(A_77, B_78) | ~r2_hidden(C_79, k3_xboole_0(A_77, B_78)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.33/1.40  tff(c_171, plain, (![A_77, B_78]: (~r1_xboole_0(A_77, B_78) | v1_xboole_0(k3_xboole_0(A_77, B_78)))), inference(resolution, [status(thm)], [c_4, c_163])).
% 2.33/1.40  tff(c_325, plain, (~r1_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6')) | v1_xboole_0(k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_318, c_171])).
% 2.33/1.40  tff(c_332, plain, (~r1_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_102, c_325])).
% 2.33/1.40  tff(c_337, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_50, c_332])).
% 2.33/1.40  tff(c_22, plain, (![C_23, A_19]: (C_23=A_19 | ~r2_hidden(C_23, k1_tarski(A_19)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.33/1.40  tff(c_340, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_337, c_22])).
% 2.33/1.40  tff(c_347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_340])).
% 2.33/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.40  
% 2.33/1.40  Inference rules
% 2.33/1.40  ----------------------
% 2.33/1.40  #Ref     : 0
% 2.33/1.40  #Sup     : 69
% 2.33/1.40  #Fact    : 0
% 2.33/1.40  #Define  : 0
% 2.33/1.40  #Split   : 1
% 2.33/1.40  #Chain   : 0
% 2.33/1.40  #Close   : 0
% 2.33/1.40  
% 2.33/1.40  Ordering : KBO
% 2.33/1.40  
% 2.33/1.40  Simplification rules
% 2.33/1.40  ----------------------
% 2.33/1.40  #Subsume      : 0
% 2.33/1.40  #Demod        : 13
% 2.33/1.40  #Tautology    : 47
% 2.33/1.40  #SimpNegUnit  : 5
% 2.33/1.40  #BackRed      : 0
% 2.33/1.40  
% 2.33/1.40  #Partial instantiations: 0
% 2.33/1.40  #Strategies tried      : 1
% 2.33/1.40  
% 2.33/1.40  Timing (in seconds)
% 2.33/1.40  ----------------------
% 2.33/1.40  Preprocessing        : 0.37
% 2.33/1.40  Parsing              : 0.18
% 2.33/1.40  CNF conversion       : 0.03
% 2.33/1.40  Main loop            : 0.26
% 2.33/1.40  Inferencing          : 0.10
% 2.33/1.40  Reduction            : 0.08
% 2.33/1.40  Demodulation         : 0.05
% 2.33/1.40  BG Simplification    : 0.02
% 2.33/1.40  Subsumption          : 0.03
% 2.33/1.40  Abstraction          : 0.01
% 2.33/1.40  MUC search           : 0.00
% 2.33/1.40  Cooper               : 0.00
% 2.33/1.40  Total                : 0.66
% 2.33/1.40  Index Insertion      : 0.00
% 2.33/1.40  Index Deletion       : 0.00
% 2.33/1.40  Index Matching       : 0.00
% 2.33/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
