%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:27 EST 2020

% Result     : Theorem 5.88s
% Output     : CNFRefutation 5.97s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 195 expanded)
%              Number of leaves         :   33 (  79 expanded)
%              Depth                    :   11
%              Number of atoms          :   68 ( 268 expanded)
%              Number of equality atoms :   48 ( 212 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A,B,C)))) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_mcart_1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

tff(f_78,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_304,plain,(
    ! [A_115,B_116,C_117] : k2_zfmisc_1(k1_tarski(A_115),k2_tarski(B_116,C_117)) = k2_tarski(k4_tarski(A_115,B_116),k4_tarski(A_115,C_117)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_367,plain,(
    ! [A_115,A_2] : k2_zfmisc_1(k1_tarski(A_115),k1_tarski(A_2)) = k2_tarski(k4_tarski(A_115,A_2),k4_tarski(A_115,A_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_304])).

tff(c_405,plain,(
    ! [A_132,A_133] : k2_zfmisc_1(k1_tarski(A_132),k1_tarski(A_133)) = k1_tarski(k4_tarski(A_132,A_133)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_367])).

tff(c_52,plain,(
    ! [A_34,B_35] :
      ( k1_relat_1(k2_zfmisc_1(A_34,B_35)) = A_34
      | k1_xboole_0 = B_35
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_414,plain,(
    ! [A_132,A_133] :
      ( k1_relat_1(k1_tarski(k4_tarski(A_132,A_133))) = k1_tarski(A_132)
      | k1_tarski(A_133) = k1_xboole_0
      | k1_tarski(A_132) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_52])).

tff(c_56,plain,(
    ! [A_38,B_39,C_40] : k4_tarski(k4_tarski(A_38,B_39),C_40) = k3_mcart_1(A_38,B_39,C_40) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_640,plain,(
    ! [A_188,A_189] :
      ( k1_relat_1(k1_tarski(k4_tarski(A_188,A_189))) = k1_tarski(A_188)
      | k1_tarski(A_189) = k1_xboole_0
      | k1_tarski(A_188) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_52])).

tff(c_2922,plain,(
    ! [A_371,B_372,C_373] :
      ( k1_relat_1(k1_tarski(k3_mcart_1(A_371,B_372,C_373))) = k1_tarski(k4_tarski(A_371,B_372))
      | k1_tarski(C_373) = k1_xboole_0
      | k1_tarski(k4_tarski(A_371,B_372)) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_640])).

tff(c_58,plain,(
    k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_3','#skF_4','#skF_5')))) != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2928,plain,
    ( k1_relat_1(k1_tarski(k4_tarski('#skF_3','#skF_4'))) != k1_tarski('#skF_3')
    | k1_tarski('#skF_5') = k1_xboole_0
    | k1_tarski(k4_tarski('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2922,c_58])).

tff(c_2938,plain,(
    k1_relat_1(k1_tarski(k4_tarski('#skF_3','#skF_4'))) != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2928])).

tff(c_2942,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_2938])).

tff(c_2943,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2942])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_142,plain,(
    ! [A_86,B_87,C_88] : k2_enumset1(A_86,A_86,B_87,C_88) = k1_enumset1(A_86,B_87,C_88) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ! [F_33,A_26,B_27,C_28] : r2_hidden(F_33,k2_enumset1(A_26,B_27,C_28,F_33)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_175,plain,(
    ! [C_89,A_90,B_91] : r2_hidden(C_89,k1_enumset1(A_90,B_91,C_89)) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_22])).

tff(c_183,plain,(
    ! [B_92,A_93] : r2_hidden(B_92,k2_tarski(A_93,B_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_175])).

tff(c_200,plain,(
    ! [A_98] : r2_hidden(A_98,k1_tarski(A_98)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_183])).

tff(c_54,plain,(
    ! [B_37,A_36] :
      ( ~ r1_tarski(B_37,A_36)
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_204,plain,(
    ! [A_98] : ~ r1_tarski(k1_tarski(A_98),A_98) ),
    inference(resolution,[status(thm)],[c_200,c_54])).

tff(c_3120,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2943,c_204])).

tff(c_3128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3120])).

tff(c_3129,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2942])).

tff(c_3305,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3129,c_204])).

tff(c_3313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3305])).

tff(c_3314,plain,
    ( k1_tarski(k4_tarski('#skF_3','#skF_4')) = k1_xboole_0
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2928])).

tff(c_3639,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3314])).

tff(c_3820,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3639,c_204])).

tff(c_3828,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3820])).

tff(c_3829,plain,(
    k1_tarski(k4_tarski('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3314])).

tff(c_4015,plain,(
    ~ r1_tarski(k1_xboole_0,k4_tarski('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3829,c_204])).

tff(c_4045,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4015])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:54:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.88/2.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.88/2.13  
% 5.88/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.88/2.13  %$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 5.88/2.13  
% 5.88/2.13  %Foreground sorts:
% 5.88/2.13  
% 5.88/2.13  
% 5.88/2.13  %Background operators:
% 5.88/2.13  
% 5.88/2.13  
% 5.88/2.13  %Foreground operators:
% 5.88/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.88/2.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.88/2.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.88/2.13  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 5.88/2.13  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.88/2.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.88/2.13  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 5.88/2.13  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.88/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.88/2.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.88/2.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.88/2.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.88/2.13  tff('#skF_5', type, '#skF_5': $i).
% 5.88/2.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.88/2.13  tff('#skF_3', type, '#skF_3': $i).
% 5.88/2.13  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.88/2.13  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 5.88/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.88/2.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.88/2.13  tff('#skF_4', type, '#skF_4': $i).
% 5.88/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.88/2.13  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.88/2.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.88/2.13  
% 5.97/2.14  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.97/2.14  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.97/2.14  tff(f_43, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 5.97/2.14  tff(f_73, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 5.97/2.14  tff(f_80, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 5.97/2.14  tff(f_83, negated_conjecture, ~(![A, B, C]: (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A, B, C)))) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_mcart_1)).
% 5.97/2.14  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.97/2.14  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 5.97/2.14  tff(f_61, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_enumset1)).
% 5.97/2.14  tff(f_78, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.97/2.14  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.97/2.14  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.97/2.14  tff(c_304, plain, (![A_115, B_116, C_117]: (k2_zfmisc_1(k1_tarski(A_115), k2_tarski(B_116, C_117))=k2_tarski(k4_tarski(A_115, B_116), k4_tarski(A_115, C_117)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.97/2.14  tff(c_367, plain, (![A_115, A_2]: (k2_zfmisc_1(k1_tarski(A_115), k1_tarski(A_2))=k2_tarski(k4_tarski(A_115, A_2), k4_tarski(A_115, A_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_304])).
% 5.97/2.14  tff(c_405, plain, (![A_132, A_133]: (k2_zfmisc_1(k1_tarski(A_132), k1_tarski(A_133))=k1_tarski(k4_tarski(A_132, A_133)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_367])).
% 5.97/2.14  tff(c_52, plain, (![A_34, B_35]: (k1_relat_1(k2_zfmisc_1(A_34, B_35))=A_34 | k1_xboole_0=B_35 | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.97/2.14  tff(c_414, plain, (![A_132, A_133]: (k1_relat_1(k1_tarski(k4_tarski(A_132, A_133)))=k1_tarski(A_132) | k1_tarski(A_133)=k1_xboole_0 | k1_tarski(A_132)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_405, c_52])).
% 5.97/2.14  tff(c_56, plain, (![A_38, B_39, C_40]: (k4_tarski(k4_tarski(A_38, B_39), C_40)=k3_mcart_1(A_38, B_39, C_40))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.97/2.14  tff(c_640, plain, (![A_188, A_189]: (k1_relat_1(k1_tarski(k4_tarski(A_188, A_189)))=k1_tarski(A_188) | k1_tarski(A_189)=k1_xboole_0 | k1_tarski(A_188)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_405, c_52])).
% 5.97/2.14  tff(c_2922, plain, (![A_371, B_372, C_373]: (k1_relat_1(k1_tarski(k3_mcart_1(A_371, B_372, C_373)))=k1_tarski(k4_tarski(A_371, B_372)) | k1_tarski(C_373)=k1_xboole_0 | k1_tarski(k4_tarski(A_371, B_372))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_56, c_640])).
% 5.97/2.14  tff(c_58, plain, (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_3', '#skF_4', '#skF_5'))))!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.97/2.14  tff(c_2928, plain, (k1_relat_1(k1_tarski(k4_tarski('#skF_3', '#skF_4')))!=k1_tarski('#skF_3') | k1_tarski('#skF_5')=k1_xboole_0 | k1_tarski(k4_tarski('#skF_3', '#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2922, c_58])).
% 5.97/2.14  tff(c_2938, plain, (k1_relat_1(k1_tarski(k4_tarski('#skF_3', '#skF_4')))!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_2928])).
% 5.97/2.14  tff(c_2942, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_tarski('#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_414, c_2938])).
% 5.97/2.14  tff(c_2943, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2942])).
% 5.97/2.14  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.97/2.14  tff(c_142, plain, (![A_86, B_87, C_88]: (k2_enumset1(A_86, A_86, B_87, C_88)=k1_enumset1(A_86, B_87, C_88))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.97/2.14  tff(c_22, plain, (![F_33, A_26, B_27, C_28]: (r2_hidden(F_33, k2_enumset1(A_26, B_27, C_28, F_33)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.97/2.14  tff(c_175, plain, (![C_89, A_90, B_91]: (r2_hidden(C_89, k1_enumset1(A_90, B_91, C_89)))), inference(superposition, [status(thm), theory('equality')], [c_142, c_22])).
% 5.97/2.14  tff(c_183, plain, (![B_92, A_93]: (r2_hidden(B_92, k2_tarski(A_93, B_92)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_175])).
% 5.97/2.14  tff(c_200, plain, (![A_98]: (r2_hidden(A_98, k1_tarski(A_98)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_183])).
% 5.97/2.14  tff(c_54, plain, (![B_37, A_36]: (~r1_tarski(B_37, A_36) | ~r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.97/2.14  tff(c_204, plain, (![A_98]: (~r1_tarski(k1_tarski(A_98), A_98))), inference(resolution, [status(thm)], [c_200, c_54])).
% 5.97/2.14  tff(c_3120, plain, (~r1_tarski(k1_xboole_0, '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2943, c_204])).
% 5.97/2.14  tff(c_3128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_3120])).
% 5.97/2.14  tff(c_3129, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2942])).
% 5.97/2.14  tff(c_3305, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3129, c_204])).
% 5.97/2.14  tff(c_3313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_3305])).
% 5.97/2.14  tff(c_3314, plain, (k1_tarski(k4_tarski('#skF_3', '#skF_4'))=k1_xboole_0 | k1_tarski('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2928])).
% 5.97/2.14  tff(c_3639, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3314])).
% 5.97/2.14  tff(c_3820, plain, (~r1_tarski(k1_xboole_0, '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3639, c_204])).
% 5.97/2.14  tff(c_3828, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_3820])).
% 5.97/2.14  tff(c_3829, plain, (k1_tarski(k4_tarski('#skF_3', '#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_3314])).
% 5.97/2.14  tff(c_4015, plain, (~r1_tarski(k1_xboole_0, k4_tarski('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3829, c_204])).
% 5.97/2.14  tff(c_4045, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_4015])).
% 5.97/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.97/2.14  
% 5.97/2.14  Inference rules
% 5.97/2.14  ----------------------
% 5.97/2.14  #Ref     : 0
% 5.97/2.14  #Sup     : 1105
% 5.97/2.14  #Fact    : 0
% 5.97/2.14  #Define  : 0
% 5.97/2.14  #Split   : 3
% 5.97/2.14  #Chain   : 0
% 5.97/2.14  #Close   : 0
% 5.97/2.14  
% 5.97/2.14  Ordering : KBO
% 5.97/2.14  
% 5.97/2.14  Simplification rules
% 5.97/2.14  ----------------------
% 5.97/2.14  #Subsume      : 154
% 5.97/2.14  #Demod        : 556
% 5.97/2.14  #Tautology    : 240
% 5.97/2.14  #SimpNegUnit  : 0
% 5.97/2.14  #BackRed      : 3
% 5.97/2.14  
% 5.97/2.14  #Partial instantiations: 0
% 5.97/2.14  #Strategies tried      : 1
% 5.97/2.14  
% 5.97/2.14  Timing (in seconds)
% 5.97/2.14  ----------------------
% 5.97/2.15  Preprocessing        : 0.32
% 5.97/2.15  Parsing              : 0.16
% 5.97/2.15  CNF conversion       : 0.02
% 5.97/2.15  Main loop            : 1.07
% 5.97/2.15  Inferencing          : 0.31
% 5.97/2.15  Reduction            : 0.44
% 5.97/2.15  Demodulation         : 0.37
% 5.97/2.15  BG Simplification    : 0.05
% 5.97/2.15  Subsumption          : 0.20
% 5.97/2.15  Abstraction          : 0.06
% 5.97/2.15  MUC search           : 0.00
% 5.97/2.15  Cooper               : 0.00
% 5.97/2.15  Total                : 1.42
% 5.97/2.15  Index Insertion      : 0.00
% 5.97/2.15  Index Deletion       : 0.00
% 5.97/2.15  Index Matching       : 0.00
% 5.97/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
