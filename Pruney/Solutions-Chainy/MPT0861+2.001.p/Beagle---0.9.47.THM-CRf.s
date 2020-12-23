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
% DateTime   : Thu Dec  3 10:09:01 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 132 expanded)
%              Number of leaves         :   30 (  57 expanded)
%              Depth                    :    7
%              Number of atoms          :   92 ( 243 expanded)
%              Number of equality atoms :   31 (  97 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k1_tarski(D)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & k2_mcart_1(A) = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_mcart_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C)
        & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_95,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) )
     => ( ! [D,E] : A != k4_tarski(D,E)
        | r2_hidden(A,k2_zfmisc_1(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_mcart_1)).

tff(c_60,plain,
    ( k1_mcart_1('#skF_3') != '#skF_5'
    | k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_93,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_58,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_151,plain,(
    ! [A_71,C_72,B_73] :
      ( k2_mcart_1(A_71) = C_72
      | ~ r2_hidden(A_71,k2_zfmisc_1(B_73,k1_tarski(C_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_154,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_58,c_151])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_154])).

tff(c_159,plain,(
    k1_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_160,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_62,plain,
    ( k1_mcart_1('#skF_3') != '#skF_4'
    | k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_166,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_62])).

tff(c_26,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_178,plain,(
    ! [B_82,C_83,A_84] :
      ( r2_hidden(B_82,C_83)
      | ~ r1_tarski(k2_tarski(A_84,B_82),C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_196,plain,(
    ! [B_88,A_89] : r2_hidden(B_88,k2_tarski(A_89,B_88)) ),
    inference(resolution,[status(thm)],[c_24,c_178])).

tff(c_199,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_196])).

tff(c_220,plain,(
    ! [A_97,B_98,C_99] :
      ( r2_hidden(k1_mcart_1(A_97),B_98)
      | ~ r2_hidden(A_97,k2_zfmisc_1(B_98,C_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_223,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_58,c_220])).

tff(c_277,plain,(
    ! [C_120,A_121,B_122] :
      ( k4_xboole_0(C_120,k2_tarski(A_121,B_122)) = C_120
      | r2_hidden(B_122,C_120)
      | r2_hidden(A_121,C_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_403,plain,(
    ! [D_144,A_145,B_146,C_147] :
      ( ~ r2_hidden(D_144,k2_tarski(A_145,B_146))
      | ~ r2_hidden(D_144,C_147)
      | r2_hidden(B_146,C_147)
      | r2_hidden(A_145,C_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_4])).

tff(c_415,plain,(
    ! [C_148] :
      ( ~ r2_hidden(k1_mcart_1('#skF_3'),C_148)
      | r2_hidden('#skF_5',C_148)
      | r2_hidden('#skF_4',C_148) ) ),
    inference(resolution,[status(thm)],[c_223,c_403])).

tff(c_439,plain,
    ( r2_hidden('#skF_5',k1_tarski(k1_mcart_1('#skF_3')))
    | r2_hidden('#skF_4',k1_tarski(k1_mcart_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_199,c_415])).

tff(c_441,plain,(
    r2_hidden('#skF_4',k1_tarski(k1_mcart_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_439])).

tff(c_56,plain,(
    ! [A_37,B_38] : k2_mcart_1(k4_tarski(A_37,B_38)) = B_38 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_54,plain,(
    ! [A_37,B_38] : k1_mcart_1(k4_tarski(A_37,B_38)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_44,plain,(
    ! [D_29,E_30,B_25,C_26] :
      ( r2_hidden(k4_tarski(D_29,E_30),k2_zfmisc_1(B_25,C_26))
      | ~ r2_hidden(k2_mcart_1(k4_tarski(D_29,E_30)),C_26)
      | ~ r2_hidden(k1_mcart_1(k4_tarski(D_29,E_30)),B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_348,plain,(
    ! [D_132,E_133,B_134,C_135] :
      ( r2_hidden(k4_tarski(D_132,E_133),k2_zfmisc_1(B_134,C_135))
      | ~ r2_hidden(E_133,C_135)
      | ~ r2_hidden(D_132,B_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_44])).

tff(c_50,plain,(
    ! [A_34,C_36,B_35] :
      ( k2_mcart_1(A_34) = C_36
      | ~ r2_hidden(A_34,k2_zfmisc_1(B_35,k1_tarski(C_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_354,plain,(
    ! [D_132,E_133,C_36,B_134] :
      ( k2_mcart_1(k4_tarski(D_132,E_133)) = C_36
      | ~ r2_hidden(E_133,k1_tarski(C_36))
      | ~ r2_hidden(D_132,B_134) ) ),
    inference(resolution,[status(thm)],[c_348,c_50])).

tff(c_364,plain,(
    ! [E_133,C_36,D_132,B_134] :
      ( E_133 = C_36
      | ~ r2_hidden(E_133,k1_tarski(C_36))
      | ~ r2_hidden(D_132,B_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_354])).

tff(c_369,plain,(
    ! [D_132,B_134] : ~ r2_hidden(D_132,B_134) ),
    inference(splitLeft,[status(thm)],[c_364])).

tff(c_386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_369,c_223])).

tff(c_387,plain,(
    ! [E_133,C_36] :
      ( E_133 = C_36
      | ~ r2_hidden(E_133,k1_tarski(C_36)) ) ),
    inference(splitRight,[status(thm)],[c_364])).

tff(c_446,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_441,c_387])).

tff(c_453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_446])).

tff(c_454,plain,(
    r2_hidden('#skF_5',k1_tarski(k1_mcart_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_439])).

tff(c_460,plain,(
    k1_mcart_1('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_454,c_387])).

tff(c_467,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_460])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:31:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.34  
% 2.35/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.34  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 2.35/1.34  
% 2.35/1.34  %Foreground sorts:
% 2.35/1.34  
% 2.35/1.34  
% 2.35/1.34  %Background operators:
% 2.35/1.34  
% 2.35/1.34  
% 2.35/1.34  %Foreground operators:
% 2.35/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.35/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.35/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.35/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.35/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.35/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.35/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.35/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.35/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.35/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.35/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.35/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.35/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.34  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.35/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.35/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.35/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.34  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.35/1.34  
% 2.58/1.36  tff(f_104, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k1_tarski(D))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & (k2_mcart_1(A) = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_mcart_1)).
% 2.58/1.36  tff(f_91, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_mcart_1)).
% 2.58/1.36  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.58/1.36  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.58/1.36  tff(f_63, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.58/1.36  tff(f_69, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.58/1.36  tff(f_57, axiom, (![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 2.58/1.36  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.58/1.36  tff(f_95, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.58/1.36  tff(f_79, axiom, (![A, B, C]: ((r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)) => ((![D, E]: ~(A = k4_tarski(D, E))) | r2_hidden(A, k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_mcart_1)).
% 2.58/1.36  tff(c_60, plain, (k1_mcart_1('#skF_3')!='#skF_5' | k2_mcart_1('#skF_3')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.58/1.36  tff(c_93, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(splitLeft, [status(thm)], [c_60])).
% 2.58/1.36  tff(c_58, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.58/1.36  tff(c_151, plain, (![A_71, C_72, B_73]: (k2_mcart_1(A_71)=C_72 | ~r2_hidden(A_71, k2_zfmisc_1(B_73, k1_tarski(C_72))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.58/1.36  tff(c_154, plain, (k2_mcart_1('#skF_3')='#skF_6'), inference(resolution, [status(thm)], [c_58, c_151])).
% 2.58/1.36  tff(c_158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_154])).
% 2.58/1.36  tff(c_159, plain, (k1_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_60])).
% 2.58/1.36  tff(c_160, plain, (k2_mcart_1('#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_60])).
% 2.58/1.36  tff(c_62, plain, (k1_mcart_1('#skF_3')!='#skF_4' | k2_mcart_1('#skF_3')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.58/1.36  tff(c_166, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_160, c_62])).
% 2.58/1.36  tff(c_26, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.58/1.36  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.58/1.36  tff(c_178, plain, (![B_82, C_83, A_84]: (r2_hidden(B_82, C_83) | ~r1_tarski(k2_tarski(A_84, B_82), C_83))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.58/1.36  tff(c_196, plain, (![B_88, A_89]: (r2_hidden(B_88, k2_tarski(A_89, B_88)))), inference(resolution, [status(thm)], [c_24, c_178])).
% 2.58/1.36  tff(c_199, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_196])).
% 2.58/1.36  tff(c_220, plain, (![A_97, B_98, C_99]: (r2_hidden(k1_mcart_1(A_97), B_98) | ~r2_hidden(A_97, k2_zfmisc_1(B_98, C_99)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.58/1.36  tff(c_223, plain, (r2_hidden(k1_mcart_1('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_58, c_220])).
% 2.58/1.36  tff(c_277, plain, (![C_120, A_121, B_122]: (k4_xboole_0(C_120, k2_tarski(A_121, B_122))=C_120 | r2_hidden(B_122, C_120) | r2_hidden(A_121, C_120))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.58/1.36  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.58/1.36  tff(c_403, plain, (![D_144, A_145, B_146, C_147]: (~r2_hidden(D_144, k2_tarski(A_145, B_146)) | ~r2_hidden(D_144, C_147) | r2_hidden(B_146, C_147) | r2_hidden(A_145, C_147))), inference(superposition, [status(thm), theory('equality')], [c_277, c_4])).
% 2.58/1.36  tff(c_415, plain, (![C_148]: (~r2_hidden(k1_mcart_1('#skF_3'), C_148) | r2_hidden('#skF_5', C_148) | r2_hidden('#skF_4', C_148))), inference(resolution, [status(thm)], [c_223, c_403])).
% 2.58/1.36  tff(c_439, plain, (r2_hidden('#skF_5', k1_tarski(k1_mcart_1('#skF_3'))) | r2_hidden('#skF_4', k1_tarski(k1_mcart_1('#skF_3')))), inference(resolution, [status(thm)], [c_199, c_415])).
% 2.58/1.36  tff(c_441, plain, (r2_hidden('#skF_4', k1_tarski(k1_mcart_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_439])).
% 2.58/1.36  tff(c_56, plain, (![A_37, B_38]: (k2_mcart_1(k4_tarski(A_37, B_38))=B_38)), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.58/1.36  tff(c_54, plain, (![A_37, B_38]: (k1_mcart_1(k4_tarski(A_37, B_38))=A_37)), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.58/1.36  tff(c_44, plain, (![D_29, E_30, B_25, C_26]: (r2_hidden(k4_tarski(D_29, E_30), k2_zfmisc_1(B_25, C_26)) | ~r2_hidden(k2_mcart_1(k4_tarski(D_29, E_30)), C_26) | ~r2_hidden(k1_mcart_1(k4_tarski(D_29, E_30)), B_25))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.58/1.36  tff(c_348, plain, (![D_132, E_133, B_134, C_135]: (r2_hidden(k4_tarski(D_132, E_133), k2_zfmisc_1(B_134, C_135)) | ~r2_hidden(E_133, C_135) | ~r2_hidden(D_132, B_134))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_44])).
% 2.58/1.36  tff(c_50, plain, (![A_34, C_36, B_35]: (k2_mcart_1(A_34)=C_36 | ~r2_hidden(A_34, k2_zfmisc_1(B_35, k1_tarski(C_36))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.58/1.36  tff(c_354, plain, (![D_132, E_133, C_36, B_134]: (k2_mcart_1(k4_tarski(D_132, E_133))=C_36 | ~r2_hidden(E_133, k1_tarski(C_36)) | ~r2_hidden(D_132, B_134))), inference(resolution, [status(thm)], [c_348, c_50])).
% 2.58/1.36  tff(c_364, plain, (![E_133, C_36, D_132, B_134]: (E_133=C_36 | ~r2_hidden(E_133, k1_tarski(C_36)) | ~r2_hidden(D_132, B_134))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_354])).
% 2.58/1.36  tff(c_369, plain, (![D_132, B_134]: (~r2_hidden(D_132, B_134))), inference(splitLeft, [status(thm)], [c_364])).
% 2.58/1.36  tff(c_386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_369, c_223])).
% 2.58/1.36  tff(c_387, plain, (![E_133, C_36]: (E_133=C_36 | ~r2_hidden(E_133, k1_tarski(C_36)))), inference(splitRight, [status(thm)], [c_364])).
% 2.58/1.36  tff(c_446, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_441, c_387])).
% 2.58/1.36  tff(c_453, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_446])).
% 2.58/1.36  tff(c_454, plain, (r2_hidden('#skF_5', k1_tarski(k1_mcart_1('#skF_3')))), inference(splitRight, [status(thm)], [c_439])).
% 2.58/1.36  tff(c_460, plain, (k1_mcart_1('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_454, c_387])).
% 2.58/1.36  tff(c_467, plain, $false, inference(negUnitSimplification, [status(thm)], [c_159, c_460])).
% 2.58/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.36  
% 2.58/1.36  Inference rules
% 2.58/1.36  ----------------------
% 2.58/1.36  #Ref     : 0
% 2.58/1.36  #Sup     : 81
% 2.58/1.36  #Fact    : 0
% 2.58/1.36  #Define  : 0
% 2.58/1.36  #Split   : 3
% 2.58/1.36  #Chain   : 0
% 2.58/1.36  #Close   : 0
% 2.58/1.36  
% 2.58/1.36  Ordering : KBO
% 2.58/1.36  
% 2.58/1.36  Simplification rules
% 2.58/1.36  ----------------------
% 2.58/1.36  #Subsume      : 20
% 2.58/1.36  #Demod        : 21
% 2.58/1.36  #Tautology    : 45
% 2.58/1.36  #SimpNegUnit  : 19
% 2.58/1.36  #BackRed      : 10
% 2.58/1.36  
% 2.58/1.36  #Partial instantiations: 0
% 2.58/1.36  #Strategies tried      : 1
% 2.58/1.36  
% 2.58/1.36  Timing (in seconds)
% 2.58/1.36  ----------------------
% 2.58/1.36  Preprocessing        : 0.32
% 2.58/1.36  Parsing              : 0.17
% 2.58/1.36  CNF conversion       : 0.02
% 2.58/1.36  Main loop            : 0.25
% 2.58/1.36  Inferencing          : 0.09
% 2.58/1.36  Reduction            : 0.08
% 2.58/1.36  Demodulation         : 0.06
% 2.58/1.36  BG Simplification    : 0.02
% 2.58/1.36  Subsumption          : 0.05
% 2.58/1.36  Abstraction          : 0.01
% 2.58/1.36  MUC search           : 0.00
% 2.58/1.36  Cooper               : 0.00
% 2.58/1.36  Total                : 0.61
% 2.58/1.36  Index Insertion      : 0.00
% 2.58/1.36  Index Deletion       : 0.00
% 2.58/1.36  Index Matching       : 0.00
% 2.58/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
