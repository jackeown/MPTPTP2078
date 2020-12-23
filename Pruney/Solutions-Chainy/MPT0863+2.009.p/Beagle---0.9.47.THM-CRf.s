%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:08 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 136 expanded)
%              Number of leaves         :   21 (  58 expanded)
%              Depth                    :    7
%              Number of atoms          :   93 ( 292 expanded)
%              Number of equality atoms :   49 ( 174 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k2_tarski(D,E)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & ( k2_mcart_1(A) = D
            | k2_mcart_1(A) = E ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_mcart_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(B,k2_tarski(C,D)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & ( k2_mcart_1(A) = C
          | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) )
     => ( ! [D,E] : A != k4_tarski(D,E)
        | r2_hidden(A,k2_zfmisc_1(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_mcart_1)).

tff(c_26,plain,
    ( k1_mcart_1('#skF_1') != '#skF_3'
    | k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_48,plain,(
    k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_22,plain,
    ( k1_mcart_1('#skF_1') != '#skF_3'
    | k2_mcart_1('#skF_1') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_49,plain,(
    k2_mcart_1('#skF_1') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_20,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k2_tarski('#skF_2','#skF_3'),k2_tarski('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_85,plain,(
    ! [A_41,D_42,C_43,B_44] :
      ( k2_mcart_1(A_41) = D_42
      | k2_mcart_1(A_41) = C_43
      | ~ r2_hidden(A_41,k2_zfmisc_1(B_44,k2_tarski(C_43,D_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_92,plain,
    ( k2_mcart_1('#skF_1') = '#skF_5'
    | k2_mcart_1('#skF_1') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20,c_85])).

tff(c_98,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_49,c_92])).

tff(c_100,plain,(
    k2_mcart_1('#skF_1') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_24,plain,
    ( k1_mcart_1('#skF_1') != '#skF_2'
    | k2_mcart_1('#skF_1') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_107,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_24])).

tff(c_99,plain,(
    k1_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_132,plain,(
    ! [A_53,B_54,C_55] :
      ( r2_hidden(k1_mcart_1(A_53),B_54)
      | ~ r2_hidden(A_53,k2_zfmisc_1(B_54,C_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_135,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),k2_tarski('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_132])).

tff(c_18,plain,(
    ! [A_20,B_21] : k2_mcart_1(k4_tarski(A_20,B_21)) = B_21 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [A_20,B_21] : k1_mcart_1(k4_tarski(A_20,B_21)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [D_14,E_15,B_10,C_11] :
      ( r2_hidden(k4_tarski(D_14,E_15),k2_zfmisc_1(B_10,C_11))
      | ~ r2_hidden(k2_mcart_1(k4_tarski(D_14,E_15)),C_11)
      | ~ r2_hidden(k1_mcart_1(k4_tarski(D_14,E_15)),B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_143,plain,(
    ! [D_60,E_61,B_62,C_63] :
      ( r2_hidden(k4_tarski(D_60,E_61),k2_zfmisc_1(B_62,C_63))
      | ~ r2_hidden(E_61,C_63)
      | ~ r2_hidden(D_60,B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18,c_10])).

tff(c_12,plain,(
    ! [A_16,D_19,C_18,B_17] :
      ( k2_mcart_1(A_16) = D_19
      | k2_mcart_1(A_16) = C_18
      | ~ r2_hidden(A_16,k2_zfmisc_1(B_17,k2_tarski(C_18,D_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_147,plain,(
    ! [E_61,B_62,C_18,D_19,D_60] :
      ( k2_mcart_1(k4_tarski(D_60,E_61)) = D_19
      | k2_mcart_1(k4_tarski(D_60,E_61)) = C_18
      | ~ r2_hidden(E_61,k2_tarski(C_18,D_19))
      | ~ r2_hidden(D_60,B_62) ) ),
    inference(resolution,[status(thm)],[c_143,c_12])).

tff(c_153,plain,(
    ! [E_61,B_62,C_18,D_19,D_60] :
      ( E_61 = D_19
      | E_61 = C_18
      | ~ r2_hidden(E_61,k2_tarski(C_18,D_19))
      | ~ r2_hidden(D_60,B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_147])).

tff(c_158,plain,(
    ! [D_60,B_62] : ~ r2_hidden(D_60,B_62) ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_135])).

tff(c_167,plain,(
    ! [E_64,D_65,C_66] :
      ( E_64 = D_65
      | E_64 = C_66
      | ~ r2_hidden(E_64,k2_tarski(C_66,D_65)) ) ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_170,plain,
    ( k1_mcart_1('#skF_1') = '#skF_3'
    | k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_135,c_167])).

tff(c_177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_99,c_170])).

tff(c_179,plain,(
    k2_mcart_1('#skF_1') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_28,plain,
    ( k1_mcart_1('#skF_1') != '#skF_2'
    | k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_185,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_28])).

tff(c_178,plain,(
    k1_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_211,plain,(
    ! [A_75,B_76,C_77] :
      ( r2_hidden(k1_mcart_1(A_75),B_76)
      | ~ r2_hidden(A_75,k2_zfmisc_1(B_76,C_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_214,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),k2_tarski('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_211])).

tff(c_221,plain,(
    ! [D_82,E_83,B_84,C_85] :
      ( r2_hidden(k4_tarski(D_82,E_83),k2_zfmisc_1(B_84,C_85))
      | ~ r2_hidden(E_83,C_85)
      | ~ r2_hidden(D_82,B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18,c_10])).

tff(c_225,plain,(
    ! [E_83,C_18,B_84,D_19,D_82] :
      ( k2_mcart_1(k4_tarski(D_82,E_83)) = D_19
      | k2_mcart_1(k4_tarski(D_82,E_83)) = C_18
      | ~ r2_hidden(E_83,k2_tarski(C_18,D_19))
      | ~ r2_hidden(D_82,B_84) ) ),
    inference(resolution,[status(thm)],[c_221,c_12])).

tff(c_231,plain,(
    ! [E_83,C_18,B_84,D_19,D_82] :
      ( E_83 = D_19
      | E_83 = C_18
      | ~ r2_hidden(E_83,k2_tarski(C_18,D_19))
      | ~ r2_hidden(D_82,B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_225])).

tff(c_236,plain,(
    ! [D_82,B_84] : ~ r2_hidden(D_82,B_84) ),
    inference(splitLeft,[status(thm)],[c_231])).

tff(c_243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_214])).

tff(c_245,plain,(
    ! [E_86,D_87,C_88] :
      ( E_86 = D_87
      | E_86 = C_88
      | ~ r2_hidden(E_86,k2_tarski(C_88,D_87)) ) ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_248,plain,
    ( k1_mcart_1('#skF_1') = '#skF_3'
    | k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_214,c_245])).

tff(c_255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_178,c_248])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.26  
% 2.10/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.26  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.10/1.26  
% 2.10/1.26  %Foreground sorts:
% 2.10/1.26  
% 2.10/1.26  
% 2.10/1.26  %Background operators:
% 2.10/1.26  
% 2.10/1.26  
% 2.10/1.26  %Foreground operators:
% 2.10/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.10/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.10/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.10/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.10/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.26  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.10/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.10/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.26  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.10/1.26  
% 2.19/1.27  tff(f_68, negated_conjecture, ~(![A, B, C, D, E]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k2_tarski(D, E))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & ((k2_mcart_1(A) = D) | (k2_mcart_1(A) = E))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_mcart_1)).
% 2.19/1.27  tff(f_53, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(B, k2_tarski(C, D))) => (r2_hidden(k1_mcart_1(A), B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_mcart_1)).
% 2.19/1.27  tff(f_35, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.19/1.27  tff(f_57, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.19/1.27  tff(f_45, axiom, (![A, B, C]: ((r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)) => ((![D, E]: ~(A = k4_tarski(D, E))) | r2_hidden(A, k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_mcart_1)).
% 2.19/1.27  tff(c_26, plain, (k1_mcart_1('#skF_1')!='#skF_3' | k2_mcart_1('#skF_1')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.19/1.27  tff(c_48, plain, (k2_mcart_1('#skF_1')!='#skF_4'), inference(splitLeft, [status(thm)], [c_26])).
% 2.19/1.27  tff(c_22, plain, (k1_mcart_1('#skF_1')!='#skF_3' | k2_mcart_1('#skF_1')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.19/1.27  tff(c_49, plain, (k2_mcart_1('#skF_1')!='#skF_5'), inference(splitLeft, [status(thm)], [c_22])).
% 2.19/1.27  tff(c_20, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k2_tarski('#skF_2', '#skF_3'), k2_tarski('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.19/1.27  tff(c_85, plain, (![A_41, D_42, C_43, B_44]: (k2_mcart_1(A_41)=D_42 | k2_mcart_1(A_41)=C_43 | ~r2_hidden(A_41, k2_zfmisc_1(B_44, k2_tarski(C_43, D_42))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.19/1.27  tff(c_92, plain, (k2_mcart_1('#skF_1')='#skF_5' | k2_mcart_1('#skF_1')='#skF_4'), inference(resolution, [status(thm)], [c_20, c_85])).
% 2.19/1.27  tff(c_98, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_49, c_92])).
% 2.19/1.27  tff(c_100, plain, (k2_mcart_1('#skF_1')='#skF_5'), inference(splitRight, [status(thm)], [c_22])).
% 2.19/1.27  tff(c_24, plain, (k1_mcart_1('#skF_1')!='#skF_2' | k2_mcart_1('#skF_1')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.19/1.27  tff(c_107, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_24])).
% 2.19/1.27  tff(c_99, plain, (k1_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_22])).
% 2.19/1.27  tff(c_132, plain, (![A_53, B_54, C_55]: (r2_hidden(k1_mcart_1(A_53), B_54) | ~r2_hidden(A_53, k2_zfmisc_1(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.19/1.27  tff(c_135, plain, (r2_hidden(k1_mcart_1('#skF_1'), k2_tarski('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_132])).
% 2.19/1.27  tff(c_18, plain, (![A_20, B_21]: (k2_mcart_1(k4_tarski(A_20, B_21))=B_21)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.19/1.27  tff(c_16, plain, (![A_20, B_21]: (k1_mcart_1(k4_tarski(A_20, B_21))=A_20)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.19/1.27  tff(c_10, plain, (![D_14, E_15, B_10, C_11]: (r2_hidden(k4_tarski(D_14, E_15), k2_zfmisc_1(B_10, C_11)) | ~r2_hidden(k2_mcart_1(k4_tarski(D_14, E_15)), C_11) | ~r2_hidden(k1_mcart_1(k4_tarski(D_14, E_15)), B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.19/1.27  tff(c_143, plain, (![D_60, E_61, B_62, C_63]: (r2_hidden(k4_tarski(D_60, E_61), k2_zfmisc_1(B_62, C_63)) | ~r2_hidden(E_61, C_63) | ~r2_hidden(D_60, B_62))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18, c_10])).
% 2.19/1.27  tff(c_12, plain, (![A_16, D_19, C_18, B_17]: (k2_mcart_1(A_16)=D_19 | k2_mcart_1(A_16)=C_18 | ~r2_hidden(A_16, k2_zfmisc_1(B_17, k2_tarski(C_18, D_19))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.19/1.27  tff(c_147, plain, (![E_61, B_62, C_18, D_19, D_60]: (k2_mcart_1(k4_tarski(D_60, E_61))=D_19 | k2_mcart_1(k4_tarski(D_60, E_61))=C_18 | ~r2_hidden(E_61, k2_tarski(C_18, D_19)) | ~r2_hidden(D_60, B_62))), inference(resolution, [status(thm)], [c_143, c_12])).
% 2.19/1.27  tff(c_153, plain, (![E_61, B_62, C_18, D_19, D_60]: (E_61=D_19 | E_61=C_18 | ~r2_hidden(E_61, k2_tarski(C_18, D_19)) | ~r2_hidden(D_60, B_62))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_147])).
% 2.19/1.27  tff(c_158, plain, (![D_60, B_62]: (~r2_hidden(D_60, B_62))), inference(splitLeft, [status(thm)], [c_153])).
% 2.19/1.27  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_158, c_135])).
% 2.19/1.27  tff(c_167, plain, (![E_64, D_65, C_66]: (E_64=D_65 | E_64=C_66 | ~r2_hidden(E_64, k2_tarski(C_66, D_65)))), inference(splitRight, [status(thm)], [c_153])).
% 2.19/1.27  tff(c_170, plain, (k1_mcart_1('#skF_1')='#skF_3' | k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_135, c_167])).
% 2.19/1.27  tff(c_177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_99, c_170])).
% 2.19/1.27  tff(c_179, plain, (k2_mcart_1('#skF_1')='#skF_4'), inference(splitRight, [status(thm)], [c_26])).
% 2.19/1.27  tff(c_28, plain, (k1_mcart_1('#skF_1')!='#skF_2' | k2_mcart_1('#skF_1')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.19/1.27  tff(c_185, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_179, c_28])).
% 2.19/1.27  tff(c_178, plain, (k1_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_26])).
% 2.19/1.27  tff(c_211, plain, (![A_75, B_76, C_77]: (r2_hidden(k1_mcart_1(A_75), B_76) | ~r2_hidden(A_75, k2_zfmisc_1(B_76, C_77)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.19/1.27  tff(c_214, plain, (r2_hidden(k1_mcart_1('#skF_1'), k2_tarski('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_211])).
% 2.19/1.27  tff(c_221, plain, (![D_82, E_83, B_84, C_85]: (r2_hidden(k4_tarski(D_82, E_83), k2_zfmisc_1(B_84, C_85)) | ~r2_hidden(E_83, C_85) | ~r2_hidden(D_82, B_84))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18, c_10])).
% 2.19/1.27  tff(c_225, plain, (![E_83, C_18, B_84, D_19, D_82]: (k2_mcart_1(k4_tarski(D_82, E_83))=D_19 | k2_mcart_1(k4_tarski(D_82, E_83))=C_18 | ~r2_hidden(E_83, k2_tarski(C_18, D_19)) | ~r2_hidden(D_82, B_84))), inference(resolution, [status(thm)], [c_221, c_12])).
% 2.19/1.27  tff(c_231, plain, (![E_83, C_18, B_84, D_19, D_82]: (E_83=D_19 | E_83=C_18 | ~r2_hidden(E_83, k2_tarski(C_18, D_19)) | ~r2_hidden(D_82, B_84))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_225])).
% 2.19/1.27  tff(c_236, plain, (![D_82, B_84]: (~r2_hidden(D_82, B_84))), inference(splitLeft, [status(thm)], [c_231])).
% 2.19/1.27  tff(c_243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_236, c_214])).
% 2.19/1.27  tff(c_245, plain, (![E_86, D_87, C_88]: (E_86=D_87 | E_86=C_88 | ~r2_hidden(E_86, k2_tarski(C_88, D_87)))), inference(splitRight, [status(thm)], [c_231])).
% 2.19/1.27  tff(c_248, plain, (k1_mcart_1('#skF_1')='#skF_3' | k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_214, c_245])).
% 2.19/1.27  tff(c_255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_185, c_178, c_248])).
% 2.19/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.27  
% 2.19/1.27  Inference rules
% 2.19/1.27  ----------------------
% 2.19/1.27  #Ref     : 0
% 2.19/1.27  #Sup     : 42
% 2.19/1.27  #Fact    : 0
% 2.19/1.27  #Define  : 0
% 2.19/1.27  #Split   : 4
% 2.19/1.27  #Chain   : 0
% 2.19/1.27  #Close   : 0
% 2.19/1.27  
% 2.19/1.27  Ordering : KBO
% 2.19/1.27  
% 2.19/1.27  Simplification rules
% 2.19/1.27  ----------------------
% 2.19/1.27  #Subsume      : 14
% 2.19/1.27  #Demod        : 26
% 2.19/1.27  #Tautology    : 28
% 2.19/1.27  #SimpNegUnit  : 16
% 2.19/1.27  #BackRed      : 7
% 2.19/1.27  
% 2.19/1.27  #Partial instantiations: 0
% 2.19/1.27  #Strategies tried      : 1
% 2.19/1.27  
% 2.19/1.27  Timing (in seconds)
% 2.19/1.27  ----------------------
% 2.19/1.28  Preprocessing        : 0.31
% 2.19/1.28  Parsing              : 0.16
% 2.19/1.28  CNF conversion       : 0.02
% 2.19/1.28  Main loop            : 0.18
% 2.19/1.28  Inferencing          : 0.07
% 2.19/1.28  Reduction            : 0.06
% 2.19/1.28  Demodulation         : 0.04
% 2.19/1.28  BG Simplification    : 0.01
% 2.19/1.28  Subsumption          : 0.02
% 2.19/1.28  Abstraction          : 0.01
% 2.19/1.28  MUC search           : 0.00
% 2.19/1.28  Cooper               : 0.00
% 2.19/1.28  Total                : 0.52
% 2.19/1.28  Index Insertion      : 0.00
% 2.19/1.28  Index Deletion       : 0.00
% 2.19/1.28  Index Matching       : 0.00
% 2.19/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
