%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:03 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   51 (  87 expanded)
%              Number of leaves         :   22 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   69 ( 160 expanded)
%              Number of equality atoms :   32 (  94 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k1_tarski(D)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & k2_mcart_1(A) = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_mcart_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) )
     => ( ! [D,E] : A != k4_tarski(D,E)
        | r2_hidden(A,k2_zfmisc_1(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_mcart_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(B,k2_tarski(C,D)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & ( k2_mcart_1(A) = C
          | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_mcart_1)).

tff(c_28,plain,
    ( k1_mcart_1('#skF_1') != '#skF_3'
    | k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_59,plain,(
    k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_26,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k2_tarski('#skF_2','#skF_3'),k1_tarski('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_69,plain,(
    ! [A_33,C_34,B_35] :
      ( k2_mcart_1(A_33) = C_34
      | ~ r2_hidden(A_33,k2_zfmisc_1(B_35,k1_tarski(C_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_72,plain,(
    k2_mcart_1('#skF_1') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_26,c_69])).

tff(c_76,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_72])).

tff(c_78,plain,(
    k2_mcart_1('#skF_1') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_30,plain,
    ( k1_mcart_1('#skF_1') != '#skF_2'
    | k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_79,plain,(
    k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_85,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_79])).

tff(c_86,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_77,plain,(
    k1_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_108,plain,(
    ! [A_41,B_42,C_43] :
      ( r2_hidden(k1_mcart_1(A_41),B_42)
      | ~ r2_hidden(A_41,k2_zfmisc_1(B_42,C_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_111,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),k2_tarski('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_108])).

tff(c_24,plain,(
    ! [A_24,B_25] : k2_mcart_1(k4_tarski(A_24,B_25)) = B_25 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22,plain,(
    ! [A_24,B_25] : k1_mcart_1(k4_tarski(A_24,B_25)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12,plain,(
    ! [D_15,E_16,B_11,C_12] :
      ( r2_hidden(k4_tarski(D_15,E_16),k2_zfmisc_1(B_11,C_12))
      | ~ r2_hidden(k2_mcart_1(k4_tarski(D_15,E_16)),C_12)
      | ~ r2_hidden(k1_mcart_1(k4_tarski(D_15,E_16)),B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_130,plain,(
    ! [D_54,E_55,B_56,C_57] :
      ( r2_hidden(k4_tarski(D_54,E_55),k2_zfmisc_1(B_56,C_57))
      | ~ r2_hidden(E_55,C_57)
      | ~ r2_hidden(D_54,B_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_12])).

tff(c_18,plain,(
    ! [A_20,D_23,C_22,B_21] :
      ( k2_mcart_1(A_20) = D_23
      | k2_mcart_1(A_20) = C_22
      | ~ r2_hidden(A_20,k2_zfmisc_1(B_21,k2_tarski(C_22,D_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_134,plain,(
    ! [E_55,B_56,C_22,D_23,D_54] :
      ( k2_mcart_1(k4_tarski(D_54,E_55)) = D_23
      | k2_mcart_1(k4_tarski(D_54,E_55)) = C_22
      | ~ r2_hidden(E_55,k2_tarski(C_22,D_23))
      | ~ r2_hidden(D_54,B_56) ) ),
    inference(resolution,[status(thm)],[c_130,c_18])).

tff(c_144,plain,(
    ! [E_55,B_56,C_22,D_23,D_54] :
      ( E_55 = D_23
      | E_55 = C_22
      | ~ r2_hidden(E_55,k2_tarski(C_22,D_23))
      | ~ r2_hidden(D_54,B_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_134])).

tff(c_160,plain,(
    ! [D_54,B_56] : ~ r2_hidden(D_54,B_56) ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_121,plain,(
    ! [A_47,C_48,B_49] :
      ( r2_hidden(k2_mcart_1(A_47),C_48)
      | ~ r2_hidden(A_47,k2_zfmisc_1(B_49,C_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_123,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_26,c_121])).

tff(c_125,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_123])).

tff(c_167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_125])).

tff(c_175,plain,(
    ! [E_60,D_61,C_62] :
      ( E_60 = D_61
      | E_60 = C_62
      | ~ r2_hidden(E_60,k2_tarski(C_62,D_61)) ) ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_178,plain,
    ( k1_mcart_1('#skF_1') = '#skF_3'
    | k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_111,c_175])).

tff(c_185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_77,c_178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.29  
% 2.07/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.30  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.07/1.30  
% 2.07/1.30  %Foreground sorts:
% 2.07/1.30  
% 2.07/1.30  
% 2.07/1.30  %Background operators:
% 2.07/1.30  
% 2.07/1.30  
% 2.07/1.30  %Foreground operators:
% 2.07/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.07/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.07/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.07/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.07/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.07/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.30  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.07/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.07/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.30  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.07/1.30  
% 2.07/1.31  tff(f_74, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k1_tarski(D))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & (k2_mcart_1(A) = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_mcart_1)).
% 2.07/1.31  tff(f_53, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_mcart_1)).
% 2.07/1.31  tff(f_37, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.07/1.31  tff(f_65, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.07/1.31  tff(f_47, axiom, (![A, B, C]: ((r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)) => ((![D, E]: ~(A = k4_tarski(D, E))) | r2_hidden(A, k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_mcart_1)).
% 2.07/1.31  tff(f_61, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(B, k2_tarski(C, D))) => (r2_hidden(k1_mcart_1(A), B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_mcart_1)).
% 2.07/1.31  tff(c_28, plain, (k1_mcart_1('#skF_1')!='#skF_3' | k2_mcart_1('#skF_1')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.07/1.31  tff(c_59, plain, (k2_mcart_1('#skF_1')!='#skF_4'), inference(splitLeft, [status(thm)], [c_28])).
% 2.07/1.31  tff(c_26, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k2_tarski('#skF_2', '#skF_3'), k1_tarski('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.07/1.31  tff(c_69, plain, (![A_33, C_34, B_35]: (k2_mcart_1(A_33)=C_34 | ~r2_hidden(A_33, k2_zfmisc_1(B_35, k1_tarski(C_34))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.07/1.31  tff(c_72, plain, (k2_mcart_1('#skF_1')='#skF_4'), inference(resolution, [status(thm)], [c_26, c_69])).
% 2.07/1.31  tff(c_76, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_72])).
% 2.07/1.31  tff(c_78, plain, (k2_mcart_1('#skF_1')='#skF_4'), inference(splitRight, [status(thm)], [c_28])).
% 2.07/1.31  tff(c_30, plain, (k1_mcart_1('#skF_1')!='#skF_2' | k2_mcart_1('#skF_1')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.07/1.31  tff(c_79, plain, (k2_mcart_1('#skF_1')!='#skF_4'), inference(splitLeft, [status(thm)], [c_30])).
% 2.07/1.31  tff(c_85, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_79])).
% 2.07/1.31  tff(c_86, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(splitRight, [status(thm)], [c_30])).
% 2.07/1.31  tff(c_77, plain, (k1_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_28])).
% 2.07/1.31  tff(c_108, plain, (![A_41, B_42, C_43]: (r2_hidden(k1_mcart_1(A_41), B_42) | ~r2_hidden(A_41, k2_zfmisc_1(B_42, C_43)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.07/1.31  tff(c_111, plain, (r2_hidden(k1_mcart_1('#skF_1'), k2_tarski('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_108])).
% 2.07/1.31  tff(c_24, plain, (![A_24, B_25]: (k2_mcart_1(k4_tarski(A_24, B_25))=B_25)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.07/1.31  tff(c_22, plain, (![A_24, B_25]: (k1_mcart_1(k4_tarski(A_24, B_25))=A_24)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.07/1.31  tff(c_12, plain, (![D_15, E_16, B_11, C_12]: (r2_hidden(k4_tarski(D_15, E_16), k2_zfmisc_1(B_11, C_12)) | ~r2_hidden(k2_mcart_1(k4_tarski(D_15, E_16)), C_12) | ~r2_hidden(k1_mcart_1(k4_tarski(D_15, E_16)), B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.07/1.31  tff(c_130, plain, (![D_54, E_55, B_56, C_57]: (r2_hidden(k4_tarski(D_54, E_55), k2_zfmisc_1(B_56, C_57)) | ~r2_hidden(E_55, C_57) | ~r2_hidden(D_54, B_56))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_12])).
% 2.07/1.31  tff(c_18, plain, (![A_20, D_23, C_22, B_21]: (k2_mcart_1(A_20)=D_23 | k2_mcart_1(A_20)=C_22 | ~r2_hidden(A_20, k2_zfmisc_1(B_21, k2_tarski(C_22, D_23))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.07/1.31  tff(c_134, plain, (![E_55, B_56, C_22, D_23, D_54]: (k2_mcart_1(k4_tarski(D_54, E_55))=D_23 | k2_mcart_1(k4_tarski(D_54, E_55))=C_22 | ~r2_hidden(E_55, k2_tarski(C_22, D_23)) | ~r2_hidden(D_54, B_56))), inference(resolution, [status(thm)], [c_130, c_18])).
% 2.07/1.31  tff(c_144, plain, (![E_55, B_56, C_22, D_23, D_54]: (E_55=D_23 | E_55=C_22 | ~r2_hidden(E_55, k2_tarski(C_22, D_23)) | ~r2_hidden(D_54, B_56))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_134])).
% 2.07/1.31  tff(c_160, plain, (![D_54, B_56]: (~r2_hidden(D_54, B_56))), inference(splitLeft, [status(thm)], [c_144])).
% 2.07/1.31  tff(c_121, plain, (![A_47, C_48, B_49]: (r2_hidden(k2_mcart_1(A_47), C_48) | ~r2_hidden(A_47, k2_zfmisc_1(B_49, C_48)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.07/1.31  tff(c_123, plain, (r2_hidden(k2_mcart_1('#skF_1'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_121])).
% 2.07/1.31  tff(c_125, plain, (r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_123])).
% 2.07/1.31  tff(c_167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_125])).
% 2.07/1.31  tff(c_175, plain, (![E_60, D_61, C_62]: (E_60=D_61 | E_60=C_62 | ~r2_hidden(E_60, k2_tarski(C_62, D_61)))), inference(splitRight, [status(thm)], [c_144])).
% 2.07/1.31  tff(c_178, plain, (k1_mcart_1('#skF_1')='#skF_3' | k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_111, c_175])).
% 2.07/1.31  tff(c_185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_77, c_178])).
% 2.07/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.31  
% 2.07/1.31  Inference rules
% 2.07/1.31  ----------------------
% 2.07/1.31  #Ref     : 0
% 2.07/1.31  #Sup     : 28
% 2.07/1.31  #Fact    : 0
% 2.07/1.31  #Define  : 0
% 2.07/1.31  #Split   : 4
% 2.07/1.31  #Chain   : 0
% 2.07/1.31  #Close   : 0
% 2.07/1.31  
% 2.07/1.31  Ordering : KBO
% 2.07/1.31  
% 2.07/1.31  Simplification rules
% 2.07/1.31  ----------------------
% 2.07/1.31  #Subsume      : 14
% 2.07/1.31  #Demod        : 11
% 2.07/1.31  #Tautology    : 21
% 2.07/1.31  #SimpNegUnit  : 14
% 2.07/1.31  #BackRed      : 6
% 2.07/1.31  
% 2.07/1.31  #Partial instantiations: 0
% 2.07/1.31  #Strategies tried      : 1
% 2.07/1.31  
% 2.07/1.31  Timing (in seconds)
% 2.07/1.31  ----------------------
% 2.07/1.31  Preprocessing        : 0.36
% 2.07/1.31  Parsing              : 0.17
% 2.07/1.31  CNF conversion       : 0.02
% 2.07/1.31  Main loop            : 0.15
% 2.07/1.31  Inferencing          : 0.05
% 2.07/1.31  Reduction            : 0.05
% 2.07/1.31  Demodulation         : 0.04
% 2.07/1.31  BG Simplification    : 0.01
% 2.07/1.31  Subsumption          : 0.02
% 2.07/1.31  Abstraction          : 0.01
% 2.07/1.31  MUC search           : 0.00
% 2.07/1.31  Cooper               : 0.00
% 2.07/1.31  Total                : 0.53
% 2.07/1.31  Index Insertion      : 0.00
% 2.07/1.31  Index Deletion       : 0.00
% 2.07/1.31  Index Matching       : 0.00
% 2.07/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
