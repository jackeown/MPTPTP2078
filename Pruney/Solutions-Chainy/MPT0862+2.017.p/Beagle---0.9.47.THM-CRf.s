%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:06 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   47 (  81 expanded)
%              Number of leaves         :   20 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 ( 152 expanded)
%              Number of equality atoms :   31 (  88 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k2_tarski(C,D)))
       => ( k1_mcart_1(A) = B
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) )
     => ( ! [D,E] : A != k4_tarski(D,E)
        | r2_hidden(A,k2_zfmisc_1(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_mcart_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),D))
     => ( ( k1_mcart_1(A) = B
          | k1_mcart_1(A) = C )
        & r2_hidden(k2_mcart_1(A),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

tff(c_24,plain,
    ( k2_mcart_1('#skF_1') != '#skF_4'
    | k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_55,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_22,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k1_tarski('#skF_2'),k2_tarski('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_64,plain,(
    ! [A_32,B_33,C_34] :
      ( k1_mcart_1(A_32) = B_33
      | ~ r2_hidden(A_32,k2_zfmisc_1(k1_tarski(B_33),C_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_67,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_22,c_64])).

tff(c_71,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_67])).

tff(c_73,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_26,plain,
    ( k2_mcart_1('#skF_1') != '#skF_3'
    | k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_79,plain,(
    k2_mcart_1('#skF_1') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_26])).

tff(c_72,plain,(
    k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_86,plain,(
    ! [A_38,C_39,B_40] :
      ( r2_hidden(k2_mcart_1(A_38),C_39)
      | ~ r2_hidden(A_38,k2_zfmisc_1(B_40,C_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_89,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),k2_tarski('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_22,c_86])).

tff(c_18,plain,(
    ! [A_19,B_20] : k1_mcart_1(k4_tarski(A_19,B_20)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    ! [A_19,B_20] : k2_mcart_1(k4_tarski(A_19,B_20)) = B_20 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [D_10,E_11,B_6,C_7] :
      ( r2_hidden(k4_tarski(D_10,E_11),k2_zfmisc_1(B_6,C_7))
      | ~ r2_hidden(k2_mcart_1(k4_tarski(D_10,E_11)),C_7)
      | ~ r2_hidden(k1_mcart_1(k4_tarski(D_10,E_11)),B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_27,plain,(
    ! [D_10,E_11,B_6,C_7] :
      ( r2_hidden(k4_tarski(D_10,E_11),k2_zfmisc_1(B_6,C_7))
      | ~ r2_hidden(E_11,C_7)
      | ~ r2_hidden(D_10,B_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_8])).

tff(c_125,plain,(
    ! [A_50,C_51,B_52,D_53] :
      ( k1_mcart_1(A_50) = C_51
      | k1_mcart_1(A_50) = B_52
      | ~ r2_hidden(A_50,k2_zfmisc_1(k2_tarski(B_52,C_51),D_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_129,plain,(
    ! [B_52,C_7,C_51,D_10,E_11] :
      ( k1_mcart_1(k4_tarski(D_10,E_11)) = C_51
      | k1_mcart_1(k4_tarski(D_10,E_11)) = B_52
      | ~ r2_hidden(E_11,C_7)
      | ~ r2_hidden(D_10,k2_tarski(B_52,C_51)) ) ),
    inference(resolution,[status(thm)],[c_27,c_125])).

tff(c_134,plain,(
    ! [B_52,C_7,C_51,D_10,E_11] :
      ( D_10 = C_51
      | D_10 = B_52
      | ~ r2_hidden(E_11,C_7)
      | ~ r2_hidden(D_10,k2_tarski(B_52,C_51)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_129])).

tff(c_135,plain,(
    ! [E_11,C_7] : ~ r2_hidden(E_11,C_7) ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_90,plain,(
    ! [A_41,B_42,C_43] :
      ( r2_hidden(k1_mcart_1(A_41),B_42)
      | ~ r2_hidden(A_41,k2_zfmisc_1(B_42,C_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_92,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_90])).

tff(c_94,plain,(
    r2_hidden('#skF_2',k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_92])).

tff(c_142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_94])).

tff(c_144,plain,(
    ! [D_54,C_55,B_56] :
      ( D_54 = C_55
      | D_54 = B_56
      | ~ r2_hidden(D_54,k2_tarski(B_56,C_55)) ) ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_147,plain,
    ( k2_mcart_1('#skF_1') = '#skF_4'
    | k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_89,c_144])).

tff(c_154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_72,c_147])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:09:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.29  
% 1.96/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.30  %$ r2_hidden > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.96/1.30  
% 1.96/1.30  %Foreground sorts:
% 1.96/1.30  
% 1.96/1.30  
% 1.96/1.30  %Background operators:
% 1.96/1.30  
% 1.96/1.30  
% 1.96/1.30  %Foreground operators:
% 1.96/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.96/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.96/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.30  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.30  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.30  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.30  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.96/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.96/1.30  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.30  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.96/1.30  
% 2.12/1.31  tff(f_70, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k2_tarski(C, D))) => ((k1_mcart_1(A) = B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_mcart_1)).
% 2.12/1.31  tff(f_49, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 2.12/1.31  tff(f_33, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.12/1.31  tff(f_61, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.12/1.31  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)) => ((![D, E]: ~(A = k4_tarski(D, E))) | r2_hidden(A, k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_mcart_1)).
% 2.12/1.31  tff(f_57, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), D)) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & r2_hidden(k2_mcart_1(A), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_mcart_1)).
% 2.12/1.31  tff(c_24, plain, (k2_mcart_1('#skF_1')!='#skF_4' | k1_mcart_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.12/1.31  tff(c_55, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_24])).
% 2.12/1.31  tff(c_22, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k1_tarski('#skF_2'), k2_tarski('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.12/1.31  tff(c_64, plain, (![A_32, B_33, C_34]: (k1_mcart_1(A_32)=B_33 | ~r2_hidden(A_32, k2_zfmisc_1(k1_tarski(B_33), C_34)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.12/1.31  tff(c_67, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_22, c_64])).
% 2.12/1.31  tff(c_71, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_67])).
% 2.12/1.31  tff(c_73, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 2.12/1.31  tff(c_26, plain, (k2_mcart_1('#skF_1')!='#skF_3' | k1_mcart_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.12/1.31  tff(c_79, plain, (k2_mcart_1('#skF_1')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_73, c_26])).
% 2.12/1.31  tff(c_72, plain, (k2_mcart_1('#skF_1')!='#skF_4'), inference(splitRight, [status(thm)], [c_24])).
% 2.12/1.31  tff(c_86, plain, (![A_38, C_39, B_40]: (r2_hidden(k2_mcart_1(A_38), C_39) | ~r2_hidden(A_38, k2_zfmisc_1(B_40, C_39)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.12/1.31  tff(c_89, plain, (r2_hidden(k2_mcart_1('#skF_1'), k2_tarski('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_22, c_86])).
% 2.12/1.31  tff(c_18, plain, (![A_19, B_20]: (k1_mcart_1(k4_tarski(A_19, B_20))=A_19)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.12/1.31  tff(c_20, plain, (![A_19, B_20]: (k2_mcart_1(k4_tarski(A_19, B_20))=B_20)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.12/1.31  tff(c_8, plain, (![D_10, E_11, B_6, C_7]: (r2_hidden(k4_tarski(D_10, E_11), k2_zfmisc_1(B_6, C_7)) | ~r2_hidden(k2_mcart_1(k4_tarski(D_10, E_11)), C_7) | ~r2_hidden(k1_mcart_1(k4_tarski(D_10, E_11)), B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.12/1.31  tff(c_27, plain, (![D_10, E_11, B_6, C_7]: (r2_hidden(k4_tarski(D_10, E_11), k2_zfmisc_1(B_6, C_7)) | ~r2_hidden(E_11, C_7) | ~r2_hidden(D_10, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_8])).
% 2.12/1.31  tff(c_125, plain, (![A_50, C_51, B_52, D_53]: (k1_mcart_1(A_50)=C_51 | k1_mcart_1(A_50)=B_52 | ~r2_hidden(A_50, k2_zfmisc_1(k2_tarski(B_52, C_51), D_53)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.12/1.31  tff(c_129, plain, (![B_52, C_7, C_51, D_10, E_11]: (k1_mcart_1(k4_tarski(D_10, E_11))=C_51 | k1_mcart_1(k4_tarski(D_10, E_11))=B_52 | ~r2_hidden(E_11, C_7) | ~r2_hidden(D_10, k2_tarski(B_52, C_51)))), inference(resolution, [status(thm)], [c_27, c_125])).
% 2.12/1.31  tff(c_134, plain, (![B_52, C_7, C_51, D_10, E_11]: (D_10=C_51 | D_10=B_52 | ~r2_hidden(E_11, C_7) | ~r2_hidden(D_10, k2_tarski(B_52, C_51)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_129])).
% 2.12/1.31  tff(c_135, plain, (![E_11, C_7]: (~r2_hidden(E_11, C_7))), inference(splitLeft, [status(thm)], [c_134])).
% 2.12/1.31  tff(c_90, plain, (![A_41, B_42, C_43]: (r2_hidden(k1_mcart_1(A_41), B_42) | ~r2_hidden(A_41, k2_zfmisc_1(B_42, C_43)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.12/1.31  tff(c_92, plain, (r2_hidden(k1_mcart_1('#skF_1'), k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_90])).
% 2.12/1.31  tff(c_94, plain, (r2_hidden('#skF_2', k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_92])).
% 2.12/1.31  tff(c_142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_94])).
% 2.12/1.31  tff(c_144, plain, (![D_54, C_55, B_56]: (D_54=C_55 | D_54=B_56 | ~r2_hidden(D_54, k2_tarski(B_56, C_55)))), inference(splitRight, [status(thm)], [c_134])).
% 2.12/1.31  tff(c_147, plain, (k2_mcart_1('#skF_1')='#skF_4' | k2_mcart_1('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_89, c_144])).
% 2.12/1.31  tff(c_154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_72, c_147])).
% 2.12/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.31  
% 2.12/1.31  Inference rules
% 2.12/1.31  ----------------------
% 2.12/1.31  #Ref     : 0
% 2.12/1.31  #Sup     : 22
% 2.12/1.31  #Fact    : 0
% 2.12/1.31  #Define  : 0
% 2.12/1.31  #Split   : 3
% 2.12/1.31  #Chain   : 0
% 2.12/1.31  #Close   : 0
% 2.12/1.31  
% 2.12/1.31  Ordering : KBO
% 2.12/1.31  
% 2.12/1.31  Simplification rules
% 2.12/1.31  ----------------------
% 2.12/1.31  #Subsume      : 14
% 2.12/1.31  #Demod        : 10
% 2.12/1.31  #Tautology    : 12
% 2.12/1.31  #SimpNegUnit  : 14
% 2.12/1.31  #BackRed      : 6
% 2.12/1.31  
% 2.12/1.31  #Partial instantiations: 0
% 2.12/1.31  #Strategies tried      : 1
% 2.12/1.31  
% 2.12/1.31  Timing (in seconds)
% 2.12/1.31  ----------------------
% 2.12/1.31  Preprocessing        : 0.31
% 2.12/1.31  Parsing              : 0.16
% 2.12/1.31  CNF conversion       : 0.02
% 2.12/1.31  Main loop            : 0.17
% 2.12/1.31  Inferencing          : 0.05
% 2.12/1.31  Reduction            : 0.07
% 2.12/1.31  Demodulation         : 0.05
% 2.12/1.31  BG Simplification    : 0.01
% 2.12/1.31  Subsumption          : 0.02
% 2.12/1.31  Abstraction          : 0.02
% 2.12/1.31  MUC search           : 0.00
% 2.12/1.31  Cooper               : 0.00
% 2.12/1.31  Total                : 0.53
% 2.12/1.31  Index Insertion      : 0.00
% 2.12/1.31  Index Deletion       : 0.00
% 2.12/1.31  Index Matching       : 0.00
% 2.12/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
