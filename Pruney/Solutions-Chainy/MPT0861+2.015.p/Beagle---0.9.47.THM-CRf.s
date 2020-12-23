%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:03 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   55 (  84 expanded)
%              Number of leaves         :   31 (  45 expanded)
%              Depth                    :    6
%              Number of atoms          :   63 ( 142 expanded)
%              Number of equality atoms :   35 (  84 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k1_tarski(D)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & k2_mcart_1(A) = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(B,k2_tarski(C,D)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & ( k2_mcart_1(A) = C
          | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_68,plain,
    ( k1_mcart_1('#skF_9') != '#skF_11'
    | k2_mcart_1('#skF_9') != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_98,plain,(
    k2_mcart_1('#skF_9') != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_66,plain,(
    r2_hidden('#skF_9',k2_zfmisc_1(k2_tarski('#skF_10','#skF_11'),k1_tarski('#skF_12'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_176,plain,(
    ! [A_91,D_92,C_93,B_94] :
      ( k2_mcart_1(A_91) = D_92
      | k2_mcart_1(A_91) = C_93
      | ~ r2_hidden(A_91,k2_zfmisc_1(B_94,k2_tarski(C_93,D_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_180,plain,(
    ! [A_95,A_96,B_97] :
      ( k2_mcart_1(A_95) = A_96
      | k2_mcart_1(A_95) = A_96
      | ~ r2_hidden(A_95,k2_zfmisc_1(B_97,k1_tarski(A_96))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_176])).

tff(c_183,plain,(
    k2_mcart_1('#skF_9') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_66,c_180])).

tff(c_187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_98,c_183])).

tff(c_189,plain,(
    k2_mcart_1('#skF_9') = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_70,plain,
    ( k1_mcart_1('#skF_9') != '#skF_10'
    | k2_mcart_1('#skF_9') != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_195,plain,(
    k1_mcart_1('#skF_9') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_70])).

tff(c_188,plain,(
    k1_mcart_1('#skF_9') != '#skF_11' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_241,plain,(
    ! [A_116,B_117,C_118] :
      ( r2_hidden(k1_mcart_1(A_116),B_117)
      | ~ r2_hidden(A_116,k2_zfmisc_1(B_117,C_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_244,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_tarski('#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_66,c_241])).

tff(c_64,plain,(
    ! [A_56,B_57] : k2_mcart_1(k4_tarski(A_56,B_57)) = B_57 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    ! [E_45,F_46,A_13,B_14] :
      ( r2_hidden(k4_tarski(E_45,F_46),k2_zfmisc_1(A_13,B_14))
      | ~ r2_hidden(F_46,B_14)
      | ~ r2_hidden(E_45,A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_270,plain,(
    ! [A_129,D_130,C_131,B_132] :
      ( k2_mcart_1(A_129) = D_130
      | k2_mcart_1(A_129) = C_131
      | ~ r2_hidden(A_129,k2_zfmisc_1(B_132,k2_tarski(C_131,D_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_274,plain,(
    ! [F_46,D_130,A_13,E_45,C_131] :
      ( k2_mcart_1(k4_tarski(E_45,F_46)) = D_130
      | k2_mcart_1(k4_tarski(E_45,F_46)) = C_131
      | ~ r2_hidden(F_46,k2_tarski(C_131,D_130))
      | ~ r2_hidden(E_45,A_13) ) ),
    inference(resolution,[status(thm)],[c_26,c_270])).

tff(c_279,plain,(
    ! [F_46,D_130,A_13,E_45,C_131] :
      ( F_46 = D_130
      | F_46 = C_131
      | ~ r2_hidden(F_46,k2_tarski(C_131,D_130))
      | ~ r2_hidden(E_45,A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_274])).

tff(c_280,plain,(
    ! [E_45,A_13] : ~ r2_hidden(E_45,A_13) ),
    inference(splitLeft,[status(thm)],[c_279])).

tff(c_291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_280,c_244])).

tff(c_293,plain,(
    ! [F_133,D_134,C_135] :
      ( F_133 = D_134
      | F_133 = C_135
      | ~ r2_hidden(F_133,k2_tarski(C_135,D_134)) ) ),
    inference(splitRight,[status(thm)],[c_279])).

tff(c_296,plain,
    ( k1_mcart_1('#skF_9') = '#skF_11'
    | k1_mcart_1('#skF_9') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_244,c_293])).

tff(c_303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_188,c_296])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:14:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.26  
% 2.29/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.27  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_12
% 2.29/1.27  
% 2.29/1.27  %Foreground sorts:
% 2.29/1.27  
% 2.29/1.27  
% 2.29/1.27  %Background operators:
% 2.29/1.27  
% 2.29/1.27  
% 2.29/1.27  %Foreground operators:
% 2.29/1.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.29/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.27  tff('#skF_11', type, '#skF_11': $i).
% 2.29/1.27  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.29/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.29/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.29/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.29/1.27  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.29/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.29/1.27  tff('#skF_10', type, '#skF_10': $i).
% 2.29/1.27  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 2.29/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.29/1.27  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.29/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.29/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.29/1.27  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.29/1.27  tff('#skF_9', type, '#skF_9': $i).
% 2.29/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.27  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.29/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.29/1.27  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.29/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.27  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.29/1.27  tff('#skF_12', type, '#skF_12': $i).
% 2.29/1.27  
% 2.42/1.28  tff(f_85, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k1_tarski(D))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & (k2_mcart_1(A) = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_mcart_1)).
% 2.42/1.28  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.42/1.28  tff(f_72, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(B, k2_tarski(C, D))) => (r2_hidden(k1_mcart_1(A), B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_mcart_1)).
% 2.42/1.28  tff(f_64, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.42/1.28  tff(f_76, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.42/1.28  tff(f_53, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 2.42/1.28  tff(c_68, plain, (k1_mcart_1('#skF_9')!='#skF_11' | k2_mcart_1('#skF_9')!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.42/1.28  tff(c_98, plain, (k2_mcart_1('#skF_9')!='#skF_12'), inference(splitLeft, [status(thm)], [c_68])).
% 2.42/1.28  tff(c_66, plain, (r2_hidden('#skF_9', k2_zfmisc_1(k2_tarski('#skF_10', '#skF_11'), k1_tarski('#skF_12')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.42/1.28  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.42/1.28  tff(c_176, plain, (![A_91, D_92, C_93, B_94]: (k2_mcart_1(A_91)=D_92 | k2_mcart_1(A_91)=C_93 | ~r2_hidden(A_91, k2_zfmisc_1(B_94, k2_tarski(C_93, D_92))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.42/1.28  tff(c_180, plain, (![A_95, A_96, B_97]: (k2_mcart_1(A_95)=A_96 | k2_mcart_1(A_95)=A_96 | ~r2_hidden(A_95, k2_zfmisc_1(B_97, k1_tarski(A_96))))), inference(superposition, [status(thm), theory('equality')], [c_20, c_176])).
% 2.42/1.28  tff(c_183, plain, (k2_mcart_1('#skF_9')='#skF_12'), inference(resolution, [status(thm)], [c_66, c_180])).
% 2.42/1.28  tff(c_187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_98, c_183])).
% 2.42/1.28  tff(c_189, plain, (k2_mcart_1('#skF_9')='#skF_12'), inference(splitRight, [status(thm)], [c_68])).
% 2.42/1.28  tff(c_70, plain, (k1_mcart_1('#skF_9')!='#skF_10' | k2_mcart_1('#skF_9')!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.42/1.28  tff(c_195, plain, (k1_mcart_1('#skF_9')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_189, c_70])).
% 2.42/1.28  tff(c_188, plain, (k1_mcart_1('#skF_9')!='#skF_11'), inference(splitRight, [status(thm)], [c_68])).
% 2.42/1.28  tff(c_241, plain, (![A_116, B_117, C_118]: (r2_hidden(k1_mcart_1(A_116), B_117) | ~r2_hidden(A_116, k2_zfmisc_1(B_117, C_118)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.42/1.28  tff(c_244, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_tarski('#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_66, c_241])).
% 2.42/1.28  tff(c_64, plain, (![A_56, B_57]: (k2_mcart_1(k4_tarski(A_56, B_57))=B_57)), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.42/1.28  tff(c_26, plain, (![E_45, F_46, A_13, B_14]: (r2_hidden(k4_tarski(E_45, F_46), k2_zfmisc_1(A_13, B_14)) | ~r2_hidden(F_46, B_14) | ~r2_hidden(E_45, A_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.42/1.28  tff(c_270, plain, (![A_129, D_130, C_131, B_132]: (k2_mcart_1(A_129)=D_130 | k2_mcart_1(A_129)=C_131 | ~r2_hidden(A_129, k2_zfmisc_1(B_132, k2_tarski(C_131, D_130))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.42/1.28  tff(c_274, plain, (![F_46, D_130, A_13, E_45, C_131]: (k2_mcart_1(k4_tarski(E_45, F_46))=D_130 | k2_mcart_1(k4_tarski(E_45, F_46))=C_131 | ~r2_hidden(F_46, k2_tarski(C_131, D_130)) | ~r2_hidden(E_45, A_13))), inference(resolution, [status(thm)], [c_26, c_270])).
% 2.42/1.28  tff(c_279, plain, (![F_46, D_130, A_13, E_45, C_131]: (F_46=D_130 | F_46=C_131 | ~r2_hidden(F_46, k2_tarski(C_131, D_130)) | ~r2_hidden(E_45, A_13))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_64, c_274])).
% 2.42/1.28  tff(c_280, plain, (![E_45, A_13]: (~r2_hidden(E_45, A_13))), inference(splitLeft, [status(thm)], [c_279])).
% 2.42/1.28  tff(c_291, plain, $false, inference(negUnitSimplification, [status(thm)], [c_280, c_244])).
% 2.42/1.28  tff(c_293, plain, (![F_133, D_134, C_135]: (F_133=D_134 | F_133=C_135 | ~r2_hidden(F_133, k2_tarski(C_135, D_134)))), inference(splitRight, [status(thm)], [c_279])).
% 2.42/1.28  tff(c_296, plain, (k1_mcart_1('#skF_9')='#skF_11' | k1_mcart_1('#skF_9')='#skF_10'), inference(resolution, [status(thm)], [c_244, c_293])).
% 2.42/1.28  tff(c_303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_195, c_188, c_296])).
% 2.42/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.28  
% 2.42/1.28  Inference rules
% 2.42/1.28  ----------------------
% 2.42/1.28  #Ref     : 0
% 2.42/1.28  #Sup     : 49
% 2.42/1.28  #Fact    : 0
% 2.42/1.28  #Define  : 0
% 2.42/1.28  #Split   : 2
% 2.42/1.28  #Chain   : 0
% 2.42/1.28  #Close   : 0
% 2.42/1.28  
% 2.42/1.28  Ordering : KBO
% 2.42/1.28  
% 2.42/1.28  Simplification rules
% 2.42/1.28  ----------------------
% 2.42/1.28  #Subsume      : 11
% 2.42/1.28  #Demod        : 6
% 2.42/1.28  #Tautology    : 34
% 2.42/1.28  #SimpNegUnit  : 12
% 2.42/1.28  #BackRed      : 4
% 2.42/1.28  
% 2.42/1.28  #Partial instantiations: 0
% 2.42/1.28  #Strategies tried      : 1
% 2.42/1.28  
% 2.42/1.28  Timing (in seconds)
% 2.42/1.28  ----------------------
% 2.42/1.28  Preprocessing        : 0.33
% 2.42/1.28  Parsing              : 0.16
% 2.42/1.28  CNF conversion       : 0.03
% 2.42/1.28  Main loop            : 0.19
% 2.42/1.28  Inferencing          : 0.07
% 2.42/1.28  Reduction            : 0.06
% 2.42/1.28  Demodulation         : 0.04
% 2.42/1.28  BG Simplification    : 0.02
% 2.42/1.28  Subsumption          : 0.03
% 2.42/1.28  Abstraction          : 0.01
% 2.42/1.28  MUC search           : 0.00
% 2.42/1.28  Cooper               : 0.00
% 2.42/1.28  Total                : 0.55
% 2.42/1.28  Index Insertion      : 0.00
% 2.42/1.28  Index Deletion       : 0.00
% 2.42/1.28  Index Matching       : 0.00
% 2.42/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
