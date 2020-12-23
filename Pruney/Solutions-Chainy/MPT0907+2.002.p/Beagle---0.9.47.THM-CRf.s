%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:55 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   38 (  54 expanded)
%              Number of leaves         :   18 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   57 ( 102 expanded)
%              Number of equality atoms :   22 (  42 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(B,C))
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_mcart_1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ~ ( r1_tarski(A,k2_zfmisc_1(B,C))
        & r2_hidden(D,A)
        & ! [E,F] :
            ~ ( r2_hidden(E,B)
              & r2_hidden(F,C)
              & D = k4_tarski(E,F) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_23,plain,(
    k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5,D_6] :
      ( k4_tarski('#skF_1'(A_3,B_4,C_5,D_6),'#skF_2'(A_3,B_4,C_5,D_6)) = D_6
      | ~ r2_hidden(D_6,A_3)
      | ~ r1_tarski(A_3,k2_zfmisc_1(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_39,plain,(
    ! [A_29,B_30,C_31,D_32] :
      ( k4_tarski('#skF_1'(A_29,B_30,C_31,D_32),'#skF_2'(A_29,B_30,C_31,D_32)) = D_32
      | ~ r2_hidden(D_32,A_29)
      | ~ r1_tarski(A_29,k2_zfmisc_1(B_30,C_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16,plain,(
    ! [B_12,C_13] : k1_mcart_1(k4_tarski(B_12,C_13)) != k4_tarski(B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_71,plain,(
    ! [A_41,B_42,C_43,D_44] :
      ( k4_tarski('#skF_1'(A_41,B_42,C_43,D_44),'#skF_2'(A_41,B_42,C_43,D_44)) != k1_mcart_1(D_44)
      | ~ r2_hidden(D_44,A_41)
      | ~ r1_tarski(A_41,k2_zfmisc_1(B_42,C_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_16])).

tff(c_75,plain,(
    ! [D_45,A_46,B_47,C_48] :
      ( k1_mcart_1(D_45) != D_45
      | ~ r2_hidden(D_45,A_46)
      | ~ r1_tarski(A_46,k2_zfmisc_1(B_47,C_48))
      | ~ r2_hidden(D_45,A_46)
      | ~ r1_tarski(A_46,k2_zfmisc_1(B_47,C_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_71])).

tff(c_81,plain,(
    ! [B_47,C_48] :
      ( k1_mcart_1('#skF_3') != '#skF_3'
      | ~ r2_hidden('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1(B_47,C_48)) ) ),
    inference(resolution,[status(thm)],[c_20,c_75])).

tff(c_87,plain,(
    ! [B_49,C_50] : ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1(B_49,C_50)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_23,c_81])).

tff(c_92,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_87])).

tff(c_93,plain,(
    k2_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_110,plain,(
    ! [A_65,B_66,C_67,D_68] :
      ( k4_tarski('#skF_1'(A_65,B_66,C_67,D_68),'#skF_2'(A_65,B_66,C_67,D_68)) = D_68
      | ~ r2_hidden(D_68,A_65)
      | ~ r1_tarski(A_65,k2_zfmisc_1(B_66,C_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [B_12,C_13] : k2_mcart_1(k4_tarski(B_12,C_13)) != k4_tarski(B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_125,plain,(
    ! [A_69,B_70,C_71,D_72] :
      ( k4_tarski('#skF_1'(A_69,B_70,C_71,D_72),'#skF_2'(A_69,B_70,C_71,D_72)) != k2_mcart_1(D_72)
      | ~ r2_hidden(D_72,A_69)
      | ~ r1_tarski(A_69,k2_zfmisc_1(B_70,C_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_14])).

tff(c_129,plain,(
    ! [D_73,A_74,B_75,C_76] :
      ( k2_mcart_1(D_73) != D_73
      | ~ r2_hidden(D_73,A_74)
      | ~ r1_tarski(A_74,k2_zfmisc_1(B_75,C_76))
      | ~ r2_hidden(D_73,A_74)
      | ~ r1_tarski(A_74,k2_zfmisc_1(B_75,C_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_125])).

tff(c_135,plain,(
    ! [B_75,C_76] :
      ( k2_mcart_1('#skF_3') != '#skF_3'
      | ~ r2_hidden('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1(B_75,C_76)) ) ),
    inference(resolution,[status(thm)],[c_20,c_129])).

tff(c_141,plain,(
    ! [B_77,C_78] : ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1(B_77,C_78)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_93,c_135])).

tff(c_146,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_141])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:45:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.16  
% 1.64/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.16  %$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.85/1.16  
% 1.85/1.16  %Foreground sorts:
% 1.85/1.16  
% 1.85/1.16  
% 1.85/1.16  %Background operators:
% 1.85/1.16  
% 1.85/1.16  
% 1.85/1.16  %Foreground operators:
% 1.85/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.85/1.16  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.85/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.85/1.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.85/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.16  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.85/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.85/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.85/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.16  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.85/1.16  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 1.85/1.16  
% 1.85/1.17  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.85/1.17  tff(f_62, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_mcart_1)).
% 1.85/1.17  tff(f_44, axiom, (![A, B, C, D]: ~((r1_tarski(A, k2_zfmisc_1(B, C)) & r2_hidden(D, A)) & (![E, F]: ~((r2_hidden(E, B) & r2_hidden(F, C)) & (D = k4_tarski(E, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 1.85/1.17  tff(f_53, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 1.85/1.17  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.85/1.17  tff(c_20, plain, (r2_hidden('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.85/1.17  tff(c_18, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.85/1.17  tff(c_23, plain, (k1_mcart_1('#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_18])).
% 1.85/1.17  tff(c_8, plain, (![A_3, B_4, C_5, D_6]: (k4_tarski('#skF_1'(A_3, B_4, C_5, D_6), '#skF_2'(A_3, B_4, C_5, D_6))=D_6 | ~r2_hidden(D_6, A_3) | ~r1_tarski(A_3, k2_zfmisc_1(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.85/1.17  tff(c_39, plain, (![A_29, B_30, C_31, D_32]: (k4_tarski('#skF_1'(A_29, B_30, C_31, D_32), '#skF_2'(A_29, B_30, C_31, D_32))=D_32 | ~r2_hidden(D_32, A_29) | ~r1_tarski(A_29, k2_zfmisc_1(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.85/1.17  tff(c_16, plain, (![B_12, C_13]: (k1_mcart_1(k4_tarski(B_12, C_13))!=k4_tarski(B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.85/1.17  tff(c_71, plain, (![A_41, B_42, C_43, D_44]: (k4_tarski('#skF_1'(A_41, B_42, C_43, D_44), '#skF_2'(A_41, B_42, C_43, D_44))!=k1_mcart_1(D_44) | ~r2_hidden(D_44, A_41) | ~r1_tarski(A_41, k2_zfmisc_1(B_42, C_43)))), inference(superposition, [status(thm), theory('equality')], [c_39, c_16])).
% 1.85/1.17  tff(c_75, plain, (![D_45, A_46, B_47, C_48]: (k1_mcart_1(D_45)!=D_45 | ~r2_hidden(D_45, A_46) | ~r1_tarski(A_46, k2_zfmisc_1(B_47, C_48)) | ~r2_hidden(D_45, A_46) | ~r1_tarski(A_46, k2_zfmisc_1(B_47, C_48)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_71])).
% 1.85/1.17  tff(c_81, plain, (![B_47, C_48]: (k1_mcart_1('#skF_3')!='#skF_3' | ~r2_hidden('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5')) | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1(B_47, C_48)))), inference(resolution, [status(thm)], [c_20, c_75])).
% 1.85/1.17  tff(c_87, plain, (![B_49, C_50]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1(B_49, C_50)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_23, c_81])).
% 1.85/1.17  tff(c_92, plain, $false, inference(resolution, [status(thm)], [c_6, c_87])).
% 1.85/1.17  tff(c_93, plain, (k2_mcart_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_18])).
% 1.85/1.17  tff(c_110, plain, (![A_65, B_66, C_67, D_68]: (k4_tarski('#skF_1'(A_65, B_66, C_67, D_68), '#skF_2'(A_65, B_66, C_67, D_68))=D_68 | ~r2_hidden(D_68, A_65) | ~r1_tarski(A_65, k2_zfmisc_1(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.85/1.17  tff(c_14, plain, (![B_12, C_13]: (k2_mcart_1(k4_tarski(B_12, C_13))!=k4_tarski(B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.85/1.17  tff(c_125, plain, (![A_69, B_70, C_71, D_72]: (k4_tarski('#skF_1'(A_69, B_70, C_71, D_72), '#skF_2'(A_69, B_70, C_71, D_72))!=k2_mcart_1(D_72) | ~r2_hidden(D_72, A_69) | ~r1_tarski(A_69, k2_zfmisc_1(B_70, C_71)))), inference(superposition, [status(thm), theory('equality')], [c_110, c_14])).
% 1.85/1.17  tff(c_129, plain, (![D_73, A_74, B_75, C_76]: (k2_mcart_1(D_73)!=D_73 | ~r2_hidden(D_73, A_74) | ~r1_tarski(A_74, k2_zfmisc_1(B_75, C_76)) | ~r2_hidden(D_73, A_74) | ~r1_tarski(A_74, k2_zfmisc_1(B_75, C_76)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_125])).
% 1.85/1.17  tff(c_135, plain, (![B_75, C_76]: (k2_mcart_1('#skF_3')!='#skF_3' | ~r2_hidden('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5')) | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1(B_75, C_76)))), inference(resolution, [status(thm)], [c_20, c_129])).
% 1.85/1.17  tff(c_141, plain, (![B_77, C_78]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1(B_77, C_78)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_93, c_135])).
% 1.85/1.17  tff(c_146, plain, $false, inference(resolution, [status(thm)], [c_6, c_141])).
% 1.85/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.17  
% 1.85/1.17  Inference rules
% 1.85/1.17  ----------------------
% 1.85/1.17  #Ref     : 0
% 1.85/1.17  #Sup     : 28
% 1.85/1.17  #Fact    : 0
% 1.85/1.17  #Define  : 0
% 1.85/1.17  #Split   : 2
% 1.85/1.17  #Chain   : 0
% 1.85/1.17  #Close   : 0
% 1.85/1.17  
% 1.85/1.17  Ordering : KBO
% 1.85/1.17  
% 1.85/1.17  Simplification rules
% 1.85/1.17  ----------------------
% 1.85/1.17  #Subsume      : 0
% 1.85/1.17  #Demod        : 8
% 1.85/1.17  #Tautology    : 11
% 1.85/1.17  #SimpNegUnit  : 0
% 1.85/1.17  #BackRed      : 0
% 1.85/1.17  
% 1.85/1.17  #Partial instantiations: 0
% 1.85/1.17  #Strategies tried      : 1
% 1.85/1.17  
% 1.85/1.17  Timing (in seconds)
% 1.85/1.17  ----------------------
% 1.85/1.17  Preprocessing        : 0.25
% 1.85/1.17  Parsing              : 0.14
% 1.85/1.17  CNF conversion       : 0.02
% 1.85/1.17  Main loop            : 0.16
% 1.85/1.17  Inferencing          : 0.07
% 1.85/1.17  Reduction            : 0.04
% 1.85/1.17  Demodulation         : 0.03
% 1.85/1.17  BG Simplification    : 0.01
% 1.85/1.17  Subsumption          : 0.03
% 1.85/1.17  Abstraction          : 0.01
% 1.85/1.17  MUC search           : 0.00
% 1.85/1.17  Cooper               : 0.00
% 1.85/1.17  Total                : 0.44
% 1.85/1.17  Index Insertion      : 0.00
% 1.85/1.17  Index Deletion       : 0.00
% 1.85/1.17  Index Matching       : 0.00
% 1.85/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
