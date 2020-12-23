%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:07 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   40 (  50 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :   82 ( 122 expanded)
%              Number of equality atoms :   19 (  26 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r2_hidden(A,k3_zfmisc_1(B,C,D))
          & ! [E,F,G] :
              ~ ( r2_hidden(E,B)
                & r2_hidden(F,C)
                & r2_hidden(G,D)
                & A = k3_mcart_1(E,F,G) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_mcart_1)).

tff(f_48,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ~ ( r1_tarski(A,k2_zfmisc_1(B,C))
        & r2_hidden(D,A)
        & ! [E,F] :
            ~ ( r2_hidden(E,B)
              & r2_hidden(F,C)
              & D = k4_tarski(E,F) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    r2_hidden('#skF_3',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    ! [A_12,B_13,C_14] : k2_zfmisc_1(k2_zfmisc_1(A_12,B_13),C_14) = k3_zfmisc_1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12,plain,(
    ! [A_3,B_4,C_5,D_6] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5,D_6),B_4)
      | ~ r2_hidden(D_6,A_3)
      | ~ r1_tarski(A_3,k2_zfmisc_1(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    ! [A_3,B_4,C_5,D_6] :
      ( r2_hidden('#skF_2'(A_3,B_4,C_5,D_6),C_5)
      | ~ r2_hidden(D_6,A_3)
      | ~ r1_tarski(A_3,k2_zfmisc_1(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5,D_6] :
      ( k4_tarski('#skF_1'(A_3,B_4,C_5,D_6),'#skF_2'(A_3,B_4,C_5,D_6)) = D_6
      | ~ r2_hidden(D_6,A_3)
      | ~ r1_tarski(A_3,k2_zfmisc_1(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_97,plain,(
    ! [A_53,B_54,C_55,D_56] :
      ( k4_tarski('#skF_1'(A_53,B_54,C_55,D_56),'#skF_2'(A_53,B_54,C_55,D_56)) = D_56
      | ~ r2_hidden(D_56,A_53)
      | ~ r1_tarski(A_53,k2_zfmisc_1(B_54,C_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] : k4_tarski(k4_tarski(A_9,B_10),C_11) = k3_mcart_1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_112,plain,(
    ! [A_58,D_59,C_57,B_61,C_60] :
      ( k3_mcart_1('#skF_1'(A_58,B_61,C_57,D_59),'#skF_2'(A_58,B_61,C_57,D_59),C_60) = k4_tarski(D_59,C_60)
      | ~ r2_hidden(D_59,A_58)
      | ~ r1_tarski(A_58,k2_zfmisc_1(B_61,C_57)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_14])).

tff(c_18,plain,(
    ! [E_18,F_19,G_20] :
      ( k3_mcart_1(E_18,F_19,G_20) != '#skF_3'
      | ~ r2_hidden(G_20,'#skF_6')
      | ~ r2_hidden(F_19,'#skF_5')
      | ~ r2_hidden(E_18,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_147,plain,(
    ! [D_70,C_72,B_69,C_71,A_68] :
      ( k4_tarski(D_70,C_72) != '#skF_3'
      | ~ r2_hidden(C_72,'#skF_6')
      | ~ r2_hidden('#skF_2'(A_68,B_69,C_71,D_70),'#skF_5')
      | ~ r2_hidden('#skF_1'(A_68,B_69,C_71,D_70),'#skF_4')
      | ~ r2_hidden(D_70,A_68)
      | ~ r1_tarski(A_68,k2_zfmisc_1(B_69,C_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_18])).

tff(c_275,plain,(
    ! [C_128,B_125,A_126,D_124,B_130,A_129,C_127] :
      ( D_124 != '#skF_3'
      | ~ r2_hidden('#skF_2'(A_126,B_130,C_128,D_124),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_129,B_125,C_127,'#skF_1'(A_126,B_130,C_128,D_124)),'#skF_5')
      | ~ r2_hidden('#skF_1'(A_129,B_125,C_127,'#skF_1'(A_126,B_130,C_128,D_124)),'#skF_4')
      | ~ r2_hidden('#skF_1'(A_126,B_130,C_128,D_124),A_129)
      | ~ r1_tarski(A_129,k2_zfmisc_1(B_125,C_127))
      | ~ r2_hidden(D_124,A_126)
      | ~ r1_tarski(A_126,k2_zfmisc_1(B_130,C_128)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_147])).

tff(c_357,plain,(
    ! [C_161,A_159,D_160,A_158,B_157,B_162] :
      ( D_160 != '#skF_3'
      | ~ r2_hidden('#skF_2'(A_158,B_157,C_161,D_160),'#skF_6')
      | ~ r2_hidden('#skF_1'(A_159,B_162,'#skF_5','#skF_1'(A_158,B_157,C_161,D_160)),'#skF_4')
      | ~ r2_hidden(D_160,A_158)
      | ~ r1_tarski(A_158,k2_zfmisc_1(B_157,C_161))
      | ~ r2_hidden('#skF_1'(A_158,B_157,C_161,D_160),A_159)
      | ~ r1_tarski(A_159,k2_zfmisc_1(B_162,'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_10,c_275])).

tff(c_364,plain,(
    ! [B_166,A_167,C_163,D_165,A_164] :
      ( D_165 != '#skF_3'
      | ~ r2_hidden('#skF_2'(A_164,B_166,C_163,D_165),'#skF_6')
      | ~ r2_hidden(D_165,A_164)
      | ~ r1_tarski(A_164,k2_zfmisc_1(B_166,C_163))
      | ~ r2_hidden('#skF_1'(A_164,B_166,C_163,D_165),A_167)
      | ~ r1_tarski(A_167,k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_12,c_357])).

tff(c_370,plain,(
    ! [D_168,A_169,B_170,A_171] :
      ( D_168 != '#skF_3'
      | ~ r2_hidden('#skF_1'(A_169,B_170,'#skF_6',D_168),A_171)
      | ~ r1_tarski(A_171,k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(D_168,A_169)
      | ~ r1_tarski(A_169,k2_zfmisc_1(B_170,'#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_10,c_364])).

tff(c_377,plain,(
    ! [D_172,B_173,A_174] :
      ( D_172 != '#skF_3'
      | ~ r1_tarski(B_173,k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(D_172,A_174)
      | ~ r1_tarski(A_174,k2_zfmisc_1(B_173,'#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_12,c_370])).

tff(c_380,plain,(
    ! [D_172,A_174] :
      ( D_172 != '#skF_3'
      | ~ r2_hidden(D_172,A_174)
      | ~ r1_tarski(A_174,k2_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_6,c_377])).

tff(c_384,plain,(
    ! [D_175,A_176] :
      ( D_175 != '#skF_3'
      | ~ r2_hidden(D_175,A_176)
      | ~ r1_tarski(A_176,k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_380])).

tff(c_390,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_5','#skF_6'),k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_20,c_384])).

tff(c_396,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_390])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:18:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.54  
% 2.83/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.54  %$ r2_hidden > r1_tarski > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.83/1.54  
% 2.83/1.54  %Foreground sorts:
% 2.83/1.54  
% 2.83/1.54  
% 2.83/1.54  %Background operators:
% 2.83/1.54  
% 2.83/1.54  
% 2.83/1.54  %Foreground operators:
% 2.83/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.54  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.83/1.54  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.83/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.54  tff('#skF_5', type, '#skF_5': $i).
% 2.83/1.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.83/1.54  tff('#skF_6', type, '#skF_6': $i).
% 2.83/1.54  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.54  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.83/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.83/1.54  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.83/1.54  
% 2.92/1.55  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.92/1.55  tff(f_62, negated_conjecture, ~(![A, B, C, D]: ~(r2_hidden(A, k3_zfmisc_1(B, C, D)) & (![E, F, G]: ~(((r2_hidden(E, B) & r2_hidden(F, C)) & r2_hidden(G, D)) & (A = k3_mcart_1(E, F, G)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_mcart_1)).
% 2.92/1.55  tff(f_48, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 2.92/1.55  tff(f_44, axiom, (![A, B, C, D]: ~((r1_tarski(A, k2_zfmisc_1(B, C)) & r2_hidden(D, A)) & (![E, F]: ~((r2_hidden(E, B) & r2_hidden(F, C)) & (D = k4_tarski(E, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 2.92/1.55  tff(f_46, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.92/1.55  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.55  tff(c_20, plain, (r2_hidden('#skF_3', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.92/1.55  tff(c_16, plain, (![A_12, B_13, C_14]: (k2_zfmisc_1(k2_zfmisc_1(A_12, B_13), C_14)=k3_zfmisc_1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.92/1.55  tff(c_12, plain, (![A_3, B_4, C_5, D_6]: (r2_hidden('#skF_1'(A_3, B_4, C_5, D_6), B_4) | ~r2_hidden(D_6, A_3) | ~r1_tarski(A_3, k2_zfmisc_1(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.92/1.55  tff(c_10, plain, (![A_3, B_4, C_5, D_6]: (r2_hidden('#skF_2'(A_3, B_4, C_5, D_6), C_5) | ~r2_hidden(D_6, A_3) | ~r1_tarski(A_3, k2_zfmisc_1(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.92/1.55  tff(c_8, plain, (![A_3, B_4, C_5, D_6]: (k4_tarski('#skF_1'(A_3, B_4, C_5, D_6), '#skF_2'(A_3, B_4, C_5, D_6))=D_6 | ~r2_hidden(D_6, A_3) | ~r1_tarski(A_3, k2_zfmisc_1(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.92/1.55  tff(c_97, plain, (![A_53, B_54, C_55, D_56]: (k4_tarski('#skF_1'(A_53, B_54, C_55, D_56), '#skF_2'(A_53, B_54, C_55, D_56))=D_56 | ~r2_hidden(D_56, A_53) | ~r1_tarski(A_53, k2_zfmisc_1(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.92/1.55  tff(c_14, plain, (![A_9, B_10, C_11]: (k4_tarski(k4_tarski(A_9, B_10), C_11)=k3_mcart_1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.92/1.55  tff(c_112, plain, (![A_58, D_59, C_57, B_61, C_60]: (k3_mcart_1('#skF_1'(A_58, B_61, C_57, D_59), '#skF_2'(A_58, B_61, C_57, D_59), C_60)=k4_tarski(D_59, C_60) | ~r2_hidden(D_59, A_58) | ~r1_tarski(A_58, k2_zfmisc_1(B_61, C_57)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_14])).
% 2.92/1.55  tff(c_18, plain, (![E_18, F_19, G_20]: (k3_mcart_1(E_18, F_19, G_20)!='#skF_3' | ~r2_hidden(G_20, '#skF_6') | ~r2_hidden(F_19, '#skF_5') | ~r2_hidden(E_18, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.92/1.55  tff(c_147, plain, (![D_70, C_72, B_69, C_71, A_68]: (k4_tarski(D_70, C_72)!='#skF_3' | ~r2_hidden(C_72, '#skF_6') | ~r2_hidden('#skF_2'(A_68, B_69, C_71, D_70), '#skF_5') | ~r2_hidden('#skF_1'(A_68, B_69, C_71, D_70), '#skF_4') | ~r2_hidden(D_70, A_68) | ~r1_tarski(A_68, k2_zfmisc_1(B_69, C_71)))), inference(superposition, [status(thm), theory('equality')], [c_112, c_18])).
% 2.92/1.55  tff(c_275, plain, (![C_128, B_125, A_126, D_124, B_130, A_129, C_127]: (D_124!='#skF_3' | ~r2_hidden('#skF_2'(A_126, B_130, C_128, D_124), '#skF_6') | ~r2_hidden('#skF_2'(A_129, B_125, C_127, '#skF_1'(A_126, B_130, C_128, D_124)), '#skF_5') | ~r2_hidden('#skF_1'(A_129, B_125, C_127, '#skF_1'(A_126, B_130, C_128, D_124)), '#skF_4') | ~r2_hidden('#skF_1'(A_126, B_130, C_128, D_124), A_129) | ~r1_tarski(A_129, k2_zfmisc_1(B_125, C_127)) | ~r2_hidden(D_124, A_126) | ~r1_tarski(A_126, k2_zfmisc_1(B_130, C_128)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_147])).
% 2.92/1.55  tff(c_357, plain, (![C_161, A_159, D_160, A_158, B_157, B_162]: (D_160!='#skF_3' | ~r2_hidden('#skF_2'(A_158, B_157, C_161, D_160), '#skF_6') | ~r2_hidden('#skF_1'(A_159, B_162, '#skF_5', '#skF_1'(A_158, B_157, C_161, D_160)), '#skF_4') | ~r2_hidden(D_160, A_158) | ~r1_tarski(A_158, k2_zfmisc_1(B_157, C_161)) | ~r2_hidden('#skF_1'(A_158, B_157, C_161, D_160), A_159) | ~r1_tarski(A_159, k2_zfmisc_1(B_162, '#skF_5')))), inference(resolution, [status(thm)], [c_10, c_275])).
% 2.92/1.55  tff(c_364, plain, (![B_166, A_167, C_163, D_165, A_164]: (D_165!='#skF_3' | ~r2_hidden('#skF_2'(A_164, B_166, C_163, D_165), '#skF_6') | ~r2_hidden(D_165, A_164) | ~r1_tarski(A_164, k2_zfmisc_1(B_166, C_163)) | ~r2_hidden('#skF_1'(A_164, B_166, C_163, D_165), A_167) | ~r1_tarski(A_167, k2_zfmisc_1('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_12, c_357])).
% 2.92/1.55  tff(c_370, plain, (![D_168, A_169, B_170, A_171]: (D_168!='#skF_3' | ~r2_hidden('#skF_1'(A_169, B_170, '#skF_6', D_168), A_171) | ~r1_tarski(A_171, k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(D_168, A_169) | ~r1_tarski(A_169, k2_zfmisc_1(B_170, '#skF_6')))), inference(resolution, [status(thm)], [c_10, c_364])).
% 2.92/1.55  tff(c_377, plain, (![D_172, B_173, A_174]: (D_172!='#skF_3' | ~r1_tarski(B_173, k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(D_172, A_174) | ~r1_tarski(A_174, k2_zfmisc_1(B_173, '#skF_6')))), inference(resolution, [status(thm)], [c_12, c_370])).
% 2.92/1.55  tff(c_380, plain, (![D_172, A_174]: (D_172!='#skF_3' | ~r2_hidden(D_172, A_174) | ~r1_tarski(A_174, k2_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')))), inference(resolution, [status(thm)], [c_6, c_377])).
% 2.92/1.55  tff(c_384, plain, (![D_175, A_176]: (D_175!='#skF_3' | ~r2_hidden(D_175, A_176) | ~r1_tarski(A_176, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_380])).
% 2.92/1.55  tff(c_390, plain, (~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'), k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_20, c_384])).
% 2.92/1.55  tff(c_396, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_390])).
% 2.92/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.55  
% 2.92/1.55  Inference rules
% 2.92/1.55  ----------------------
% 2.92/1.55  #Ref     : 0
% 2.92/1.55  #Sup     : 106
% 2.92/1.55  #Fact    : 0
% 2.92/1.55  #Define  : 0
% 2.92/1.55  #Split   : 0
% 2.92/1.55  #Chain   : 0
% 2.92/1.55  #Close   : 0
% 2.92/1.55  
% 2.92/1.55  Ordering : KBO
% 2.92/1.55  
% 2.92/1.55  Simplification rules
% 2.92/1.55  ----------------------
% 2.92/1.55  #Subsume      : 5
% 2.92/1.55  #Demod        : 57
% 2.92/1.55  #Tautology    : 37
% 2.92/1.55  #SimpNegUnit  : 0
% 2.92/1.55  #BackRed      : 0
% 2.92/1.55  
% 2.92/1.55  #Partial instantiations: 0
% 2.92/1.55  #Strategies tried      : 1
% 2.92/1.55  
% 2.92/1.55  Timing (in seconds)
% 2.92/1.55  ----------------------
% 2.92/1.55  Preprocessing        : 0.34
% 2.92/1.55  Parsing              : 0.20
% 2.92/1.55  CNF conversion       : 0.02
% 2.92/1.55  Main loop            : 0.36
% 2.92/1.55  Inferencing          : 0.15
% 2.92/1.55  Reduction            : 0.09
% 2.92/1.56  Demodulation         : 0.08
% 2.92/1.56  BG Simplification    : 0.02
% 2.92/1.56  Subsumption          : 0.08
% 2.92/1.56  Abstraction          : 0.02
% 2.92/1.56  MUC search           : 0.00
% 2.92/1.56  Cooper               : 0.00
% 2.92/1.56  Total                : 0.73
% 2.92/1.56  Index Insertion      : 0.00
% 2.92/1.56  Index Deletion       : 0.00
% 2.92/1.56  Index Matching       : 0.00
% 2.92/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
