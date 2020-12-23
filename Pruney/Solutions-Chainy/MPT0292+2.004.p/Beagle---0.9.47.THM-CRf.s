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
% DateTime   : Thu Dec  3 09:53:35 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   43 (  53 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 (  92 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_6 > #skF_3 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_92,plain,(
    ! [A_49,C_50] :
      ( r2_hidden('#skF_7'(A_49,k3_tarski(A_49),C_50),A_49)
      | ~ r2_hidden(C_50,k3_tarski(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    ! [C_12,A_8] :
      ( r1_tarski(C_12,A_8)
      | ~ r2_hidden(C_12,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_450,plain,(
    ! [A_110,C_111] :
      ( r1_tarski('#skF_7'(k1_zfmisc_1(A_110),k3_tarski(k1_zfmisc_1(A_110)),C_111),A_110)
      | ~ r2_hidden(C_111,k3_tarski(k1_zfmisc_1(A_110))) ) ),
    inference(resolution,[status(thm)],[c_92,c_14])).

tff(c_120,plain,(
    ! [C_58,A_59] :
      ( r2_hidden(C_58,'#skF_7'(A_59,k3_tarski(A_59),C_58))
      | ~ r2_hidden(C_58,k3_tarski(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_126,plain,(
    ! [C_58,B_2,A_59] :
      ( r2_hidden(C_58,B_2)
      | ~ r1_tarski('#skF_7'(A_59,k3_tarski(A_59),C_58),B_2)
      | ~ r2_hidden(C_58,k3_tarski(A_59)) ) ),
    inference(resolution,[status(thm)],[c_120,c_2])).

tff(c_467,plain,(
    ! [C_115,A_116] :
      ( r2_hidden(C_115,A_116)
      | ~ r2_hidden(C_115,k3_tarski(k1_zfmisc_1(A_116))) ) ),
    inference(resolution,[status(thm)],[c_450,c_126])).

tff(c_521,plain,(
    ! [A_117,B_118] :
      ( r2_hidden('#skF_1'(k3_tarski(k1_zfmisc_1(A_117)),B_118),A_117)
      | r1_tarski(k3_tarski(k1_zfmisc_1(A_117)),B_118) ) ),
    inference(resolution,[status(thm)],[c_6,c_467])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_553,plain,(
    ! [A_119] : r1_tarski(k3_tarski(k1_zfmisc_1(A_119)),A_119) ),
    inference(resolution,[status(thm)],[c_521,c_4])).

tff(c_16,plain,(
    ! [C_12,A_8] :
      ( r2_hidden(C_12,k1_zfmisc_1(A_8))
      | ~ r1_tarski(C_12,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_85,plain,(
    ! [C_46,A_47,D_48] :
      ( r2_hidden(C_46,k3_tarski(A_47))
      | ~ r2_hidden(D_48,A_47)
      | ~ r2_hidden(C_46,D_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_127,plain,(
    ! [C_60,A_61,C_62] :
      ( r2_hidden(C_60,k3_tarski(k1_zfmisc_1(A_61)))
      | ~ r2_hidden(C_60,C_62)
      | ~ r1_tarski(C_62,A_61) ) ),
    inference(resolution,[status(thm)],[c_16,c_85])).

tff(c_314,plain,(
    ! [A_92,B_93,A_94] :
      ( r2_hidden('#skF_1'(A_92,B_93),k3_tarski(k1_zfmisc_1(A_94)))
      | ~ r1_tarski(A_92,A_94)
      | r1_tarski(A_92,B_93) ) ),
    inference(resolution,[status(thm)],[c_6,c_127])).

tff(c_329,plain,(
    ! [A_95,A_96] :
      ( ~ r1_tarski(A_95,A_96)
      | r1_tarski(A_95,k3_tarski(k1_zfmisc_1(A_96))) ) ),
    inference(resolution,[status(thm)],[c_314,c_4])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_354,plain,(
    ! [A_96,A_95] :
      ( k3_tarski(k1_zfmisc_1(A_96)) = A_95
      | ~ r1_tarski(k3_tarski(k1_zfmisc_1(A_96)),A_95)
      | ~ r1_tarski(A_95,A_96) ) ),
    inference(resolution,[status(thm)],[c_329,c_8])).

tff(c_556,plain,(
    ! [A_119] :
      ( k3_tarski(k1_zfmisc_1(A_119)) = A_119
      | ~ r1_tarski(A_119,A_119) ) ),
    inference(resolution,[status(thm)],[c_553,c_354])).

tff(c_564,plain,(
    ! [A_119] : k3_tarski(k1_zfmisc_1(A_119)) = A_119 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_556])).

tff(c_44,plain,(
    k3_tarski(k1_zfmisc_1('#skF_8')) != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_601,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_564,c_44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n004.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 14:09:23 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.16/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.24  
% 2.55/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.25  %$ r2_hidden > r1_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_6 > #skF_3 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 2.55/1.25  
% 2.55/1.25  %Foreground sorts:
% 2.55/1.25  
% 2.55/1.25  
% 2.55/1.25  %Background operators:
% 2.55/1.25  
% 2.55/1.25  
% 2.55/1.25  %Foreground operators:
% 2.55/1.25  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.55/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.25  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.55/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.55/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.55/1.25  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 2.55/1.25  tff('#skF_8', type, '#skF_8': $i).
% 2.55/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.55/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.55/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.55/1.25  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.55/1.25  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.55/1.25  
% 2.55/1.26  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.55/1.26  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.55/1.26  tff(f_55, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 2.55/1.26  tff(f_45, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.55/1.26  tff(f_58, negated_conjecture, ~(![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.55/1.26  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.55/1.26  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.55/1.26  tff(c_92, plain, (![A_49, C_50]: (r2_hidden('#skF_7'(A_49, k3_tarski(A_49), C_50), A_49) | ~r2_hidden(C_50, k3_tarski(A_49)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.55/1.26  tff(c_14, plain, (![C_12, A_8]: (r1_tarski(C_12, A_8) | ~r2_hidden(C_12, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.55/1.26  tff(c_450, plain, (![A_110, C_111]: (r1_tarski('#skF_7'(k1_zfmisc_1(A_110), k3_tarski(k1_zfmisc_1(A_110)), C_111), A_110) | ~r2_hidden(C_111, k3_tarski(k1_zfmisc_1(A_110))))), inference(resolution, [status(thm)], [c_92, c_14])).
% 2.55/1.26  tff(c_120, plain, (![C_58, A_59]: (r2_hidden(C_58, '#skF_7'(A_59, k3_tarski(A_59), C_58)) | ~r2_hidden(C_58, k3_tarski(A_59)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.55/1.26  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.55/1.26  tff(c_126, plain, (![C_58, B_2, A_59]: (r2_hidden(C_58, B_2) | ~r1_tarski('#skF_7'(A_59, k3_tarski(A_59), C_58), B_2) | ~r2_hidden(C_58, k3_tarski(A_59)))), inference(resolution, [status(thm)], [c_120, c_2])).
% 2.55/1.26  tff(c_467, plain, (![C_115, A_116]: (r2_hidden(C_115, A_116) | ~r2_hidden(C_115, k3_tarski(k1_zfmisc_1(A_116))))), inference(resolution, [status(thm)], [c_450, c_126])).
% 2.55/1.26  tff(c_521, plain, (![A_117, B_118]: (r2_hidden('#skF_1'(k3_tarski(k1_zfmisc_1(A_117)), B_118), A_117) | r1_tarski(k3_tarski(k1_zfmisc_1(A_117)), B_118))), inference(resolution, [status(thm)], [c_6, c_467])).
% 2.55/1.26  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.55/1.26  tff(c_553, plain, (![A_119]: (r1_tarski(k3_tarski(k1_zfmisc_1(A_119)), A_119))), inference(resolution, [status(thm)], [c_521, c_4])).
% 2.55/1.26  tff(c_16, plain, (![C_12, A_8]: (r2_hidden(C_12, k1_zfmisc_1(A_8)) | ~r1_tarski(C_12, A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.55/1.26  tff(c_85, plain, (![C_46, A_47, D_48]: (r2_hidden(C_46, k3_tarski(A_47)) | ~r2_hidden(D_48, A_47) | ~r2_hidden(C_46, D_48))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.55/1.26  tff(c_127, plain, (![C_60, A_61, C_62]: (r2_hidden(C_60, k3_tarski(k1_zfmisc_1(A_61))) | ~r2_hidden(C_60, C_62) | ~r1_tarski(C_62, A_61))), inference(resolution, [status(thm)], [c_16, c_85])).
% 2.55/1.26  tff(c_314, plain, (![A_92, B_93, A_94]: (r2_hidden('#skF_1'(A_92, B_93), k3_tarski(k1_zfmisc_1(A_94))) | ~r1_tarski(A_92, A_94) | r1_tarski(A_92, B_93))), inference(resolution, [status(thm)], [c_6, c_127])).
% 2.55/1.26  tff(c_329, plain, (![A_95, A_96]: (~r1_tarski(A_95, A_96) | r1_tarski(A_95, k3_tarski(k1_zfmisc_1(A_96))))), inference(resolution, [status(thm)], [c_314, c_4])).
% 2.55/1.26  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.55/1.26  tff(c_354, plain, (![A_96, A_95]: (k3_tarski(k1_zfmisc_1(A_96))=A_95 | ~r1_tarski(k3_tarski(k1_zfmisc_1(A_96)), A_95) | ~r1_tarski(A_95, A_96))), inference(resolution, [status(thm)], [c_329, c_8])).
% 2.55/1.26  tff(c_556, plain, (![A_119]: (k3_tarski(k1_zfmisc_1(A_119))=A_119 | ~r1_tarski(A_119, A_119))), inference(resolution, [status(thm)], [c_553, c_354])).
% 2.55/1.26  tff(c_564, plain, (![A_119]: (k3_tarski(k1_zfmisc_1(A_119))=A_119)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_556])).
% 2.55/1.26  tff(c_44, plain, (k3_tarski(k1_zfmisc_1('#skF_8'))!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.55/1.26  tff(c_601, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_564, c_44])).
% 2.55/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.26  
% 2.55/1.26  Inference rules
% 2.55/1.26  ----------------------
% 2.55/1.26  #Ref     : 0
% 2.55/1.26  #Sup     : 132
% 2.55/1.26  #Fact    : 0
% 2.55/1.26  #Define  : 0
% 2.55/1.26  #Split   : 0
% 2.55/1.26  #Chain   : 0
% 2.55/1.26  #Close   : 0
% 2.55/1.26  
% 2.55/1.26  Ordering : KBO
% 2.55/1.26  
% 2.55/1.26  Simplification rules
% 2.55/1.26  ----------------------
% 2.55/1.26  #Subsume      : 15
% 2.55/1.26  #Demod        : 23
% 2.55/1.26  #Tautology    : 11
% 2.55/1.26  #SimpNegUnit  : 0
% 2.55/1.26  #BackRed      : 11
% 2.55/1.26  
% 2.55/1.26  #Partial instantiations: 0
% 2.55/1.26  #Strategies tried      : 1
% 2.55/1.26  
% 2.55/1.26  Timing (in seconds)
% 2.55/1.26  ----------------------
% 2.55/1.26  Preprocessing        : 0.29
% 2.55/1.26  Parsing              : 0.15
% 2.55/1.26  CNF conversion       : 0.02
% 2.55/1.26  Main loop            : 0.31
% 2.55/1.26  Inferencing          : 0.11
% 2.55/1.26  Reduction            : 0.07
% 2.55/1.26  Demodulation         : 0.05
% 2.55/1.26  BG Simplification    : 0.02
% 2.55/1.26  Subsumption          : 0.09
% 2.55/1.26  Abstraction          : 0.02
% 2.55/1.26  MUC search           : 0.00
% 2.55/1.26  Cooper               : 0.00
% 2.55/1.26  Total                : 0.63
% 2.55/1.26  Index Insertion      : 0.00
% 2.55/1.26  Index Deletion       : 0.00
% 2.55/1.26  Index Matching       : 0.00
% 2.55/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
