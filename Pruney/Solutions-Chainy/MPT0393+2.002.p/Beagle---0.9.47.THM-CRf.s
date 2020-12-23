%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:17 EST 2020

% Result     : Theorem 33.94s
% Output     : CNFRefutation 33.94s
% Verified   : 
% Statistics : Number of formulae       :   63 (  78 expanded)
%              Number of leaves         :   37 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :   60 (  82 expanded)
%              Number of equality atoms :   31 (  45 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_8 > #skF_13 > #skF_16 > #skF_14 > #skF_12 > #skF_10 > #skF_2 > #skF_11 > #skF_3 > #skF_7 > #skF_9 > #skF_5 > #skF_15 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_13',type,(
    '#skF_13': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_14',type,(
    '#skF_14': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_190,negated_conjecture,(
    ~ ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_129,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_168,axiom,(
    ! [A] : r1_tarski(k1_setfam_1(A),k3_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_136,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_181,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_142,plain,(
    k1_setfam_1(k1_tarski('#skF_16')) != '#skF_16' ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_94,plain,(
    ! [A_94] : k3_tarski(k1_tarski(A_94)) = A_94 ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_224,plain,(
    ! [A_143] : r1_tarski(k1_setfam_1(A_143),k3_tarski(A_143)) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_227,plain,(
    ! [A_94] : r1_tarski(k1_setfam_1(k1_tarski(A_94)),A_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_224])).

tff(c_24,plain,(
    ! [A_11] : k2_xboole_0(A_11,A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_193,plain,(
    ! [A_137,B_138] : k2_xboole_0(k1_tarski(A_137),B_138) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_197,plain,(
    ! [A_137] : k1_tarski(A_137) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_193])).

tff(c_32,plain,(
    ! [B_16] : r1_tarski(B_16,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1840,plain,(
    ! [A_261,B_262] :
      ( r2_hidden('#skF_15'(A_261,B_262),A_261)
      | r1_tarski(B_262,k1_setfam_1(A_261))
      | k1_xboole_0 = A_261 ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_48,plain,(
    ! [C_33,A_29] :
      ( C_33 = A_29
      | ~ r2_hidden(C_33,k1_tarski(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1864,plain,(
    ! [A_29,B_262] :
      ( '#skF_15'(k1_tarski(A_29),B_262) = A_29
      | r1_tarski(B_262,k1_setfam_1(k1_tarski(A_29)))
      | k1_tarski(A_29) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1840,c_48])).

tff(c_16139,plain,(
    ! [A_611,B_612] :
      ( '#skF_15'(k1_tarski(A_611),B_612) = A_611
      | r1_tarski(B_612,k1_setfam_1(k1_tarski(A_611))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_1864])).

tff(c_132,plain,(
    ! [A_123] : r1_tarski(k1_setfam_1(A_123),k3_tarski(A_123)) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_858,plain,(
    ! [B_200,A_201] :
      ( B_200 = A_201
      | ~ r1_tarski(B_200,A_201)
      | ~ r1_tarski(A_201,B_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_888,plain,(
    ! [A_123] :
      ( k3_tarski(A_123) = k1_setfam_1(A_123)
      | ~ r1_tarski(k3_tarski(A_123),k1_setfam_1(A_123)) ) ),
    inference(resolution,[status(thm)],[c_132,c_858])).

tff(c_16161,plain,(
    ! [A_611] :
      ( k3_tarski(k1_tarski(A_611)) = k1_setfam_1(k1_tarski(A_611))
      | '#skF_15'(k1_tarski(A_611),k3_tarski(k1_tarski(A_611))) = A_611 ) ),
    inference(resolution,[status(thm)],[c_16139,c_888])).

tff(c_123683,plain,(
    ! [A_1659] :
      ( k1_setfam_1(k1_tarski(A_1659)) = A_1659
      | '#skF_15'(k1_tarski(A_1659),A_1659) = A_1659 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_94,c_16161])).

tff(c_124354,plain,(
    '#skF_15'(k1_tarski('#skF_16'),'#skF_16') = '#skF_16' ),
    inference(superposition,[status(thm),theory(equality)],[c_123683,c_142])).

tff(c_136,plain,(
    ! [B_126,A_125] :
      ( ~ r1_tarski(B_126,'#skF_15'(A_125,B_126))
      | r1_tarski(B_126,k1_setfam_1(A_125))
      | k1_xboole_0 = A_125 ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_124388,plain,
    ( ~ r1_tarski('#skF_16','#skF_16')
    | r1_tarski('#skF_16',k1_setfam_1(k1_tarski('#skF_16')))
    | k1_tarski('#skF_16') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_124354,c_136])).

tff(c_124403,plain,
    ( r1_tarski('#skF_16',k1_setfam_1(k1_tarski('#skF_16')))
    | k1_tarski('#skF_16') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_124388])).

tff(c_124404,plain,(
    r1_tarski('#skF_16',k1_setfam_1(k1_tarski('#skF_16'))) ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_124403])).

tff(c_28,plain,(
    ! [B_16,A_15] :
      ( B_16 = A_15
      | ~ r1_tarski(B_16,A_15)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_124571,plain,
    ( k1_setfam_1(k1_tarski('#skF_16')) = '#skF_16'
    | ~ r1_tarski(k1_setfam_1(k1_tarski('#skF_16')),'#skF_16') ),
    inference(resolution,[status(thm)],[c_124404,c_28])).

tff(c_124594,plain,(
    k1_setfam_1(k1_tarski('#skF_16')) = '#skF_16' ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_124571])).

tff(c_124596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_124594])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:01:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 33.94/25.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 33.94/25.23  
% 33.94/25.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 33.94/25.23  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_8 > #skF_13 > #skF_16 > #skF_14 > #skF_12 > #skF_10 > #skF_2 > #skF_11 > #skF_3 > #skF_7 > #skF_9 > #skF_5 > #skF_15 > #skF_4
% 33.94/25.23  
% 33.94/25.23  %Foreground sorts:
% 33.94/25.23  
% 33.94/25.23  
% 33.94/25.23  %Background operators:
% 33.94/25.23  
% 33.94/25.23  
% 33.94/25.23  %Foreground operators:
% 33.94/25.23  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 33.94/25.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 33.94/25.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 33.94/25.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 33.94/25.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 33.94/25.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 33.94/25.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 33.94/25.23  tff('#skF_8', type, '#skF_8': $i > $i).
% 33.94/25.23  tff('#skF_13', type, '#skF_13': ($i * $i) > $i).
% 33.94/25.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 33.94/25.23  tff('#skF_16', type, '#skF_16': $i).
% 33.94/25.23  tff('#skF_14', type, '#skF_14': ($i * $i) > $i).
% 33.94/25.23  tff('#skF_12', type, '#skF_12': ($i * $i) > $i).
% 33.94/25.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 33.94/25.23  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 33.94/25.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 33.94/25.23  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 33.94/25.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 33.94/25.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 33.94/25.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 33.94/25.23  tff('#skF_3', type, '#skF_3': $i > $i).
% 33.94/25.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 33.94/25.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 33.94/25.23  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 33.94/25.23  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 33.94/25.23  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 33.94/25.23  tff('#skF_15', type, '#skF_15': ($i * $i) > $i).
% 33.94/25.23  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 33.94/25.23  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 33.94/25.23  
% 33.94/25.24  tff(f_190, negated_conjecture, ~(![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 33.94/25.24  tff(f_129, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 33.94/25.24  tff(f_168, axiom, (![A]: r1_tarski(k1_setfam_1(A), k3_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_setfam_1)).
% 33.94/25.24  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 33.94/25.24  tff(f_136, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 33.94/25.24  tff(f_57, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 33.94/25.24  tff(f_181, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 33.94/25.24  tff(f_96, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 33.94/25.24  tff(c_142, plain, (k1_setfam_1(k1_tarski('#skF_16'))!='#skF_16'), inference(cnfTransformation, [status(thm)], [f_190])).
% 33.94/25.24  tff(c_94, plain, (![A_94]: (k3_tarski(k1_tarski(A_94))=A_94)), inference(cnfTransformation, [status(thm)], [f_129])).
% 33.94/25.24  tff(c_224, plain, (![A_143]: (r1_tarski(k1_setfam_1(A_143), k3_tarski(A_143)))), inference(cnfTransformation, [status(thm)], [f_168])).
% 33.94/25.24  tff(c_227, plain, (![A_94]: (r1_tarski(k1_setfam_1(k1_tarski(A_94)), A_94))), inference(superposition, [status(thm), theory('equality')], [c_94, c_224])).
% 33.94/25.24  tff(c_24, plain, (![A_11]: (k2_xboole_0(A_11, A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 33.94/25.24  tff(c_193, plain, (![A_137, B_138]: (k2_xboole_0(k1_tarski(A_137), B_138)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_136])).
% 33.94/25.24  tff(c_197, plain, (![A_137]: (k1_tarski(A_137)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_193])).
% 33.94/25.24  tff(c_32, plain, (![B_16]: (r1_tarski(B_16, B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 33.94/25.24  tff(c_1840, plain, (![A_261, B_262]: (r2_hidden('#skF_15'(A_261, B_262), A_261) | r1_tarski(B_262, k1_setfam_1(A_261)) | k1_xboole_0=A_261)), inference(cnfTransformation, [status(thm)], [f_181])).
% 33.94/25.24  tff(c_48, plain, (![C_33, A_29]: (C_33=A_29 | ~r2_hidden(C_33, k1_tarski(A_29)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 33.94/25.24  tff(c_1864, plain, (![A_29, B_262]: ('#skF_15'(k1_tarski(A_29), B_262)=A_29 | r1_tarski(B_262, k1_setfam_1(k1_tarski(A_29))) | k1_tarski(A_29)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1840, c_48])).
% 33.94/25.24  tff(c_16139, plain, (![A_611, B_612]: ('#skF_15'(k1_tarski(A_611), B_612)=A_611 | r1_tarski(B_612, k1_setfam_1(k1_tarski(A_611))))), inference(negUnitSimplification, [status(thm)], [c_197, c_1864])).
% 33.94/25.24  tff(c_132, plain, (![A_123]: (r1_tarski(k1_setfam_1(A_123), k3_tarski(A_123)))), inference(cnfTransformation, [status(thm)], [f_168])).
% 33.94/25.24  tff(c_858, plain, (![B_200, A_201]: (B_200=A_201 | ~r1_tarski(B_200, A_201) | ~r1_tarski(A_201, B_200))), inference(cnfTransformation, [status(thm)], [f_57])).
% 33.94/25.24  tff(c_888, plain, (![A_123]: (k3_tarski(A_123)=k1_setfam_1(A_123) | ~r1_tarski(k3_tarski(A_123), k1_setfam_1(A_123)))), inference(resolution, [status(thm)], [c_132, c_858])).
% 33.94/25.24  tff(c_16161, plain, (![A_611]: (k3_tarski(k1_tarski(A_611))=k1_setfam_1(k1_tarski(A_611)) | '#skF_15'(k1_tarski(A_611), k3_tarski(k1_tarski(A_611)))=A_611)), inference(resolution, [status(thm)], [c_16139, c_888])).
% 33.94/25.24  tff(c_123683, plain, (![A_1659]: (k1_setfam_1(k1_tarski(A_1659))=A_1659 | '#skF_15'(k1_tarski(A_1659), A_1659)=A_1659)), inference(demodulation, [status(thm), theory('equality')], [c_94, c_94, c_16161])).
% 33.94/25.24  tff(c_124354, plain, ('#skF_15'(k1_tarski('#skF_16'), '#skF_16')='#skF_16'), inference(superposition, [status(thm), theory('equality')], [c_123683, c_142])).
% 33.94/25.24  tff(c_136, plain, (![B_126, A_125]: (~r1_tarski(B_126, '#skF_15'(A_125, B_126)) | r1_tarski(B_126, k1_setfam_1(A_125)) | k1_xboole_0=A_125)), inference(cnfTransformation, [status(thm)], [f_181])).
% 33.94/25.24  tff(c_124388, plain, (~r1_tarski('#skF_16', '#skF_16') | r1_tarski('#skF_16', k1_setfam_1(k1_tarski('#skF_16'))) | k1_tarski('#skF_16')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_124354, c_136])).
% 33.94/25.24  tff(c_124403, plain, (r1_tarski('#skF_16', k1_setfam_1(k1_tarski('#skF_16'))) | k1_tarski('#skF_16')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_124388])).
% 33.94/25.24  tff(c_124404, plain, (r1_tarski('#skF_16', k1_setfam_1(k1_tarski('#skF_16')))), inference(negUnitSimplification, [status(thm)], [c_197, c_124403])).
% 33.94/25.24  tff(c_28, plain, (![B_16, A_15]: (B_16=A_15 | ~r1_tarski(B_16, A_15) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 33.94/25.24  tff(c_124571, plain, (k1_setfam_1(k1_tarski('#skF_16'))='#skF_16' | ~r1_tarski(k1_setfam_1(k1_tarski('#skF_16')), '#skF_16')), inference(resolution, [status(thm)], [c_124404, c_28])).
% 33.94/25.24  tff(c_124594, plain, (k1_setfam_1(k1_tarski('#skF_16'))='#skF_16'), inference(demodulation, [status(thm), theory('equality')], [c_227, c_124571])).
% 33.94/25.24  tff(c_124596, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_124594])).
% 33.94/25.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 33.94/25.24  
% 33.94/25.24  Inference rules
% 33.94/25.24  ----------------------
% 33.94/25.24  #Ref     : 0
% 33.94/25.24  #Sup     : 32085
% 33.94/25.24  #Fact    : 11
% 33.94/25.24  #Define  : 0
% 33.94/25.24  #Split   : 1
% 33.94/25.24  #Chain   : 0
% 33.94/25.24  #Close   : 0
% 33.94/25.24  
% 33.94/25.24  Ordering : KBO
% 33.94/25.24  
% 33.94/25.24  Simplification rules
% 33.94/25.24  ----------------------
% 33.94/25.24  #Subsume      : 13652
% 33.94/25.24  #Demod        : 20659
% 33.94/25.24  #Tautology    : 5484
% 33.94/25.24  #SimpNegUnit  : 855
% 33.94/25.24  #BackRed      : 6
% 33.94/25.24  
% 33.94/25.24  #Partial instantiations: 0
% 33.94/25.24  #Strategies tried      : 1
% 33.94/25.24  
% 33.94/25.24  Timing (in seconds)
% 33.94/25.24  ----------------------
% 34.04/25.25  Preprocessing        : 0.36
% 34.04/25.25  Parsing              : 0.18
% 34.04/25.25  CNF conversion       : 0.03
% 34.04/25.25  Main loop            : 24.09
% 34.04/25.25  Inferencing          : 2.31
% 34.04/25.25  Reduction            : 11.28
% 34.04/25.25  Demodulation         : 8.27
% 34.04/25.25  BG Simplification    : 0.27
% 34.04/25.25  Subsumption          : 9.02
% 34.04/25.25  Abstraction          : 0.45
% 34.04/25.25  MUC search           : 0.00
% 34.04/25.25  Cooper               : 0.00
% 34.04/25.25  Total                : 24.48
% 34.04/25.25  Index Insertion      : 0.00
% 34.04/25.25  Index Deletion       : 0.00
% 34.04/25.25  Index Matching       : 0.00
% 34.04/25.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
