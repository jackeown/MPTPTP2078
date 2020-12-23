%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:40 EST 2020

% Result     : Theorem 8.06s
% Output     : CNFRefutation 8.25s
% Verified   : 
% Statistics : Number of formulae       :   59 (  79 expanded)
%              Number of leaves         :   27 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   89 ( 147 expanded)
%              Number of equality atoms :   13 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_46,plain,
    ( k10_relat_1('#skF_9','#skF_8') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_84,plain,(
    r1_xboole_0(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_40,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_9'),'#skF_8')
    | k10_relat_1('#skF_9','#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_86,plain,(
    k10_relat_1('#skF_9','#skF_8') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_40])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_38,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32,plain,(
    ! [A_31,B_32,C_33] :
      ( r2_hidden('#skF_7'(A_31,B_32,C_33),B_32)
      | ~ r2_hidden(A_31,k10_relat_1(C_33,B_32))
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_419,plain,(
    ! [A_88,B_89,C_90] :
      ( r2_hidden('#skF_7'(A_88,B_89,C_90),k2_relat_1(C_90))
      | ~ r2_hidden(A_88,k10_relat_1(C_90,B_89))
      | ~ v1_relat_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_112,plain,(
    ! [A_51,B_52,C_53] :
      ( ~ r1_xboole_0(A_51,B_52)
      | ~ r2_hidden(C_53,B_52)
      | ~ r2_hidden(C_53,A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_121,plain,(
    ! [C_53] :
      ( ~ r2_hidden(C_53,'#skF_8')
      | ~ r2_hidden(C_53,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_84,c_112])).

tff(c_431,plain,(
    ! [A_88,B_89] :
      ( ~ r2_hidden('#skF_7'(A_88,B_89,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_88,k10_relat_1('#skF_9',B_89))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_419,c_121])).

tff(c_467,plain,(
    ! [A_93,B_94] :
      ( ~ r2_hidden('#skF_7'(A_93,B_94,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_93,k10_relat_1('#skF_9',B_94)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_431])).

tff(c_471,plain,(
    ! [A_31] :
      ( ~ r2_hidden(A_31,k10_relat_1('#skF_9','#skF_8'))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_32,c_467])).

tff(c_475,plain,(
    ! [A_95] : ~ r2_hidden(A_95,k10_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_471])).

tff(c_495,plain,(
    k10_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_475])).

tff(c_503,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_495])).

tff(c_505,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_69,plain,(
    ! [A_39,B_40] : ~ r2_hidden(A_39,k2_zfmisc_1(A_39,B_40)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_75,plain,(
    ! [A_8] : ~ r2_hidden(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_69])).

tff(c_504,plain,(
    k10_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_18,plain,(
    ! [A_12,C_27] :
      ( r2_hidden(k4_tarski('#skF_6'(A_12,k2_relat_1(A_12),C_27),C_27),A_12)
      | ~ r2_hidden(C_27,k2_relat_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1018,plain,(
    ! [A_157,C_158,B_159,D_160] :
      ( r2_hidden(A_157,k10_relat_1(C_158,B_159))
      | ~ r2_hidden(D_160,B_159)
      | ~ r2_hidden(k4_tarski(A_157,D_160),C_158)
      | ~ r2_hidden(D_160,k2_relat_1(C_158))
      | ~ v1_relat_1(C_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2402,plain,(
    ! [A_254,C_255,B_256,A_257] :
      ( r2_hidden(A_254,k10_relat_1(C_255,B_256))
      | ~ r2_hidden(k4_tarski(A_254,'#skF_1'(A_257,B_256)),C_255)
      | ~ r2_hidden('#skF_1'(A_257,B_256),k2_relat_1(C_255))
      | ~ v1_relat_1(C_255)
      | r1_xboole_0(A_257,B_256) ) ),
    inference(resolution,[status(thm)],[c_4,c_1018])).

tff(c_7913,plain,(
    ! [A_450,A_451,B_452] :
      ( r2_hidden('#skF_6'(A_450,k2_relat_1(A_450),'#skF_1'(A_451,B_452)),k10_relat_1(A_450,B_452))
      | ~ v1_relat_1(A_450)
      | r1_xboole_0(A_451,B_452)
      | ~ r2_hidden('#skF_1'(A_451,B_452),k2_relat_1(A_450)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2402])).

tff(c_8029,plain,(
    ! [A_451] :
      ( r2_hidden('#skF_6'('#skF_9',k2_relat_1('#skF_9'),'#skF_1'(A_451,'#skF_8')),k1_xboole_0)
      | ~ v1_relat_1('#skF_9')
      | r1_xboole_0(A_451,'#skF_8')
      | ~ r2_hidden('#skF_1'(A_451,'#skF_8'),k2_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_7913])).

tff(c_8050,plain,(
    ! [A_451] :
      ( r2_hidden('#skF_6'('#skF_9',k2_relat_1('#skF_9'),'#skF_1'(A_451,'#skF_8')),k1_xboole_0)
      | r1_xboole_0(A_451,'#skF_8')
      | ~ r2_hidden('#skF_1'(A_451,'#skF_8'),k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_8029])).

tff(c_8052,plain,(
    ! [A_453] :
      ( r1_xboole_0(A_453,'#skF_8')
      | ~ r2_hidden('#skF_1'(A_453,'#skF_8'),k2_relat_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_8050])).

tff(c_8056,plain,(
    r1_xboole_0(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_6,c_8052])).

tff(c_8060,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_505,c_505,c_8056])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:56:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.06/2.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.06/2.71  
% 8.06/2.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.06/2.71  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_1 > #skF_5 > #skF_4
% 8.06/2.71  
% 8.06/2.71  %Foreground sorts:
% 8.06/2.71  
% 8.06/2.71  
% 8.06/2.71  %Background operators:
% 8.06/2.71  
% 8.06/2.71  
% 8.06/2.71  %Foreground operators:
% 8.06/2.71  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.06/2.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.06/2.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.06/2.71  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 8.06/2.71  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.06/2.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.06/2.71  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.06/2.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.06/2.71  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.06/2.71  tff('#skF_9', type, '#skF_9': $i).
% 8.06/2.71  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 8.06/2.71  tff('#skF_8', type, '#skF_8': $i).
% 8.06/2.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.06/2.71  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 8.06/2.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.06/2.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.06/2.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.06/2.71  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.06/2.71  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.06/2.71  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.06/2.71  
% 8.25/2.72  tff(f_86, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 8.25/2.72  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.25/2.72  tff(f_79, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 8.25/2.72  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.25/2.72  tff(f_57, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.25/2.72  tff(f_60, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 8.25/2.72  tff(f_68, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 8.25/2.72  tff(c_46, plain, (k10_relat_1('#skF_9', '#skF_8')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_9'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.25/2.72  tff(c_84, plain, (r1_xboole_0(k2_relat_1('#skF_9'), '#skF_8')), inference(splitLeft, [status(thm)], [c_46])).
% 8.25/2.72  tff(c_40, plain, (~r1_xboole_0(k2_relat_1('#skF_9'), '#skF_8') | k10_relat_1('#skF_9', '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.25/2.72  tff(c_86, plain, (k10_relat_1('#skF_9', '#skF_8')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_84, c_40])).
% 8.25/2.72  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.25/2.72  tff(c_38, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.25/2.72  tff(c_32, plain, (![A_31, B_32, C_33]: (r2_hidden('#skF_7'(A_31, B_32, C_33), B_32) | ~r2_hidden(A_31, k10_relat_1(C_33, B_32)) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.25/2.72  tff(c_419, plain, (![A_88, B_89, C_90]: (r2_hidden('#skF_7'(A_88, B_89, C_90), k2_relat_1(C_90)) | ~r2_hidden(A_88, k10_relat_1(C_90, B_89)) | ~v1_relat_1(C_90))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.25/2.72  tff(c_112, plain, (![A_51, B_52, C_53]: (~r1_xboole_0(A_51, B_52) | ~r2_hidden(C_53, B_52) | ~r2_hidden(C_53, A_51))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.25/2.72  tff(c_121, plain, (![C_53]: (~r2_hidden(C_53, '#skF_8') | ~r2_hidden(C_53, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_84, c_112])).
% 8.25/2.72  tff(c_431, plain, (![A_88, B_89]: (~r2_hidden('#skF_7'(A_88, B_89, '#skF_9'), '#skF_8') | ~r2_hidden(A_88, k10_relat_1('#skF_9', B_89)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_419, c_121])).
% 8.25/2.72  tff(c_467, plain, (![A_93, B_94]: (~r2_hidden('#skF_7'(A_93, B_94, '#skF_9'), '#skF_8') | ~r2_hidden(A_93, k10_relat_1('#skF_9', B_94)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_431])).
% 8.25/2.72  tff(c_471, plain, (![A_31]: (~r2_hidden(A_31, k10_relat_1('#skF_9', '#skF_8')) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_32, c_467])).
% 8.25/2.72  tff(c_475, plain, (![A_95]: (~r2_hidden(A_95, k10_relat_1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_471])).
% 8.25/2.72  tff(c_495, plain, (k10_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_475])).
% 8.25/2.72  tff(c_503, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_495])).
% 8.25/2.72  tff(c_505, plain, (~r1_xboole_0(k2_relat_1('#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_46])).
% 8.25/2.72  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.25/2.72  tff(c_12, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.25/2.72  tff(c_69, plain, (![A_39, B_40]: (~r2_hidden(A_39, k2_zfmisc_1(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.25/2.72  tff(c_75, plain, (![A_8]: (~r2_hidden(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_69])).
% 8.25/2.72  tff(c_504, plain, (k10_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_46])).
% 8.25/2.72  tff(c_18, plain, (![A_12, C_27]: (r2_hidden(k4_tarski('#skF_6'(A_12, k2_relat_1(A_12), C_27), C_27), A_12) | ~r2_hidden(C_27, k2_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.25/2.72  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.25/2.72  tff(c_1018, plain, (![A_157, C_158, B_159, D_160]: (r2_hidden(A_157, k10_relat_1(C_158, B_159)) | ~r2_hidden(D_160, B_159) | ~r2_hidden(k4_tarski(A_157, D_160), C_158) | ~r2_hidden(D_160, k2_relat_1(C_158)) | ~v1_relat_1(C_158))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.25/2.72  tff(c_2402, plain, (![A_254, C_255, B_256, A_257]: (r2_hidden(A_254, k10_relat_1(C_255, B_256)) | ~r2_hidden(k4_tarski(A_254, '#skF_1'(A_257, B_256)), C_255) | ~r2_hidden('#skF_1'(A_257, B_256), k2_relat_1(C_255)) | ~v1_relat_1(C_255) | r1_xboole_0(A_257, B_256))), inference(resolution, [status(thm)], [c_4, c_1018])).
% 8.25/2.72  tff(c_7913, plain, (![A_450, A_451, B_452]: (r2_hidden('#skF_6'(A_450, k2_relat_1(A_450), '#skF_1'(A_451, B_452)), k10_relat_1(A_450, B_452)) | ~v1_relat_1(A_450) | r1_xboole_0(A_451, B_452) | ~r2_hidden('#skF_1'(A_451, B_452), k2_relat_1(A_450)))), inference(resolution, [status(thm)], [c_18, c_2402])).
% 8.25/2.72  tff(c_8029, plain, (![A_451]: (r2_hidden('#skF_6'('#skF_9', k2_relat_1('#skF_9'), '#skF_1'(A_451, '#skF_8')), k1_xboole_0) | ~v1_relat_1('#skF_9') | r1_xboole_0(A_451, '#skF_8') | ~r2_hidden('#skF_1'(A_451, '#skF_8'), k2_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_504, c_7913])).
% 8.25/2.72  tff(c_8050, plain, (![A_451]: (r2_hidden('#skF_6'('#skF_9', k2_relat_1('#skF_9'), '#skF_1'(A_451, '#skF_8')), k1_xboole_0) | r1_xboole_0(A_451, '#skF_8') | ~r2_hidden('#skF_1'(A_451, '#skF_8'), k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_8029])).
% 8.25/2.72  tff(c_8052, plain, (![A_453]: (r1_xboole_0(A_453, '#skF_8') | ~r2_hidden('#skF_1'(A_453, '#skF_8'), k2_relat_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_75, c_8050])).
% 8.25/2.72  tff(c_8056, plain, (r1_xboole_0(k2_relat_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_6, c_8052])).
% 8.25/2.72  tff(c_8060, plain, $false, inference(negUnitSimplification, [status(thm)], [c_505, c_505, c_8056])).
% 8.25/2.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.25/2.72  
% 8.25/2.72  Inference rules
% 8.25/2.72  ----------------------
% 8.25/2.72  #Ref     : 0
% 8.25/2.72  #Sup     : 1943
% 8.25/2.72  #Fact    : 0
% 8.25/2.72  #Define  : 0
% 8.25/2.72  #Split   : 9
% 8.25/2.72  #Chain   : 0
% 8.25/2.72  #Close   : 0
% 8.25/2.72  
% 8.25/2.72  Ordering : KBO
% 8.25/2.72  
% 8.25/2.72  Simplification rules
% 8.25/2.72  ----------------------
% 8.25/2.72  #Subsume      : 971
% 8.25/2.72  #Demod        : 1139
% 8.25/2.72  #Tautology    : 387
% 8.25/2.72  #SimpNegUnit  : 115
% 8.25/2.72  #BackRed      : 2
% 8.25/2.72  
% 8.25/2.72  #Partial instantiations: 0
% 8.25/2.72  #Strategies tried      : 1
% 8.25/2.72  
% 8.25/2.72  Timing (in seconds)
% 8.25/2.72  ----------------------
% 8.25/2.73  Preprocessing        : 0.30
% 8.25/2.73  Parsing              : 0.17
% 8.25/2.73  CNF conversion       : 0.02
% 8.25/2.73  Main loop            : 1.66
% 8.25/2.73  Inferencing          : 0.46
% 8.25/2.73  Reduction            : 0.35
% 8.25/2.73  Demodulation         : 0.23
% 8.25/2.73  BG Simplification    : 0.04
% 8.25/2.73  Subsumption          : 0.72
% 8.25/2.73  Abstraction          : 0.06
% 8.25/2.73  MUC search           : 0.00
% 8.25/2.73  Cooper               : 0.00
% 8.25/2.73  Total                : 1.98
% 8.25/2.73  Index Insertion      : 0.00
% 8.25/2.73  Index Deletion       : 0.00
% 8.25/2.73  Index Matching       : 0.00
% 8.25/2.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
