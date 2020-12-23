%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:52 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 126 expanded)
%              Number of leaves         :   22 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :  106 ( 262 expanded)
%              Number of equality atoms :   13 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
            | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
          & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(c_28,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),k2_zfmisc_1('#skF_5','#skF_7'))
    | r1_tarski(k2_zfmisc_1('#skF_6','#skF_5'),k2_zfmisc_1('#skF_7','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_56,plain,(
    r1_tarski(k2_zfmisc_1('#skF_6','#skF_5'),k2_zfmisc_1('#skF_7','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_193,plain,(
    ! [A_63,B_64,C_65,D_66] :
      ( r2_hidden(k4_tarski(A_63,B_64),k2_zfmisc_1(C_65,D_66))
      | ~ r2_hidden(B_64,D_66)
      | ~ r2_hidden(A_63,C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_558,plain,(
    ! [A_134,B_133,B_132,D_135,C_131] :
      ( r2_hidden(k4_tarski(A_134,B_133),B_132)
      | ~ r1_tarski(k2_zfmisc_1(C_131,D_135),B_132)
      | ~ r2_hidden(B_133,D_135)
      | ~ r2_hidden(A_134,C_131) ) ),
    inference(resolution,[status(thm)],[c_193,c_6])).

tff(c_574,plain,(
    ! [A_136,B_137] :
      ( r2_hidden(k4_tarski(A_136,B_137),k2_zfmisc_1('#skF_7','#skF_5'))
      | ~ r2_hidden(B_137,'#skF_5')
      | ~ r2_hidden(A_136,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_56,c_558])).

tff(c_26,plain,(
    ! [A_13,C_15,B_14,D_16] :
      ( r2_hidden(A_13,C_15)
      | ~ r2_hidden(k4_tarski(A_13,B_14),k2_zfmisc_1(C_15,D_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_587,plain,(
    ! [A_136,B_137] :
      ( r2_hidden(A_136,'#skF_7')
      | ~ r2_hidden(B_137,'#skF_5')
      | ~ r2_hidden(A_136,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_574,c_26])).

tff(c_591,plain,(
    ! [B_138] : ~ r2_hidden(B_138,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_587])).

tff(c_672,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_591])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_112,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_3'(A_50,B_51),B_51)
      | r2_hidden('#skF_4'(A_50,B_51),A_50)
      | B_51 = A_50 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_132,plain,(
    ! [B_52,A_53] :
      ( ~ v1_xboole_0(B_52)
      | r2_hidden('#skF_4'(A_53,B_52),A_53)
      | B_52 = A_53 ) ),
    inference(resolution,[status(thm)],[c_112,c_2])).

tff(c_140,plain,(
    ! [A_54,B_55] :
      ( ~ v1_xboole_0(A_54)
      | ~ v1_xboole_0(B_55)
      | B_55 = A_54 ) ),
    inference(resolution,[status(thm)],[c_132,c_2])).

tff(c_143,plain,(
    ! [B_55] :
      ( ~ v1_xboole_0(B_55)
      | k1_xboole_0 = B_55 ) ),
    inference(resolution,[status(thm)],[c_12,c_140])).

tff(c_692,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_672,c_143])).

tff(c_698,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_692])).

tff(c_700,plain,(
    ! [A_141] :
      ( r2_hidden(A_141,'#skF_7')
      | ~ r2_hidden(A_141,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_587])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_727,plain,(
    ! [A_142] :
      ( r1_tarski(A_142,'#skF_7')
      | ~ r2_hidden('#skF_2'(A_142,'#skF_7'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_700,c_8])).

tff(c_735,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_727])).

tff(c_740,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_28,c_735])).

tff(c_741,plain,(
    r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),k2_zfmisc_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_866,plain,(
    ! [A_177,B_178,C_179,D_180] :
      ( r2_hidden(k4_tarski(A_177,B_178),k2_zfmisc_1(C_179,D_180))
      | ~ r2_hidden(B_178,D_180)
      | ~ r2_hidden(A_177,C_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1266,plain,(
    ! [B_259,A_257,C_256,D_255,B_258] :
      ( r2_hidden(k4_tarski(A_257,B_259),B_258)
      | ~ r1_tarski(k2_zfmisc_1(C_256,D_255),B_258)
      | ~ r2_hidden(B_259,D_255)
      | ~ r2_hidden(A_257,C_256) ) ),
    inference(resolution,[status(thm)],[c_866,c_6])).

tff(c_1282,plain,(
    ! [A_260,B_261] :
      ( r2_hidden(k4_tarski(A_260,B_261),k2_zfmisc_1('#skF_5','#skF_7'))
      | ~ r2_hidden(B_261,'#skF_6')
      | ~ r2_hidden(A_260,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_741,c_1266])).

tff(c_24,plain,(
    ! [B_14,D_16,A_13,C_15] :
      ( r2_hidden(B_14,D_16)
      | ~ r2_hidden(k4_tarski(A_13,B_14),k2_zfmisc_1(C_15,D_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1294,plain,(
    ! [B_261,A_260] :
      ( r2_hidden(B_261,'#skF_7')
      | ~ r2_hidden(B_261,'#skF_6')
      | ~ r2_hidden(A_260,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1282,c_24])).

tff(c_1299,plain,(
    ! [A_262] : ~ r2_hidden(A_262,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1294])).

tff(c_1380,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_1299])).

tff(c_822,plain,(
    ! [A_170,B_171] :
      ( r2_hidden('#skF_3'(A_170,B_171),B_171)
      | r2_hidden('#skF_4'(A_170,B_171),A_170)
      | B_171 = A_170 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_848,plain,(
    ! [B_172,A_173] :
      ( ~ v1_xboole_0(B_172)
      | r2_hidden('#skF_4'(A_173,B_172),A_173)
      | B_172 = A_173 ) ),
    inference(resolution,[status(thm)],[c_822,c_2])).

tff(c_856,plain,(
    ! [A_174,B_175] :
      ( ~ v1_xboole_0(A_174)
      | ~ v1_xboole_0(B_175)
      | B_175 = A_174 ) ),
    inference(resolution,[status(thm)],[c_848,c_2])).

tff(c_859,plain,(
    ! [B_175] :
      ( ~ v1_xboole_0(B_175)
      | k1_xboole_0 = B_175 ) ),
    inference(resolution,[status(thm)],[c_12,c_856])).

tff(c_1395,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1380,c_859])).

tff(c_1401,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1395])).

tff(c_1403,plain,(
    ! [B_265] :
      ( r2_hidden(B_265,'#skF_7')
      | ~ r2_hidden(B_265,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_1294])).

tff(c_1430,plain,(
    ! [A_266] :
      ( r1_tarski(A_266,'#skF_7')
      | ~ r2_hidden('#skF_2'(A_266,'#skF_7'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1403,c_8])).

tff(c_1438,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_1430])).

tff(c_1443,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_28,c_1438])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:21:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.72  
% 3.58/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.72  %$ r2_hidden > r1_tarski > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.58/1.72  
% 3.58/1.72  %Foreground sorts:
% 3.58/1.72  
% 3.58/1.72  
% 3.58/1.72  %Background operators:
% 3.58/1.72  
% 3.58/1.72  
% 3.58/1.72  %Foreground operators:
% 3.58/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.58/1.72  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.58/1.72  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.58/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.58/1.72  tff('#skF_7', type, '#skF_7': $i).
% 3.58/1.72  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.58/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.58/1.72  tff('#skF_5', type, '#skF_5': $i).
% 3.58/1.72  tff('#skF_6', type, '#skF_6': $i).
% 3.58/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.58/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.72  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.58/1.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.58/1.72  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.58/1.72  
% 3.58/1.74  tff(f_64, negated_conjecture, ~(![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 3.58/1.74  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.58/1.74  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.58/1.74  tff(f_52, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.58/1.74  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.58/1.74  tff(f_46, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 3.58/1.74  tff(c_28, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.58/1.74  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.58/1.74  tff(c_32, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.58/1.74  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.58/1.74  tff(c_30, plain, (r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_5', '#skF_7')) | r1_tarski(k2_zfmisc_1('#skF_6', '#skF_5'), k2_zfmisc_1('#skF_7', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.58/1.74  tff(c_56, plain, (r1_tarski(k2_zfmisc_1('#skF_6', '#skF_5'), k2_zfmisc_1('#skF_7', '#skF_5'))), inference(splitLeft, [status(thm)], [c_30])).
% 3.58/1.74  tff(c_193, plain, (![A_63, B_64, C_65, D_66]: (r2_hidden(k4_tarski(A_63, B_64), k2_zfmisc_1(C_65, D_66)) | ~r2_hidden(B_64, D_66) | ~r2_hidden(A_63, C_65))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.58/1.74  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.58/1.74  tff(c_558, plain, (![A_134, B_133, B_132, D_135, C_131]: (r2_hidden(k4_tarski(A_134, B_133), B_132) | ~r1_tarski(k2_zfmisc_1(C_131, D_135), B_132) | ~r2_hidden(B_133, D_135) | ~r2_hidden(A_134, C_131))), inference(resolution, [status(thm)], [c_193, c_6])).
% 3.58/1.74  tff(c_574, plain, (![A_136, B_137]: (r2_hidden(k4_tarski(A_136, B_137), k2_zfmisc_1('#skF_7', '#skF_5')) | ~r2_hidden(B_137, '#skF_5') | ~r2_hidden(A_136, '#skF_6'))), inference(resolution, [status(thm)], [c_56, c_558])).
% 3.58/1.74  tff(c_26, plain, (![A_13, C_15, B_14, D_16]: (r2_hidden(A_13, C_15) | ~r2_hidden(k4_tarski(A_13, B_14), k2_zfmisc_1(C_15, D_16)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.58/1.74  tff(c_587, plain, (![A_136, B_137]: (r2_hidden(A_136, '#skF_7') | ~r2_hidden(B_137, '#skF_5') | ~r2_hidden(A_136, '#skF_6'))), inference(resolution, [status(thm)], [c_574, c_26])).
% 3.58/1.74  tff(c_591, plain, (![B_138]: (~r2_hidden(B_138, '#skF_5'))), inference(splitLeft, [status(thm)], [c_587])).
% 3.58/1.74  tff(c_672, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_591])).
% 3.58/1.74  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.58/1.74  tff(c_112, plain, (![A_50, B_51]: (r2_hidden('#skF_3'(A_50, B_51), B_51) | r2_hidden('#skF_4'(A_50, B_51), A_50) | B_51=A_50)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.58/1.74  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.58/1.74  tff(c_132, plain, (![B_52, A_53]: (~v1_xboole_0(B_52) | r2_hidden('#skF_4'(A_53, B_52), A_53) | B_52=A_53)), inference(resolution, [status(thm)], [c_112, c_2])).
% 3.58/1.74  tff(c_140, plain, (![A_54, B_55]: (~v1_xboole_0(A_54) | ~v1_xboole_0(B_55) | B_55=A_54)), inference(resolution, [status(thm)], [c_132, c_2])).
% 3.58/1.74  tff(c_143, plain, (![B_55]: (~v1_xboole_0(B_55) | k1_xboole_0=B_55)), inference(resolution, [status(thm)], [c_12, c_140])).
% 3.58/1.74  tff(c_692, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_672, c_143])).
% 3.58/1.74  tff(c_698, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_692])).
% 3.58/1.74  tff(c_700, plain, (![A_141]: (r2_hidden(A_141, '#skF_7') | ~r2_hidden(A_141, '#skF_6'))), inference(splitRight, [status(thm)], [c_587])).
% 3.58/1.74  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.58/1.74  tff(c_727, plain, (![A_142]: (r1_tarski(A_142, '#skF_7') | ~r2_hidden('#skF_2'(A_142, '#skF_7'), '#skF_6'))), inference(resolution, [status(thm)], [c_700, c_8])).
% 3.58/1.74  tff(c_735, plain, (r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_10, c_727])).
% 3.58/1.74  tff(c_740, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_28, c_735])).
% 3.58/1.74  tff(c_741, plain, (r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_30])).
% 3.58/1.74  tff(c_866, plain, (![A_177, B_178, C_179, D_180]: (r2_hidden(k4_tarski(A_177, B_178), k2_zfmisc_1(C_179, D_180)) | ~r2_hidden(B_178, D_180) | ~r2_hidden(A_177, C_179))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.58/1.74  tff(c_1266, plain, (![B_259, A_257, C_256, D_255, B_258]: (r2_hidden(k4_tarski(A_257, B_259), B_258) | ~r1_tarski(k2_zfmisc_1(C_256, D_255), B_258) | ~r2_hidden(B_259, D_255) | ~r2_hidden(A_257, C_256))), inference(resolution, [status(thm)], [c_866, c_6])).
% 3.58/1.74  tff(c_1282, plain, (![A_260, B_261]: (r2_hidden(k4_tarski(A_260, B_261), k2_zfmisc_1('#skF_5', '#skF_7')) | ~r2_hidden(B_261, '#skF_6') | ~r2_hidden(A_260, '#skF_5'))), inference(resolution, [status(thm)], [c_741, c_1266])).
% 3.58/1.74  tff(c_24, plain, (![B_14, D_16, A_13, C_15]: (r2_hidden(B_14, D_16) | ~r2_hidden(k4_tarski(A_13, B_14), k2_zfmisc_1(C_15, D_16)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.58/1.74  tff(c_1294, plain, (![B_261, A_260]: (r2_hidden(B_261, '#skF_7') | ~r2_hidden(B_261, '#skF_6') | ~r2_hidden(A_260, '#skF_5'))), inference(resolution, [status(thm)], [c_1282, c_24])).
% 3.58/1.74  tff(c_1299, plain, (![A_262]: (~r2_hidden(A_262, '#skF_5'))), inference(splitLeft, [status(thm)], [c_1294])).
% 3.58/1.74  tff(c_1380, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_1299])).
% 3.58/1.74  tff(c_822, plain, (![A_170, B_171]: (r2_hidden('#skF_3'(A_170, B_171), B_171) | r2_hidden('#skF_4'(A_170, B_171), A_170) | B_171=A_170)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.58/1.74  tff(c_848, plain, (![B_172, A_173]: (~v1_xboole_0(B_172) | r2_hidden('#skF_4'(A_173, B_172), A_173) | B_172=A_173)), inference(resolution, [status(thm)], [c_822, c_2])).
% 3.58/1.74  tff(c_856, plain, (![A_174, B_175]: (~v1_xboole_0(A_174) | ~v1_xboole_0(B_175) | B_175=A_174)), inference(resolution, [status(thm)], [c_848, c_2])).
% 3.58/1.74  tff(c_859, plain, (![B_175]: (~v1_xboole_0(B_175) | k1_xboole_0=B_175)), inference(resolution, [status(thm)], [c_12, c_856])).
% 3.58/1.74  tff(c_1395, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1380, c_859])).
% 3.58/1.74  tff(c_1401, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_1395])).
% 3.58/1.74  tff(c_1403, plain, (![B_265]: (r2_hidden(B_265, '#skF_7') | ~r2_hidden(B_265, '#skF_6'))), inference(splitRight, [status(thm)], [c_1294])).
% 3.58/1.74  tff(c_1430, plain, (![A_266]: (r1_tarski(A_266, '#skF_7') | ~r2_hidden('#skF_2'(A_266, '#skF_7'), '#skF_6'))), inference(resolution, [status(thm)], [c_1403, c_8])).
% 3.58/1.74  tff(c_1438, plain, (r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_10, c_1430])).
% 3.58/1.74  tff(c_1443, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_28, c_1438])).
% 3.58/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.74  
% 3.58/1.74  Inference rules
% 3.58/1.74  ----------------------
% 3.58/1.74  #Ref     : 0
% 3.58/1.74  #Sup     : 321
% 3.58/1.74  #Fact    : 0
% 3.58/1.74  #Define  : 0
% 3.58/1.74  #Split   : 9
% 3.58/1.74  #Chain   : 0
% 3.58/1.74  #Close   : 0
% 3.58/1.74  
% 3.58/1.74  Ordering : KBO
% 3.58/1.74  
% 3.58/1.74  Simplification rules
% 3.58/1.74  ----------------------
% 3.58/1.74  #Subsume      : 129
% 3.58/1.74  #Demod        : 11
% 3.58/1.74  #Tautology    : 37
% 3.58/1.74  #SimpNegUnit  : 4
% 3.58/1.74  #BackRed      : 0
% 3.58/1.74  
% 3.58/1.74  #Partial instantiations: 0
% 3.58/1.74  #Strategies tried      : 1
% 3.58/1.74  
% 3.58/1.74  Timing (in seconds)
% 3.58/1.74  ----------------------
% 3.58/1.74  Preprocessing        : 0.32
% 3.58/1.74  Parsing              : 0.17
% 3.58/1.74  CNF conversion       : 0.02
% 3.58/1.74  Main loop            : 0.53
% 3.58/1.74  Inferencing          : 0.20
% 3.58/1.74  Reduction            : 0.12
% 3.58/1.74  Demodulation         : 0.08
% 3.58/1.74  BG Simplification    : 0.02
% 3.58/1.74  Subsumption          : 0.15
% 3.58/1.74  Abstraction          : 0.02
% 3.58/1.74  MUC search           : 0.00
% 3.58/1.74  Cooper               : 0.00
% 3.58/1.74  Total                : 0.88
% 3.58/1.74  Index Insertion      : 0.00
% 3.58/1.74  Index Deletion       : 0.00
% 3.58/1.74  Index Matching       : 0.00
% 3.58/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
