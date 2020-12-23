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
% DateTime   : Thu Dec  3 10:02:49 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   47 (  69 expanded)
%              Number of leaves         :   16 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :   82 ( 147 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
            <=> r1_tarski(A,k7_relat_1(B,k1_relat_1(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t219_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,
    ( ~ r1_tarski('#skF_2',k7_relat_1('#skF_3',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_49,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    ! [A_20,B_21] :
      ( ~ r2_hidden('#skF_1'(A_20,B_21),B_21)
      | r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_45,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_40])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k7_relat_1(B_11,A_10),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | r1_tarski('#skF_2',k7_relat_1('#skF_3',k1_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_48,plain,(
    r1_tarski('#skF_2',k7_relat_1('#skF_3',k1_relat_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_50,plain,(
    ! [C_23,B_24,A_25] :
      ( r2_hidden(C_23,B_24)
      | ~ r2_hidden(C_23,A_25)
      | ~ r1_tarski(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,(
    ! [A_26,B_27,B_28] :
      ( r2_hidden('#skF_1'(A_26,B_27),B_28)
      | ~ r1_tarski(A_26,B_28)
      | r1_tarski(A_26,B_27) ) ),
    inference(resolution,[status(thm)],[c_6,c_50])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    ! [A_34,B_35,B_36,B_37] :
      ( r2_hidden('#skF_1'(A_34,B_35),B_36)
      | ~ r1_tarski(B_37,B_36)
      | ~ r1_tarski(A_34,B_37)
      | r1_tarski(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_92,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_1'(A_38,B_39),k7_relat_1('#skF_3',k1_relat_1('#skF_2')))
      | ~ r1_tarski(A_38,'#skF_2')
      | r1_tarski(A_38,B_39) ) ),
    inference(resolution,[status(thm)],[c_48,c_76])).

tff(c_105,plain,(
    ! [A_41,B_42,B_43] :
      ( r2_hidden('#skF_1'(A_41,B_42),B_43)
      | ~ r1_tarski(k7_relat_1('#skF_3',k1_relat_1('#skF_2')),B_43)
      | ~ r1_tarski(A_41,'#skF_2')
      | r1_tarski(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_92,c_2])).

tff(c_120,plain,(
    ! [A_41,B_42] :
      ( r2_hidden('#skF_1'(A_41,B_42),'#skF_3')
      | ~ r1_tarski(A_41,'#skF_2')
      | r1_tarski(A_41,B_42)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10,c_105])).

tff(c_132,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_1'(A_44,B_45),'#skF_3')
      | ~ r1_tarski(A_44,'#skF_2')
      | r1_tarski(A_44,B_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_120])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_141,plain,(
    ! [A_46] :
      ( ~ r1_tarski(A_46,'#skF_2')
      | r1_tarski(A_46,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_132,c_4])).

tff(c_149,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_45,c_141])).

tff(c_160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_149])).

tff(c_161,plain,(
    ~ r1_tarski('#skF_2',k7_relat_1('#skF_3',k1_relat_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_48])).

tff(c_164,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_12,plain,(
    ! [A_12] :
      ( k7_relat_1(A_12,k1_relat_1(A_12)) = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_172,plain,(
    ! [B_50,A_51,C_52] :
      ( r1_tarski(k7_relat_1(B_50,A_51),k7_relat_1(C_52,A_51))
      | ~ r1_tarski(B_50,C_52)
      | ~ v1_relat_1(C_52)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_234,plain,(
    ! [A_64,C_65] :
      ( r1_tarski(A_64,k7_relat_1(C_65,k1_relat_1(A_64)))
      | ~ r1_tarski(A_64,C_65)
      | ~ v1_relat_1(C_65)
      | ~ v1_relat_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_172])).

tff(c_165,plain,(
    ~ r1_tarski('#skF_2',k7_relat_1('#skF_3',k1_relat_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_239,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_234,c_165])).

tff(c_247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_164,c_239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:54:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.24  
% 1.86/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.24  %$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.86/1.24  
% 1.86/1.24  %Foreground sorts:
% 1.86/1.24  
% 1.86/1.24  
% 1.86/1.24  %Background operators:
% 1.86/1.24  
% 1.86/1.24  
% 1.86/1.24  %Foreground operators:
% 1.86/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.24  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.86/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.86/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.86/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.86/1.24  
% 2.10/1.26  tff(f_59, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) <=> r1_tarski(A, k7_relat_1(B, k1_relat_1(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t219_relat_1)).
% 2.10/1.26  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.10/1.26  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 2.10/1.26  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 2.10/1.26  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_relat_1)).
% 2.10/1.26  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.10/1.26  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.10/1.26  tff(c_18, plain, (~r1_tarski('#skF_2', k7_relat_1('#skF_3', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.10/1.26  tff(c_49, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_18])).
% 2.10/1.26  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.10/1.26  tff(c_40, plain, (![A_20, B_21]: (~r2_hidden('#skF_1'(A_20, B_21), B_21) | r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.10/1.26  tff(c_45, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_40])).
% 2.10/1.26  tff(c_10, plain, (![B_11, A_10]: (r1_tarski(k7_relat_1(B_11, A_10), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.10/1.26  tff(c_24, plain, (r1_tarski('#skF_2', '#skF_3') | r1_tarski('#skF_2', k7_relat_1('#skF_3', k1_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.10/1.26  tff(c_48, plain, (r1_tarski('#skF_2', k7_relat_1('#skF_3', k1_relat_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_24])).
% 2.10/1.26  tff(c_50, plain, (![C_23, B_24, A_25]: (r2_hidden(C_23, B_24) | ~r2_hidden(C_23, A_25) | ~r1_tarski(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.10/1.26  tff(c_54, plain, (![A_26, B_27, B_28]: (r2_hidden('#skF_1'(A_26, B_27), B_28) | ~r1_tarski(A_26, B_28) | r1_tarski(A_26, B_27))), inference(resolution, [status(thm)], [c_6, c_50])).
% 2.10/1.26  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.10/1.26  tff(c_76, plain, (![A_34, B_35, B_36, B_37]: (r2_hidden('#skF_1'(A_34, B_35), B_36) | ~r1_tarski(B_37, B_36) | ~r1_tarski(A_34, B_37) | r1_tarski(A_34, B_35))), inference(resolution, [status(thm)], [c_54, c_2])).
% 2.10/1.26  tff(c_92, plain, (![A_38, B_39]: (r2_hidden('#skF_1'(A_38, B_39), k7_relat_1('#skF_3', k1_relat_1('#skF_2'))) | ~r1_tarski(A_38, '#skF_2') | r1_tarski(A_38, B_39))), inference(resolution, [status(thm)], [c_48, c_76])).
% 2.10/1.26  tff(c_105, plain, (![A_41, B_42, B_43]: (r2_hidden('#skF_1'(A_41, B_42), B_43) | ~r1_tarski(k7_relat_1('#skF_3', k1_relat_1('#skF_2')), B_43) | ~r1_tarski(A_41, '#skF_2') | r1_tarski(A_41, B_42))), inference(resolution, [status(thm)], [c_92, c_2])).
% 2.10/1.26  tff(c_120, plain, (![A_41, B_42]: (r2_hidden('#skF_1'(A_41, B_42), '#skF_3') | ~r1_tarski(A_41, '#skF_2') | r1_tarski(A_41, B_42) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_10, c_105])).
% 2.10/1.26  tff(c_132, plain, (![A_44, B_45]: (r2_hidden('#skF_1'(A_44, B_45), '#skF_3') | ~r1_tarski(A_44, '#skF_2') | r1_tarski(A_44, B_45))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_120])).
% 2.10/1.26  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.10/1.26  tff(c_141, plain, (![A_46]: (~r1_tarski(A_46, '#skF_2') | r1_tarski(A_46, '#skF_3'))), inference(resolution, [status(thm)], [c_132, c_4])).
% 2.10/1.26  tff(c_149, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_45, c_141])).
% 2.10/1.26  tff(c_160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_149])).
% 2.10/1.26  tff(c_161, plain, (~r1_tarski('#skF_2', k7_relat_1('#skF_3', k1_relat_1('#skF_2')))), inference(splitRight, [status(thm)], [c_18])).
% 2.10/1.26  tff(c_163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_161, c_48])).
% 2.10/1.26  tff(c_164, plain, (r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_24])).
% 2.10/1.26  tff(c_12, plain, (![A_12]: (k7_relat_1(A_12, k1_relat_1(A_12))=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.10/1.26  tff(c_172, plain, (![B_50, A_51, C_52]: (r1_tarski(k7_relat_1(B_50, A_51), k7_relat_1(C_52, A_51)) | ~r1_tarski(B_50, C_52) | ~v1_relat_1(C_52) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.10/1.26  tff(c_234, plain, (![A_64, C_65]: (r1_tarski(A_64, k7_relat_1(C_65, k1_relat_1(A_64))) | ~r1_tarski(A_64, C_65) | ~v1_relat_1(C_65) | ~v1_relat_1(A_64) | ~v1_relat_1(A_64))), inference(superposition, [status(thm), theory('equality')], [c_12, c_172])).
% 2.10/1.26  tff(c_165, plain, (~r1_tarski('#skF_2', k7_relat_1('#skF_3', k1_relat_1('#skF_2')))), inference(splitRight, [status(thm)], [c_24])).
% 2.10/1.26  tff(c_239, plain, (~r1_tarski('#skF_2', '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_234, c_165])).
% 2.10/1.26  tff(c_247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_164, c_239])).
% 2.10/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.26  
% 2.10/1.26  Inference rules
% 2.10/1.26  ----------------------
% 2.10/1.26  #Ref     : 0
% 2.10/1.26  #Sup     : 46
% 2.10/1.26  #Fact    : 0
% 2.10/1.26  #Define  : 0
% 2.10/1.26  #Split   : 2
% 2.10/1.26  #Chain   : 0
% 2.10/1.26  #Close   : 0
% 2.10/1.26  
% 2.10/1.26  Ordering : KBO
% 2.10/1.26  
% 2.10/1.26  Simplification rules
% 2.10/1.26  ----------------------
% 2.10/1.26  #Subsume      : 6
% 2.10/1.26  #Demod        : 16
% 2.10/1.26  #Tautology    : 10
% 2.10/1.26  #SimpNegUnit  : 2
% 2.10/1.26  #BackRed      : 0
% 2.10/1.26  
% 2.10/1.26  #Partial instantiations: 0
% 2.10/1.26  #Strategies tried      : 1
% 2.10/1.26  
% 2.10/1.26  Timing (in seconds)
% 2.10/1.26  ----------------------
% 2.10/1.26  Preprocessing        : 0.25
% 2.10/1.26  Parsing              : 0.13
% 2.10/1.26  CNF conversion       : 0.02
% 2.10/1.26  Main loop            : 0.22
% 2.10/1.26  Inferencing          : 0.09
% 2.10/1.26  Reduction            : 0.05
% 2.10/1.26  Demodulation         : 0.04
% 2.10/1.26  BG Simplification    : 0.01
% 2.10/1.26  Subsumption          : 0.05
% 2.10/1.26  Abstraction          : 0.01
% 2.10/1.26  MUC search           : 0.00
% 2.10/1.26  Cooper               : 0.00
% 2.10/1.26  Total                : 0.49
% 2.10/1.26  Index Insertion      : 0.00
% 2.10/1.26  Index Deletion       : 0.00
% 2.10/1.26  Index Matching       : 0.00
% 2.10/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
