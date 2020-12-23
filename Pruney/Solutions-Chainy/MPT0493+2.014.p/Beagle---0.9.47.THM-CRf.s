%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:37 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   41 (  60 expanded)
%              Number of leaves         :   15 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :   82 ( 133 expanded)
%              Number of equality atoms :    7 (  12 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_52,plain,(
    ! [C_22,B_23,A_24] :
      ( r2_hidden(C_22,B_23)
      | ~ r2_hidden(C_22,A_24)
      | ~ r1_tarski(A_24,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    ! [A_28,B_29,B_30] :
      ( r2_hidden('#skF_1'(A_28,B_29),B_30)
      | ~ r1_tarski(A_28,B_30)
      | r1_tarski(A_28,B_29) ) ),
    inference(resolution,[status(thm)],[c_6,c_52])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_105,plain,(
    ! [A_39,B_40,B_41,B_42] :
      ( r2_hidden('#skF_1'(A_39,B_40),B_41)
      | ~ r1_tarski(B_42,B_41)
      | ~ r1_tarski(A_39,B_42)
      | r1_tarski(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_62,c_2])).

tff(c_113,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_1'(A_39,B_40),k1_relat_1('#skF_3'))
      | ~ r1_tarski(A_39,'#skF_2')
      | r1_tarski(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_24,c_105])).

tff(c_88,plain,(
    ! [A_36,C_37,B_38] :
      ( r2_hidden(A_36,k1_relat_1(k7_relat_1(C_37,B_38)))
      | ~ r2_hidden(A_36,k1_relat_1(C_37))
      | ~ r2_hidden(A_36,B_38)
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_342,plain,(
    ! [A_88,C_89,B_90] :
      ( r1_tarski(A_88,k1_relat_1(k7_relat_1(C_89,B_90)))
      | ~ r2_hidden('#skF_1'(A_88,k1_relat_1(k7_relat_1(C_89,B_90))),k1_relat_1(C_89))
      | ~ r2_hidden('#skF_1'(A_88,k1_relat_1(k7_relat_1(C_89,B_90))),B_90)
      | ~ v1_relat_1(C_89) ) ),
    inference(resolution,[status(thm)],[c_88,c_4])).

tff(c_357,plain,(
    ! [A_39,B_90] :
      ( ~ r2_hidden('#skF_1'(A_39,k1_relat_1(k7_relat_1('#skF_3',B_90))),B_90)
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_39,'#skF_2')
      | r1_tarski(A_39,k1_relat_1(k7_relat_1('#skF_3',B_90))) ) ),
    inference(resolution,[status(thm)],[c_113,c_342])).

tff(c_399,plain,(
    ! [A_94,B_95] :
      ( ~ r2_hidden('#skF_1'(A_94,k1_relat_1(k7_relat_1('#skF_3',B_95))),B_95)
      | ~ r1_tarski(A_94,'#skF_2')
      | r1_tarski(A_94,k1_relat_1(k7_relat_1('#skF_3',B_95))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_357])).

tff(c_440,plain,(
    ! [A_96] :
      ( ~ r1_tarski(A_96,'#skF_2')
      | r1_tarski(A_96,k1_relat_1(k7_relat_1('#skF_3',A_96))) ) ),
    inference(resolution,[status(thm)],[c_6,c_399])).

tff(c_56,plain,(
    ! [A_25,B_26,C_27] :
      ( r2_hidden(A_25,B_26)
      | ~ r2_hidden(A_25,k1_relat_1(k7_relat_1(C_27,B_26)))
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_183,plain,(
    ! [C_55,B_56,B_57] :
      ( r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_55,B_56)),B_57),B_56)
      | ~ v1_relat_1(C_55)
      | r1_tarski(k1_relat_1(k7_relat_1(C_55,B_56)),B_57) ) ),
    inference(resolution,[status(thm)],[c_6,c_56])).

tff(c_289,plain,(
    ! [C_81,B_82,B_83,B_84] :
      ( r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_81,B_82)),B_83),B_84)
      | ~ r1_tarski(B_82,B_84)
      | ~ v1_relat_1(C_81)
      | r1_tarski(k1_relat_1(k7_relat_1(C_81,B_82)),B_83) ) ),
    inference(resolution,[status(thm)],[c_183,c_2])).

tff(c_308,plain,(
    ! [B_85,B_86,C_87] :
      ( ~ r1_tarski(B_85,B_86)
      | ~ v1_relat_1(C_87)
      | r1_tarski(k1_relat_1(k7_relat_1(C_87,B_85)),B_86) ) ),
    inference(resolution,[status(thm)],[c_289,c_4])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_341,plain,(
    ! [C_87,B_85,B_86] :
      ( k1_relat_1(k7_relat_1(C_87,B_85)) = B_86
      | ~ r1_tarski(B_86,k1_relat_1(k7_relat_1(C_87,B_85)))
      | ~ r1_tarski(B_85,B_86)
      | ~ v1_relat_1(C_87) ) ),
    inference(resolution,[status(thm)],[c_308,c_8])).

tff(c_443,plain,(
    ! [A_96] :
      ( k1_relat_1(k7_relat_1('#skF_3',A_96)) = A_96
      | ~ r1_tarski(A_96,A_96)
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_96,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_440,c_341])).

tff(c_551,plain,(
    ! [A_98] :
      ( k1_relat_1(k7_relat_1('#skF_3',A_98)) = A_98
      | ~ r1_tarski(A_98,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_12,c_443])).

tff(c_22,plain,(
    k1_relat_1(k7_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_621,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_22])).

tff(c_662,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_621])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:01:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.40  
% 2.90/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.41  %$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.90/1.41  
% 2.90/1.41  %Foreground sorts:
% 2.90/1.41  
% 2.90/1.41  
% 2.90/1.41  %Background operators:
% 2.90/1.41  
% 2.90/1.41  
% 2.90/1.41  %Foreground operators:
% 2.90/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.90/1.41  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.90/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.90/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.90/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.90/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.90/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.90/1.41  
% 2.90/1.42  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.90/1.42  tff(f_57, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 2.90/1.42  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.90/1.42  tff(f_46, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 2.90/1.42  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.90/1.42  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.90/1.42  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.90/1.42  tff(c_24, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.90/1.42  tff(c_52, plain, (![C_22, B_23, A_24]: (r2_hidden(C_22, B_23) | ~r2_hidden(C_22, A_24) | ~r1_tarski(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.90/1.42  tff(c_62, plain, (![A_28, B_29, B_30]: (r2_hidden('#skF_1'(A_28, B_29), B_30) | ~r1_tarski(A_28, B_30) | r1_tarski(A_28, B_29))), inference(resolution, [status(thm)], [c_6, c_52])).
% 2.90/1.42  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.90/1.42  tff(c_105, plain, (![A_39, B_40, B_41, B_42]: (r2_hidden('#skF_1'(A_39, B_40), B_41) | ~r1_tarski(B_42, B_41) | ~r1_tarski(A_39, B_42) | r1_tarski(A_39, B_40))), inference(resolution, [status(thm)], [c_62, c_2])).
% 2.90/1.42  tff(c_113, plain, (![A_39, B_40]: (r2_hidden('#skF_1'(A_39, B_40), k1_relat_1('#skF_3')) | ~r1_tarski(A_39, '#skF_2') | r1_tarski(A_39, B_40))), inference(resolution, [status(thm)], [c_24, c_105])).
% 2.90/1.42  tff(c_88, plain, (![A_36, C_37, B_38]: (r2_hidden(A_36, k1_relat_1(k7_relat_1(C_37, B_38))) | ~r2_hidden(A_36, k1_relat_1(C_37)) | ~r2_hidden(A_36, B_38) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.90/1.42  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.90/1.42  tff(c_342, plain, (![A_88, C_89, B_90]: (r1_tarski(A_88, k1_relat_1(k7_relat_1(C_89, B_90))) | ~r2_hidden('#skF_1'(A_88, k1_relat_1(k7_relat_1(C_89, B_90))), k1_relat_1(C_89)) | ~r2_hidden('#skF_1'(A_88, k1_relat_1(k7_relat_1(C_89, B_90))), B_90) | ~v1_relat_1(C_89))), inference(resolution, [status(thm)], [c_88, c_4])).
% 2.90/1.42  tff(c_357, plain, (![A_39, B_90]: (~r2_hidden('#skF_1'(A_39, k1_relat_1(k7_relat_1('#skF_3', B_90))), B_90) | ~v1_relat_1('#skF_3') | ~r1_tarski(A_39, '#skF_2') | r1_tarski(A_39, k1_relat_1(k7_relat_1('#skF_3', B_90))))), inference(resolution, [status(thm)], [c_113, c_342])).
% 2.90/1.42  tff(c_399, plain, (![A_94, B_95]: (~r2_hidden('#skF_1'(A_94, k1_relat_1(k7_relat_1('#skF_3', B_95))), B_95) | ~r1_tarski(A_94, '#skF_2') | r1_tarski(A_94, k1_relat_1(k7_relat_1('#skF_3', B_95))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_357])).
% 2.90/1.42  tff(c_440, plain, (![A_96]: (~r1_tarski(A_96, '#skF_2') | r1_tarski(A_96, k1_relat_1(k7_relat_1('#skF_3', A_96))))), inference(resolution, [status(thm)], [c_6, c_399])).
% 2.90/1.42  tff(c_56, plain, (![A_25, B_26, C_27]: (r2_hidden(A_25, B_26) | ~r2_hidden(A_25, k1_relat_1(k7_relat_1(C_27, B_26))) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.90/1.42  tff(c_183, plain, (![C_55, B_56, B_57]: (r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_55, B_56)), B_57), B_56) | ~v1_relat_1(C_55) | r1_tarski(k1_relat_1(k7_relat_1(C_55, B_56)), B_57))), inference(resolution, [status(thm)], [c_6, c_56])).
% 2.90/1.42  tff(c_289, plain, (![C_81, B_82, B_83, B_84]: (r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_81, B_82)), B_83), B_84) | ~r1_tarski(B_82, B_84) | ~v1_relat_1(C_81) | r1_tarski(k1_relat_1(k7_relat_1(C_81, B_82)), B_83))), inference(resolution, [status(thm)], [c_183, c_2])).
% 2.90/1.42  tff(c_308, plain, (![B_85, B_86, C_87]: (~r1_tarski(B_85, B_86) | ~v1_relat_1(C_87) | r1_tarski(k1_relat_1(k7_relat_1(C_87, B_85)), B_86))), inference(resolution, [status(thm)], [c_289, c_4])).
% 2.90/1.42  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.90/1.42  tff(c_341, plain, (![C_87, B_85, B_86]: (k1_relat_1(k7_relat_1(C_87, B_85))=B_86 | ~r1_tarski(B_86, k1_relat_1(k7_relat_1(C_87, B_85))) | ~r1_tarski(B_85, B_86) | ~v1_relat_1(C_87))), inference(resolution, [status(thm)], [c_308, c_8])).
% 2.90/1.42  tff(c_443, plain, (![A_96]: (k1_relat_1(k7_relat_1('#skF_3', A_96))=A_96 | ~r1_tarski(A_96, A_96) | ~v1_relat_1('#skF_3') | ~r1_tarski(A_96, '#skF_2'))), inference(resolution, [status(thm)], [c_440, c_341])).
% 2.90/1.42  tff(c_551, plain, (![A_98]: (k1_relat_1(k7_relat_1('#skF_3', A_98))=A_98 | ~r1_tarski(A_98, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_12, c_443])).
% 2.90/1.42  tff(c_22, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.90/1.42  tff(c_621, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_551, c_22])).
% 2.90/1.42  tff(c_662, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_621])).
% 2.90/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.42  
% 2.90/1.42  Inference rules
% 2.90/1.42  ----------------------
% 2.90/1.42  #Ref     : 0
% 2.90/1.42  #Sup     : 143
% 2.90/1.42  #Fact    : 0
% 2.90/1.42  #Define  : 0
% 2.90/1.42  #Split   : 1
% 2.90/1.42  #Chain   : 0
% 2.90/1.42  #Close   : 0
% 2.90/1.42  
% 2.90/1.42  Ordering : KBO
% 2.90/1.42  
% 2.90/1.42  Simplification rules
% 2.90/1.42  ----------------------
% 2.90/1.42  #Subsume      : 37
% 2.90/1.42  #Demod        : 35
% 2.90/1.42  #Tautology    : 15
% 2.90/1.42  #SimpNegUnit  : 0
% 2.90/1.42  #BackRed      : 0
% 2.90/1.42  
% 2.90/1.42  #Partial instantiations: 0
% 2.90/1.42  #Strategies tried      : 1
% 2.90/1.42  
% 2.90/1.42  Timing (in seconds)
% 2.90/1.42  ----------------------
% 2.90/1.42  Preprocessing        : 0.27
% 2.90/1.42  Parsing              : 0.15
% 2.90/1.42  CNF conversion       : 0.02
% 2.90/1.42  Main loop            : 0.38
% 2.90/1.42  Inferencing          : 0.14
% 2.90/1.42  Reduction            : 0.09
% 2.90/1.42  Demodulation         : 0.06
% 2.90/1.42  BG Simplification    : 0.02
% 2.90/1.42  Subsumption          : 0.11
% 2.90/1.42  Abstraction          : 0.02
% 2.90/1.42  MUC search           : 0.00
% 2.90/1.42  Cooper               : 0.00
% 2.90/1.42  Total                : 0.68
% 2.90/1.42  Index Insertion      : 0.00
% 2.90/1.42  Index Deletion       : 0.00
% 2.90/1.42  Index Matching       : 0.00
% 2.90/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
