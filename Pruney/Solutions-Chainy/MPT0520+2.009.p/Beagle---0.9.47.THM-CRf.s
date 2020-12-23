%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:08 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
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
%$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k2_relat_1(B))
         => k2_relat_1(k8_relat_1(A,B)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_relat_1)).

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
     => ( r2_hidden(A,k2_relat_1(k8_relat_1(B,C)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_relat_1)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_46,plain,(
    ! [C_18,B_19,A_20] :
      ( r2_hidden(C_18,B_19)
      | ~ r2_hidden(C_18,A_20)
      | ~ r1_tarski(A_20,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    ! [A_24,B_25,B_26] :
      ( r2_hidden('#skF_1'(A_24,B_25),B_26)
      | ~ r1_tarski(A_24,B_26)
      | r1_tarski(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_6,c_46])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_81,plain,(
    ! [A_30,B_31,B_32,B_33] :
      ( r2_hidden('#skF_1'(A_30,B_31),B_32)
      | ~ r1_tarski(B_33,B_32)
      | ~ r1_tarski(A_30,B_33)
      | r1_tarski(A_30,B_31) ) ),
    inference(resolution,[status(thm)],[c_56,c_2])).

tff(c_86,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_1'(A_30,B_31),k2_relat_1('#skF_3'))
      | ~ r1_tarski(A_30,'#skF_2')
      | r1_tarski(A_30,B_31) ) ),
    inference(resolution,[status(thm)],[c_22,c_81])).

tff(c_97,plain,(
    ! [A_36,B_37,C_38] :
      ( r2_hidden(A_36,k2_relat_1(k8_relat_1(B_37,C_38)))
      | ~ r2_hidden(A_36,k2_relat_1(C_38))
      | ~ r2_hidden(A_36,B_37)
      | ~ v1_relat_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_340,plain,(
    ! [A_86,B_87,C_88] :
      ( r1_tarski(A_86,k2_relat_1(k8_relat_1(B_87,C_88)))
      | ~ r2_hidden('#skF_1'(A_86,k2_relat_1(k8_relat_1(B_87,C_88))),k2_relat_1(C_88))
      | ~ r2_hidden('#skF_1'(A_86,k2_relat_1(k8_relat_1(B_87,C_88))),B_87)
      | ~ v1_relat_1(C_88) ) ),
    inference(resolution,[status(thm)],[c_97,c_4])).

tff(c_358,plain,(
    ! [A_30,B_87] :
      ( ~ r2_hidden('#skF_1'(A_30,k2_relat_1(k8_relat_1(B_87,'#skF_3'))),B_87)
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_30,'#skF_2')
      | r1_tarski(A_30,k2_relat_1(k8_relat_1(B_87,'#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_86,c_340])).

tff(c_397,plain,(
    ! [A_92,B_93] :
      ( ~ r2_hidden('#skF_1'(A_92,k2_relat_1(k8_relat_1(B_93,'#skF_3'))),B_93)
      | ~ r1_tarski(A_92,'#skF_2')
      | r1_tarski(A_92,k2_relat_1(k8_relat_1(B_93,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_358])).

tff(c_438,plain,(
    ! [A_94] :
      ( ~ r1_tarski(A_94,'#skF_2')
      | r1_tarski(A_94,k2_relat_1(k8_relat_1(A_94,'#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_6,c_397])).

tff(c_50,plain,(
    ! [A_21,B_22,C_23] :
      ( r2_hidden(A_21,B_22)
      | ~ r2_hidden(A_21,k2_relat_1(k8_relat_1(B_22,C_23)))
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_170,plain,(
    ! [B_49,C_50,B_51] :
      ( r2_hidden('#skF_1'(k2_relat_1(k8_relat_1(B_49,C_50)),B_51),B_49)
      | ~ v1_relat_1(C_50)
      | r1_tarski(k2_relat_1(k8_relat_1(B_49,C_50)),B_51) ) ),
    inference(resolution,[status(thm)],[c_6,c_50])).

tff(c_287,plain,(
    ! [B_79,C_80,B_81,B_82] :
      ( r2_hidden('#skF_1'(k2_relat_1(k8_relat_1(B_79,C_80)),B_81),B_82)
      | ~ r1_tarski(B_79,B_82)
      | ~ v1_relat_1(C_80)
      | r1_tarski(k2_relat_1(k8_relat_1(B_79,C_80)),B_81) ) ),
    inference(resolution,[status(thm)],[c_170,c_2])).

tff(c_306,plain,(
    ! [B_83,B_84,C_85] :
      ( ~ r1_tarski(B_83,B_84)
      | ~ v1_relat_1(C_85)
      | r1_tarski(k2_relat_1(k8_relat_1(B_83,C_85)),B_84) ) ),
    inference(resolution,[status(thm)],[c_287,c_4])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_339,plain,(
    ! [B_83,C_85,B_84] :
      ( k2_relat_1(k8_relat_1(B_83,C_85)) = B_84
      | ~ r1_tarski(B_84,k2_relat_1(k8_relat_1(B_83,C_85)))
      | ~ r1_tarski(B_83,B_84)
      | ~ v1_relat_1(C_85) ) ),
    inference(resolution,[status(thm)],[c_306,c_8])).

tff(c_441,plain,(
    ! [A_94] :
      ( k2_relat_1(k8_relat_1(A_94,'#skF_3')) = A_94
      | ~ r1_tarski(A_94,A_94)
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_94,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_438,c_339])).

tff(c_549,plain,(
    ! [A_96] :
      ( k2_relat_1(k8_relat_1(A_96,'#skF_3')) = A_96
      | ~ r1_tarski(A_96,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_12,c_441])).

tff(c_20,plain,(
    k2_relat_1(k8_relat_1('#skF_2','#skF_3')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_619,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_549,c_20])).

tff(c_660,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_619])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:54:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.38  
% 2.72/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.38  %$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.72/1.38  
% 2.72/1.38  %Foreground sorts:
% 2.72/1.38  
% 2.72/1.38  
% 2.72/1.38  %Background operators:
% 2.72/1.38  
% 2.72/1.38  
% 2.72/1.38  %Foreground operators:
% 2.72/1.38  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.72/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.72/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.72/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.72/1.38  
% 2.72/1.39  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.72/1.39  tff(f_53, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k2_relat_1(B)) => (k2_relat_1(k8_relat_1(A, B)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_relat_1)).
% 2.72/1.39  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.72/1.39  tff(f_46, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k2_relat_1(k8_relat_1(B, C))) <=> (r2_hidden(A, B) & r2_hidden(A, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_relat_1)).
% 2.72/1.39  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.72/1.39  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.72/1.39  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.72/1.39  tff(c_22, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.72/1.39  tff(c_46, plain, (![C_18, B_19, A_20]: (r2_hidden(C_18, B_19) | ~r2_hidden(C_18, A_20) | ~r1_tarski(A_20, B_19))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.72/1.39  tff(c_56, plain, (![A_24, B_25, B_26]: (r2_hidden('#skF_1'(A_24, B_25), B_26) | ~r1_tarski(A_24, B_26) | r1_tarski(A_24, B_25))), inference(resolution, [status(thm)], [c_6, c_46])).
% 2.72/1.39  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.72/1.39  tff(c_81, plain, (![A_30, B_31, B_32, B_33]: (r2_hidden('#skF_1'(A_30, B_31), B_32) | ~r1_tarski(B_33, B_32) | ~r1_tarski(A_30, B_33) | r1_tarski(A_30, B_31))), inference(resolution, [status(thm)], [c_56, c_2])).
% 2.72/1.39  tff(c_86, plain, (![A_30, B_31]: (r2_hidden('#skF_1'(A_30, B_31), k2_relat_1('#skF_3')) | ~r1_tarski(A_30, '#skF_2') | r1_tarski(A_30, B_31))), inference(resolution, [status(thm)], [c_22, c_81])).
% 2.72/1.39  tff(c_97, plain, (![A_36, B_37, C_38]: (r2_hidden(A_36, k2_relat_1(k8_relat_1(B_37, C_38))) | ~r2_hidden(A_36, k2_relat_1(C_38)) | ~r2_hidden(A_36, B_37) | ~v1_relat_1(C_38))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.72/1.39  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.72/1.39  tff(c_340, plain, (![A_86, B_87, C_88]: (r1_tarski(A_86, k2_relat_1(k8_relat_1(B_87, C_88))) | ~r2_hidden('#skF_1'(A_86, k2_relat_1(k8_relat_1(B_87, C_88))), k2_relat_1(C_88)) | ~r2_hidden('#skF_1'(A_86, k2_relat_1(k8_relat_1(B_87, C_88))), B_87) | ~v1_relat_1(C_88))), inference(resolution, [status(thm)], [c_97, c_4])).
% 2.72/1.39  tff(c_358, plain, (![A_30, B_87]: (~r2_hidden('#skF_1'(A_30, k2_relat_1(k8_relat_1(B_87, '#skF_3'))), B_87) | ~v1_relat_1('#skF_3') | ~r1_tarski(A_30, '#skF_2') | r1_tarski(A_30, k2_relat_1(k8_relat_1(B_87, '#skF_3'))))), inference(resolution, [status(thm)], [c_86, c_340])).
% 2.72/1.39  tff(c_397, plain, (![A_92, B_93]: (~r2_hidden('#skF_1'(A_92, k2_relat_1(k8_relat_1(B_93, '#skF_3'))), B_93) | ~r1_tarski(A_92, '#skF_2') | r1_tarski(A_92, k2_relat_1(k8_relat_1(B_93, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_358])).
% 2.72/1.39  tff(c_438, plain, (![A_94]: (~r1_tarski(A_94, '#skF_2') | r1_tarski(A_94, k2_relat_1(k8_relat_1(A_94, '#skF_3'))))), inference(resolution, [status(thm)], [c_6, c_397])).
% 2.72/1.39  tff(c_50, plain, (![A_21, B_22, C_23]: (r2_hidden(A_21, B_22) | ~r2_hidden(A_21, k2_relat_1(k8_relat_1(B_22, C_23))) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.72/1.39  tff(c_170, plain, (![B_49, C_50, B_51]: (r2_hidden('#skF_1'(k2_relat_1(k8_relat_1(B_49, C_50)), B_51), B_49) | ~v1_relat_1(C_50) | r1_tarski(k2_relat_1(k8_relat_1(B_49, C_50)), B_51))), inference(resolution, [status(thm)], [c_6, c_50])).
% 2.72/1.39  tff(c_287, plain, (![B_79, C_80, B_81, B_82]: (r2_hidden('#skF_1'(k2_relat_1(k8_relat_1(B_79, C_80)), B_81), B_82) | ~r1_tarski(B_79, B_82) | ~v1_relat_1(C_80) | r1_tarski(k2_relat_1(k8_relat_1(B_79, C_80)), B_81))), inference(resolution, [status(thm)], [c_170, c_2])).
% 2.72/1.39  tff(c_306, plain, (![B_83, B_84, C_85]: (~r1_tarski(B_83, B_84) | ~v1_relat_1(C_85) | r1_tarski(k2_relat_1(k8_relat_1(B_83, C_85)), B_84))), inference(resolution, [status(thm)], [c_287, c_4])).
% 2.72/1.39  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.72/1.39  tff(c_339, plain, (![B_83, C_85, B_84]: (k2_relat_1(k8_relat_1(B_83, C_85))=B_84 | ~r1_tarski(B_84, k2_relat_1(k8_relat_1(B_83, C_85))) | ~r1_tarski(B_83, B_84) | ~v1_relat_1(C_85))), inference(resolution, [status(thm)], [c_306, c_8])).
% 2.72/1.39  tff(c_441, plain, (![A_94]: (k2_relat_1(k8_relat_1(A_94, '#skF_3'))=A_94 | ~r1_tarski(A_94, A_94) | ~v1_relat_1('#skF_3') | ~r1_tarski(A_94, '#skF_2'))), inference(resolution, [status(thm)], [c_438, c_339])).
% 2.72/1.39  tff(c_549, plain, (![A_96]: (k2_relat_1(k8_relat_1(A_96, '#skF_3'))=A_96 | ~r1_tarski(A_96, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_12, c_441])).
% 2.72/1.39  tff(c_20, plain, (k2_relat_1(k8_relat_1('#skF_2', '#skF_3'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.72/1.39  tff(c_619, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_549, c_20])).
% 2.72/1.39  tff(c_660, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_619])).
% 2.72/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.39  
% 2.72/1.39  Inference rules
% 2.72/1.39  ----------------------
% 2.72/1.39  #Ref     : 0
% 2.72/1.39  #Sup     : 143
% 2.72/1.39  #Fact    : 0
% 2.72/1.39  #Define  : 0
% 2.72/1.39  #Split   : 1
% 2.72/1.39  #Chain   : 0
% 2.72/1.39  #Close   : 0
% 2.72/1.39  
% 2.72/1.39  Ordering : KBO
% 2.72/1.39  
% 2.72/1.39  Simplification rules
% 2.72/1.39  ----------------------
% 2.72/1.39  #Subsume      : 36
% 2.72/1.39  #Demod        : 35
% 2.72/1.39  #Tautology    : 15
% 2.72/1.39  #SimpNegUnit  : 0
% 2.72/1.40  #BackRed      : 0
% 2.72/1.40  
% 2.72/1.40  #Partial instantiations: 0
% 2.72/1.40  #Strategies tried      : 1
% 2.72/1.40  
% 2.72/1.40  Timing (in seconds)
% 2.72/1.40  ----------------------
% 2.72/1.40  Preprocessing        : 0.25
% 2.72/1.40  Parsing              : 0.14
% 2.72/1.40  CNF conversion       : 0.02
% 2.72/1.40  Main loop            : 0.37
% 2.72/1.40  Inferencing          : 0.13
% 2.72/1.40  Reduction            : 0.09
% 2.72/1.40  Demodulation         : 0.06
% 2.72/1.40  BG Simplification    : 0.02
% 2.72/1.40  Subsumption          : 0.11
% 2.72/1.40  Abstraction          : 0.02
% 2.72/1.40  MUC search           : 0.00
% 2.72/1.40  Cooper               : 0.00
% 2.72/1.40  Total                : 0.65
% 2.72/1.40  Index Insertion      : 0.00
% 2.72/1.40  Index Deletion       : 0.00
% 2.72/1.40  Index Matching       : 0.00
% 2.72/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
