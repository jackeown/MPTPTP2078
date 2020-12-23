%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:56 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   45 (  71 expanded)
%              Number of leaves         :   18 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 169 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k7_relat_1(C,A),k7_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k7_relat_1(B_16,A_15),B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_34,plain,(
    ! [C_26,B_27,A_28] :
      ( r2_hidden(C_26,B_27)
      | ~ r2_hidden(C_26,A_28)
      | ~ r1_tarski(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_39,plain,(
    ! [A_30,B_31,B_32] :
      ( r2_hidden('#skF_1'(A_30,B_31),B_32)
      | ~ r1_tarski(A_30,B_32)
      | r1_tarski(A_30,B_31) ) ),
    inference(resolution,[status(thm)],[c_6,c_34])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_77,plain,(
    ! [A_39,B_40,B_41,B_42] :
      ( r2_hidden('#skF_1'(A_39,B_40),B_41)
      | ~ r1_tarski(B_42,B_41)
      | ~ r1_tarski(A_39,B_42)
      | r1_tarski(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_39,c_2])).

tff(c_110,plain,(
    ! [A_47,B_48] :
      ( r2_hidden('#skF_1'(A_47,B_48),'#skF_5')
      | ~ r1_tarski(A_47,'#skF_4')
      | r1_tarski(A_47,B_48) ) ),
    inference(resolution,[status(thm)],[c_20,c_77])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_118,plain,(
    ! [A_47] :
      ( ~ r1_tarski(A_47,'#skF_4')
      | r1_tarski(A_47,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_110,c_4])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k7_relat_1(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10,plain,(
    ! [C_10,A_8,B_9] :
      ( k7_relat_1(k7_relat_1(C_10,A_8),B_9) = k7_relat_1(C_10,A_8)
      | ~ r1_tarski(A_8,B_9)
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_70,plain,(
    ! [B_36,A_37,C_38] :
      ( r1_tarski(k7_relat_1(B_36,A_37),k7_relat_1(C_38,A_37))
      | ~ r1_tarski(B_36,C_38)
      | ~ v1_relat_1(C_38)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_433,plain,(
    ! [C_93,A_94,C_95,B_96] :
      ( r1_tarski(k7_relat_1(C_93,A_94),k7_relat_1(C_95,B_96))
      | ~ r1_tarski(k7_relat_1(C_93,A_94),C_95)
      | ~ v1_relat_1(C_95)
      | ~ v1_relat_1(k7_relat_1(C_93,A_94))
      | ~ r1_tarski(A_94,B_96)
      | ~ v1_relat_1(C_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_70])).

tff(c_16,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_2'),k7_relat_1('#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_448,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_4','#skF_2'),'#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_433,c_16])).

tff(c_475,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_4','#skF_2'),'#skF_5')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18,c_22,c_448])).

tff(c_476,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_475])).

tff(c_479,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_476])).

tff(c_483,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_479])).

tff(c_484,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_2'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_475])).

tff(c_489,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_118,c_484])).

tff(c_492,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_489])).

tff(c_496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_492])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:03:45 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.40  
% 2.72/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.40  %$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.72/1.40  
% 2.72/1.40  %Foreground sorts:
% 2.72/1.40  
% 2.72/1.40  
% 2.72/1.40  %Background operators:
% 2.72/1.40  
% 2.72/1.40  
% 2.72/1.40  %Foreground operators:
% 2.72/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.40  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.72/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.72/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.72/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.72/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.72/1.40  
% 2.72/1.41  tff(f_67, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k7_relat_1(C, A), k7_relat_1(D, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_relat_1)).
% 2.72/1.41  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 2.72/1.41  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.72/1.41  tff(f_36, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.72/1.41  tff(f_42, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_relat_1)).
% 2.72/1.41  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_relat_1)).
% 2.72/1.41  tff(c_24, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.72/1.41  tff(c_14, plain, (![B_16, A_15]: (r1_tarski(k7_relat_1(B_16, A_15), B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.72/1.41  tff(c_20, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.72/1.41  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.72/1.41  tff(c_34, plain, (![C_26, B_27, A_28]: (r2_hidden(C_26, B_27) | ~r2_hidden(C_26, A_28) | ~r1_tarski(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.72/1.41  tff(c_39, plain, (![A_30, B_31, B_32]: (r2_hidden('#skF_1'(A_30, B_31), B_32) | ~r1_tarski(A_30, B_32) | r1_tarski(A_30, B_31))), inference(resolution, [status(thm)], [c_6, c_34])).
% 2.72/1.41  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.72/1.41  tff(c_77, plain, (![A_39, B_40, B_41, B_42]: (r2_hidden('#skF_1'(A_39, B_40), B_41) | ~r1_tarski(B_42, B_41) | ~r1_tarski(A_39, B_42) | r1_tarski(A_39, B_40))), inference(resolution, [status(thm)], [c_39, c_2])).
% 2.72/1.41  tff(c_110, plain, (![A_47, B_48]: (r2_hidden('#skF_1'(A_47, B_48), '#skF_5') | ~r1_tarski(A_47, '#skF_4') | r1_tarski(A_47, B_48))), inference(resolution, [status(thm)], [c_20, c_77])).
% 2.72/1.41  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.72/1.41  tff(c_118, plain, (![A_47]: (~r1_tarski(A_47, '#skF_4') | r1_tarski(A_47, '#skF_5'))), inference(resolution, [status(thm)], [c_110, c_4])).
% 2.72/1.41  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k7_relat_1(A_6, B_7)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.72/1.41  tff(c_18, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.72/1.41  tff(c_22, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.72/1.41  tff(c_10, plain, (![C_10, A_8, B_9]: (k7_relat_1(k7_relat_1(C_10, A_8), B_9)=k7_relat_1(C_10, A_8) | ~r1_tarski(A_8, B_9) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.72/1.41  tff(c_70, plain, (![B_36, A_37, C_38]: (r1_tarski(k7_relat_1(B_36, A_37), k7_relat_1(C_38, A_37)) | ~r1_tarski(B_36, C_38) | ~v1_relat_1(C_38) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.72/1.41  tff(c_433, plain, (![C_93, A_94, C_95, B_96]: (r1_tarski(k7_relat_1(C_93, A_94), k7_relat_1(C_95, B_96)) | ~r1_tarski(k7_relat_1(C_93, A_94), C_95) | ~v1_relat_1(C_95) | ~v1_relat_1(k7_relat_1(C_93, A_94)) | ~r1_tarski(A_94, B_96) | ~v1_relat_1(C_93))), inference(superposition, [status(thm), theory('equality')], [c_10, c_70])).
% 2.72/1.41  tff(c_16, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_2'), k7_relat_1('#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.72/1.41  tff(c_448, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_2'), '#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_433, c_16])).
% 2.72/1.41  tff(c_475, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_2'), '#skF_5') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_18, c_22, c_448])).
% 2.72/1.41  tff(c_476, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(splitLeft, [status(thm)], [c_475])).
% 2.72/1.41  tff(c_479, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_476])).
% 2.72/1.41  tff(c_483, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_479])).
% 2.72/1.41  tff(c_484, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_2'), '#skF_5')), inference(splitRight, [status(thm)], [c_475])).
% 2.72/1.41  tff(c_489, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_118, c_484])).
% 2.72/1.41  tff(c_492, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_489])).
% 2.72/1.41  tff(c_496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_492])).
% 2.72/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.41  
% 2.72/1.41  Inference rules
% 2.72/1.41  ----------------------
% 2.72/1.41  #Ref     : 0
% 2.72/1.41  #Sup     : 127
% 2.72/1.41  #Fact    : 0
% 2.72/1.41  #Define  : 0
% 2.72/1.41  #Split   : 6
% 2.72/1.41  #Chain   : 0
% 2.72/1.41  #Close   : 0
% 2.72/1.41  
% 2.72/1.41  Ordering : KBO
% 2.72/1.41  
% 2.72/1.41  Simplification rules
% 2.72/1.41  ----------------------
% 2.72/1.41  #Subsume      : 31
% 2.72/1.41  #Demod        : 11
% 2.72/1.41  #Tautology    : 12
% 2.72/1.41  #SimpNegUnit  : 0
% 2.72/1.41  #BackRed      : 0
% 2.72/1.41  
% 2.72/1.41  #Partial instantiations: 0
% 2.72/1.41  #Strategies tried      : 1
% 2.72/1.41  
% 2.72/1.41  Timing (in seconds)
% 2.72/1.41  ----------------------
% 2.72/1.42  Preprocessing        : 0.27
% 2.72/1.42  Parsing              : 0.15
% 2.72/1.42  CNF conversion       : 0.02
% 2.72/1.42  Main loop            : 0.35
% 2.72/1.42  Inferencing          : 0.13
% 2.72/1.42  Reduction            : 0.08
% 2.72/1.42  Demodulation         : 0.05
% 2.72/1.42  BG Simplification    : 0.02
% 2.72/1.42  Subsumption          : 0.09
% 2.72/1.42  Abstraction          : 0.02
% 2.72/1.42  MUC search           : 0.00
% 2.72/1.42  Cooper               : 0.00
% 2.72/1.42  Total                : 0.64
% 2.72/1.42  Index Insertion      : 0.00
% 2.72/1.42  Index Deletion       : 0.00
% 2.72/1.42  Index Matching       : 0.00
% 2.72/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
