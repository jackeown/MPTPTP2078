%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:19 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
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
%$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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
             => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k8_relat_1(A,B),k8_relat_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k8_relat_1(A_8,B_9),B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

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
      ( v1_relat_1(k8_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12,plain,(
    ! [B_11,A_10,C_12] :
      ( k8_relat_1(B_11,k8_relat_1(A_10,C_12)) = k8_relat_1(A_10,C_12)
      | ~ r1_tarski(A_10,B_11)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_70,plain,(
    ! [A_36,B_37,C_38] :
      ( r1_tarski(k8_relat_1(A_36,B_37),k8_relat_1(A_36,C_38))
      | ~ r1_tarski(B_37,C_38)
      | ~ v1_relat_1(C_38)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_433,plain,(
    ! [A_93,C_94,B_95,C_96] :
      ( r1_tarski(k8_relat_1(A_93,C_94),k8_relat_1(B_95,C_96))
      | ~ r1_tarski(k8_relat_1(A_93,C_94),C_96)
      | ~ v1_relat_1(C_96)
      | ~ v1_relat_1(k8_relat_1(A_93,C_94))
      | ~ r1_tarski(A_93,B_95)
      | ~ v1_relat_1(C_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_70])).

tff(c_16,plain,(
    ~ r1_tarski(k8_relat_1('#skF_2','#skF_4'),k8_relat_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_448,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_2','#skF_4'),'#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_2','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_433,c_16])).

tff(c_475,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_2','#skF_4'),'#skF_5')
    | ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18,c_22,c_448])).

tff(c_476,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_475])).

tff(c_479,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_476])).

tff(c_483,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_479])).

tff(c_484,plain,(
    ~ r1_tarski(k8_relat_1('#skF_2','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_475])).

tff(c_489,plain,(
    ~ r1_tarski(k8_relat_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_118,c_484])).

tff(c_492,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_489])).

tff(c_496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_492])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:09:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.48  
% 2.76/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.48  %$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.76/1.48  
% 2.76/1.48  %Foreground sorts:
% 2.76/1.48  
% 2.76/1.48  
% 2.76/1.48  %Background operators:
% 2.76/1.48  
% 2.76/1.48  
% 2.76/1.48  %Foreground operators:
% 2.76/1.48  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.76/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.48  tff('#skF_5', type, '#skF_5': $i).
% 2.76/1.48  tff('#skF_2', type, '#skF_2': $i).
% 2.76/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.76/1.48  tff('#skF_4', type, '#skF_4': $i).
% 2.76/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.76/1.48  
% 2.76/1.49  tff(f_67, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t133_relat_1)).
% 2.76/1.49  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 2.76/1.49  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.76/1.49  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.76/1.49  tff(f_46, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_relat_1)).
% 2.76/1.49  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k8_relat_1(A, B), k8_relat_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_relat_1)).
% 2.76/1.49  tff(c_24, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.76/1.49  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k8_relat_1(A_8, B_9), B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.76/1.49  tff(c_20, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.76/1.49  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.76/1.49  tff(c_34, plain, (![C_26, B_27, A_28]: (r2_hidden(C_26, B_27) | ~r2_hidden(C_26, A_28) | ~r1_tarski(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.76/1.49  tff(c_39, plain, (![A_30, B_31, B_32]: (r2_hidden('#skF_1'(A_30, B_31), B_32) | ~r1_tarski(A_30, B_32) | r1_tarski(A_30, B_31))), inference(resolution, [status(thm)], [c_6, c_34])).
% 2.76/1.49  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.76/1.49  tff(c_77, plain, (![A_39, B_40, B_41, B_42]: (r2_hidden('#skF_1'(A_39, B_40), B_41) | ~r1_tarski(B_42, B_41) | ~r1_tarski(A_39, B_42) | r1_tarski(A_39, B_40))), inference(resolution, [status(thm)], [c_39, c_2])).
% 2.76/1.49  tff(c_110, plain, (![A_47, B_48]: (r2_hidden('#skF_1'(A_47, B_48), '#skF_5') | ~r1_tarski(A_47, '#skF_4') | r1_tarski(A_47, B_48))), inference(resolution, [status(thm)], [c_20, c_77])).
% 2.76/1.49  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.76/1.49  tff(c_118, plain, (![A_47]: (~r1_tarski(A_47, '#skF_4') | r1_tarski(A_47, '#skF_5'))), inference(resolution, [status(thm)], [c_110, c_4])).
% 2.76/1.49  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k8_relat_1(A_6, B_7)) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.76/1.49  tff(c_18, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.76/1.49  tff(c_22, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.76/1.49  tff(c_12, plain, (![B_11, A_10, C_12]: (k8_relat_1(B_11, k8_relat_1(A_10, C_12))=k8_relat_1(A_10, C_12) | ~r1_tarski(A_10, B_11) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.76/1.49  tff(c_70, plain, (![A_36, B_37, C_38]: (r1_tarski(k8_relat_1(A_36, B_37), k8_relat_1(A_36, C_38)) | ~r1_tarski(B_37, C_38) | ~v1_relat_1(C_38) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.76/1.49  tff(c_433, plain, (![A_93, C_94, B_95, C_96]: (r1_tarski(k8_relat_1(A_93, C_94), k8_relat_1(B_95, C_96)) | ~r1_tarski(k8_relat_1(A_93, C_94), C_96) | ~v1_relat_1(C_96) | ~v1_relat_1(k8_relat_1(A_93, C_94)) | ~r1_tarski(A_93, B_95) | ~v1_relat_1(C_94))), inference(superposition, [status(thm), theory('equality')], [c_12, c_70])).
% 2.76/1.49  tff(c_16, plain, (~r1_tarski(k8_relat_1('#skF_2', '#skF_4'), k8_relat_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.76/1.49  tff(c_448, plain, (~r1_tarski(k8_relat_1('#skF_2', '#skF_4'), '#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k8_relat_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_2', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_433, c_16])).
% 2.76/1.49  tff(c_475, plain, (~r1_tarski(k8_relat_1('#skF_2', '#skF_4'), '#skF_5') | ~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_18, c_22, c_448])).
% 2.76/1.49  tff(c_476, plain, (~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_475])).
% 2.76/1.49  tff(c_479, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_476])).
% 2.76/1.49  tff(c_483, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_479])).
% 2.76/1.49  tff(c_484, plain, (~r1_tarski(k8_relat_1('#skF_2', '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_475])).
% 2.76/1.49  tff(c_489, plain, (~r1_tarski(k8_relat_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_118, c_484])).
% 2.76/1.49  tff(c_492, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_489])).
% 2.76/1.49  tff(c_496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_492])).
% 2.76/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.49  
% 2.76/1.49  Inference rules
% 2.76/1.49  ----------------------
% 2.76/1.49  #Ref     : 0
% 2.76/1.49  #Sup     : 127
% 2.76/1.49  #Fact    : 0
% 2.76/1.49  #Define  : 0
% 2.76/1.49  #Split   : 6
% 2.76/1.49  #Chain   : 0
% 2.76/1.49  #Close   : 0
% 2.76/1.49  
% 2.76/1.49  Ordering : KBO
% 2.76/1.49  
% 2.76/1.49  Simplification rules
% 2.76/1.49  ----------------------
% 2.76/1.49  #Subsume      : 31
% 2.76/1.49  #Demod        : 11
% 2.76/1.49  #Tautology    : 12
% 2.76/1.49  #SimpNegUnit  : 0
% 2.76/1.49  #BackRed      : 0
% 2.76/1.49  
% 2.76/1.49  #Partial instantiations: 0
% 2.76/1.49  #Strategies tried      : 1
% 2.76/1.49  
% 2.76/1.49  Timing (in seconds)
% 2.76/1.49  ----------------------
% 2.76/1.50  Preprocessing        : 0.31
% 2.76/1.50  Parsing              : 0.17
% 2.76/1.50  CNF conversion       : 0.02
% 2.76/1.50  Main loop            : 0.35
% 2.76/1.50  Inferencing          : 0.14
% 2.76/1.50  Reduction            : 0.08
% 2.76/1.50  Demodulation         : 0.05
% 2.76/1.50  BG Simplification    : 0.02
% 2.76/1.50  Subsumption          : 0.09
% 2.76/1.50  Abstraction          : 0.02
% 2.76/1.50  MUC search           : 0.00
% 2.76/1.50  Cooper               : 0.00
% 2.76/1.50  Total                : 0.69
% 2.76/1.50  Index Insertion      : 0.00
% 2.76/1.50  Index Deletion       : 0.00
% 2.76/1.50  Index Matching       : 0.00
% 2.76/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
