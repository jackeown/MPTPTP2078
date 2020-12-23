%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:49 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   45 (  87 expanded)
%              Number of leaves         :   19 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :   74 ( 169 expanded)
%              Number of equality atoms :   10 (  29 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k10_relat_1(B,A),k10_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t179_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k7_relat_1(B_11,A_10),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( k2_relat_1(k7_relat_1(B_4,A_3)) = k9_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k7_relat_1(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,(
    ! [B_21,A_22] :
      ( k1_relat_1(k7_relat_1(B_21,A_22)) = A_22
      | ~ r1_tarski(A_22,k1_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_49,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_42])).

tff(c_53,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_49])).

tff(c_12,plain,(
    ! [B_13,A_12] :
      ( k1_relat_1(k7_relat_1(B_13,A_12)) = A_12
      | ~ r1_tarski(A_12,k1_relat_1(B_13))
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_57,plain,(
    ! [A_12] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_12)) = A_12
      | ~ r1_tarski(A_12,'#skF_1')
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_12])).

tff(c_61,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_57])).

tff(c_64,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_61])).

tff(c_68,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_64])).

tff(c_70,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_6,plain,(
    ! [A_5] :
      ( k10_relat_1(A_5,k2_relat_1(A_5)) = k1_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_83,plain,(
    ! [B_24,A_25,C_26] :
      ( r1_tarski(k10_relat_1(B_24,A_25),k10_relat_1(C_26,A_25))
      | ~ r1_tarski(B_24,C_26)
      | ~ v1_relat_1(C_26)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_193,plain,(
    ! [A_35,C_36] :
      ( r1_tarski(k1_relat_1(A_35),k10_relat_1(C_36,k2_relat_1(A_35)))
      | ~ r1_tarski(A_35,C_36)
      | ~ v1_relat_1(C_36)
      | ~ v1_relat_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_83])).

tff(c_205,plain,(
    ! [C_36] :
      ( r1_tarski('#skF_1',k10_relat_1(C_36,k2_relat_1(k7_relat_1('#skF_2','#skF_1'))))
      | ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),C_36)
      | ~ v1_relat_1(C_36)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_193])).

tff(c_214,plain,(
    ! [C_37] :
      ( r1_tarski('#skF_1',k10_relat_1(C_37,k2_relat_1(k7_relat_1('#skF_2','#skF_1'))))
      | ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),C_37)
      | ~ v1_relat_1(C_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_70,c_205])).

tff(c_217,plain,(
    ! [C_37] :
      ( r1_tarski('#skF_1',k10_relat_1(C_37,k9_relat_1('#skF_2','#skF_1')))
      | ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),C_37)
      | ~ v1_relat_1(C_37)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_214])).

tff(c_247,plain,(
    ! [C_40] :
      ( r1_tarski('#skF_1',k10_relat_1(C_40,k9_relat_1('#skF_2','#skF_1')))
      | ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),C_40)
      | ~ v1_relat_1(C_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_217])).

tff(c_14,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_250,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_247,c_14])).

tff(c_257,plain,(
    ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_250])).

tff(c_262,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_257])).

tff(c_266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_262])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.40  
% 1.95/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.40  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.95/1.40  
% 1.95/1.40  %Foreground sorts:
% 1.95/1.40  
% 1.95/1.40  
% 1.95/1.40  %Background operators:
% 1.95/1.40  
% 1.95/1.40  
% 1.95/1.40  %Foreground operators:
% 1.95/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.40  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.95/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.95/1.40  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.95/1.40  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.40  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.95/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.95/1.40  
% 1.95/1.41  tff(f_63, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 1.95/1.41  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 1.95/1.41  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.95/1.41  tff(f_29, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.95/1.41  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 1.95/1.41  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 1.95/1.41  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k10_relat_1(B, A), k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t179_relat_1)).
% 1.95/1.41  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.95/1.41  tff(c_10, plain, (![B_11, A_10]: (r1_tarski(k7_relat_1(B_11, A_10), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.95/1.41  tff(c_4, plain, (![B_4, A_3]: (k2_relat_1(k7_relat_1(B_4, A_3))=k9_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.95/1.41  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k7_relat_1(A_1, B_2)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.41  tff(c_16, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.95/1.41  tff(c_42, plain, (![B_21, A_22]: (k1_relat_1(k7_relat_1(B_21, A_22))=A_22 | ~r1_tarski(A_22, k1_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.95/1.41  tff(c_49, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_42])).
% 1.95/1.41  tff(c_53, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_49])).
% 1.95/1.41  tff(c_12, plain, (![B_13, A_12]: (k1_relat_1(k7_relat_1(B_13, A_12))=A_12 | ~r1_tarski(A_12, k1_relat_1(B_13)) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.95/1.41  tff(c_57, plain, (![A_12]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_12))=A_12 | ~r1_tarski(A_12, '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_53, c_12])).
% 1.95/1.41  tff(c_61, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_57])).
% 1.95/1.41  tff(c_64, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2, c_61])).
% 1.95/1.41  tff(c_68, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_64])).
% 1.95/1.41  tff(c_70, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_57])).
% 1.95/1.41  tff(c_6, plain, (![A_5]: (k10_relat_1(A_5, k2_relat_1(A_5))=k1_relat_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.95/1.41  tff(c_83, plain, (![B_24, A_25, C_26]: (r1_tarski(k10_relat_1(B_24, A_25), k10_relat_1(C_26, A_25)) | ~r1_tarski(B_24, C_26) | ~v1_relat_1(C_26) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.95/1.41  tff(c_193, plain, (![A_35, C_36]: (r1_tarski(k1_relat_1(A_35), k10_relat_1(C_36, k2_relat_1(A_35))) | ~r1_tarski(A_35, C_36) | ~v1_relat_1(C_36) | ~v1_relat_1(A_35) | ~v1_relat_1(A_35))), inference(superposition, [status(thm), theory('equality')], [c_6, c_83])).
% 1.95/1.41  tff(c_205, plain, (![C_36]: (r1_tarski('#skF_1', k10_relat_1(C_36, k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))) | ~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), C_36) | ~v1_relat_1(C_36) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_53, c_193])).
% 1.95/1.41  tff(c_214, plain, (![C_37]: (r1_tarski('#skF_1', k10_relat_1(C_37, k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))) | ~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), C_37) | ~v1_relat_1(C_37))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_70, c_205])).
% 1.95/1.41  tff(c_217, plain, (![C_37]: (r1_tarski('#skF_1', k10_relat_1(C_37, k9_relat_1('#skF_2', '#skF_1'))) | ~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), C_37) | ~v1_relat_1(C_37) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_214])).
% 1.95/1.41  tff(c_247, plain, (![C_40]: (r1_tarski('#skF_1', k10_relat_1(C_40, k9_relat_1('#skF_2', '#skF_1'))) | ~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), C_40) | ~v1_relat_1(C_40))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_217])).
% 1.95/1.41  tff(c_14, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.95/1.41  tff(c_250, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_247, c_14])).
% 1.95/1.41  tff(c_257, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_250])).
% 1.95/1.41  tff(c_262, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_257])).
% 1.95/1.41  tff(c_266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_262])).
% 1.95/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.41  
% 1.95/1.41  Inference rules
% 1.95/1.41  ----------------------
% 1.95/1.41  #Ref     : 0
% 1.95/1.41  #Sup     : 56
% 1.95/1.41  #Fact    : 0
% 1.95/1.41  #Define  : 0
% 1.95/1.41  #Split   : 3
% 1.95/1.41  #Chain   : 0
% 1.95/1.41  #Close   : 0
% 1.95/1.41  
% 1.95/1.41  Ordering : KBO
% 1.95/1.41  
% 1.95/1.41  Simplification rules
% 1.95/1.41  ----------------------
% 1.95/1.41  #Subsume      : 3
% 1.95/1.41  #Demod        : 37
% 1.95/1.41  #Tautology    : 18
% 1.95/1.41  #SimpNegUnit  : 0
% 1.95/1.41  #BackRed      : 0
% 1.95/1.41  
% 1.95/1.41  #Partial instantiations: 0
% 1.95/1.41  #Strategies tried      : 1
% 1.95/1.41  
% 1.95/1.41  Timing (in seconds)
% 1.95/1.41  ----------------------
% 1.95/1.41  Preprocessing        : 0.27
% 1.95/1.41  Parsing              : 0.15
% 1.95/1.41  CNF conversion       : 0.02
% 1.95/1.41  Main loop            : 0.23
% 1.95/1.41  Inferencing          : 0.09
% 1.95/1.41  Reduction            : 0.06
% 1.95/1.41  Demodulation         : 0.05
% 1.95/1.41  BG Simplification    : 0.01
% 1.95/1.41  Subsumption          : 0.05
% 1.95/1.41  Abstraction          : 0.01
% 1.95/1.41  MUC search           : 0.00
% 1.95/1.41  Cooper               : 0.00
% 1.95/1.41  Total                : 0.53
% 1.95/1.41  Index Insertion      : 0.00
% 1.95/1.42  Index Deletion       : 0.00
% 1.95/1.42  Index Matching       : 0.00
% 1.95/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
