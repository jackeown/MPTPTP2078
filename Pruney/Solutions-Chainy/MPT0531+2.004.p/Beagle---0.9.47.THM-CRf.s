%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:16 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   43 (  77 expanded)
%              Number of leaves         :   22 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :   64 ( 160 expanded)
%              Number of equality atoms :    3 (   8 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > #nlpp > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( C = k8_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(E,A)
                  & r2_hidden(k4_tarski(D,E),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    ! [A_36,B_37] :
      ( v1_relat_1(k8_relat_1(A_36,B_37))
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_28,plain,(
    ! [A_38,B_39,C_40] :
      ( k8_relat_1(A_38,k8_relat_1(B_39,C_40)) = k8_relat_1(A_38,C_40)
      | ~ r1_tarski(A_38,B_39)
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    ! [A_19,B_29] :
      ( r2_hidden(k4_tarski('#skF_5'(A_19,B_29),'#skF_6'(A_19,B_29)),A_19)
      | r1_tarski(A_19,B_29)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_89,plain,(
    ! [D_62,E_63,B_64,A_65] :
      ( r2_hidden(k4_tarski(D_62,E_63),B_64)
      | ~ r2_hidden(k4_tarski(D_62,E_63),k8_relat_1(A_65,B_64))
      | ~ v1_relat_1(k8_relat_1(A_65,B_64))
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_325,plain,(
    ! [A_101,B_102,B_103] :
      ( r2_hidden(k4_tarski('#skF_5'(k8_relat_1(A_101,B_102),B_103),'#skF_6'(k8_relat_1(A_101,B_102),B_103)),B_102)
      | ~ v1_relat_1(B_102)
      | r1_tarski(k8_relat_1(A_101,B_102),B_103)
      | ~ v1_relat_1(k8_relat_1(A_101,B_102)) ) ),
    inference(resolution,[status(thm)],[c_24,c_89])).

tff(c_22,plain,(
    ! [A_19,B_29] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(A_19,B_29),'#skF_6'(A_19,B_29)),B_29)
      | r1_tarski(A_19,B_29)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_362,plain,(
    ! [B_104,A_105] :
      ( ~ v1_relat_1(B_104)
      | r1_tarski(k8_relat_1(A_105,B_104),B_104)
      | ~ v1_relat_1(k8_relat_1(A_105,B_104)) ) ),
    inference(resolution,[status(thm)],[c_325,c_22])).

tff(c_490,plain,(
    ! [B_109,C_110,A_111] :
      ( ~ v1_relat_1(k8_relat_1(B_109,C_110))
      | r1_tarski(k8_relat_1(A_111,C_110),k8_relat_1(B_109,C_110))
      | ~ v1_relat_1(k8_relat_1(A_111,k8_relat_1(B_109,C_110)))
      | ~ r1_tarski(A_111,B_109)
      | ~ v1_relat_1(C_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_362])).

tff(c_30,plain,(
    ~ r1_tarski(k8_relat_1('#skF_7','#skF_9'),k8_relat_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_499,plain,
    ( ~ v1_relat_1(k8_relat_1('#skF_8','#skF_9'))
    | ~ v1_relat_1(k8_relat_1('#skF_7',k8_relat_1('#skF_8','#skF_9')))
    | ~ r1_tarski('#skF_7','#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_490,c_30])).

tff(c_529,plain,
    ( ~ v1_relat_1(k8_relat_1('#skF_8','#skF_9'))
    | ~ v1_relat_1(k8_relat_1('#skF_7',k8_relat_1('#skF_8','#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_499])).

tff(c_530,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_7',k8_relat_1('#skF_8','#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_529])).

tff(c_539,plain,
    ( ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9'))
    | ~ r1_tarski('#skF_7','#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_530])).

tff(c_549,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_539])).

tff(c_553,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_549])).

tff(c_557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_553])).

tff(c_558,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_529])).

tff(c_562,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_558])).

tff(c_566,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_562])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:13:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.48  
% 3.00/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.48  %$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > #nlpp > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5
% 3.00/1.48  
% 3.00/1.48  %Foreground sorts:
% 3.00/1.48  
% 3.00/1.48  
% 3.00/1.48  %Background operators:
% 3.00/1.48  
% 3.00/1.48  
% 3.00/1.48  %Foreground operators:
% 3.00/1.48  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.00/1.48  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.00/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.00/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.00/1.48  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.00/1.48  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.00/1.48  tff('#skF_7', type, '#skF_7': $i).
% 3.00/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.00/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.00/1.48  tff('#skF_9', type, '#skF_9': $i).
% 3.00/1.48  tff('#skF_8', type, '#skF_8': $i).
% 3.00/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.00/1.48  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.00/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.48  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.00/1.48  
% 3.00/1.50  tff(f_66, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_relat_1)).
% 3.00/1.50  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 3.00/1.50  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_relat_1)).
% 3.00/1.50  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 3.00/1.50  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k8_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(E, A) & r2_hidden(k4_tarski(D, E), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_relat_1)).
% 3.00/1.50  tff(c_34, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.00/1.50  tff(c_26, plain, (![A_36, B_37]: (v1_relat_1(k8_relat_1(A_36, B_37)) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.00/1.50  tff(c_32, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.00/1.50  tff(c_28, plain, (![A_38, B_39, C_40]: (k8_relat_1(A_38, k8_relat_1(B_39, C_40))=k8_relat_1(A_38, C_40) | ~r1_tarski(A_38, B_39) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.00/1.50  tff(c_24, plain, (![A_19, B_29]: (r2_hidden(k4_tarski('#skF_5'(A_19, B_29), '#skF_6'(A_19, B_29)), A_19) | r1_tarski(A_19, B_29) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.00/1.50  tff(c_89, plain, (![D_62, E_63, B_64, A_65]: (r2_hidden(k4_tarski(D_62, E_63), B_64) | ~r2_hidden(k4_tarski(D_62, E_63), k8_relat_1(A_65, B_64)) | ~v1_relat_1(k8_relat_1(A_65, B_64)) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.00/1.50  tff(c_325, plain, (![A_101, B_102, B_103]: (r2_hidden(k4_tarski('#skF_5'(k8_relat_1(A_101, B_102), B_103), '#skF_6'(k8_relat_1(A_101, B_102), B_103)), B_102) | ~v1_relat_1(B_102) | r1_tarski(k8_relat_1(A_101, B_102), B_103) | ~v1_relat_1(k8_relat_1(A_101, B_102)))), inference(resolution, [status(thm)], [c_24, c_89])).
% 3.00/1.50  tff(c_22, plain, (![A_19, B_29]: (~r2_hidden(k4_tarski('#skF_5'(A_19, B_29), '#skF_6'(A_19, B_29)), B_29) | r1_tarski(A_19, B_29) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.00/1.50  tff(c_362, plain, (![B_104, A_105]: (~v1_relat_1(B_104) | r1_tarski(k8_relat_1(A_105, B_104), B_104) | ~v1_relat_1(k8_relat_1(A_105, B_104)))), inference(resolution, [status(thm)], [c_325, c_22])).
% 3.00/1.50  tff(c_490, plain, (![B_109, C_110, A_111]: (~v1_relat_1(k8_relat_1(B_109, C_110)) | r1_tarski(k8_relat_1(A_111, C_110), k8_relat_1(B_109, C_110)) | ~v1_relat_1(k8_relat_1(A_111, k8_relat_1(B_109, C_110))) | ~r1_tarski(A_111, B_109) | ~v1_relat_1(C_110))), inference(superposition, [status(thm), theory('equality')], [c_28, c_362])).
% 3.00/1.50  tff(c_30, plain, (~r1_tarski(k8_relat_1('#skF_7', '#skF_9'), k8_relat_1('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.00/1.50  tff(c_499, plain, (~v1_relat_1(k8_relat_1('#skF_8', '#skF_9')) | ~v1_relat_1(k8_relat_1('#skF_7', k8_relat_1('#skF_8', '#skF_9'))) | ~r1_tarski('#skF_7', '#skF_8') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_490, c_30])).
% 3.00/1.50  tff(c_529, plain, (~v1_relat_1(k8_relat_1('#skF_8', '#skF_9')) | ~v1_relat_1(k8_relat_1('#skF_7', k8_relat_1('#skF_8', '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_499])).
% 3.00/1.50  tff(c_530, plain, (~v1_relat_1(k8_relat_1('#skF_7', k8_relat_1('#skF_8', '#skF_9')))), inference(splitLeft, [status(thm)], [c_529])).
% 3.00/1.50  tff(c_539, plain, (~v1_relat_1(k8_relat_1('#skF_7', '#skF_9')) | ~r1_tarski('#skF_7', '#skF_8') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_28, c_530])).
% 3.00/1.50  tff(c_549, plain, (~v1_relat_1(k8_relat_1('#skF_7', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_539])).
% 3.00/1.50  tff(c_553, plain, (~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_26, c_549])).
% 3.00/1.50  tff(c_557, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_553])).
% 3.00/1.50  tff(c_558, plain, (~v1_relat_1(k8_relat_1('#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_529])).
% 3.00/1.50  tff(c_562, plain, (~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_26, c_558])).
% 3.00/1.50  tff(c_566, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_562])).
% 3.00/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.50  
% 3.00/1.50  Inference rules
% 3.00/1.50  ----------------------
% 3.00/1.50  #Ref     : 0
% 3.00/1.50  #Sup     : 137
% 3.00/1.50  #Fact    : 0
% 3.00/1.50  #Define  : 0
% 3.00/1.50  #Split   : 2
% 3.00/1.50  #Chain   : 0
% 3.00/1.50  #Close   : 0
% 3.00/1.50  
% 3.00/1.50  Ordering : KBO
% 3.00/1.50  
% 3.00/1.50  Simplification rules
% 3.00/1.50  ----------------------
% 3.00/1.50  #Subsume      : 16
% 3.00/1.50  #Demod        : 12
% 3.00/1.50  #Tautology    : 16
% 3.00/1.50  #SimpNegUnit  : 0
% 3.00/1.50  #BackRed      : 0
% 3.00/1.50  
% 3.00/1.50  #Partial instantiations: 0
% 3.00/1.50  #Strategies tried      : 1
% 3.00/1.50  
% 3.00/1.50  Timing (in seconds)
% 3.00/1.50  ----------------------
% 3.13/1.50  Preprocessing        : 0.30
% 3.13/1.50  Parsing              : 0.16
% 3.13/1.50  CNF conversion       : 0.03
% 3.13/1.50  Main loop            : 0.43
% 3.13/1.50  Inferencing          : 0.16
% 3.13/1.50  Reduction            : 0.10
% 3.13/1.50  Demodulation         : 0.07
% 3.13/1.50  BG Simplification    : 0.02
% 3.13/1.50  Subsumption          : 0.12
% 3.13/1.50  Abstraction          : 0.02
% 3.13/1.50  MUC search           : 0.00
% 3.13/1.50  Cooper               : 0.00
% 3.13/1.50  Total                : 0.75
% 3.13/1.50  Index Insertion      : 0.00
% 3.13/1.50  Index Deletion       : 0.00
% 3.13/1.50  Index Matching       : 0.00
% 3.13/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
