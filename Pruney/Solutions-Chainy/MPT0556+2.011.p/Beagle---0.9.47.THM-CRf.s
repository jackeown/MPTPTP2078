%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:07 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   41 (  90 expanded)
%              Number of leaves         :   18 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 232 expanded)
%              Number of equality atoms :    2 (  12 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k9_relat_1(C,A),k9_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ! [D] :
          ( v1_relat_1(D)
         => ( ( r1_tarski(C,D)
              & r1_tarski(A,B) )
           => r1_tarski(k7_relat_1(C,A),k7_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k7_relat_1(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4,plain,(
    ! [C_5,A_3,D_7,B_4] :
      ( r1_tarski(k7_relat_1(C_5,A_3),k7_relat_1(D_7,B_4))
      | ~ r1_tarski(A_3,B_4)
      | ~ r1_tarski(C_5,D_7)
      | ~ v1_relat_1(D_7)
      | ~ v1_relat_1(C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(k2_relat_1(A_20),k2_relat_1(B_21))
      | ~ r1_tarski(A_20,B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40,plain,(
    ! [B_26,A_27,B_28] :
      ( r1_tarski(k9_relat_1(B_26,A_27),k2_relat_1(B_28))
      | ~ r1_tarski(k7_relat_1(B_26,A_27),B_28)
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(k7_relat_1(B_26,A_27))
      | ~ v1_relat_1(B_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_32])).

tff(c_48,plain,(
    ! [B_32,A_33,B_34,A_35] :
      ( r1_tarski(k9_relat_1(B_32,A_33),k9_relat_1(B_34,A_35))
      | ~ r1_tarski(k7_relat_1(B_32,A_33),k7_relat_1(B_34,A_35))
      | ~ v1_relat_1(k7_relat_1(B_34,A_35))
      | ~ v1_relat_1(k7_relat_1(B_32,A_33))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(B_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_40])).

tff(c_12,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_51,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_4','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_12])).

tff(c_54,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_4','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_51])).

tff(c_55,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_58,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_55])).

tff(c_62,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_58])).

tff(c_63,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2'))
    | ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_65,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_68,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_65])).

tff(c_72,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_14,c_68])).

tff(c_73,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_77,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_73])).

tff(c_81,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_77])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:15:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.22  
% 1.87/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.22  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.87/1.22  
% 1.87/1.22  %Foreground sorts:
% 1.87/1.22  
% 1.87/1.22  
% 1.87/1.22  %Background operators:
% 1.87/1.22  
% 1.87/1.22  
% 1.87/1.22  %Foreground operators:
% 1.87/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.87/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.87/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.87/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.87/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.87/1.22  
% 1.87/1.23  tff(f_67, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k9_relat_1(C, A), k9_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_relat_1)).
% 1.87/1.23  tff(f_29, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.87/1.23  tff(f_40, axiom, (![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k7_relat_1(C, A), k7_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_relat_1)).
% 1.87/1.23  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.87/1.23  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 1.87/1.23  tff(c_18, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.87/1.23  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k7_relat_1(A_1, B_2)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.87/1.23  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.87/1.23  tff(c_16, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.87/1.23  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.87/1.23  tff(c_4, plain, (![C_5, A_3, D_7, B_4]: (r1_tarski(k7_relat_1(C_5, A_3), k7_relat_1(D_7, B_4)) | ~r1_tarski(A_3, B_4) | ~r1_tarski(C_5, D_7) | ~v1_relat_1(D_7) | ~v1_relat_1(C_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.87/1.23  tff(c_6, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.87/1.23  tff(c_32, plain, (![A_20, B_21]: (r1_tarski(k2_relat_1(A_20), k2_relat_1(B_21)) | ~r1_tarski(A_20, B_21) | ~v1_relat_1(B_21) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.87/1.23  tff(c_40, plain, (![B_26, A_27, B_28]: (r1_tarski(k9_relat_1(B_26, A_27), k2_relat_1(B_28)) | ~r1_tarski(k7_relat_1(B_26, A_27), B_28) | ~v1_relat_1(B_28) | ~v1_relat_1(k7_relat_1(B_26, A_27)) | ~v1_relat_1(B_26))), inference(superposition, [status(thm), theory('equality')], [c_6, c_32])).
% 1.87/1.23  tff(c_48, plain, (![B_32, A_33, B_34, A_35]: (r1_tarski(k9_relat_1(B_32, A_33), k9_relat_1(B_34, A_35)) | ~r1_tarski(k7_relat_1(B_32, A_33), k7_relat_1(B_34, A_35)) | ~v1_relat_1(k7_relat_1(B_34, A_35)) | ~v1_relat_1(k7_relat_1(B_32, A_33)) | ~v1_relat_1(B_32) | ~v1_relat_1(B_34))), inference(superposition, [status(thm), theory('equality')], [c_6, c_40])).
% 1.87/1.23  tff(c_12, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.87/1.23  tff(c_51, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_12])).
% 1.87/1.23  tff(c_54, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_51])).
% 1.87/1.23  tff(c_55, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_54])).
% 1.87/1.23  tff(c_58, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_55])).
% 1.87/1.23  tff(c_62, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_58])).
% 1.87/1.23  tff(c_63, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_2')) | ~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_4', '#skF_2'))), inference(splitRight, [status(thm)], [c_54])).
% 1.87/1.23  tff(c_65, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_4', '#skF_2'))), inference(splitLeft, [status(thm)], [c_63])).
% 1.87/1.23  tff(c_68, plain, (~r1_tarski('#skF_1', '#skF_2') | ~r1_tarski('#skF_3', '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_65])).
% 1.87/1.23  tff(c_72, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_14, c_68])).
% 1.87/1.23  tff(c_73, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(splitRight, [status(thm)], [c_63])).
% 1.87/1.23  tff(c_77, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2, c_73])).
% 1.87/1.23  tff(c_81, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_77])).
% 1.87/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.23  
% 1.87/1.23  Inference rules
% 1.87/1.23  ----------------------
% 1.87/1.23  #Ref     : 0
% 1.87/1.23  #Sup     : 10
% 1.87/1.23  #Fact    : 0
% 1.87/1.23  #Define  : 0
% 1.87/1.23  #Split   : 2
% 1.87/1.23  #Chain   : 0
% 1.87/1.23  #Close   : 0
% 1.87/1.23  
% 1.87/1.23  Ordering : KBO
% 1.87/1.23  
% 1.87/1.23  Simplification rules
% 1.87/1.23  ----------------------
% 1.87/1.23  #Subsume      : 1
% 1.87/1.23  #Demod        : 8
% 1.87/1.23  #Tautology    : 2
% 1.87/1.23  #SimpNegUnit  : 0
% 1.87/1.23  #BackRed      : 0
% 1.87/1.23  
% 1.87/1.23  #Partial instantiations: 0
% 1.87/1.23  #Strategies tried      : 1
% 1.87/1.23  
% 1.87/1.23  Timing (in seconds)
% 1.87/1.23  ----------------------
% 1.87/1.23  Preprocessing        : 0.29
% 1.96/1.23  Parsing              : 0.16
% 1.96/1.23  CNF conversion       : 0.02
% 1.96/1.23  Main loop            : 0.14
% 1.96/1.23  Inferencing          : 0.06
% 1.96/1.23  Reduction            : 0.03
% 1.96/1.23  Demodulation         : 0.03
% 1.96/1.23  BG Simplification    : 0.01
% 1.96/1.23  Subsumption          : 0.02
% 1.96/1.23  Abstraction          : 0.00
% 1.96/1.24  MUC search           : 0.00
% 1.96/1.24  Cooper               : 0.00
% 1.96/1.24  Total                : 0.45
% 1.96/1.24  Index Insertion      : 0.00
% 1.96/1.24  Index Deletion       : 0.00
% 1.96/1.24  Index Matching       : 0.00
% 1.96/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
