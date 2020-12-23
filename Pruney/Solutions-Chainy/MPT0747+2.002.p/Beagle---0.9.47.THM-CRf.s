%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:23 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   42 (  54 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  78 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v3_ordinal1 > #nlpp > k3_tarski > k1_ordinal1 > #skF_5 > #skF_4 > #skF_3 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_54,axiom,(
    ! [A] :
      ( ! [B] :
          ( r2_hidden(B,A)
         => v3_ordinal1(B) )
     => v3_ordinal1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_ordinal1)).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ~ ! [B] :
            ( r2_hidden(B,A)
          <=> v3_ordinal1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_ordinal1)).

tff(f_47,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_66,plain,(
    ! [A_40] :
      ( r2_hidden('#skF_5'(A_40),A_40)
      | v3_ordinal1(k3_tarski(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_36,plain,(
    ! [B_29] :
      ( v3_ordinal1(B_29)
      | ~ r2_hidden(B_29,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_75,plain,
    ( v3_ordinal1('#skF_5'('#skF_6'))
    | v3_ordinal1(k3_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_66,c_36])).

tff(c_76,plain,(
    v3_ordinal1(k3_tarski('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_28,plain,(
    ! [A_23] :
      ( v3_ordinal1(k1_ordinal1(A_23))
      | ~ v3_ordinal1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_22] : r2_hidden(A_22,k1_ordinal1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38,plain,(
    ! [B_29] :
      ( r2_hidden(B_29,'#skF_6')
      | ~ v3_ordinal1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_85,plain,(
    ! [C_44,A_45,D_46] :
      ( r2_hidden(C_44,k3_tarski(A_45))
      | ~ r2_hidden(D_46,A_45)
      | ~ r2_hidden(C_44,D_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_139,plain,(
    ! [C_53,B_54] :
      ( r2_hidden(C_53,k3_tarski('#skF_6'))
      | ~ r2_hidden(C_53,B_54)
      | ~ v3_ordinal1(B_54) ) ),
    inference(resolution,[status(thm)],[c_38,c_85])).

tff(c_163,plain,(
    ! [A_57] :
      ( r2_hidden(A_57,k3_tarski('#skF_6'))
      | ~ v3_ordinal1(k1_ordinal1(A_57)) ) ),
    inference(resolution,[status(thm)],[c_26,c_139])).

tff(c_34,plain,(
    ! [B_27,A_26] :
      ( ~ r1_tarski(B_27,A_26)
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_207,plain,(
    ! [A_59] :
      ( ~ r1_tarski(k3_tarski('#skF_6'),A_59)
      | ~ v3_ordinal1(k1_ordinal1(A_59)) ) ),
    inference(resolution,[status(thm)],[c_163,c_34])).

tff(c_212,plain,(
    ~ v3_ordinal1(k1_ordinal1(k3_tarski('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_6,c_207])).

tff(c_215,plain,(
    ~ v3_ordinal1(k3_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_28,c_212])).

tff(c_219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_215])).

tff(c_220,plain,(
    v3_ordinal1('#skF_5'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_30,plain,(
    ! [A_24] :
      ( ~ v3_ordinal1('#skF_5'(A_24))
      | v3_ordinal1(k3_tarski(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_221,plain,(
    ~ v3_ordinal1(k3_tarski('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_224,plain,(
    ~ v3_ordinal1('#skF_5'('#skF_6')) ),
    inference(resolution,[status(thm)],[c_30,c_221])).

tff(c_228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_224])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:06:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.25  
% 2.00/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.25  %$ r2_hidden > r1_tarski > v3_ordinal1 > #nlpp > k3_tarski > k1_ordinal1 > #skF_5 > #skF_4 > #skF_3 > #skF_6 > #skF_2 > #skF_1
% 2.00/1.25  
% 2.00/1.25  %Foreground sorts:
% 2.00/1.25  
% 2.00/1.25  
% 2.00/1.25  %Background operators:
% 2.00/1.25  
% 2.00/1.25  
% 2.00/1.25  %Foreground operators:
% 2.00/1.25  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.00/1.25  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.00/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.25  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.00/1.25  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.00/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.00/1.25  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.00/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.00/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.00/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.00/1.25  
% 2.00/1.26  tff(f_54, axiom, (![A]: ((![B]: (r2_hidden(B, A) => v3_ordinal1(B))) => v3_ordinal1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_ordinal1)).
% 2.00/1.26  tff(f_66, negated_conjecture, ~(![A]: ~(![B]: (r2_hidden(B, A) <=> v3_ordinal1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_ordinal1)).
% 2.00/1.26  tff(f_47, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 2.00/1.26  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.00/1.26  tff(f_43, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 2.00/1.26  tff(f_41, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 2.00/1.26  tff(f_59, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.00/1.26  tff(c_66, plain, (![A_40]: (r2_hidden('#skF_5'(A_40), A_40) | v3_ordinal1(k3_tarski(A_40)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.00/1.26  tff(c_36, plain, (![B_29]: (v3_ordinal1(B_29) | ~r2_hidden(B_29, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.00/1.26  tff(c_75, plain, (v3_ordinal1('#skF_5'('#skF_6')) | v3_ordinal1(k3_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_66, c_36])).
% 2.00/1.26  tff(c_76, plain, (v3_ordinal1(k3_tarski('#skF_6'))), inference(splitLeft, [status(thm)], [c_75])).
% 2.00/1.26  tff(c_28, plain, (![A_23]: (v3_ordinal1(k1_ordinal1(A_23)) | ~v3_ordinal1(A_23))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.00/1.26  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.00/1.26  tff(c_26, plain, (![A_22]: (r2_hidden(A_22, k1_ordinal1(A_22)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.00/1.26  tff(c_38, plain, (![B_29]: (r2_hidden(B_29, '#skF_6') | ~v3_ordinal1(B_29))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.00/1.26  tff(c_85, plain, (![C_44, A_45, D_46]: (r2_hidden(C_44, k3_tarski(A_45)) | ~r2_hidden(D_46, A_45) | ~r2_hidden(C_44, D_46))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.00/1.26  tff(c_139, plain, (![C_53, B_54]: (r2_hidden(C_53, k3_tarski('#skF_6')) | ~r2_hidden(C_53, B_54) | ~v3_ordinal1(B_54))), inference(resolution, [status(thm)], [c_38, c_85])).
% 2.00/1.26  tff(c_163, plain, (![A_57]: (r2_hidden(A_57, k3_tarski('#skF_6')) | ~v3_ordinal1(k1_ordinal1(A_57)))), inference(resolution, [status(thm)], [c_26, c_139])).
% 2.00/1.26  tff(c_34, plain, (![B_27, A_26]: (~r1_tarski(B_27, A_26) | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.00/1.26  tff(c_207, plain, (![A_59]: (~r1_tarski(k3_tarski('#skF_6'), A_59) | ~v3_ordinal1(k1_ordinal1(A_59)))), inference(resolution, [status(thm)], [c_163, c_34])).
% 2.00/1.26  tff(c_212, plain, (~v3_ordinal1(k1_ordinal1(k3_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_6, c_207])).
% 2.00/1.26  tff(c_215, plain, (~v3_ordinal1(k3_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_28, c_212])).
% 2.00/1.26  tff(c_219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_215])).
% 2.00/1.26  tff(c_220, plain, (v3_ordinal1('#skF_5'('#skF_6'))), inference(splitRight, [status(thm)], [c_75])).
% 2.00/1.26  tff(c_30, plain, (![A_24]: (~v3_ordinal1('#skF_5'(A_24)) | v3_ordinal1(k3_tarski(A_24)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.00/1.26  tff(c_221, plain, (~v3_ordinal1(k3_tarski('#skF_6'))), inference(splitRight, [status(thm)], [c_75])).
% 2.00/1.26  tff(c_224, plain, (~v3_ordinal1('#skF_5'('#skF_6'))), inference(resolution, [status(thm)], [c_30, c_221])).
% 2.00/1.26  tff(c_228, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_220, c_224])).
% 2.00/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.26  
% 2.00/1.26  Inference rules
% 2.00/1.26  ----------------------
% 2.00/1.26  #Ref     : 0
% 2.00/1.26  #Sup     : 39
% 2.00/1.26  #Fact    : 0
% 2.00/1.26  #Define  : 0
% 2.00/1.26  #Split   : 1
% 2.00/1.26  #Chain   : 0
% 2.00/1.26  #Close   : 0
% 2.00/1.26  
% 2.00/1.26  Ordering : KBO
% 2.00/1.26  
% 2.00/1.26  Simplification rules
% 2.00/1.26  ----------------------
% 2.00/1.26  #Subsume      : 3
% 2.00/1.26  #Demod        : 6
% 2.00/1.26  #Tautology    : 3
% 2.00/1.26  #SimpNegUnit  : 0
% 2.00/1.26  #BackRed      : 0
% 2.00/1.26  
% 2.00/1.26  #Partial instantiations: 0
% 2.00/1.26  #Strategies tried      : 1
% 2.00/1.26  
% 2.00/1.26  Timing (in seconds)
% 2.00/1.26  ----------------------
% 2.00/1.27  Preprocessing        : 0.29
% 2.00/1.27  Parsing              : 0.15
% 2.00/1.27  CNF conversion       : 0.02
% 2.00/1.27  Main loop            : 0.20
% 2.00/1.27  Inferencing          : 0.08
% 2.00/1.27  Reduction            : 0.05
% 2.00/1.27  Demodulation         : 0.04
% 2.00/1.27  BG Simplification    : 0.02
% 2.00/1.27  Subsumption          : 0.04
% 2.00/1.27  Abstraction          : 0.01
% 2.00/1.27  MUC search           : 0.00
% 2.00/1.27  Cooper               : 0.00
% 2.00/1.27  Total                : 0.52
% 2.00/1.27  Index Insertion      : 0.00
% 2.00/1.27  Index Deletion       : 0.00
% 2.00/1.27  Index Matching       : 0.00
% 2.00/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
