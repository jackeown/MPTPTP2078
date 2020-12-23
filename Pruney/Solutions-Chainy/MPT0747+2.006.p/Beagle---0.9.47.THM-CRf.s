%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:23 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   45 (  71 expanded)
%              Number of leaves         :   20 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   64 ( 121 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > k3_tarski > k1_ordinal1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_66,axiom,(
    ! [A] :
      ( ! [B] :
          ( r2_hidden(B,A)
         => v3_ordinal1(B) )
     => v3_ordinal1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_ordinal1)).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ~ ! [B] :
            ( r2_hidden(B,A)
          <=> v3_ordinal1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_ordinal1)).

tff(f_41,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => r1_ordinal1(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_ordinal1)).

tff(f_59,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
          <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_71,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_119,plain,(
    ! [A_36] :
      ( r2_hidden('#skF_2'(A_36),A_36)
      | v3_ordinal1(k3_tarski(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    ! [B_17] :
      ( v3_ordinal1(B_17)
      | ~ r2_hidden(B_17,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_128,plain,
    ( v3_ordinal1('#skF_2'('#skF_3'))
    | v3_ordinal1(k3_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_119,c_24])).

tff(c_129,plain,(
    v3_ordinal1(k3_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_8,plain,(
    ! [A_6] :
      ( v3_ordinal1(k1_ordinal1(A_6))
      | ~ v3_ordinal1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ! [B_17] :
      ( r2_hidden(B_17,'#skF_3')
      | ~ v3_ordinal1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( r1_tarski(A_2,k3_tarski(B_3))
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r1_ordinal1(A_4,A_4)
      | ~ v3_ordinal1(B_5)
      | ~ v3_ordinal1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_130,plain,(
    ! [B_5] : ~ v3_ordinal1(B_5) ),
    inference(splitLeft,[status(thm)],[c_6])).

tff(c_140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_129])).

tff(c_141,plain,(
    ! [A_4] :
      ( r1_ordinal1(A_4,A_4)
      | ~ v3_ordinal1(A_4) ) ),
    inference(splitRight,[status(thm)],[c_6])).

tff(c_179,plain,(
    ! [A_44,B_45] :
      ( r2_hidden(A_44,B_45)
      | ~ r1_ordinal1(k1_ordinal1(A_44),B_45)
      | ~ v3_ordinal1(B_45)
      | ~ v3_ordinal1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_185,plain,(
    ! [A_46] :
      ( r2_hidden(A_46,k1_ordinal1(A_46))
      | ~ v3_ordinal1(A_46)
      | ~ v3_ordinal1(k1_ordinal1(A_46)) ) ),
    inference(resolution,[status(thm)],[c_141,c_179])).

tff(c_22,plain,(
    ! [B_15,A_14] :
      ( ~ r1_tarski(B_15,A_14)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_190,plain,(
    ! [A_47] :
      ( ~ r1_tarski(k1_ordinal1(A_47),A_47)
      | ~ v3_ordinal1(A_47)
      | ~ v3_ordinal1(k1_ordinal1(A_47)) ) ),
    inference(resolution,[status(thm)],[c_185,c_22])).

tff(c_208,plain,(
    ! [B_51] :
      ( ~ v3_ordinal1(k3_tarski(B_51))
      | ~ v3_ordinal1(k1_ordinal1(k3_tarski(B_51)))
      | ~ r2_hidden(k1_ordinal1(k3_tarski(B_51)),B_51) ) ),
    inference(resolution,[status(thm)],[c_4,c_190])).

tff(c_212,plain,
    ( ~ v3_ordinal1(k3_tarski('#skF_3'))
    | ~ v3_ordinal1(k1_ordinal1(k3_tarski('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_26,c_208])).

tff(c_215,plain,(
    ~ v3_ordinal1(k1_ordinal1(k3_tarski('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_212])).

tff(c_218,plain,(
    ~ v3_ordinal1(k3_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_215])).

tff(c_222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_218])).

tff(c_223,plain,(
    v3_ordinal1('#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_18,plain,(
    ! [A_12] :
      ( ~ v3_ordinal1('#skF_2'(A_12))
      | v3_ordinal1(k3_tarski(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_224,plain,(
    ~ v3_ordinal1(k3_tarski('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_227,plain,(
    ~ v3_ordinal1('#skF_2'('#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_224])).

tff(c_231,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_227])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:02:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.28  
% 2.16/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.28  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > k3_tarski > k1_ordinal1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3
% 2.16/1.28  
% 2.16/1.28  %Foreground sorts:
% 2.16/1.28  
% 2.16/1.28  
% 2.16/1.28  %Background operators:
% 2.16/1.28  
% 2.16/1.28  
% 2.16/1.28  %Foreground operators:
% 2.16/1.28  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.16/1.28  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.16/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.16/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.28  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 2.16/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.28  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.16/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.16/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.28  
% 2.16/1.29  tff(f_66, axiom, (![A]: ((![B]: (r2_hidden(B, A) => v3_ordinal1(B))) => v3_ordinal1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_ordinal1)).
% 2.16/1.29  tff(f_78, negated_conjecture, ~(![A]: ~(![B]: (r2_hidden(B, A) <=> v3_ordinal1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_ordinal1)).
% 2.16/1.29  tff(f_41, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 2.16/1.29  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.16/1.29  tff(f_37, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => r1_ordinal1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r1_ordinal1)).
% 2.16/1.29  tff(f_59, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 2.16/1.29  tff(f_71, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.16/1.29  tff(c_119, plain, (![A_36]: (r2_hidden('#skF_2'(A_36), A_36) | v3_ordinal1(k3_tarski(A_36)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.16/1.29  tff(c_24, plain, (![B_17]: (v3_ordinal1(B_17) | ~r2_hidden(B_17, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.16/1.29  tff(c_128, plain, (v3_ordinal1('#skF_2'('#skF_3')) | v3_ordinal1(k3_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_119, c_24])).
% 2.16/1.29  tff(c_129, plain, (v3_ordinal1(k3_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_128])).
% 2.16/1.29  tff(c_8, plain, (![A_6]: (v3_ordinal1(k1_ordinal1(A_6)) | ~v3_ordinal1(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.16/1.29  tff(c_26, plain, (![B_17]: (r2_hidden(B_17, '#skF_3') | ~v3_ordinal1(B_17))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.16/1.29  tff(c_4, plain, (![A_2, B_3]: (r1_tarski(A_2, k3_tarski(B_3)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.29  tff(c_6, plain, (![A_4, B_5]: (r1_ordinal1(A_4, A_4) | ~v3_ordinal1(B_5) | ~v3_ordinal1(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.16/1.29  tff(c_130, plain, (![B_5]: (~v3_ordinal1(B_5))), inference(splitLeft, [status(thm)], [c_6])).
% 2.16/1.29  tff(c_140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_129])).
% 2.16/1.29  tff(c_141, plain, (![A_4]: (r1_ordinal1(A_4, A_4) | ~v3_ordinal1(A_4))), inference(splitRight, [status(thm)], [c_6])).
% 2.16/1.29  tff(c_179, plain, (![A_44, B_45]: (r2_hidden(A_44, B_45) | ~r1_ordinal1(k1_ordinal1(A_44), B_45) | ~v3_ordinal1(B_45) | ~v3_ordinal1(A_44))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.16/1.29  tff(c_185, plain, (![A_46]: (r2_hidden(A_46, k1_ordinal1(A_46)) | ~v3_ordinal1(A_46) | ~v3_ordinal1(k1_ordinal1(A_46)))), inference(resolution, [status(thm)], [c_141, c_179])).
% 2.16/1.29  tff(c_22, plain, (![B_15, A_14]: (~r1_tarski(B_15, A_14) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.16/1.29  tff(c_190, plain, (![A_47]: (~r1_tarski(k1_ordinal1(A_47), A_47) | ~v3_ordinal1(A_47) | ~v3_ordinal1(k1_ordinal1(A_47)))), inference(resolution, [status(thm)], [c_185, c_22])).
% 2.16/1.29  tff(c_208, plain, (![B_51]: (~v3_ordinal1(k3_tarski(B_51)) | ~v3_ordinal1(k1_ordinal1(k3_tarski(B_51))) | ~r2_hidden(k1_ordinal1(k3_tarski(B_51)), B_51))), inference(resolution, [status(thm)], [c_4, c_190])).
% 2.16/1.29  tff(c_212, plain, (~v3_ordinal1(k3_tarski('#skF_3')) | ~v3_ordinal1(k1_ordinal1(k3_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_26, c_208])).
% 2.16/1.29  tff(c_215, plain, (~v3_ordinal1(k1_ordinal1(k3_tarski('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_212])).
% 2.16/1.29  tff(c_218, plain, (~v3_ordinal1(k3_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_215])).
% 2.16/1.29  tff(c_222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_129, c_218])).
% 2.16/1.29  tff(c_223, plain, (v3_ordinal1('#skF_2'('#skF_3'))), inference(splitRight, [status(thm)], [c_128])).
% 2.16/1.29  tff(c_18, plain, (![A_12]: (~v3_ordinal1('#skF_2'(A_12)) | v3_ordinal1(k3_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.16/1.29  tff(c_224, plain, (~v3_ordinal1(k3_tarski('#skF_3'))), inference(splitRight, [status(thm)], [c_128])).
% 2.16/1.29  tff(c_227, plain, (~v3_ordinal1('#skF_2'('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_224])).
% 2.16/1.29  tff(c_231, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_223, c_227])).
% 2.16/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.29  
% 2.16/1.29  Inference rules
% 2.16/1.29  ----------------------
% 2.16/1.29  #Ref     : 0
% 2.16/1.29  #Sup     : 32
% 2.16/1.29  #Fact    : 0
% 2.16/1.29  #Define  : 0
% 2.16/1.29  #Split   : 4
% 2.16/1.29  #Chain   : 0
% 2.16/1.29  #Close   : 0
% 2.16/1.29  
% 2.16/1.29  Ordering : KBO
% 2.16/1.29  
% 2.16/1.29  Simplification rules
% 2.16/1.29  ----------------------
% 2.16/1.29  #Subsume      : 6
% 2.16/1.29  #Demod        : 6
% 2.16/1.29  #Tautology    : 3
% 2.16/1.29  #SimpNegUnit  : 9
% 2.16/1.29  #BackRed      : 7
% 2.16/1.29  
% 2.16/1.29  #Partial instantiations: 0
% 2.16/1.29  #Strategies tried      : 1
% 2.16/1.29  
% 2.16/1.29  Timing (in seconds)
% 2.16/1.29  ----------------------
% 2.16/1.30  Preprocessing        : 0.29
% 2.16/1.30  Parsing              : 0.16
% 2.16/1.30  CNF conversion       : 0.02
% 2.16/1.30  Main loop            : 0.19
% 2.16/1.30  Inferencing          : 0.09
% 2.16/1.30  Reduction            : 0.05
% 2.16/1.30  Demodulation         : 0.03
% 2.16/1.30  BG Simplification    : 0.01
% 2.16/1.30  Subsumption          : 0.03
% 2.16/1.30  Abstraction          : 0.01
% 2.16/1.30  MUC search           : 0.00
% 2.16/1.30  Cooper               : 0.00
% 2.16/1.30  Total                : 0.51
% 2.16/1.30  Index Insertion      : 0.00
% 2.16/1.30  Index Deletion       : 0.00
% 2.16/1.30  Index Matching       : 0.00
% 2.16/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
