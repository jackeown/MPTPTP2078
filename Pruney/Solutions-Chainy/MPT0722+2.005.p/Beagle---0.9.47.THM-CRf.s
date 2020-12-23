%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:54 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   39 (  72 expanded)
%              Number of leaves         :   19 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   78 ( 206 expanded)
%              Number of equality atoms :   11 (  34 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v2_funct_1(A)
              & r1_tarski(B,k1_relat_1(A)) )
           => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_funct_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_relat_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_16,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( k10_relat_1(k2_funct_1(B_5),A_4) = k9_relat_1(B_5,A_4)
      | ~ v2_funct_1(B_5)
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_6] :
      ( k2_relat_1(k2_funct_1(A_6)) = k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_52,plain,(
    ! [B_14,A_15] :
      ( k9_relat_1(B_14,k10_relat_1(B_14,A_15)) = A_15
      | ~ r1_tarski(A_15,k2_relat_1(B_14))
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_55,plain,(
    ! [A_16,A_17] :
      ( k9_relat_1(k2_funct_1(A_16),k10_relat_1(k2_funct_1(A_16),A_17)) = A_17
      | ~ r1_tarski(A_17,k1_relat_1(A_16))
      | ~ v1_funct_1(k2_funct_1(A_16))
      | ~ v1_relat_1(k2_funct_1(A_16))
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_52])).

tff(c_67,plain,(
    ! [B_18,A_19] :
      ( k9_relat_1(k2_funct_1(B_18),k9_relat_1(B_18,A_19)) = A_19
      | ~ r1_tarski(A_19,k1_relat_1(B_18))
      | ~ v1_funct_1(k2_funct_1(B_18))
      | ~ v1_relat_1(k2_funct_1(B_18))
      | ~ v2_funct_1(B_18)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v2_funct_1(B_18)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_55])).

tff(c_14,plain,(
    k9_relat_1(k2_funct_1('#skF_1'),k9_relat_1('#skF_1','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_76,plain,
    ( ~ r1_tarski('#skF_2',k1_relat_1('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_14])).

tff(c_89,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_16,c_76])).

tff(c_91,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_94,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_91])).

tff(c_98,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_94])).

tff(c_99,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_103,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_99])).

tff(c_107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_103])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:05:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.25  
% 1.79/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.25  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.79/1.25  
% 1.79/1.25  %Foreground sorts:
% 1.79/1.25  
% 1.79/1.25  
% 1.79/1.25  %Background operators:
% 1.79/1.25  
% 1.79/1.25  
% 1.79/1.25  %Foreground operators:
% 1.79/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.79/1.25  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.79/1.25  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.79/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.79/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.25  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.79/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.25  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.79/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.79/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.79/1.25  
% 1.79/1.27  tff(f_71, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t177_funct_1)).
% 1.79/1.27  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 1.79/1.27  tff(f_49, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_funct_1)).
% 1.79/1.27  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 1.79/1.27  tff(f_41, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 1.79/1.27  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.79/1.27  tff(c_20, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.79/1.27  tff(c_2, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.79/1.27  tff(c_4, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.79/1.27  tff(c_18, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.79/1.27  tff(c_16, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.79/1.27  tff(c_8, plain, (![B_5, A_4]: (k10_relat_1(k2_funct_1(B_5), A_4)=k9_relat_1(B_5, A_4) | ~v2_funct_1(B_5) | ~v1_funct_1(B_5) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.79/1.27  tff(c_10, plain, (![A_6]: (k2_relat_1(k2_funct_1(A_6))=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.79/1.27  tff(c_52, plain, (![B_14, A_15]: (k9_relat_1(B_14, k10_relat_1(B_14, A_15))=A_15 | ~r1_tarski(A_15, k2_relat_1(B_14)) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.79/1.27  tff(c_55, plain, (![A_16, A_17]: (k9_relat_1(k2_funct_1(A_16), k10_relat_1(k2_funct_1(A_16), A_17))=A_17 | ~r1_tarski(A_17, k1_relat_1(A_16)) | ~v1_funct_1(k2_funct_1(A_16)) | ~v1_relat_1(k2_funct_1(A_16)) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(superposition, [status(thm), theory('equality')], [c_10, c_52])).
% 1.79/1.27  tff(c_67, plain, (![B_18, A_19]: (k9_relat_1(k2_funct_1(B_18), k9_relat_1(B_18, A_19))=A_19 | ~r1_tarski(A_19, k1_relat_1(B_18)) | ~v1_funct_1(k2_funct_1(B_18)) | ~v1_relat_1(k2_funct_1(B_18)) | ~v2_funct_1(B_18) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v2_funct_1(B_18) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18))), inference(superposition, [status(thm), theory('equality')], [c_8, c_55])).
% 1.79/1.27  tff(c_14, plain, (k9_relat_1(k2_funct_1('#skF_1'), k9_relat_1('#skF_1', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.79/1.27  tff(c_76, plain, (~r1_tarski('#skF_2', k1_relat_1('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_67, c_14])).
% 1.79/1.27  tff(c_89, plain, (~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_16, c_76])).
% 1.79/1.27  tff(c_91, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_89])).
% 1.79/1.27  tff(c_94, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4, c_91])).
% 1.79/1.27  tff(c_98, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_94])).
% 1.79/1.27  tff(c_99, plain, (~v1_funct_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_89])).
% 1.79/1.27  tff(c_103, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2, c_99])).
% 1.79/1.27  tff(c_107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_103])).
% 1.79/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.27  
% 1.79/1.27  Inference rules
% 1.79/1.27  ----------------------
% 1.79/1.27  #Ref     : 0
% 1.79/1.27  #Sup     : 18
% 1.79/1.27  #Fact    : 0
% 1.79/1.27  #Define  : 0
% 1.79/1.27  #Split   : 1
% 1.79/1.27  #Chain   : 0
% 1.79/1.27  #Close   : 0
% 1.79/1.27  
% 1.79/1.27  Ordering : KBO
% 1.79/1.27  
% 1.79/1.27  Simplification rules
% 1.79/1.27  ----------------------
% 1.79/1.27  #Subsume      : 0
% 1.79/1.27  #Demod        : 8
% 1.79/1.27  #Tautology    : 10
% 1.79/1.27  #SimpNegUnit  : 0
% 1.79/1.27  #BackRed      : 0
% 1.79/1.27  
% 1.79/1.27  #Partial instantiations: 0
% 1.79/1.27  #Strategies tried      : 1
% 1.79/1.27  
% 1.79/1.27  Timing (in seconds)
% 1.79/1.27  ----------------------
% 1.79/1.27  Preprocessing        : 0.33
% 1.79/1.27  Parsing              : 0.19
% 1.79/1.27  CNF conversion       : 0.02
% 1.79/1.27  Main loop            : 0.17
% 1.79/1.27  Inferencing          : 0.07
% 1.79/1.27  Reduction            : 0.04
% 1.79/1.27  Demodulation         : 0.03
% 1.79/1.27  BG Simplification    : 0.01
% 1.79/1.27  Subsumption          : 0.03
% 1.79/1.27  Abstraction          : 0.01
% 1.79/1.27  MUC search           : 0.00
% 1.79/1.27  Cooper               : 0.00
% 1.79/1.27  Total                : 0.53
% 1.79/1.27  Index Insertion      : 0.00
% 1.79/1.27  Index Deletion       : 0.00
% 1.79/1.27  Index Matching       : 0.00
% 1.79/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
