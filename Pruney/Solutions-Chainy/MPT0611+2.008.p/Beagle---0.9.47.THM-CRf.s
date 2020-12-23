%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:40 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   40 (  50 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :   12
%              Number of atoms          :   52 (  79 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k2_relat_1(A),k2_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t215_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(c_18,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [A_12] :
      ( r1_tarski(A_12,k2_zfmisc_1(k1_relat_1(A_12),k2_relat_1(A_12)))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    r1_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_25,plain,(
    ! [B_14,A_15] :
      ( r1_xboole_0(B_14,A_15)
      | ~ r1_xboole_0(A_15,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    r1_xboole_0(k2_relat_1('#skF_2'),k2_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_25])).

tff(c_140,plain,(
    ! [C_41,D_42,A_43,B_44] :
      ( ~ r1_xboole_0(C_41,D_42)
      | r1_xboole_0(k2_zfmisc_1(A_43,C_41),k2_zfmisc_1(B_44,D_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = A_6
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_184,plain,(
    ! [A_59,C_60,B_61,D_62] :
      ( k4_xboole_0(k2_zfmisc_1(A_59,C_60),k2_zfmisc_1(B_61,D_62)) = k2_zfmisc_1(A_59,C_60)
      | ~ r1_xboole_0(C_60,D_62) ) ),
    inference(resolution,[status(thm)],[c_140,c_8])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_285,plain,(
    ! [C_85,A_81,D_84,B_82,A_83] :
      ( r1_xboole_0(A_83,k2_zfmisc_1(B_82,D_84))
      | ~ r1_tarski(A_83,k2_zfmisc_1(A_81,C_85))
      | ~ r1_xboole_0(C_85,D_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_4])).

tff(c_289,plain,(
    ! [A_86,B_87,D_88] :
      ( r1_xboole_0(A_86,k2_zfmisc_1(B_87,D_88))
      | ~ r1_xboole_0(k2_relat_1(A_86),D_88)
      | ~ v1_relat_1(A_86) ) ),
    inference(resolution,[status(thm)],[c_16,c_285])).

tff(c_307,plain,(
    ! [B_87] :
      ( r1_xboole_0('#skF_2',k2_zfmisc_1(B_87,k2_relat_1('#skF_1')))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_289])).

tff(c_330,plain,(
    ! [B_89] : r1_xboole_0('#skF_2',k2_zfmisc_1(B_89,k2_relat_1('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_307])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_346,plain,(
    ! [B_91] : r1_xboole_0(k2_zfmisc_1(B_91,k2_relat_1('#skF_1')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_330,c_2])).

tff(c_540,plain,(
    ! [B_126] : k4_xboole_0(k2_zfmisc_1(B_126,k2_relat_1('#skF_1')),'#skF_2') = k2_zfmisc_1(B_126,k2_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_346,c_8])).

tff(c_559,plain,(
    ! [A_127,B_128] :
      ( r1_xboole_0(A_127,'#skF_2')
      | ~ r1_tarski(A_127,k2_zfmisc_1(B_128,k2_relat_1('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_4])).

tff(c_563,plain,
    ( r1_xboole_0('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_559])).

tff(c_566,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_563])).

tff(c_568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_566])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:26:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.35  
% 2.55/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.35  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.55/1.35  
% 2.55/1.35  %Foreground sorts:
% 2.55/1.35  
% 2.55/1.35  
% 2.55/1.35  %Background operators:
% 2.55/1.35  
% 2.55/1.35  
% 2.55/1.35  %Foreground operators:
% 2.55/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.55/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.55/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.55/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.55/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.55/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.55/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.55/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.55/1.35  
% 2.55/1.36  tff(f_59, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k2_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t215_relat_1)).
% 2.55/1.36  tff(f_49, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 2.55/1.36  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.55/1.36  tff(f_45, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 2.55/1.36  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.55/1.36  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.55/1.36  tff(c_18, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.55/1.36  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.55/1.36  tff(c_16, plain, (![A_12]: (r1_tarski(A_12, k2_zfmisc_1(k1_relat_1(A_12), k2_relat_1(A_12))) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.55/1.36  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.55/1.36  tff(c_20, plain, (r1_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.55/1.36  tff(c_25, plain, (![B_14, A_15]: (r1_xboole_0(B_14, A_15) | ~r1_xboole_0(A_15, B_14))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.55/1.36  tff(c_28, plain, (r1_xboole_0(k2_relat_1('#skF_2'), k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_25])).
% 2.55/1.36  tff(c_140, plain, (![C_41, D_42, A_43, B_44]: (~r1_xboole_0(C_41, D_42) | r1_xboole_0(k2_zfmisc_1(A_43, C_41), k2_zfmisc_1(B_44, D_42)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.55/1.36  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=A_6 | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.55/1.36  tff(c_184, plain, (![A_59, C_60, B_61, D_62]: (k4_xboole_0(k2_zfmisc_1(A_59, C_60), k2_zfmisc_1(B_61, D_62))=k2_zfmisc_1(A_59, C_60) | ~r1_xboole_0(C_60, D_62))), inference(resolution, [status(thm)], [c_140, c_8])).
% 2.55/1.36  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_tarski(A_3, k4_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.55/1.36  tff(c_285, plain, (![C_85, A_81, D_84, B_82, A_83]: (r1_xboole_0(A_83, k2_zfmisc_1(B_82, D_84)) | ~r1_tarski(A_83, k2_zfmisc_1(A_81, C_85)) | ~r1_xboole_0(C_85, D_84))), inference(superposition, [status(thm), theory('equality')], [c_184, c_4])).
% 2.55/1.36  tff(c_289, plain, (![A_86, B_87, D_88]: (r1_xboole_0(A_86, k2_zfmisc_1(B_87, D_88)) | ~r1_xboole_0(k2_relat_1(A_86), D_88) | ~v1_relat_1(A_86))), inference(resolution, [status(thm)], [c_16, c_285])).
% 2.55/1.36  tff(c_307, plain, (![B_87]: (r1_xboole_0('#skF_2', k2_zfmisc_1(B_87, k2_relat_1('#skF_1'))) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_289])).
% 2.55/1.36  tff(c_330, plain, (![B_89]: (r1_xboole_0('#skF_2', k2_zfmisc_1(B_89, k2_relat_1('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_307])).
% 2.55/1.36  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.55/1.36  tff(c_346, plain, (![B_91]: (r1_xboole_0(k2_zfmisc_1(B_91, k2_relat_1('#skF_1')), '#skF_2'))), inference(resolution, [status(thm)], [c_330, c_2])).
% 2.55/1.36  tff(c_540, plain, (![B_126]: (k4_xboole_0(k2_zfmisc_1(B_126, k2_relat_1('#skF_1')), '#skF_2')=k2_zfmisc_1(B_126, k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_346, c_8])).
% 2.55/1.36  tff(c_559, plain, (![A_127, B_128]: (r1_xboole_0(A_127, '#skF_2') | ~r1_tarski(A_127, k2_zfmisc_1(B_128, k2_relat_1('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_540, c_4])).
% 2.55/1.36  tff(c_563, plain, (r1_xboole_0('#skF_1', '#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_559])).
% 2.55/1.36  tff(c_566, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_563])).
% 2.55/1.36  tff(c_568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_566])).
% 2.55/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.36  
% 2.55/1.36  Inference rules
% 2.55/1.36  ----------------------
% 2.55/1.36  #Ref     : 0
% 2.55/1.36  #Sup     : 137
% 2.55/1.36  #Fact    : 0
% 2.55/1.36  #Define  : 0
% 2.55/1.36  #Split   : 0
% 2.55/1.36  #Chain   : 0
% 2.55/1.36  #Close   : 0
% 2.55/1.36  
% 2.55/1.36  Ordering : KBO
% 2.55/1.36  
% 2.55/1.36  Simplification rules
% 2.55/1.36  ----------------------
% 2.55/1.36  #Subsume      : 12
% 2.55/1.36  #Demod        : 11
% 2.55/1.36  #Tautology    : 46
% 2.55/1.36  #SimpNegUnit  : 1
% 2.55/1.36  #BackRed      : 0
% 2.55/1.36  
% 2.55/1.36  #Partial instantiations: 0
% 2.55/1.36  #Strategies tried      : 1
% 2.55/1.36  
% 2.55/1.36  Timing (in seconds)
% 2.55/1.36  ----------------------
% 2.55/1.36  Preprocessing        : 0.26
% 2.55/1.36  Parsing              : 0.15
% 2.55/1.36  CNF conversion       : 0.02
% 2.55/1.36  Main loop            : 0.34
% 2.55/1.36  Inferencing          : 0.14
% 2.55/1.36  Reduction            : 0.08
% 2.55/1.36  Demodulation         : 0.05
% 2.55/1.36  BG Simplification    : 0.01
% 2.55/1.36  Subsumption          : 0.08
% 2.55/1.36  Abstraction          : 0.02
% 2.55/1.36  MUC search           : 0.00
% 2.55/1.36  Cooper               : 0.00
% 2.55/1.36  Total                : 0.63
% 2.55/1.36  Index Insertion      : 0.00
% 2.55/1.36  Index Deletion       : 0.00
% 2.55/1.36  Index Matching       : 0.00
% 2.55/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
