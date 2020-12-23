%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:32 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   35 (  38 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 (  57 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    ! [A_16] :
      ( r1_tarski(A_16,k2_zfmisc_1(k1_relat_1(A_16),k2_relat_1(A_16)))
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_78,plain,(
    ! [A_51,B_52,C_53] :
      ( r2_hidden(k4_tarski('#skF_2'(A_51,B_52,C_53),A_51),C_53)
      | ~ r2_hidden(A_51,k9_relat_1(C_53,B_52))
      | ~ v1_relat_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_185,plain,(
    ! [A_80,B_81,C_82,B_83] :
      ( r2_hidden(k4_tarski('#skF_2'(A_80,B_81,C_82),A_80),B_83)
      | ~ r1_tarski(C_82,B_83)
      | ~ r2_hidden(A_80,k9_relat_1(C_82,B_81))
      | ~ v1_relat_1(C_82) ) ),
    inference(resolution,[status(thm)],[c_78,c_2])).

tff(c_10,plain,(
    ! [B_7,D_9,A_6,C_8] :
      ( r2_hidden(B_7,D_9)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_207,plain,(
    ! [C_86,B_85,D_87,A_84,C_88] :
      ( r2_hidden(A_84,D_87)
      | ~ r1_tarski(C_86,k2_zfmisc_1(C_88,D_87))
      | ~ r2_hidden(A_84,k9_relat_1(C_86,B_85))
      | ~ v1_relat_1(C_86) ) ),
    inference(resolution,[status(thm)],[c_185,c_10])).

tff(c_218,plain,(
    ! [A_89,A_90,B_91] :
      ( r2_hidden(A_89,k2_relat_1(A_90))
      | ~ r2_hidden(A_89,k9_relat_1(A_90,B_91))
      | ~ v1_relat_1(A_90) ) ),
    inference(resolution,[status(thm)],[c_22,c_207])).

tff(c_271,plain,(
    ! [A_96,B_97,B_98] :
      ( r2_hidden('#skF_1'(k9_relat_1(A_96,B_97),B_98),k2_relat_1(A_96))
      | ~ v1_relat_1(A_96)
      | r1_tarski(k9_relat_1(A_96,B_97),B_98) ) ),
    inference(resolution,[status(thm)],[c_6,c_218])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_283,plain,(
    ! [A_99,B_100] :
      ( ~ v1_relat_1(A_99)
      | r1_tarski(k9_relat_1(A_99,B_100),k2_relat_1(A_99)) ) ),
    inference(resolution,[status(thm)],[c_271,c_4])).

tff(c_24,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_288,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_283,c_24])).

tff(c_293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_288])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:41:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.28  
% 2.18/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.28  %$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 2.18/1.28  
% 2.18/1.28  %Foreground sorts:
% 2.18/1.28  
% 2.18/1.28  
% 2.18/1.28  %Background operators:
% 2.18/1.28  
% 2.18/1.28  
% 2.18/1.28  %Foreground operators:
% 2.18/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.18/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.18/1.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.18/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.18/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.18/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.18/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.18/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.18/1.28  
% 2.18/1.29  tff(f_58, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 2.18/1.29  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.18/1.29  tff(f_53, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 2.18/1.29  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.18/1.29  tff(f_38, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.18/1.29  tff(c_26, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.18/1.29  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.18/1.29  tff(c_22, plain, (![A_16]: (r1_tarski(A_16, k2_zfmisc_1(k1_relat_1(A_16), k2_relat_1(A_16))) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.18/1.29  tff(c_78, plain, (![A_51, B_52, C_53]: (r2_hidden(k4_tarski('#skF_2'(A_51, B_52, C_53), A_51), C_53) | ~r2_hidden(A_51, k9_relat_1(C_53, B_52)) | ~v1_relat_1(C_53))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.18/1.29  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.18/1.29  tff(c_185, plain, (![A_80, B_81, C_82, B_83]: (r2_hidden(k4_tarski('#skF_2'(A_80, B_81, C_82), A_80), B_83) | ~r1_tarski(C_82, B_83) | ~r2_hidden(A_80, k9_relat_1(C_82, B_81)) | ~v1_relat_1(C_82))), inference(resolution, [status(thm)], [c_78, c_2])).
% 2.18/1.29  tff(c_10, plain, (![B_7, D_9, A_6, C_8]: (r2_hidden(B_7, D_9) | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.18/1.29  tff(c_207, plain, (![C_86, B_85, D_87, A_84, C_88]: (r2_hidden(A_84, D_87) | ~r1_tarski(C_86, k2_zfmisc_1(C_88, D_87)) | ~r2_hidden(A_84, k9_relat_1(C_86, B_85)) | ~v1_relat_1(C_86))), inference(resolution, [status(thm)], [c_185, c_10])).
% 2.18/1.29  tff(c_218, plain, (![A_89, A_90, B_91]: (r2_hidden(A_89, k2_relat_1(A_90)) | ~r2_hidden(A_89, k9_relat_1(A_90, B_91)) | ~v1_relat_1(A_90))), inference(resolution, [status(thm)], [c_22, c_207])).
% 2.18/1.29  tff(c_271, plain, (![A_96, B_97, B_98]: (r2_hidden('#skF_1'(k9_relat_1(A_96, B_97), B_98), k2_relat_1(A_96)) | ~v1_relat_1(A_96) | r1_tarski(k9_relat_1(A_96, B_97), B_98))), inference(resolution, [status(thm)], [c_6, c_218])).
% 2.18/1.29  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.18/1.29  tff(c_283, plain, (![A_99, B_100]: (~v1_relat_1(A_99) | r1_tarski(k9_relat_1(A_99, B_100), k2_relat_1(A_99)))), inference(resolution, [status(thm)], [c_271, c_4])).
% 2.18/1.29  tff(c_24, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.18/1.29  tff(c_288, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_283, c_24])).
% 2.18/1.29  tff(c_293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_288])).
% 2.18/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.29  
% 2.18/1.29  Inference rules
% 2.18/1.29  ----------------------
% 2.18/1.29  #Ref     : 0
% 2.18/1.29  #Sup     : 61
% 2.18/1.29  #Fact    : 0
% 2.18/1.29  #Define  : 0
% 2.18/1.29  #Split   : 0
% 2.18/1.29  #Chain   : 0
% 2.18/1.29  #Close   : 0
% 2.18/1.29  
% 2.18/1.29  Ordering : KBO
% 2.18/1.29  
% 2.18/1.29  Simplification rules
% 2.18/1.29  ----------------------
% 2.18/1.29  #Subsume      : 3
% 2.18/1.29  #Demod        : 1
% 2.18/1.29  #Tautology    : 3
% 2.18/1.29  #SimpNegUnit  : 0
% 2.18/1.29  #BackRed      : 0
% 2.18/1.29  
% 2.18/1.29  #Partial instantiations: 0
% 2.18/1.29  #Strategies tried      : 1
% 2.18/1.29  
% 2.18/1.29  Timing (in seconds)
% 2.18/1.29  ----------------------
% 2.18/1.30  Preprocessing        : 0.26
% 2.18/1.30  Parsing              : 0.14
% 2.18/1.30  CNF conversion       : 0.02
% 2.18/1.30  Main loop            : 0.24
% 2.18/1.30  Inferencing          : 0.10
% 2.18/1.30  Reduction            : 0.05
% 2.18/1.30  Demodulation         : 0.04
% 2.18/1.30  BG Simplification    : 0.01
% 2.18/1.30  Subsumption          : 0.06
% 2.18/1.30  Abstraction          : 0.01
% 2.18/1.30  MUC search           : 0.00
% 2.18/1.30  Cooper               : 0.00
% 2.18/1.30  Total                : 0.53
% 2.18/1.30  Index Insertion      : 0.00
% 2.18/1.30  Index Deletion       : 0.00
% 2.18/1.30  Index Matching       : 0.00
% 2.18/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
