%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:38 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   48 (  53 expanded)
%              Number of leaves         :   28 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  63 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_setfam_1(B,k1_tarski(A))
       => ! [C] :
            ( r2_hidden(C,B)
           => r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_setfam_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_47,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( r1_setfam_1(A,B)
        & r1_setfam_1(B,C) )
     => r1_setfam_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_setfam_1)).

tff(f_45,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).

tff(c_34,plain,(
    ~ r1_tarski('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_36,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_97,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_1'(A_64,B_65),A_64)
      | r1_setfam_1(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [A_32] : k3_tarski(k1_zfmisc_1(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_66,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,k3_tarski(B_55))
      | ~ r2_hidden(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_72,plain,(
    ! [A_54,A_32] :
      ( r1_tarski(A_54,A_32)
      | ~ r2_hidden(A_54,k1_zfmisc_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_66])).

tff(c_106,plain,(
    ! [A_32,B_65] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_32),B_65),A_32)
      | r1_setfam_1(k1_zfmisc_1(A_32),B_65) ) ),
    inference(resolution,[status(thm)],[c_97,c_72])).

tff(c_188,plain,(
    ! [A_101,B_102,D_103] :
      ( ~ r1_tarski('#skF_1'(A_101,B_102),D_103)
      | ~ r2_hidden(D_103,B_102)
      | r1_setfam_1(A_101,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_212,plain,(
    ! [A_104,B_105] :
      ( ~ r2_hidden(A_104,B_105)
      | r1_setfam_1(k1_zfmisc_1(A_104),B_105) ) ),
    inference(resolution,[status(thm)],[c_106,c_188])).

tff(c_38,plain,(
    r1_setfam_1('#skF_4',k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_129,plain,(
    ! [A_72,C_73,B_74] :
      ( r1_setfam_1(A_72,C_73)
      | ~ r1_setfam_1(B_74,C_73)
      | ~ r1_setfam_1(A_72,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_132,plain,(
    ! [A_72] :
      ( r1_setfam_1(A_72,k1_tarski('#skF_3'))
      | ~ r1_setfam_1(A_72,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_129])).

tff(c_18,plain,(
    ! [A_31] : k3_tarski(k1_tarski(A_31)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_83,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(k3_tarski(A_60),k3_tarski(B_61))
      | ~ r1_setfam_1(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_137,plain,(
    ! [A_76,B_77] :
      ( r1_tarski(A_76,k3_tarski(B_77))
      | ~ r1_setfam_1(k1_zfmisc_1(A_76),B_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_83])).

tff(c_152,plain,(
    ! [A_83,A_84] :
      ( r1_tarski(A_83,A_84)
      | ~ r1_setfam_1(k1_zfmisc_1(A_83),k1_tarski(A_84)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_137])).

tff(c_157,plain,(
    ! [A_83] :
      ( r1_tarski(A_83,'#skF_3')
      | ~ r1_setfam_1(k1_zfmisc_1(A_83),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_132,c_152])).

tff(c_240,plain,(
    ! [A_109] :
      ( r1_tarski(A_109,'#skF_3')
      | ~ r2_hidden(A_109,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_212,c_157])).

tff(c_247,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_240])).

tff(c_252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:26:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.32  
% 2.12/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.32  %$ r2_hidden > r1_tarski > r1_setfam_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 2.12/1.32  
% 2.12/1.32  %Foreground sorts:
% 2.12/1.32  
% 2.12/1.32  
% 2.12/1.32  %Background operators:
% 2.12/1.32  
% 2.12/1.32  
% 2.12/1.32  %Foreground operators:
% 2.12/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.32  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.12/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.12/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.12/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.12/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.12/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.12/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.12/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.12/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.12/1.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.12/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.12/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.12/1.32  
% 2.42/1.33  tff(f_77, negated_conjecture, ~(![A, B]: (r1_setfam_1(B, k1_tarski(A)) => (![C]: (r2_hidden(C, B) => r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_setfam_1)).
% 2.42/1.33  tff(f_59, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.42/1.33  tff(f_47, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.42/1.33  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.42/1.33  tff(f_69, axiom, (![A, B, C]: ((r1_setfam_1(A, B) & r1_setfam_1(B, C)) => r1_setfam_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_setfam_1)).
% 2.42/1.33  tff(f_45, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 2.42/1.33  tff(f_63, axiom, (![A, B]: (r1_setfam_1(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_setfam_1)).
% 2.42/1.33  tff(c_34, plain, (~r1_tarski('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.42/1.33  tff(c_36, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.42/1.33  tff(c_97, plain, (![A_64, B_65]: (r2_hidden('#skF_1'(A_64, B_65), A_64) | r1_setfam_1(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.42/1.33  tff(c_20, plain, (![A_32]: (k3_tarski(k1_zfmisc_1(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.42/1.33  tff(c_66, plain, (![A_54, B_55]: (r1_tarski(A_54, k3_tarski(B_55)) | ~r2_hidden(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.42/1.33  tff(c_72, plain, (![A_54, A_32]: (r1_tarski(A_54, A_32) | ~r2_hidden(A_54, k1_zfmisc_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_66])).
% 2.42/1.33  tff(c_106, plain, (![A_32, B_65]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_32), B_65), A_32) | r1_setfam_1(k1_zfmisc_1(A_32), B_65))), inference(resolution, [status(thm)], [c_97, c_72])).
% 2.42/1.33  tff(c_188, plain, (![A_101, B_102, D_103]: (~r1_tarski('#skF_1'(A_101, B_102), D_103) | ~r2_hidden(D_103, B_102) | r1_setfam_1(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.42/1.33  tff(c_212, plain, (![A_104, B_105]: (~r2_hidden(A_104, B_105) | r1_setfam_1(k1_zfmisc_1(A_104), B_105))), inference(resolution, [status(thm)], [c_106, c_188])).
% 2.42/1.33  tff(c_38, plain, (r1_setfam_1('#skF_4', k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.42/1.33  tff(c_129, plain, (![A_72, C_73, B_74]: (r1_setfam_1(A_72, C_73) | ~r1_setfam_1(B_74, C_73) | ~r1_setfam_1(A_72, B_74))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.42/1.33  tff(c_132, plain, (![A_72]: (r1_setfam_1(A_72, k1_tarski('#skF_3')) | ~r1_setfam_1(A_72, '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_129])).
% 2.42/1.33  tff(c_18, plain, (![A_31]: (k3_tarski(k1_tarski(A_31))=A_31)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.42/1.33  tff(c_83, plain, (![A_60, B_61]: (r1_tarski(k3_tarski(A_60), k3_tarski(B_61)) | ~r1_setfam_1(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.42/1.33  tff(c_137, plain, (![A_76, B_77]: (r1_tarski(A_76, k3_tarski(B_77)) | ~r1_setfam_1(k1_zfmisc_1(A_76), B_77))), inference(superposition, [status(thm), theory('equality')], [c_20, c_83])).
% 2.42/1.33  tff(c_152, plain, (![A_83, A_84]: (r1_tarski(A_83, A_84) | ~r1_setfam_1(k1_zfmisc_1(A_83), k1_tarski(A_84)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_137])).
% 2.42/1.33  tff(c_157, plain, (![A_83]: (r1_tarski(A_83, '#skF_3') | ~r1_setfam_1(k1_zfmisc_1(A_83), '#skF_4'))), inference(resolution, [status(thm)], [c_132, c_152])).
% 2.42/1.33  tff(c_240, plain, (![A_109]: (r1_tarski(A_109, '#skF_3') | ~r2_hidden(A_109, '#skF_4'))), inference(resolution, [status(thm)], [c_212, c_157])).
% 2.42/1.33  tff(c_247, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_240])).
% 2.42/1.33  tff(c_252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_247])).
% 2.42/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.33  
% 2.42/1.33  Inference rules
% 2.42/1.33  ----------------------
% 2.42/1.33  #Ref     : 0
% 2.42/1.33  #Sup     : 47
% 2.42/1.33  #Fact    : 0
% 2.42/1.33  #Define  : 0
% 2.42/1.33  #Split   : 0
% 2.42/1.33  #Chain   : 0
% 2.42/1.33  #Close   : 0
% 2.42/1.33  
% 2.42/1.33  Ordering : KBO
% 2.42/1.33  
% 2.42/1.33  Simplification rules
% 2.42/1.33  ----------------------
% 2.42/1.33  #Subsume      : 7
% 2.42/1.33  #Demod        : 1
% 2.42/1.33  #Tautology    : 13
% 2.42/1.33  #SimpNegUnit  : 1
% 2.42/1.33  #BackRed      : 0
% 2.42/1.33  
% 2.42/1.33  #Partial instantiations: 0
% 2.42/1.33  #Strategies tried      : 1
% 2.42/1.33  
% 2.42/1.33  Timing (in seconds)
% 2.42/1.33  ----------------------
% 2.42/1.34  Preprocessing        : 0.36
% 2.42/1.34  Parsing              : 0.16
% 2.42/1.34  CNF conversion       : 0.04
% 2.42/1.34  Main loop            : 0.21
% 2.42/1.34  Inferencing          : 0.09
% 2.42/1.34  Reduction            : 0.06
% 2.42/1.34  Demodulation         : 0.04
% 2.42/1.34  BG Simplification    : 0.02
% 2.42/1.34  Subsumption          : 0.04
% 2.42/1.34  Abstraction          : 0.01
% 2.42/1.34  MUC search           : 0.00
% 2.42/1.34  Cooper               : 0.00
% 2.42/1.34  Total                : 0.61
% 2.42/1.34  Index Insertion      : 0.00
% 2.42/1.34  Index Deletion       : 0.00
% 2.42/1.34  Index Matching       : 0.00
% 2.42/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
