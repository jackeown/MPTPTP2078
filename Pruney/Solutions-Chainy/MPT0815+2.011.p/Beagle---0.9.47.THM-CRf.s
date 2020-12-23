%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:54 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   52 (  90 expanded)
%              Number of leaves         :   28 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :   49 ( 108 expanded)
%              Number of equality atoms :   12 (  36 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,D) )
       => m1_subset_1(k1_tarski(k4_tarski(A,C)),k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_relset_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k2_tarski(A,B),k2_tarski(C,D)) = k2_enumset1(k4_tarski(A,C),k4_tarski(A,D),k4_tarski(B,C),k4_tarski(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_30,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_88,plain,(
    ! [A_57,B_58,C_59] :
      ( r1_tarski(k2_tarski(A_57,B_58),C_59)
      | ~ r2_hidden(B_58,C_59)
      | ~ r2_hidden(A_57,C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_97,plain,(
    ! [A_1,C_59] :
      ( r1_tarski(k1_tarski(A_1),C_59)
      | ~ r2_hidden(A_1,C_59)
      | ~ r2_hidden(A_1,C_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_88])).

tff(c_32,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_128,plain,(
    ! [A_77,C_78,D_79,B_80] : k2_enumset1(k4_tarski(A_77,C_78),k4_tarski(A_77,D_79),k4_tarski(B_80,C_78),k4_tarski(B_80,D_79)) = k2_zfmisc_1(k2_tarski(A_77,B_80),k2_tarski(C_78,D_79)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [A_77,D_79,B_80] : k1_enumset1(k4_tarski(A_77,D_79),k4_tarski(B_80,D_79),k4_tarski(B_80,D_79)) = k2_zfmisc_1(k2_tarski(A_77,B_80),k2_tarski(D_79,D_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_6])).

tff(c_147,plain,(
    ! [A_81,D_82,B_83] : k1_enumset1(k4_tarski(A_81,D_82),k4_tarski(B_83,D_82),k4_tarski(B_83,D_82)) = k2_zfmisc_1(k2_tarski(A_81,B_83),k1_tarski(D_82)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_135])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_154,plain,(
    ! [B_83,D_82] : k2_zfmisc_1(k2_tarski(B_83,B_83),k1_tarski(D_82)) = k2_tarski(k4_tarski(B_83,D_82),k4_tarski(B_83,D_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_4])).

tff(c_166,plain,(
    ! [B_84,D_85] : k2_zfmisc_1(k1_tarski(B_84),k1_tarski(D_85)) = k1_tarski(k4_tarski(B_84,D_85)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_154])).

tff(c_14,plain,(
    ! [A_22,C_24,B_23,D_25] :
      ( r1_tarski(k2_zfmisc_1(A_22,C_24),k2_zfmisc_1(B_23,D_25))
      | ~ r1_tarski(C_24,D_25)
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_183,plain,(
    ! [B_86,D_87,B_88,D_89] :
      ( r1_tarski(k1_tarski(k4_tarski(B_86,D_87)),k2_zfmisc_1(B_88,D_89))
      | ~ r1_tarski(k1_tarski(D_87),D_89)
      | ~ r1_tarski(k1_tarski(B_86),B_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_14])).

tff(c_26,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(A_33,k1_zfmisc_1(B_34))
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ~ m1_subset_1(k1_tarski(k4_tarski('#skF_1','#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_69,plain,(
    ~ r1_tarski(k1_tarski(k4_tarski('#skF_1','#skF_3')),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_26,c_28])).

tff(c_193,plain,
    ( ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4')
    | ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_183,c_69])).

tff(c_199,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_193])).

tff(c_202,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_97,c_199])).

tff(c_206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_202])).

tff(c_207,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_193])).

tff(c_211,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_97,c_207])).

tff(c_215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_211])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.24  
% 1.95/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.24  %$ r2_hidden > r1_tarski > m1_subset_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.95/1.24  
% 1.95/1.24  %Foreground sorts:
% 1.95/1.24  
% 1.95/1.24  
% 1.95/1.24  %Background operators:
% 1.95/1.24  
% 1.95/1.24  
% 1.95/1.24  %Foreground operators:
% 1.95/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.24  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.95/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.95/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.95/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.95/1.24  tff('#skF_4', type, '#skF_4': $i).
% 1.95/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.24  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.95/1.24  
% 1.95/1.25  tff(f_62, negated_conjecture, ~(![A, B, C, D]: ((r2_hidden(A, B) & r2_hidden(C, D)) => m1_subset_1(k1_tarski(k4_tarski(A, C)), k1_zfmisc_1(k2_zfmisc_1(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_relset_1)).
% 1.95/1.25  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.95/1.25  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.95/1.25  tff(f_45, axiom, (![A, B, C, D]: (k2_zfmisc_1(k2_tarski(A, B), k2_tarski(C, D)) = k2_enumset1(k4_tarski(A, C), k4_tarski(A, D), k4_tarski(B, C), k4_tarski(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 1.95/1.25  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.95/1.25  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.95/1.25  tff(f_43, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 1.95/1.25  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.95/1.25  tff(c_30, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.95/1.25  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.95/1.25  tff(c_88, plain, (![A_57, B_58, C_59]: (r1_tarski(k2_tarski(A_57, B_58), C_59) | ~r2_hidden(B_58, C_59) | ~r2_hidden(A_57, C_59))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.95/1.25  tff(c_97, plain, (![A_1, C_59]: (r1_tarski(k1_tarski(A_1), C_59) | ~r2_hidden(A_1, C_59) | ~r2_hidden(A_1, C_59))), inference(superposition, [status(thm), theory('equality')], [c_2, c_88])).
% 1.95/1.25  tff(c_32, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.95/1.25  tff(c_128, plain, (![A_77, C_78, D_79, B_80]: (k2_enumset1(k4_tarski(A_77, C_78), k4_tarski(A_77, D_79), k4_tarski(B_80, C_78), k4_tarski(B_80, D_79))=k2_zfmisc_1(k2_tarski(A_77, B_80), k2_tarski(C_78, D_79)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.95/1.25  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.25  tff(c_135, plain, (![A_77, D_79, B_80]: (k1_enumset1(k4_tarski(A_77, D_79), k4_tarski(B_80, D_79), k4_tarski(B_80, D_79))=k2_zfmisc_1(k2_tarski(A_77, B_80), k2_tarski(D_79, D_79)))), inference(superposition, [status(thm), theory('equality')], [c_128, c_6])).
% 1.95/1.25  tff(c_147, plain, (![A_81, D_82, B_83]: (k1_enumset1(k4_tarski(A_81, D_82), k4_tarski(B_83, D_82), k4_tarski(B_83, D_82))=k2_zfmisc_1(k2_tarski(A_81, B_83), k1_tarski(D_82)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_135])).
% 1.95/1.25  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.25  tff(c_154, plain, (![B_83, D_82]: (k2_zfmisc_1(k2_tarski(B_83, B_83), k1_tarski(D_82))=k2_tarski(k4_tarski(B_83, D_82), k4_tarski(B_83, D_82)))), inference(superposition, [status(thm), theory('equality')], [c_147, c_4])).
% 1.95/1.25  tff(c_166, plain, (![B_84, D_85]: (k2_zfmisc_1(k1_tarski(B_84), k1_tarski(D_85))=k1_tarski(k4_tarski(B_84, D_85)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_154])).
% 1.95/1.25  tff(c_14, plain, (![A_22, C_24, B_23, D_25]: (r1_tarski(k2_zfmisc_1(A_22, C_24), k2_zfmisc_1(B_23, D_25)) | ~r1_tarski(C_24, D_25) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.95/1.25  tff(c_183, plain, (![B_86, D_87, B_88, D_89]: (r1_tarski(k1_tarski(k4_tarski(B_86, D_87)), k2_zfmisc_1(B_88, D_89)) | ~r1_tarski(k1_tarski(D_87), D_89) | ~r1_tarski(k1_tarski(B_86), B_88))), inference(superposition, [status(thm), theory('equality')], [c_166, c_14])).
% 1.95/1.25  tff(c_26, plain, (![A_33, B_34]: (m1_subset_1(A_33, k1_zfmisc_1(B_34)) | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.95/1.25  tff(c_28, plain, (~m1_subset_1(k1_tarski(k4_tarski('#skF_1', '#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.95/1.25  tff(c_69, plain, (~r1_tarski(k1_tarski(k4_tarski('#skF_1', '#skF_3')), k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_28])).
% 1.95/1.25  tff(c_193, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_4') | ~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_183, c_69])).
% 1.95/1.25  tff(c_199, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_193])).
% 1.95/1.25  tff(c_202, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_97, c_199])).
% 1.95/1.25  tff(c_206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_202])).
% 1.95/1.25  tff(c_207, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_193])).
% 1.95/1.25  tff(c_211, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_97, c_207])).
% 1.95/1.25  tff(c_215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_211])).
% 1.95/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.25  
% 1.95/1.25  Inference rules
% 1.95/1.25  ----------------------
% 1.95/1.25  #Ref     : 0
% 1.95/1.25  #Sup     : 39
% 1.95/1.25  #Fact    : 0
% 1.95/1.25  #Define  : 0
% 1.95/1.25  #Split   : 1
% 1.95/1.25  #Chain   : 0
% 1.95/1.25  #Close   : 0
% 1.95/1.25  
% 1.95/1.25  Ordering : KBO
% 1.95/1.25  
% 1.95/1.25  Simplification rules
% 1.95/1.25  ----------------------
% 1.95/1.25  #Subsume      : 1
% 1.95/1.25  #Demod        : 10
% 1.95/1.25  #Tautology    : 24
% 1.95/1.25  #SimpNegUnit  : 0
% 1.95/1.25  #BackRed      : 0
% 1.95/1.25  
% 1.95/1.25  #Partial instantiations: 0
% 1.95/1.25  #Strategies tried      : 1
% 1.95/1.25  
% 1.95/1.25  Timing (in seconds)
% 1.95/1.25  ----------------------
% 1.95/1.25  Preprocessing        : 0.30
% 1.95/1.25  Parsing              : 0.16
% 1.95/1.25  CNF conversion       : 0.02
% 1.95/1.25  Main loop            : 0.17
% 1.95/1.25  Inferencing          : 0.07
% 1.95/1.25  Reduction            : 0.05
% 1.95/1.25  Demodulation         : 0.04
% 1.95/1.25  BG Simplification    : 0.01
% 1.95/1.26  Subsumption          : 0.02
% 1.95/1.26  Abstraction          : 0.01
% 1.95/1.26  MUC search           : 0.00
% 1.95/1.26  Cooper               : 0.00
% 1.95/1.26  Total                : 0.50
% 1.95/1.26  Index Insertion      : 0.00
% 1.95/1.26  Index Deletion       : 0.00
% 1.95/1.26  Index Matching       : 0.00
% 1.95/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
