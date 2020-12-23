%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:54 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   52 (  85 expanded)
%              Number of leaves         :   29 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :   44 (  94 expanded)
%              Number of equality atoms :   12 (  32 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k2_tarski(A,B),k2_tarski(C,D)) = k2_enumset1(k4_tarski(A,C),k4_tarski(A,D),k4_tarski(B,C),k4_tarski(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_30,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(k1_tarski(A_29),B_30)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_117,plain,(
    ! [A_81,C_82,D_83,B_84] : k2_enumset1(k4_tarski(A_81,C_82),k4_tarski(A_81,D_83),k4_tarski(B_84,C_82),k4_tarski(B_84,D_83)) = k2_zfmisc_1(k2_tarski(A_81,B_84),k2_tarski(C_82,D_83)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_124,plain,(
    ! [A_81,D_83,B_84] : k1_enumset1(k4_tarski(A_81,D_83),k4_tarski(B_84,D_83),k4_tarski(B_84,D_83)) = k2_zfmisc_1(k2_tarski(A_81,B_84),k2_tarski(D_83,D_83)) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_6])).

tff(c_136,plain,(
    ! [A_85,D_86,B_87] : k1_enumset1(k4_tarski(A_85,D_86),k4_tarski(B_87,D_86),k4_tarski(B_87,D_86)) = k2_zfmisc_1(k2_tarski(A_85,B_87),k1_tarski(D_86)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_124])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_143,plain,(
    ! [B_87,D_86] : k2_zfmisc_1(k2_tarski(B_87,B_87),k1_tarski(D_86)) = k2_tarski(k4_tarski(B_87,D_86),k4_tarski(B_87,D_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_4])).

tff(c_155,plain,(
    ! [B_88,D_89] : k2_zfmisc_1(k1_tarski(B_88),k1_tarski(D_89)) = k1_tarski(k4_tarski(B_88,D_89)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_143])).

tff(c_20,plain,(
    ! [A_31,C_33,B_32,D_34] :
      ( r1_tarski(k2_zfmisc_1(A_31,C_33),k2_zfmisc_1(B_32,D_34))
      | ~ r1_tarski(C_33,D_34)
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_172,plain,(
    ! [B_90,D_91,B_92,D_93] :
      ( r1_tarski(k1_tarski(k4_tarski(B_90,D_91)),k2_zfmisc_1(B_92,D_93))
      | ~ r1_tarski(k1_tarski(D_91),D_93)
      | ~ r1_tarski(k1_tarski(B_90),B_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_20])).

tff(c_26,plain,(
    ! [A_39,B_40] :
      ( m1_subset_1(A_39,k1_zfmisc_1(B_40))
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ~ m1_subset_1(k1_tarski(k4_tarski('#skF_1','#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_75,plain,(
    ~ r1_tarski(k1_tarski(k4_tarski('#skF_1','#skF_3')),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_26,c_28])).

tff(c_182,plain,
    ( ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4')
    | ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_172,c_75])).

tff(c_184,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_187,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_184])).

tff(c_191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_187])).

tff(c_192,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_200,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_192])).

tff(c_204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_200])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:29:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.26  
% 2.05/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.26  %$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.05/1.26  
% 2.05/1.26  %Foreground sorts:
% 2.05/1.26  
% 2.05/1.26  
% 2.05/1.26  %Background operators:
% 2.05/1.26  
% 2.05/1.26  
% 2.05/1.26  %Foreground operators:
% 2.05/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.05/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.05/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.05/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.05/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.05/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.05/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.05/1.26  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.05/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.05/1.26  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.05/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.05/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.26  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.05/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.05/1.26  
% 2.05/1.27  tff(f_62, negated_conjecture, ~(![A, B, C, D]: ((r2_hidden(A, B) & r2_hidden(C, D)) => m1_subset_1(k1_tarski(k4_tarski(A, C)), k1_zfmisc_1(k2_zfmisc_1(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_relset_1)).
% 2.05/1.27  tff(f_43, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.05/1.27  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.05/1.27  tff(f_51, axiom, (![A, B, C, D]: (k2_zfmisc_1(k2_tarski(A, B), k2_tarski(C, D)) = k2_enumset1(k4_tarski(A, C), k4_tarski(A, D), k4_tarski(B, C), k4_tarski(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 2.05/1.27  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.05/1.27  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.05/1.27  tff(f_49, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 2.05/1.27  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.05/1.27  tff(c_30, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.05/1.27  tff(c_18, plain, (![A_29, B_30]: (r1_tarski(k1_tarski(A_29), B_30) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.05/1.27  tff(c_32, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.05/1.27  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.05/1.27  tff(c_117, plain, (![A_81, C_82, D_83, B_84]: (k2_enumset1(k4_tarski(A_81, C_82), k4_tarski(A_81, D_83), k4_tarski(B_84, C_82), k4_tarski(B_84, D_83))=k2_zfmisc_1(k2_tarski(A_81, B_84), k2_tarski(C_82, D_83)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.05/1.27  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.05/1.27  tff(c_124, plain, (![A_81, D_83, B_84]: (k1_enumset1(k4_tarski(A_81, D_83), k4_tarski(B_84, D_83), k4_tarski(B_84, D_83))=k2_zfmisc_1(k2_tarski(A_81, B_84), k2_tarski(D_83, D_83)))), inference(superposition, [status(thm), theory('equality')], [c_117, c_6])).
% 2.05/1.27  tff(c_136, plain, (![A_85, D_86, B_87]: (k1_enumset1(k4_tarski(A_85, D_86), k4_tarski(B_87, D_86), k4_tarski(B_87, D_86))=k2_zfmisc_1(k2_tarski(A_85, B_87), k1_tarski(D_86)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_124])).
% 2.05/1.27  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.05/1.27  tff(c_143, plain, (![B_87, D_86]: (k2_zfmisc_1(k2_tarski(B_87, B_87), k1_tarski(D_86))=k2_tarski(k4_tarski(B_87, D_86), k4_tarski(B_87, D_86)))), inference(superposition, [status(thm), theory('equality')], [c_136, c_4])).
% 2.05/1.27  tff(c_155, plain, (![B_88, D_89]: (k2_zfmisc_1(k1_tarski(B_88), k1_tarski(D_89))=k1_tarski(k4_tarski(B_88, D_89)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_143])).
% 2.05/1.27  tff(c_20, plain, (![A_31, C_33, B_32, D_34]: (r1_tarski(k2_zfmisc_1(A_31, C_33), k2_zfmisc_1(B_32, D_34)) | ~r1_tarski(C_33, D_34) | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.05/1.27  tff(c_172, plain, (![B_90, D_91, B_92, D_93]: (r1_tarski(k1_tarski(k4_tarski(B_90, D_91)), k2_zfmisc_1(B_92, D_93)) | ~r1_tarski(k1_tarski(D_91), D_93) | ~r1_tarski(k1_tarski(B_90), B_92))), inference(superposition, [status(thm), theory('equality')], [c_155, c_20])).
% 2.05/1.27  tff(c_26, plain, (![A_39, B_40]: (m1_subset_1(A_39, k1_zfmisc_1(B_40)) | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.05/1.27  tff(c_28, plain, (~m1_subset_1(k1_tarski(k4_tarski('#skF_1', '#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.05/1.27  tff(c_75, plain, (~r1_tarski(k1_tarski(k4_tarski('#skF_1', '#skF_3')), k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_28])).
% 2.05/1.27  tff(c_182, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_4') | ~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_172, c_75])).
% 2.05/1.27  tff(c_184, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_182])).
% 2.05/1.27  tff(c_187, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_18, c_184])).
% 2.05/1.27  tff(c_191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_187])).
% 2.05/1.27  tff(c_192, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_182])).
% 2.05/1.27  tff(c_200, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_18, c_192])).
% 2.05/1.27  tff(c_204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_200])).
% 2.05/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.27  
% 2.05/1.27  Inference rules
% 2.05/1.27  ----------------------
% 2.05/1.27  #Ref     : 0
% 2.05/1.27  #Sup     : 36
% 2.05/1.27  #Fact    : 0
% 2.05/1.27  #Define  : 0
% 2.05/1.27  #Split   : 1
% 2.05/1.27  #Chain   : 0
% 2.05/1.27  #Close   : 0
% 2.05/1.27  
% 2.05/1.27  Ordering : KBO
% 2.05/1.27  
% 2.05/1.27  Simplification rules
% 2.05/1.27  ----------------------
% 2.05/1.27  #Subsume      : 0
% 2.05/1.27  #Demod        : 10
% 2.05/1.27  #Tautology    : 24
% 2.05/1.27  #SimpNegUnit  : 0
% 2.05/1.27  #BackRed      : 0
% 2.05/1.27  
% 2.05/1.27  #Partial instantiations: 0
% 2.05/1.27  #Strategies tried      : 1
% 2.05/1.27  
% 2.05/1.27  Timing (in seconds)
% 2.05/1.27  ----------------------
% 2.05/1.27  Preprocessing        : 0.32
% 2.05/1.27  Parsing              : 0.17
% 2.05/1.27  CNF conversion       : 0.02
% 2.05/1.27  Main loop            : 0.16
% 2.05/1.27  Inferencing          : 0.07
% 2.05/1.27  Reduction            : 0.05
% 2.05/1.28  Demodulation         : 0.03
% 2.05/1.28  BG Simplification    : 0.01
% 2.05/1.28  Subsumption          : 0.02
% 2.05/1.28  Abstraction          : 0.01
% 2.18/1.28  MUC search           : 0.00
% 2.18/1.28  Cooper               : 0.00
% 2.18/1.28  Total                : 0.50
% 2.18/1.28  Index Insertion      : 0.00
% 2.18/1.28  Index Deletion       : 0.00
% 2.18/1.28  Index Matching       : 0.00
% 2.18/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
