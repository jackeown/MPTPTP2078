%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:53 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   57 (  98 expanded)
%              Number of leaves         :   31 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :   56 ( 122 expanded)
%              Number of equality atoms :   13 (  38 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,D) )
       => m1_subset_1(k1_tarski(k4_tarski(A,C)),k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_relset_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k2_tarski(A,B),k2_tarski(C,D)) = k2_enumset1(k4_tarski(A,C),k4_tarski(A,D),k4_tarski(B,C),k4_tarski(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_40,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_103,plain,(
    ! [A_62,B_63,C_64] :
      ( r1_tarski(k2_tarski(A_62,B_63),C_64)
      | ~ r2_hidden(B_63,C_64)
      | ~ r2_hidden(A_62,C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_112,plain,(
    ! [A_1,C_64] :
      ( r1_tarski(k1_tarski(A_1),C_64)
      | ~ r2_hidden(A_1,C_64)
      | ~ r2_hidden(A_1,C_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_103])).

tff(c_42,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_185,plain,(
    ! [A_98,C_99,D_100,B_101] : k2_enumset1(k4_tarski(A_98,C_99),k4_tarski(A_98,D_100),k4_tarski(B_101,C_99),k4_tarski(B_101,D_100)) = k2_zfmisc_1(k2_tarski(A_98,B_101),k2_tarski(C_99,D_100)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_192,plain,(
    ! [A_98,D_100,B_101] : k1_enumset1(k4_tarski(A_98,D_100),k4_tarski(B_101,D_100),k4_tarski(B_101,D_100)) = k2_zfmisc_1(k2_tarski(A_98,B_101),k2_tarski(D_100,D_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_6])).

tff(c_217,plain,(
    ! [A_106,D_107,B_108] : k1_enumset1(k4_tarski(A_106,D_107),k4_tarski(B_108,D_107),k4_tarski(B_108,D_107)) = k2_zfmisc_1(k2_tarski(A_106,B_108),k1_tarski(D_107)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_192])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_224,plain,(
    ! [B_108,D_107] : k2_zfmisc_1(k2_tarski(B_108,B_108),k1_tarski(D_107)) = k2_tarski(k4_tarski(B_108,D_107),k4_tarski(B_108,D_107)) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_4])).

tff(c_236,plain,(
    ! [B_109,D_110] : k2_zfmisc_1(k1_tarski(B_109),k1_tarski(D_110)) = k1_tarski(k4_tarski(B_109,D_110)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_224])).

tff(c_26,plain,(
    ! [A_27,C_29,B_28,D_30] :
      ( r1_tarski(k2_zfmisc_1(A_27,C_29),k2_zfmisc_1(B_28,D_30))
      | ~ r1_tarski(C_29,D_30)
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_257,plain,(
    ! [B_115,D_116,B_117,D_118] :
      ( r1_tarski(k1_tarski(k4_tarski(B_115,D_116)),k2_zfmisc_1(B_117,D_118))
      | ~ r1_tarski(k1_tarski(D_116),D_118)
      | ~ r1_tarski(k1_tarski(B_115),B_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_26])).

tff(c_71,plain,(
    ! [C_47,A_48] :
      ( r2_hidden(C_47,k1_zfmisc_1(A_48))
      | ~ r1_tarski(C_47,A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_36,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(A_38,B_39)
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_80,plain,(
    ! [C_49,A_50] :
      ( m1_subset_1(C_49,k1_zfmisc_1(A_50))
      | ~ r1_tarski(C_49,A_50) ) ),
    inference(resolution,[status(thm)],[c_71,c_36])).

tff(c_38,plain,(
    ~ m1_subset_1(k1_tarski(k4_tarski('#skF_3','#skF_5')),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_84,plain,(
    ~ r1_tarski(k1_tarski(k4_tarski('#skF_3','#skF_5')),k2_zfmisc_1('#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_80,c_38])).

tff(c_267,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6')
    | ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_257,c_84])).

tff(c_269,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_267])).

tff(c_272,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_112,c_269])).

tff(c_276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_272])).

tff(c_277,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_267])).

tff(c_281,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_112,c_277])).

tff(c_285,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_281])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:26:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.69  
% 2.69/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.69  %$ r2_hidden > r1_tarski > m1_subset_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.69/1.69  
% 2.69/1.69  %Foreground sorts:
% 2.69/1.69  
% 2.69/1.69  
% 2.69/1.69  %Background operators:
% 2.69/1.69  
% 2.69/1.69  
% 2.69/1.69  %Foreground operators:
% 2.69/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.69/1.69  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.69/1.69  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.69/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.69/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.69/1.69  tff('#skF_5', type, '#skF_5': $i).
% 2.69/1.69  tff('#skF_6', type, '#skF_6': $i).
% 2.69/1.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.69/1.69  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.69  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.69/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.69/1.69  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.69/1.69  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.69/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.69  
% 2.69/1.71  tff(f_69, negated_conjecture, ~(![A, B, C, D]: ((r2_hidden(A, B) & r2_hidden(C, D)) => m1_subset_1(k1_tarski(k4_tarski(A, C)), k1_zfmisc_1(k2_zfmisc_1(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_relset_1)).
% 2.69/1.71  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.69/1.71  tff(f_58, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.69/1.71  tff(f_52, axiom, (![A, B, C, D]: (k2_zfmisc_1(k2_tarski(A, B), k2_tarski(C, D)) = k2_enumset1(k4_tarski(A, C), k4_tarski(A, D), k4_tarski(B, C), k4_tarski(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 2.69/1.71  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.69/1.71  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.69/1.71  tff(f_50, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 2.69/1.71  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.69/1.71  tff(f_62, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.69/1.71  tff(c_40, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.69/1.71  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.69/1.71  tff(c_103, plain, (![A_62, B_63, C_64]: (r1_tarski(k2_tarski(A_62, B_63), C_64) | ~r2_hidden(B_63, C_64) | ~r2_hidden(A_62, C_64))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.69/1.71  tff(c_112, plain, (![A_1, C_64]: (r1_tarski(k1_tarski(A_1), C_64) | ~r2_hidden(A_1, C_64) | ~r2_hidden(A_1, C_64))), inference(superposition, [status(thm), theory('equality')], [c_2, c_103])).
% 2.69/1.71  tff(c_42, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.69/1.71  tff(c_185, plain, (![A_98, C_99, D_100, B_101]: (k2_enumset1(k4_tarski(A_98, C_99), k4_tarski(A_98, D_100), k4_tarski(B_101, C_99), k4_tarski(B_101, D_100))=k2_zfmisc_1(k2_tarski(A_98, B_101), k2_tarski(C_99, D_100)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.69/1.71  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.69/1.71  tff(c_192, plain, (![A_98, D_100, B_101]: (k1_enumset1(k4_tarski(A_98, D_100), k4_tarski(B_101, D_100), k4_tarski(B_101, D_100))=k2_zfmisc_1(k2_tarski(A_98, B_101), k2_tarski(D_100, D_100)))), inference(superposition, [status(thm), theory('equality')], [c_185, c_6])).
% 2.69/1.71  tff(c_217, plain, (![A_106, D_107, B_108]: (k1_enumset1(k4_tarski(A_106, D_107), k4_tarski(B_108, D_107), k4_tarski(B_108, D_107))=k2_zfmisc_1(k2_tarski(A_106, B_108), k1_tarski(D_107)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_192])).
% 2.69/1.71  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.69/1.71  tff(c_224, plain, (![B_108, D_107]: (k2_zfmisc_1(k2_tarski(B_108, B_108), k1_tarski(D_107))=k2_tarski(k4_tarski(B_108, D_107), k4_tarski(B_108, D_107)))), inference(superposition, [status(thm), theory('equality')], [c_217, c_4])).
% 2.69/1.71  tff(c_236, plain, (![B_109, D_110]: (k2_zfmisc_1(k1_tarski(B_109), k1_tarski(D_110))=k1_tarski(k4_tarski(B_109, D_110)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_224])).
% 2.69/1.71  tff(c_26, plain, (![A_27, C_29, B_28, D_30]: (r1_tarski(k2_zfmisc_1(A_27, C_29), k2_zfmisc_1(B_28, D_30)) | ~r1_tarski(C_29, D_30) | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.69/1.71  tff(c_257, plain, (![B_115, D_116, B_117, D_118]: (r1_tarski(k1_tarski(k4_tarski(B_115, D_116)), k2_zfmisc_1(B_117, D_118)) | ~r1_tarski(k1_tarski(D_116), D_118) | ~r1_tarski(k1_tarski(B_115), B_117))), inference(superposition, [status(thm), theory('equality')], [c_236, c_26])).
% 2.69/1.71  tff(c_71, plain, (![C_47, A_48]: (r2_hidden(C_47, k1_zfmisc_1(A_48)) | ~r1_tarski(C_47, A_48))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.69/1.71  tff(c_36, plain, (![A_38, B_39]: (m1_subset_1(A_38, B_39) | ~r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.69/1.71  tff(c_80, plain, (![C_49, A_50]: (m1_subset_1(C_49, k1_zfmisc_1(A_50)) | ~r1_tarski(C_49, A_50))), inference(resolution, [status(thm)], [c_71, c_36])).
% 2.69/1.71  tff(c_38, plain, (~m1_subset_1(k1_tarski(k4_tarski('#skF_3', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.69/1.71  tff(c_84, plain, (~r1_tarski(k1_tarski(k4_tarski('#skF_3', '#skF_5')), k2_zfmisc_1('#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_80, c_38])).
% 2.69/1.71  tff(c_267, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_6') | ~r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_257, c_84])).
% 2.69/1.71  tff(c_269, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_267])).
% 2.69/1.71  tff(c_272, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_112, c_269])).
% 2.69/1.71  tff(c_276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_272])).
% 2.69/1.71  tff(c_277, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_267])).
% 2.69/1.71  tff(c_281, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_112, c_277])).
% 2.69/1.71  tff(c_285, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_281])).
% 2.69/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.71  
% 2.69/1.71  Inference rules
% 2.69/1.71  ----------------------
% 2.69/1.71  #Ref     : 0
% 2.69/1.71  #Sup     : 50
% 2.69/1.71  #Fact    : 0
% 2.69/1.71  #Define  : 0
% 2.69/1.71  #Split   : 1
% 2.69/1.71  #Chain   : 0
% 2.69/1.71  #Close   : 0
% 2.69/1.71  
% 2.69/1.71  Ordering : KBO
% 2.69/1.71  
% 2.69/1.71  Simplification rules
% 2.69/1.71  ----------------------
% 2.69/1.71  #Subsume      : 1
% 2.69/1.71  #Demod        : 10
% 2.69/1.71  #Tautology    : 26
% 2.69/1.71  #SimpNegUnit  : 0
% 2.69/1.71  #BackRed      : 0
% 2.69/1.71  
% 2.69/1.71  #Partial instantiations: 0
% 2.69/1.71  #Strategies tried      : 1
% 2.69/1.71  
% 2.69/1.71  Timing (in seconds)
% 2.69/1.71  ----------------------
% 2.69/1.71  Preprocessing        : 0.51
% 2.69/1.71  Parsing              : 0.26
% 2.69/1.71  CNF conversion       : 0.04
% 2.69/1.71  Main loop            : 0.28
% 2.69/1.71  Inferencing          : 0.12
% 2.69/1.71  Reduction            : 0.07
% 2.69/1.71  Demodulation         : 0.05
% 2.69/1.71  BG Simplification    : 0.03
% 2.69/1.71  Subsumption          : 0.04
% 2.69/1.71  Abstraction          : 0.02
% 2.69/1.71  MUC search           : 0.00
% 2.69/1.71  Cooper               : 0.00
% 2.69/1.71  Total                : 0.83
% 2.69/1.71  Index Insertion      : 0.00
% 2.69/1.71  Index Deletion       : 0.00
% 2.69/1.71  Index Matching       : 0.00
% 2.69/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
