%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:36 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   41 (  58 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   56 ( 102 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(c_32,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_8,plain,(
    ! [C_9] : r2_hidden(C_9,k1_tarski(C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_34,plain,(
    ! [B_22,A_23] :
      ( ~ r2_hidden(B_22,A_23)
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [C_9] : ~ v1_xboole_0(k1_tarski(C_9)) ),
    inference(resolution,[status(thm)],[c_8,c_34])).

tff(c_26,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_30,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_73,plain,(
    ! [A_31,B_32] :
      ( k6_domain_1(A_31,B_32) = k1_tarski(B_32)
      | ~ m1_subset_1(B_32,A_31)
      | v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_76,plain,
    ( k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_73])).

tff(c_79,plain,(
    k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_76])).

tff(c_28,plain,(
    v1_subset_1(k6_domain_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_80,plain,(
    v1_subset_1(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_28])).

tff(c_85,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k6_domain_1(A_33,B_34),k1_zfmisc_1(A_33))
      | ~ m1_subset_1(B_34,A_33)
      | v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_94,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_85])).

tff(c_98,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_94])).

tff(c_99,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_98])).

tff(c_150,plain,(
    ! [B_46,A_47] :
      ( ~ v1_subset_1(B_46,A_47)
      | v1_xboole_0(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_zfmisc_1(A_47)
      | v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_153,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_5'),'#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5'))
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_99,c_150])).

tff(c_159,plain,
    ( v1_xboole_0(k1_tarski('#skF_5'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_80,c_153])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_38,c_159])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:06:44 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.19  
% 2.16/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.19  %$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.16/1.19  
% 2.16/1.19  %Foreground sorts:
% 2.16/1.19  
% 2.16/1.19  
% 2.16/1.19  %Background operators:
% 2.16/1.19  
% 2.16/1.19  
% 2.16/1.19  %Foreground operators:
% 2.16/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.19  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.16/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.16/1.19  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.16/1.19  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.16/1.19  tff('#skF_5', type, '#skF_5': $i).
% 2.16/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.19  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.16/1.19  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.16/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.16/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.19  
% 2.16/1.20  tff(f_86, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.16/1.20  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.16/1.20  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.16/1.20  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.16/1.20  tff(f_53, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.16/1.20  tff(f_74, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.16/1.20  tff(c_32, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.16/1.20  tff(c_8, plain, (![C_9]: (r2_hidden(C_9, k1_tarski(C_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.16/1.20  tff(c_34, plain, (![B_22, A_23]: (~r2_hidden(B_22, A_23) | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.20  tff(c_38, plain, (![C_9]: (~v1_xboole_0(k1_tarski(C_9)))), inference(resolution, [status(thm)], [c_8, c_34])).
% 2.16/1.20  tff(c_26, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.16/1.20  tff(c_30, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.16/1.20  tff(c_73, plain, (![A_31, B_32]: (k6_domain_1(A_31, B_32)=k1_tarski(B_32) | ~m1_subset_1(B_32, A_31) | v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.16/1.20  tff(c_76, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_73])).
% 2.16/1.20  tff(c_79, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_32, c_76])).
% 2.16/1.20  tff(c_28, plain, (v1_subset_1(k6_domain_1('#skF_4', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.16/1.20  tff(c_80, plain, (v1_subset_1(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_28])).
% 2.16/1.20  tff(c_85, plain, (![A_33, B_34]: (m1_subset_1(k6_domain_1(A_33, B_34), k1_zfmisc_1(A_33)) | ~m1_subset_1(B_34, A_33) | v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.16/1.20  tff(c_94, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_79, c_85])).
% 2.16/1.20  tff(c_98, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_94])).
% 2.16/1.20  tff(c_99, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_32, c_98])).
% 2.16/1.20  tff(c_150, plain, (![B_46, A_47]: (~v1_subset_1(B_46, A_47) | v1_xboole_0(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_zfmisc_1(A_47) | v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.16/1.20  tff(c_153, plain, (~v1_subset_1(k1_tarski('#skF_5'), '#skF_4') | v1_xboole_0(k1_tarski('#skF_5')) | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_99, c_150])).
% 2.16/1.20  tff(c_159, plain, (v1_xboole_0(k1_tarski('#skF_5')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_80, c_153])).
% 2.16/1.20  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_38, c_159])).
% 2.16/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.20  
% 2.16/1.20  Inference rules
% 2.16/1.20  ----------------------
% 2.16/1.20  #Ref     : 0
% 2.16/1.20  #Sup     : 25
% 2.16/1.20  #Fact    : 0
% 2.16/1.20  #Define  : 0
% 2.16/1.20  #Split   : 1
% 2.16/1.20  #Chain   : 0
% 2.16/1.20  #Close   : 0
% 2.16/1.20  
% 2.16/1.20  Ordering : KBO
% 2.16/1.20  
% 2.16/1.20  Simplification rules
% 2.16/1.20  ----------------------
% 2.16/1.20  #Subsume      : 2
% 2.16/1.20  #Demod        : 6
% 2.16/1.20  #Tautology    : 10
% 2.16/1.20  #SimpNegUnit  : 5
% 2.16/1.20  #BackRed      : 1
% 2.16/1.20  
% 2.16/1.20  #Partial instantiations: 0
% 2.16/1.20  #Strategies tried      : 1
% 2.16/1.20  
% 2.16/1.20  Timing (in seconds)
% 2.16/1.20  ----------------------
% 2.16/1.20  Preprocessing        : 0.30
% 2.16/1.20  Parsing              : 0.16
% 2.16/1.20  CNF conversion       : 0.02
% 2.16/1.20  Main loop            : 0.14
% 2.16/1.20  Inferencing          : 0.05
% 2.16/1.20  Reduction            : 0.04
% 2.16/1.20  Demodulation         : 0.02
% 2.16/1.20  BG Simplification    : 0.01
% 2.16/1.20  Subsumption          : 0.03
% 2.16/1.20  Abstraction          : 0.01
% 2.16/1.20  MUC search           : 0.00
% 2.16/1.20  Cooper               : 0.00
% 2.16/1.21  Total                : 0.46
% 2.16/1.21  Index Insertion      : 0.00
% 2.16/1.21  Index Deletion       : 0.00
% 2.16/1.21  Index Matching       : 0.00
% 2.16/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
