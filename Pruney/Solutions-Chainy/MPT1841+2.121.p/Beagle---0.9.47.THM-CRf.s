%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:44 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   41 (  50 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :   59 (  86 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1

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

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_32,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(c_24,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_22,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,B_11)
      | v1_xboole_0(B_11)
      | ~ m1_subset_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_52,plain,(
    ! [A_30,B_31] :
      ( k6_domain_1(A_30,B_31) = k1_tarski(B_31)
      | ~ m1_subset_1(B_31,A_30)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_58,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_52])).

tff(c_62,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_58])).

tff(c_20,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_63,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_20])).

tff(c_6,plain,(
    ! [A_4] : ~ v1_xboole_0(k1_tarski(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k1_tarski(A_5),k1_zfmisc_1(B_6))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_72,plain,(
    ! [B_32,A_33] :
      ( ~ v1_subset_1(B_32,A_33)
      | v1_xboole_0(B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_33))
      | ~ v1_zfmisc_1(A_33)
      | v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_75,plain,(
    ! [A_5,B_6] :
      ( ~ v1_subset_1(k1_tarski(A_5),B_6)
      | v1_xboole_0(k1_tarski(A_5))
      | ~ v1_zfmisc_1(B_6)
      | v1_xboole_0(B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_72])).

tff(c_79,plain,(
    ! [A_34,B_35] :
      ( ~ v1_subset_1(k1_tarski(A_34),B_35)
      | ~ v1_zfmisc_1(B_35)
      | v1_xboole_0(B_35)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_75])).

tff(c_82,plain,
    ( ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1')
    | ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_63,c_79])).

tff(c_85,plain,
    ( v1_xboole_0('#skF_1')
    | ~ r2_hidden('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_82])).

tff(c_86,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_85])).

tff(c_89,plain,
    ( v1_xboole_0('#skF_1')
    | ~ m1_subset_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_86])).

tff(c_92,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_89])).

tff(c_94,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.24  
% 1.89/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.24  %$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1
% 1.99/1.24  
% 1.99/1.24  %Foreground sorts:
% 1.99/1.24  
% 1.99/1.24  
% 1.99/1.24  %Background operators:
% 1.99/1.24  
% 1.99/1.24  
% 1.99/1.24  %Foreground operators:
% 1.99/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.24  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.99/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.24  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.99/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.99/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.24  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.99/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.99/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.24  
% 1.99/1.25  tff(f_83, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 1.99/1.25  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 1.99/1.25  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 1.99/1.25  tff(f_32, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 1.99/1.25  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 1.99/1.25  tff(f_71, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 1.99/1.25  tff(c_24, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.99/1.25  tff(c_22, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.99/1.25  tff(c_12, plain, (![A_10, B_11]: (r2_hidden(A_10, B_11) | v1_xboole_0(B_11) | ~m1_subset_1(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.99/1.25  tff(c_18, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.99/1.25  tff(c_52, plain, (![A_30, B_31]: (k6_domain_1(A_30, B_31)=k1_tarski(B_31) | ~m1_subset_1(B_31, A_30) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.99/1.25  tff(c_58, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_52])).
% 1.99/1.25  tff(c_62, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_24, c_58])).
% 1.99/1.25  tff(c_20, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.99/1.25  tff(c_63, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_20])).
% 1.99/1.25  tff(c_6, plain, (![A_4]: (~v1_xboole_0(k1_tarski(A_4)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.99/1.25  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(k1_tarski(A_5), k1_zfmisc_1(B_6)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.99/1.25  tff(c_72, plain, (![B_32, A_33]: (~v1_subset_1(B_32, A_33) | v1_xboole_0(B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_33)) | ~v1_zfmisc_1(A_33) | v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.99/1.25  tff(c_75, plain, (![A_5, B_6]: (~v1_subset_1(k1_tarski(A_5), B_6) | v1_xboole_0(k1_tarski(A_5)) | ~v1_zfmisc_1(B_6) | v1_xboole_0(B_6) | ~r2_hidden(A_5, B_6))), inference(resolution, [status(thm)], [c_8, c_72])).
% 1.99/1.25  tff(c_79, plain, (![A_34, B_35]: (~v1_subset_1(k1_tarski(A_34), B_35) | ~v1_zfmisc_1(B_35) | v1_xboole_0(B_35) | ~r2_hidden(A_34, B_35))), inference(negUnitSimplification, [status(thm)], [c_6, c_75])).
% 1.99/1.25  tff(c_82, plain, (~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1') | ~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_63, c_79])).
% 1.99/1.25  tff(c_85, plain, (v1_xboole_0('#skF_1') | ~r2_hidden('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_82])).
% 1.99/1.25  tff(c_86, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_24, c_85])).
% 1.99/1.25  tff(c_89, plain, (v1_xboole_0('#skF_1') | ~m1_subset_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_12, c_86])).
% 1.99/1.25  tff(c_92, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_89])).
% 1.99/1.25  tff(c_94, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_92])).
% 1.99/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.25  
% 1.99/1.25  Inference rules
% 1.99/1.25  ----------------------
% 1.99/1.25  #Ref     : 0
% 1.99/1.25  #Sup     : 13
% 1.99/1.25  #Fact    : 0
% 1.99/1.25  #Define  : 0
% 1.99/1.25  #Split   : 0
% 1.99/1.25  #Chain   : 0
% 1.99/1.25  #Close   : 0
% 1.99/1.25  
% 1.99/1.25  Ordering : KBO
% 1.99/1.25  
% 1.99/1.25  Simplification rules
% 1.99/1.25  ----------------------
% 1.99/1.25  #Subsume      : 1
% 1.99/1.25  #Demod        : 3
% 1.99/1.25  #Tautology    : 6
% 1.99/1.25  #SimpNegUnit  : 4
% 1.99/1.25  #BackRed      : 1
% 1.99/1.25  
% 1.99/1.25  #Partial instantiations: 0
% 1.99/1.25  #Strategies tried      : 1
% 1.99/1.25  
% 1.99/1.25  Timing (in seconds)
% 1.99/1.25  ----------------------
% 1.99/1.26  Preprocessing        : 0.33
% 1.99/1.26  Parsing              : 0.17
% 1.99/1.26  CNF conversion       : 0.02
% 1.99/1.26  Main loop            : 0.11
% 1.99/1.26  Inferencing          : 0.05
% 1.99/1.26  Reduction            : 0.03
% 1.99/1.26  Demodulation         : 0.02
% 1.99/1.26  BG Simplification    : 0.01
% 1.99/1.26  Subsumption          : 0.02
% 1.99/1.26  Abstraction          : 0.01
% 1.99/1.26  MUC search           : 0.00
% 1.99/1.26  Cooper               : 0.00
% 1.99/1.26  Total                : 0.46
% 1.99/1.26  Index Insertion      : 0.00
% 1.99/1.26  Index Deletion       : 0.00
% 1.99/1.26  Index Matching       : 0.00
% 1.99/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
