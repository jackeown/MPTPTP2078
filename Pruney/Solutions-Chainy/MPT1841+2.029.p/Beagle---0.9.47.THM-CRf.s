%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:32 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
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

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_56,axiom,(
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

tff(f_70,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,B_11)
      | v1_xboole_0(B_11)
      | ~ m1_subset_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_58,plain,(
    ! [A_30,B_31] :
      ( k6_domain_1(A_30,B_31) = k1_tarski(B_31)
      | ~ m1_subset_1(B_31,A_30)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_64,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_58])).

tff(c_68,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_64])).

tff(c_20,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_69,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_20])).

tff(c_6,plain,(
    ! [A_4] : ~ v1_xboole_0(k1_tarski(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k1_tarski(A_5),k1_zfmisc_1(B_6))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_74,plain,(
    ! [B_32,A_33] :
      ( ~ v1_subset_1(B_32,A_33)
      | v1_xboole_0(B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_33))
      | ~ v1_zfmisc_1(A_33)
      | v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_77,plain,(
    ! [A_5,B_6] :
      ( ~ v1_subset_1(k1_tarski(A_5),B_6)
      | v1_xboole_0(k1_tarski(A_5))
      | ~ v1_zfmisc_1(B_6)
      | v1_xboole_0(B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_74])).

tff(c_81,plain,(
    ! [A_34,B_35] :
      ( ~ v1_subset_1(k1_tarski(A_34),B_35)
      | ~ v1_zfmisc_1(B_35)
      | v1_xboole_0(B_35)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_77])).

tff(c_84,plain,
    ( ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1')
    | ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_69,c_81])).

tff(c_87,plain,
    ( v1_xboole_0('#skF_1')
    | ~ r2_hidden('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_84])).

tff(c_88,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_87])).

tff(c_91,plain,
    ( v1_xboole_0('#skF_1')
    | ~ m1_subset_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_88])).

tff(c_94,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_91])).

tff(c_96,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_94])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:00:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.13  
% 1.67/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.13  %$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1
% 1.67/1.13  
% 1.67/1.13  %Foreground sorts:
% 1.67/1.13  
% 1.67/1.13  
% 1.67/1.13  %Background operators:
% 1.67/1.13  
% 1.67/1.13  
% 1.67/1.13  %Foreground operators:
% 1.67/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.67/1.13  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.67/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.67/1.13  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.67/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.67/1.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.67/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.67/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.13  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.67/1.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.67/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.67/1.13  
% 1.67/1.14  tff(f_82, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 1.67/1.14  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 1.67/1.14  tff(f_56, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 1.67/1.14  tff(f_32, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 1.67/1.14  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 1.67/1.14  tff(f_70, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 1.67/1.14  tff(c_24, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.67/1.14  tff(c_22, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.67/1.14  tff(c_12, plain, (![A_10, B_11]: (r2_hidden(A_10, B_11) | v1_xboole_0(B_11) | ~m1_subset_1(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.67/1.14  tff(c_18, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.67/1.14  tff(c_58, plain, (![A_30, B_31]: (k6_domain_1(A_30, B_31)=k1_tarski(B_31) | ~m1_subset_1(B_31, A_30) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.67/1.14  tff(c_64, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_58])).
% 1.67/1.14  tff(c_68, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_24, c_64])).
% 1.67/1.14  tff(c_20, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.67/1.14  tff(c_69, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_20])).
% 1.67/1.14  tff(c_6, plain, (![A_4]: (~v1_xboole_0(k1_tarski(A_4)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.67/1.14  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(k1_tarski(A_5), k1_zfmisc_1(B_6)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.67/1.14  tff(c_74, plain, (![B_32, A_33]: (~v1_subset_1(B_32, A_33) | v1_xboole_0(B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_33)) | ~v1_zfmisc_1(A_33) | v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.67/1.14  tff(c_77, plain, (![A_5, B_6]: (~v1_subset_1(k1_tarski(A_5), B_6) | v1_xboole_0(k1_tarski(A_5)) | ~v1_zfmisc_1(B_6) | v1_xboole_0(B_6) | ~r2_hidden(A_5, B_6))), inference(resolution, [status(thm)], [c_8, c_74])).
% 1.67/1.14  tff(c_81, plain, (![A_34, B_35]: (~v1_subset_1(k1_tarski(A_34), B_35) | ~v1_zfmisc_1(B_35) | v1_xboole_0(B_35) | ~r2_hidden(A_34, B_35))), inference(negUnitSimplification, [status(thm)], [c_6, c_77])).
% 1.67/1.14  tff(c_84, plain, (~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1') | ~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_69, c_81])).
% 1.67/1.14  tff(c_87, plain, (v1_xboole_0('#skF_1') | ~r2_hidden('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_84])).
% 1.67/1.14  tff(c_88, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_24, c_87])).
% 1.67/1.14  tff(c_91, plain, (v1_xboole_0('#skF_1') | ~m1_subset_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_12, c_88])).
% 1.67/1.14  tff(c_94, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_91])).
% 1.67/1.14  tff(c_96, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_94])).
% 1.67/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.14  
% 1.67/1.14  Inference rules
% 1.67/1.14  ----------------------
% 1.67/1.14  #Ref     : 0
% 1.67/1.14  #Sup     : 13
% 1.67/1.14  #Fact    : 0
% 1.67/1.14  #Define  : 0
% 1.67/1.14  #Split   : 0
% 1.67/1.14  #Chain   : 0
% 1.67/1.14  #Close   : 0
% 1.67/1.14  
% 1.67/1.14  Ordering : KBO
% 1.67/1.14  
% 1.67/1.14  Simplification rules
% 1.67/1.14  ----------------------
% 1.67/1.14  #Subsume      : 0
% 1.67/1.14  #Demod        : 3
% 1.67/1.14  #Tautology    : 7
% 1.67/1.14  #SimpNegUnit  : 5
% 1.67/1.14  #BackRed      : 1
% 1.67/1.14  
% 1.67/1.14  #Partial instantiations: 0
% 1.67/1.14  #Strategies tried      : 1
% 1.67/1.14  
% 1.67/1.14  Timing (in seconds)
% 1.67/1.14  ----------------------
% 1.67/1.14  Preprocessing        : 0.29
% 1.67/1.14  Parsing              : 0.16
% 1.67/1.14  CNF conversion       : 0.02
% 1.67/1.14  Main loop            : 0.11
% 1.67/1.14  Inferencing          : 0.05
% 1.67/1.14  Reduction            : 0.03
% 1.67/1.14  Demodulation         : 0.02
% 1.67/1.14  BG Simplification    : 0.01
% 1.67/1.14  Subsumption          : 0.01
% 1.67/1.14  Abstraction          : 0.01
% 1.67/1.14  MUC search           : 0.00
% 1.67/1.14  Cooper               : 0.00
% 1.67/1.15  Total                : 0.42
% 1.67/1.15  Index Insertion      : 0.00
% 1.67/1.15  Index Deletion       : 0.00
% 1.67/1.15  Index Matching       : 0.00
% 1.67/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
