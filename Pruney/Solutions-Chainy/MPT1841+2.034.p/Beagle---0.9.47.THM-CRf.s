%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:32 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   39 (  48 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :   59 (  86 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1

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

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_28,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( v1_subset_1(B,A)
           => v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tex_2)).

tff(c_18,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_16,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( k6_domain_1(A_17,B_18) = k1_tarski(B_18)
      | ~ m1_subset_1(B_18,A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_22])).

tff(c_32,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_28])).

tff(c_14,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_33,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_14])).

tff(c_2,plain,(
    ! [A_1] : ~ v1_xboole_0(k1_tarski(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(k1_tarski(A_2),k1_zfmisc_1(B_3))
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    ! [B_19,A_20] :
      ( v1_xboole_0(B_19)
      | ~ v1_subset_1(B_19,A_20)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_20))
      | ~ v1_zfmisc_1(A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_41,plain,(
    ! [A_2,B_3] :
      ( v1_xboole_0(k1_tarski(A_2))
      | ~ v1_subset_1(k1_tarski(A_2),B_3)
      | ~ v1_zfmisc_1(B_3)
      | v1_xboole_0(B_3)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(resolution,[status(thm)],[c_4,c_38])).

tff(c_45,plain,(
    ! [A_21,B_22] :
      ( ~ v1_subset_1(k1_tarski(A_21),B_22)
      | ~ v1_zfmisc_1(B_22)
      | v1_xboole_0(B_22)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2,c_41])).

tff(c_48,plain,
    ( ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1')
    | ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_33,c_45])).

tff(c_51,plain,
    ( v1_xboole_0('#skF_1')
    | ~ r2_hidden('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_48])).

tff(c_52,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_51])).

tff(c_55,plain,
    ( v1_xboole_0('#skF_1')
    | ~ m1_subset_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_52])).

tff(c_58,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_55])).

tff(c_60,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n020.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 12:59:52 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.55/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.08  
% 1.55/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.08  %$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1
% 1.68/1.08  
% 1.68/1.08  %Foreground sorts:
% 1.68/1.08  
% 1.68/1.08  
% 1.68/1.08  %Background operators:
% 1.68/1.08  
% 1.68/1.08  
% 1.68/1.08  %Foreground operators:
% 1.68/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.68/1.08  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.68/1.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.68/1.08  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.68/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.68/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.08  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.68/1.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.68/1.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.68/1.08  
% 1.68/1.09  tff(f_69, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 1.68/1.09  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 1.68/1.09  tff(f_45, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 1.68/1.09  tff(f_28, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 1.68/1.09  tff(f_32, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 1.68/1.09  tff(f_57, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) => v1_xboole_0(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tex_2)).
% 1.68/1.09  tff(c_18, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.68/1.09  tff(c_16, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.68/1.09  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.68/1.09  tff(c_12, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.68/1.09  tff(c_22, plain, (![A_17, B_18]: (k6_domain_1(A_17, B_18)=k1_tarski(B_18) | ~m1_subset_1(B_18, A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.68/1.09  tff(c_28, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_22])).
% 1.68/1.09  tff(c_32, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_18, c_28])).
% 1.68/1.09  tff(c_14, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.68/1.09  tff(c_33, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_14])).
% 1.68/1.09  tff(c_2, plain, (![A_1]: (~v1_xboole_0(k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.68/1.09  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(k1_tarski(A_2), k1_zfmisc_1(B_3)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.68/1.09  tff(c_38, plain, (![B_19, A_20]: (v1_xboole_0(B_19) | ~v1_subset_1(B_19, A_20) | ~m1_subset_1(B_19, k1_zfmisc_1(A_20)) | ~v1_zfmisc_1(A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.68/1.09  tff(c_41, plain, (![A_2, B_3]: (v1_xboole_0(k1_tarski(A_2)) | ~v1_subset_1(k1_tarski(A_2), B_3) | ~v1_zfmisc_1(B_3) | v1_xboole_0(B_3) | ~r2_hidden(A_2, B_3))), inference(resolution, [status(thm)], [c_4, c_38])).
% 1.68/1.09  tff(c_45, plain, (![A_21, B_22]: (~v1_subset_1(k1_tarski(A_21), B_22) | ~v1_zfmisc_1(B_22) | v1_xboole_0(B_22) | ~r2_hidden(A_21, B_22))), inference(negUnitSimplification, [status(thm)], [c_2, c_41])).
% 1.68/1.09  tff(c_48, plain, (~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1') | ~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_33, c_45])).
% 1.68/1.09  tff(c_51, plain, (v1_xboole_0('#skF_1') | ~r2_hidden('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_48])).
% 1.68/1.09  tff(c_52, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_18, c_51])).
% 1.68/1.09  tff(c_55, plain, (v1_xboole_0('#skF_1') | ~m1_subset_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_6, c_52])).
% 1.68/1.09  tff(c_58, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_55])).
% 1.68/1.09  tff(c_60, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_58])).
% 1.68/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.09  
% 1.68/1.09  Inference rules
% 1.68/1.09  ----------------------
% 1.68/1.09  #Ref     : 0
% 1.68/1.09  #Sup     : 7
% 1.68/1.09  #Fact    : 0
% 1.68/1.09  #Define  : 0
% 1.68/1.09  #Split   : 0
% 1.68/1.09  #Chain   : 0
% 1.68/1.09  #Close   : 0
% 1.68/1.09  
% 1.68/1.09  Ordering : KBO
% 1.68/1.09  
% 1.68/1.09  Simplification rules
% 1.68/1.09  ----------------------
% 1.68/1.09  #Subsume      : 0
% 1.68/1.09  #Demod        : 3
% 1.68/1.09  #Tautology    : 2
% 1.68/1.09  #SimpNegUnit  : 4
% 1.68/1.09  #BackRed      : 1
% 1.68/1.09  
% 1.68/1.09  #Partial instantiations: 0
% 1.68/1.09  #Strategies tried      : 1
% 1.68/1.09  
% 1.68/1.09  Timing (in seconds)
% 1.68/1.09  ----------------------
% 1.68/1.10  Preprocessing        : 0.27
% 1.68/1.10  Parsing              : 0.15
% 1.68/1.10  CNF conversion       : 0.02
% 1.68/1.10  Main loop            : 0.09
% 1.68/1.10  Inferencing          : 0.04
% 1.68/1.10  Reduction            : 0.03
% 1.68/1.10  Demodulation         : 0.01
% 1.68/1.10  BG Simplification    : 0.01
% 1.68/1.10  Subsumption          : 0.01
% 1.68/1.10  Abstraction          : 0.01
% 1.68/1.10  MUC search           : 0.00
% 1.68/1.10  Cooper               : 0.00
% 1.68/1.10  Total                : 0.39
% 1.68/1.10  Index Insertion      : 0.00
% 1.68/1.10  Index Deletion       : 0.00
% 1.68/1.10  Index Matching       : 0.00
% 1.68/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
