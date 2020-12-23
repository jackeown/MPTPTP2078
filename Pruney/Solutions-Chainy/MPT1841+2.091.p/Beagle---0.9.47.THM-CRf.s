%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:40 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   45 (  68 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   58 ( 118 expanded)
%              Number of equality atoms :   10 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_32,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : ~ v1_xboole_0(k2_enumset1(A,B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(c_28,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_55,plain,(
    ! [A_33,B_34,C_35] : k2_enumset1(A_33,A_33,B_34,C_35) = k1_enumset1(A_33,B_34,C_35) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10,D_11] : ~ v1_xboole_0(k2_enumset1(A_8,B_9,C_10,D_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_66,plain,(
    ! [A_36,B_37,C_38] : ~ v1_xboole_0(k1_enumset1(A_36,B_37,C_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_12])).

tff(c_69,plain,(
    ! [A_39,B_40] : ~ v1_xboole_0(k2_tarski(A_39,B_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_66])).

tff(c_71,plain,(
    ! [A_2] : ~ v1_xboole_0(k1_tarski(A_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_69])).

tff(c_26,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_22,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_73,plain,(
    ! [A_42,B_43] :
      ( k6_domain_1(A_42,B_43) = k1_tarski(B_43)
      | ~ m1_subset_1(B_43,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_76,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_73])).

tff(c_79,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_76])).

tff(c_24,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_89,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_24])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k6_domain_1(A_15,B_16),k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_145,plain,(
    ! [B_47,A_48] :
      ( ~ v1_subset_1(B_47,A_48)
      | v1_xboole_0(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_zfmisc_1(A_48)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_156,plain,(
    ! [A_49,B_50] :
      ( ~ v1_subset_1(k6_domain_1(A_49,B_50),A_49)
      | v1_xboole_0(k6_domain_1(A_49,B_50))
      | ~ v1_zfmisc_1(A_49)
      | ~ m1_subset_1(B_50,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_16,c_145])).

tff(c_159,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | v1_xboole_0(k6_domain_1('#skF_1','#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_156])).

tff(c_161,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_79,c_89,c_159])).

tff(c_163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_71,c_161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:19:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.19  
% 1.82/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.19  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.82/1.19  
% 1.82/1.19  %Foreground sorts:
% 1.82/1.19  
% 1.82/1.19  
% 1.82/1.19  %Background operators:
% 1.82/1.19  
% 1.82/1.19  
% 1.82/1.19  %Foreground operators:
% 1.82/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.19  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.82/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.82/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.19  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.82/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.82/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.82/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.82/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.82/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.82/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.19  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.82/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.82/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.82/1.19  
% 1.82/1.20  tff(f_87, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 1.82/1.20  tff(f_32, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.82/1.20  tff(f_34, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.82/1.20  tff(f_36, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.82/1.20  tff(f_39, axiom, (![A, B, C, D]: ~v1_xboole_0(k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_subset_1)).
% 1.82/1.20  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 1.82/1.20  tff(f_54, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 1.82/1.20  tff(f_75, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 1.82/1.20  tff(c_28, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.82/1.20  tff(c_6, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.82/1.20  tff(c_8, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.82/1.20  tff(c_55, plain, (![A_33, B_34, C_35]: (k2_enumset1(A_33, A_33, B_34, C_35)=k1_enumset1(A_33, B_34, C_35))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.82/1.20  tff(c_12, plain, (![A_8, B_9, C_10, D_11]: (~v1_xboole_0(k2_enumset1(A_8, B_9, C_10, D_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.82/1.20  tff(c_66, plain, (![A_36, B_37, C_38]: (~v1_xboole_0(k1_enumset1(A_36, B_37, C_38)))), inference(superposition, [status(thm), theory('equality')], [c_55, c_12])).
% 1.82/1.20  tff(c_69, plain, (![A_39, B_40]: (~v1_xboole_0(k2_tarski(A_39, B_40)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_66])).
% 1.82/1.20  tff(c_71, plain, (![A_2]: (~v1_xboole_0(k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_69])).
% 1.82/1.20  tff(c_26, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.82/1.20  tff(c_22, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.82/1.20  tff(c_73, plain, (![A_42, B_43]: (k6_domain_1(A_42, B_43)=k1_tarski(B_43) | ~m1_subset_1(B_43, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.82/1.20  tff(c_76, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_73])).
% 1.82/1.20  tff(c_79, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_28, c_76])).
% 1.82/1.20  tff(c_24, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.82/1.20  tff(c_89, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_24])).
% 1.82/1.20  tff(c_16, plain, (![A_15, B_16]: (m1_subset_1(k6_domain_1(A_15, B_16), k1_zfmisc_1(A_15)) | ~m1_subset_1(B_16, A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.82/1.20  tff(c_145, plain, (![B_47, A_48]: (~v1_subset_1(B_47, A_48) | v1_xboole_0(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_zfmisc_1(A_48) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.82/1.20  tff(c_156, plain, (![A_49, B_50]: (~v1_subset_1(k6_domain_1(A_49, B_50), A_49) | v1_xboole_0(k6_domain_1(A_49, B_50)) | ~v1_zfmisc_1(A_49) | ~m1_subset_1(B_50, A_49) | v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_16, c_145])).
% 1.82/1.20  tff(c_159, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k6_domain_1('#skF_1', '#skF_2')) | ~v1_zfmisc_1('#skF_1') | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_79, c_156])).
% 1.82/1.20  tff(c_161, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_79, c_89, c_159])).
% 1.82/1.20  tff(c_163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_71, c_161])).
% 1.82/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.20  
% 1.82/1.20  Inference rules
% 1.82/1.20  ----------------------
% 1.82/1.20  #Ref     : 0
% 1.82/1.20  #Sup     : 29
% 1.82/1.20  #Fact    : 0
% 1.82/1.20  #Define  : 0
% 1.82/1.20  #Split   : 1
% 1.82/1.20  #Chain   : 0
% 1.82/1.20  #Close   : 0
% 1.82/1.20  
% 1.82/1.20  Ordering : KBO
% 1.82/1.20  
% 1.82/1.20  Simplification rules
% 1.82/1.20  ----------------------
% 1.82/1.20  #Subsume      : 2
% 1.82/1.20  #Demod        : 15
% 1.82/1.20  #Tautology    : 16
% 1.82/1.20  #SimpNegUnit  : 5
% 1.82/1.20  #BackRed      : 3
% 1.82/1.20  
% 1.82/1.20  #Partial instantiations: 0
% 1.82/1.20  #Strategies tried      : 1
% 1.82/1.20  
% 1.82/1.20  Timing (in seconds)
% 1.82/1.20  ----------------------
% 1.82/1.20  Preprocessing        : 0.28
% 1.82/1.20  Parsing              : 0.15
% 1.82/1.20  CNF conversion       : 0.02
% 1.82/1.20  Main loop            : 0.15
% 1.82/1.20  Inferencing          : 0.06
% 1.82/1.20  Reduction            : 0.04
% 1.82/1.20  Demodulation         : 0.03
% 1.82/1.20  BG Simplification    : 0.01
% 1.82/1.20  Subsumption          : 0.02
% 1.82/1.20  Abstraction          : 0.01
% 1.82/1.20  MUC search           : 0.00
% 1.82/1.20  Cooper               : 0.00
% 1.82/1.20  Total                : 0.45
% 1.82/1.20  Index Insertion      : 0.00
% 1.82/1.20  Index Deletion       : 0.00
% 1.82/1.20  Index Matching       : 0.00
% 1.82/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
