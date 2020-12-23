%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:43 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   47 (  64 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :   58 ( 104 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_40,plain,(
    ! [A_26,B_27] : k2_xboole_0(A_26,k3_xboole_0(A_26,B_27)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_9,B_10] : k2_xboole_0(k1_tarski(A_9),B_10) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_47,plain,(
    ! [A_9] : k1_tarski(A_9) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_12])).

tff(c_28,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_22,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_26,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_98,plain,(
    ! [A_37,B_38] :
      ( k6_domain_1(A_37,B_38) = k1_tarski(B_38)
      | ~ m1_subset_1(B_38,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_101,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_98])).

tff(c_104,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_101])).

tff(c_24,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_114,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_24])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k6_domain_1(A_14,B_15),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_118,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_16])).

tff(c_122,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_118])).

tff(c_123,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_122])).

tff(c_219,plain,(
    ! [B_45,A_46] :
      ( ~ v1_subset_1(B_45,A_46)
      | v1_xboole_0(B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46))
      | ~ v1_zfmisc_1(A_46)
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_225,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_123,c_219])).

tff(c_234,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_114,c_225])).

tff(c_235,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_234])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_239,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_235,c_2])).

tff(c_243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.21  
% 2.23/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.21  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.23/1.21  
% 2.23/1.21  %Foreground sorts:
% 2.23/1.21  
% 2.23/1.21  
% 2.23/1.21  %Background operators:
% 2.23/1.21  
% 2.23/1.21  
% 2.23/1.21  %Foreground operators:
% 2.23/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.21  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.23/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.23/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.21  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.23/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.21  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.23/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.21  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.23/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.23/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.21  
% 2.23/1.22  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.23/1.22  tff(f_40, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.23/1.22  tff(f_88, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.23/1.22  tff(f_62, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.23/1.22  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.23/1.22  tff(f_76, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.23/1.22  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.23/1.22  tff(c_40, plain, (![A_26, B_27]: (k2_xboole_0(A_26, k3_xboole_0(A_26, B_27))=A_26)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.22  tff(c_12, plain, (![A_9, B_10]: (k2_xboole_0(k1_tarski(A_9), B_10)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.23/1.22  tff(c_47, plain, (![A_9]: (k1_tarski(A_9)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_12])).
% 2.23/1.22  tff(c_28, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.23/1.22  tff(c_22, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.23/1.22  tff(c_26, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.23/1.22  tff(c_98, plain, (![A_37, B_38]: (k6_domain_1(A_37, B_38)=k1_tarski(B_38) | ~m1_subset_1(B_38, A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.23/1.22  tff(c_101, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_98])).
% 2.23/1.22  tff(c_104, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_28, c_101])).
% 2.23/1.22  tff(c_24, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.23/1.22  tff(c_114, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_24])).
% 2.23/1.22  tff(c_16, plain, (![A_14, B_15]: (m1_subset_1(k6_domain_1(A_14, B_15), k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.23/1.22  tff(c_118, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_104, c_16])).
% 2.23/1.22  tff(c_122, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_118])).
% 2.23/1.22  tff(c_123, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_28, c_122])).
% 2.23/1.22  tff(c_219, plain, (![B_45, A_46]: (~v1_subset_1(B_45, A_46) | v1_xboole_0(B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)) | ~v1_zfmisc_1(A_46) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.23/1.22  tff(c_225, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k1_tarski('#skF_2')) | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_123, c_219])).
% 2.23/1.22  tff(c_234, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_114, c_225])).
% 2.23/1.22  tff(c_235, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_28, c_234])).
% 2.23/1.22  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.22  tff(c_239, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_235, c_2])).
% 2.23/1.22  tff(c_243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_239])).
% 2.23/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.22  
% 2.23/1.22  Inference rules
% 2.23/1.22  ----------------------
% 2.23/1.22  #Ref     : 0
% 2.23/1.22  #Sup     : 45
% 2.23/1.22  #Fact    : 0
% 2.23/1.22  #Define  : 0
% 2.23/1.22  #Split   : 1
% 2.23/1.22  #Chain   : 0
% 2.23/1.22  #Close   : 0
% 2.23/1.22  
% 2.23/1.22  Ordering : KBO
% 2.23/1.22  
% 2.23/1.22  Simplification rules
% 2.23/1.22  ----------------------
% 2.23/1.22  #Subsume      : 3
% 2.23/1.22  #Demod        : 14
% 2.23/1.22  #Tautology    : 23
% 2.23/1.22  #SimpNegUnit  : 9
% 2.23/1.22  #BackRed      : 3
% 2.23/1.22  
% 2.23/1.22  #Partial instantiations: 0
% 2.23/1.22  #Strategies tried      : 1
% 2.23/1.22  
% 2.23/1.22  Timing (in seconds)
% 2.23/1.22  ----------------------
% 2.23/1.22  Preprocessing        : 0.30
% 2.23/1.22  Parsing              : 0.16
% 2.23/1.22  CNF conversion       : 0.02
% 2.23/1.22  Main loop            : 0.17
% 2.23/1.22  Inferencing          : 0.07
% 2.23/1.22  Reduction            : 0.05
% 2.23/1.22  Demodulation         : 0.03
% 2.23/1.22  BG Simplification    : 0.01
% 2.23/1.22  Subsumption          : 0.03
% 2.23/1.22  Abstraction          : 0.01
% 2.23/1.22  MUC search           : 0.00
% 2.23/1.22  Cooper               : 0.00
% 2.23/1.22  Total                : 0.50
% 2.23/1.22  Index Insertion      : 0.00
% 2.23/1.22  Index Deletion       : 0.00
% 2.23/1.22  Index Matching       : 0.00
% 2.23/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
