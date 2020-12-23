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
% DateTime   : Thu Dec  3 10:28:50 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   39 (  62 expanded)
%              Number of leaves         :   20 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 ( 114 expanded)
%              Number of equality atoms :    3 (  12 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > l1_struct_0 > k6_domain_1 > #nlpp > u1_struct_0 > k2_struct_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
                & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_54,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => ~ ( v1_subset_1(k6_domain_1(A,B),A)
              & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_37,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_18,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_19,plain,(
    ! [A_8] :
      ( u1_struct_0(A_8) = k2_struct_0(A_8)
      | ~ l1_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_23,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_19])).

tff(c_14,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_25,plain,(
    m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23,c_14])).

tff(c_10,plain,(
    v7_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_30,plain,(
    ! [A_10] :
      ( v1_zfmisc_1(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | ~ v7_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_33,plain,
    ( v1_zfmisc_1(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | ~ v7_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_23,c_30])).

tff(c_35,plain,(
    v1_zfmisc_1(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16,c_33])).

tff(c_12,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,(
    v1_subset_1(k6_domain_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23,c_23,c_12])).

tff(c_37,plain,(
    ! [A_11,B_12] :
      ( ~ v1_zfmisc_1(A_11)
      | ~ v1_subset_1(k6_domain_1(A_11,B_12),A_11)
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_40,plain,
    ( ~ v1_zfmisc_1(k2_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_36,c_37])).

tff(c_43,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_35,c_40])).

tff(c_4,plain,(
    ! [A_2] :
      ( ~ v1_xboole_0(k2_struct_0(A_2))
      | ~ l1_struct_0(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_43,c_4])).

tff(c_49,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_46])).

tff(c_51,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:47:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.12  
% 1.63/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.13  %$ v1_subset_1 > m1_subset_1 > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > l1_struct_0 > k6_domain_1 > #nlpp > u1_struct_0 > k2_struct_0 > #skF_2 > #skF_1
% 1.63/1.13  
% 1.63/1.13  %Foreground sorts:
% 1.63/1.13  
% 1.63/1.13  
% 1.63/1.13  %Background operators:
% 1.63/1.13  
% 1.63/1.13  
% 1.63/1.13  %Foreground operators:
% 1.63/1.13  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.63/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.13  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.63/1.13  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 1.63/1.13  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.63/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.13  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.63/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.13  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.63/1.13  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.63/1.13  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 1.63/1.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.63/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.63/1.13  
% 1.63/1.14  tff(f_68, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_tex_2)).
% 1.63/1.14  tff(f_29, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 1.63/1.14  tff(f_43, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 1.63/1.14  tff(f_54, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 1.63/1.14  tff(f_37, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 1.63/1.14  tff(c_18, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.63/1.14  tff(c_16, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.63/1.14  tff(c_19, plain, (![A_8]: (u1_struct_0(A_8)=k2_struct_0(A_8) | ~l1_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.63/1.14  tff(c_23, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_19])).
% 1.63/1.14  tff(c_14, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.63/1.14  tff(c_25, plain, (m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_23, c_14])).
% 1.63/1.14  tff(c_10, plain, (v7_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.63/1.14  tff(c_30, plain, (![A_10]: (v1_zfmisc_1(u1_struct_0(A_10)) | ~l1_struct_0(A_10) | ~v7_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.63/1.14  tff(c_33, plain, (v1_zfmisc_1(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | ~v7_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_23, c_30])).
% 1.63/1.14  tff(c_35, plain, (v1_zfmisc_1(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16, c_33])).
% 1.63/1.14  tff(c_12, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.63/1.14  tff(c_36, plain, (v1_subset_1(k6_domain_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_23, c_23, c_12])).
% 1.63/1.14  tff(c_37, plain, (![A_11, B_12]: (~v1_zfmisc_1(A_11) | ~v1_subset_1(k6_domain_1(A_11, B_12), A_11) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.63/1.14  tff(c_40, plain, (~v1_zfmisc_1(k2_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', k2_struct_0('#skF_1')) | v1_xboole_0(k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_37])).
% 1.63/1.14  tff(c_43, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_25, c_35, c_40])).
% 1.63/1.14  tff(c_4, plain, (![A_2]: (~v1_xboole_0(k2_struct_0(A_2)) | ~l1_struct_0(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.63/1.14  tff(c_46, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_43, c_4])).
% 1.63/1.14  tff(c_49, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_46])).
% 1.63/1.14  tff(c_51, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_49])).
% 1.63/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.14  
% 1.63/1.14  Inference rules
% 1.63/1.14  ----------------------
% 1.63/1.14  #Ref     : 0
% 1.63/1.14  #Sup     : 6
% 1.63/1.14  #Fact    : 0
% 1.63/1.14  #Define  : 0
% 1.63/1.14  #Split   : 0
% 1.63/1.14  #Chain   : 0
% 1.63/1.14  #Close   : 0
% 1.63/1.14  
% 1.63/1.14  Ordering : KBO
% 1.63/1.14  
% 1.63/1.14  Simplification rules
% 1.63/1.14  ----------------------
% 1.63/1.14  #Subsume      : 0
% 1.63/1.14  #Demod        : 8
% 1.63/1.14  #Tautology    : 2
% 1.63/1.14  #SimpNegUnit  : 1
% 1.63/1.14  #BackRed      : 1
% 1.63/1.14  
% 1.63/1.14  #Partial instantiations: 0
% 1.63/1.14  #Strategies tried      : 1
% 1.63/1.14  
% 1.63/1.14  Timing (in seconds)
% 1.63/1.14  ----------------------
% 1.63/1.14  Preprocessing        : 0.28
% 1.63/1.14  Parsing              : 0.15
% 1.63/1.14  CNF conversion       : 0.02
% 1.63/1.14  Main loop            : 0.08
% 1.63/1.14  Inferencing          : 0.04
% 1.63/1.14  Reduction            : 0.03
% 1.63/1.14  Demodulation         : 0.02
% 1.63/1.14  BG Simplification    : 0.01
% 1.63/1.14  Subsumption          : 0.01
% 1.63/1.14  Abstraction          : 0.01
% 1.63/1.14  MUC search           : 0.00
% 1.63/1.14  Cooper               : 0.00
% 1.63/1.14  Total                : 0.39
% 1.63/1.14  Index Insertion      : 0.00
% 1.63/1.14  Index Deletion       : 0.00
% 1.63/1.14  Index Matching       : 0.00
% 1.63/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
