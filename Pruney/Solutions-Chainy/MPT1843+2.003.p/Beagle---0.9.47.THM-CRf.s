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

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   35 (  49 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 (  95 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > l1_struct_0 > k6_domain_1 > #nlpp > u1_struct_0 > #skF_2 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
                & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_39,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_50,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => ~ ( v1_subset_1(k6_domain_1(A,B),A)
              & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_33,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_16,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    v7_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_2] :
      ( v1_zfmisc_1(u1_struct_0(A_2))
      | ~ l1_struct_0(A_2)
      | ~ v7_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_19,plain,(
    ! [A_9,B_10] :
      ( ~ v1_zfmisc_1(A_9)
      | ~ v1_subset_1(k6_domain_1(A_9,B_10),A_9)
      | ~ m1_subset_1(B_10,A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_22,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_19])).

tff(c_25,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_22])).

tff(c_26,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_25])).

tff(c_29,plain,
    ( ~ l1_struct_0('#skF_1')
    | ~ v7_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_26])).

tff(c_33,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14,c_29])).

tff(c_34,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_25])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v1_xboole_0(u1_struct_0(A_1))
      | ~ l1_struct_0(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_2])).

tff(c_41,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_38])).

tff(c_43,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:18:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.10  
% 1.64/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.10  %$ v1_subset_1 > m1_subset_1 > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > l1_struct_0 > k6_domain_1 > #nlpp > u1_struct_0 > #skF_2 > #skF_1
% 1.64/1.10  
% 1.64/1.10  %Foreground sorts:
% 1.64/1.10  
% 1.64/1.10  
% 1.64/1.10  %Background operators:
% 1.64/1.10  
% 1.64/1.10  
% 1.64/1.10  %Foreground operators:
% 1.64/1.10  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.64/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.10  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.64/1.10  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 1.64/1.10  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.64/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.10  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.64/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.10  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.64/1.10  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.64/1.10  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.64/1.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.64/1.10  
% 1.64/1.11  tff(f_64, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_tex_2)).
% 1.64/1.11  tff(f_39, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 1.64/1.11  tff(f_50, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 1.64/1.11  tff(f_33, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.64/1.11  tff(c_16, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.64/1.11  tff(c_14, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.64/1.11  tff(c_8, plain, (v7_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.64/1.11  tff(c_4, plain, (![A_2]: (v1_zfmisc_1(u1_struct_0(A_2)) | ~l1_struct_0(A_2) | ~v7_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.64/1.11  tff(c_12, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.64/1.11  tff(c_10, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.64/1.11  tff(c_19, plain, (![A_9, B_10]: (~v1_zfmisc_1(A_9) | ~v1_subset_1(k6_domain_1(A_9, B_10), A_9) | ~m1_subset_1(B_10, A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.64/1.11  tff(c_22, plain, (~v1_zfmisc_1(u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_19])).
% 1.64/1.11  tff(c_25, plain, (~v1_zfmisc_1(u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_22])).
% 1.64/1.11  tff(c_26, plain, (~v1_zfmisc_1(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_25])).
% 1.64/1.11  tff(c_29, plain, (~l1_struct_0('#skF_1') | ~v7_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_4, c_26])).
% 1.64/1.11  tff(c_33, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_14, c_29])).
% 1.64/1.11  tff(c_34, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_25])).
% 1.64/1.11  tff(c_2, plain, (![A_1]: (~v1_xboole_0(u1_struct_0(A_1)) | ~l1_struct_0(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.64/1.11  tff(c_38, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_2])).
% 1.64/1.11  tff(c_41, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_38])).
% 1.64/1.11  tff(c_43, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_41])).
% 1.64/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.11  
% 1.64/1.11  Inference rules
% 1.64/1.11  ----------------------
% 1.64/1.11  #Ref     : 0
% 1.64/1.11  #Sup     : 3
% 1.64/1.11  #Fact    : 0
% 1.64/1.11  #Define  : 0
% 1.64/1.11  #Split   : 1
% 1.64/1.11  #Chain   : 0
% 1.64/1.11  #Close   : 0
% 1.64/1.11  
% 1.64/1.11  Ordering : KBO
% 1.64/1.11  
% 1.64/1.11  Simplification rules
% 1.64/1.11  ----------------------
% 1.64/1.11  #Subsume      : 0
% 1.64/1.11  #Demod        : 4
% 1.64/1.11  #Tautology    : 0
% 1.64/1.11  #SimpNegUnit  : 1
% 1.64/1.11  #BackRed      : 0
% 1.64/1.11  
% 1.64/1.11  #Partial instantiations: 0
% 1.64/1.11  #Strategies tried      : 1
% 1.64/1.11  
% 1.64/1.11  Timing (in seconds)
% 1.64/1.11  ----------------------
% 1.64/1.11  Preprocessing        : 0.26
% 1.64/1.11  Parsing              : 0.15
% 1.64/1.11  CNF conversion       : 0.02
% 1.64/1.11  Main loop            : 0.09
% 1.64/1.11  Inferencing          : 0.04
% 1.64/1.11  Reduction            : 0.02
% 1.64/1.11  Demodulation         : 0.02
% 1.64/1.11  BG Simplification    : 0.01
% 1.64/1.11  Subsumption          : 0.01
% 1.64/1.11  Abstraction          : 0.00
% 1.64/1.11  MUC search           : 0.00
% 1.64/1.11  Cooper               : 0.00
% 1.64/1.11  Total                : 0.37
% 1.64/1.11  Index Insertion      : 0.00
% 1.64/1.11  Index Deletion       : 0.00
% 1.64/1.11  Index Matching       : 0.00
% 1.64/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
