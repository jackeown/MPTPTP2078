%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:51 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   41 (  64 expanded)
%              Number of leaves         :   20 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   53 ( 118 expanded)
%              Number of equality atoms :    3 (  12 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & ~ v7_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_45,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_37,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_18,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_16,plain,(
    ~ v7_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_19,plain,(
    ! [A_8] :
      ( u1_struct_0(A_8) = k2_struct_0(A_8)
      | ~ l1_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_23,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_19])).

tff(c_6,plain,(
    ! [A_3] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_3))
      | ~ l1_struct_0(A_3)
      | v7_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_29,plain,
    ( ~ v1_zfmisc_1(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v7_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_23,c_6])).

tff(c_33,plain,
    ( ~ v1_zfmisc_1(k2_struct_0('#skF_1'))
    | v7_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_29])).

tff(c_34,plain,(
    ~ v1_zfmisc_1(k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_33])).

tff(c_12,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_25,plain,(
    m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23,c_12])).

tff(c_38,plain,(
    ! [A_11,B_12] :
      ( v1_subset_1(k6_domain_1(A_11,B_12),A_11)
      | ~ m1_subset_1(B_12,A_11)
      | v1_zfmisc_1(A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_36,plain,(
    ~ v1_subset_1(k6_domain_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23,c_23,c_10])).

tff(c_41,plain,
    ( ~ m1_subset_1('#skF_2',k2_struct_0('#skF_1'))
    | v1_zfmisc_1(k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_38,c_36])).

tff(c_44,plain,
    ( v1_zfmisc_1(k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_41])).

tff(c_45,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_44])).

tff(c_4,plain,(
    ! [A_2] :
      ( ~ v1_xboole_0(k2_struct_0(A_2))
      | ~ l1_struct_0(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_48,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_45,c_4])).

tff(c_51,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_48])).

tff(c_53,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n023.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 14:11:36 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.16/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.17  
% 1.70/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.18  %$ v1_subset_1 > m1_subset_1 > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > l1_struct_0 > k6_domain_1 > #nlpp > u1_struct_0 > k2_struct_0 > #skF_2 > #skF_1
% 1.70/1.18  
% 1.70/1.18  %Foreground sorts:
% 1.70/1.18  
% 1.70/1.18  
% 1.70/1.18  %Background operators:
% 1.70/1.18  
% 1.70/1.18  
% 1.70/1.18  %Foreground operators:
% 1.70/1.18  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.70/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.18  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.70/1.18  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 1.70/1.18  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.70/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.70/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.70/1.18  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.70/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.18  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.70/1.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.70/1.18  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 1.70/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.70/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.70/1.18  
% 1.70/1.19  tff(f_70, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & ~v7_struct_0(A)) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_tex_2)).
% 1.70/1.19  tff(f_29, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 1.70/1.19  tff(f_45, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_struct_0)).
% 1.70/1.19  tff(f_56, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tex_2)).
% 1.70/1.19  tff(f_37, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 1.70/1.19  tff(c_18, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.70/1.19  tff(c_14, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.70/1.19  tff(c_16, plain, (~v7_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.70/1.19  tff(c_19, plain, (![A_8]: (u1_struct_0(A_8)=k2_struct_0(A_8) | ~l1_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.70/1.19  tff(c_23, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_14, c_19])).
% 1.70/1.19  tff(c_6, plain, (![A_3]: (~v1_zfmisc_1(u1_struct_0(A_3)) | ~l1_struct_0(A_3) | v7_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.70/1.19  tff(c_29, plain, (~v1_zfmisc_1(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v7_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_23, c_6])).
% 1.70/1.19  tff(c_33, plain, (~v1_zfmisc_1(k2_struct_0('#skF_1')) | v7_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_29])).
% 1.70/1.19  tff(c_34, plain, (~v1_zfmisc_1(k2_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_16, c_33])).
% 1.70/1.19  tff(c_12, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.70/1.19  tff(c_25, plain, (m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_23, c_12])).
% 1.70/1.19  tff(c_38, plain, (![A_11, B_12]: (v1_subset_1(k6_domain_1(A_11, B_12), A_11) | ~m1_subset_1(B_12, A_11) | v1_zfmisc_1(A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.70/1.19  tff(c_10, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.70/1.19  tff(c_36, plain, (~v1_subset_1(k6_domain_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_23, c_23, c_10])).
% 1.70/1.19  tff(c_41, plain, (~m1_subset_1('#skF_2', k2_struct_0('#skF_1')) | v1_zfmisc_1(k2_struct_0('#skF_1')) | v1_xboole_0(k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_36])).
% 1.70/1.19  tff(c_44, plain, (v1_zfmisc_1(k2_struct_0('#skF_1')) | v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_25, c_41])).
% 1.70/1.19  tff(c_45, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_34, c_44])).
% 1.70/1.19  tff(c_4, plain, (![A_2]: (~v1_xboole_0(k2_struct_0(A_2)) | ~l1_struct_0(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.70/1.19  tff(c_48, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_45, c_4])).
% 1.70/1.19  tff(c_51, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_48])).
% 1.70/1.19  tff(c_53, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_51])).
% 1.70/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.19  
% 1.70/1.19  Inference rules
% 1.70/1.19  ----------------------
% 1.70/1.19  #Ref     : 0
% 1.70/1.19  #Sup     : 6
% 1.70/1.19  #Fact    : 0
% 1.70/1.19  #Define  : 0
% 1.70/1.19  #Split   : 0
% 1.70/1.19  #Chain   : 0
% 1.70/1.19  #Close   : 0
% 1.70/1.19  
% 1.70/1.19  Ordering : KBO
% 1.70/1.19  
% 1.70/1.19  Simplification rules
% 1.70/1.19  ----------------------
% 1.70/1.19  #Subsume      : 0
% 1.70/1.19  #Demod        : 6
% 1.70/1.19  #Tautology    : 2
% 1.70/1.19  #SimpNegUnit  : 3
% 1.70/1.19  #BackRed      : 1
% 1.70/1.19  
% 1.70/1.19  #Partial instantiations: 0
% 1.70/1.19  #Strategies tried      : 1
% 1.70/1.19  
% 1.70/1.19  Timing (in seconds)
% 1.70/1.19  ----------------------
% 1.70/1.19  Preprocessing        : 0.28
% 1.70/1.19  Parsing              : 0.15
% 1.70/1.19  CNF conversion       : 0.02
% 1.70/1.19  Main loop            : 0.08
% 1.70/1.19  Inferencing          : 0.03
% 1.70/1.19  Reduction            : 0.02
% 1.70/1.19  Demodulation         : 0.02
% 1.70/1.19  BG Simplification    : 0.01
% 1.70/1.19  Subsumption          : 0.01
% 1.70/1.19  Abstraction          : 0.01
% 1.70/1.19  MUC search           : 0.00
% 1.70/1.19  Cooper               : 0.00
% 1.70/1.19  Total                : 0.38
% 1.70/1.19  Index Insertion      : 0.00
% 1.70/1.19  Index Deletion       : 0.00
% 1.70/1.19  Index Matching       : 0.00
% 1.70/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
