%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:51 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   36 (  50 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  96 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
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

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & ~ v7_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tex_2)).

tff(f_52,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_33,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_41,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

tff(c_14,plain,(
    ~ v7_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_12,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_19,plain,(
    ! [A_9,B_10] :
      ( v1_subset_1(k6_domain_1(A_9,B_10),A_9)
      | ~ m1_subset_1(B_10,A_9)
      | v1_zfmisc_1(A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,
    ( ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_zfmisc_1(u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_19,c_8])).

tff(c_25,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_22])).

tff(c_26,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_25])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v1_xboole_0(u1_struct_0(A_1))
      | ~ l1_struct_0(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_29,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_2])).

tff(c_32,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_29])).

tff(c_34,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_32])).

tff(c_35,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_25])).

tff(c_4,plain,(
    ! [A_2] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_2))
      | ~ l1_struct_0(A_2)
      | v7_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_39,plain,
    ( ~ l1_struct_0('#skF_1')
    | v7_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_35,c_4])).

tff(c_42,plain,(
    v7_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_39])).

tff(c_44,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:53:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.15  
% 1.69/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.17  %$ v1_subset_1 > m1_subset_1 > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > l1_struct_0 > k6_domain_1 > #nlpp > u1_struct_0 > #skF_2 > #skF_1
% 1.74/1.17  
% 1.74/1.17  %Foreground sorts:
% 1.74/1.17  
% 1.74/1.17  
% 1.74/1.17  %Background operators:
% 1.74/1.17  
% 1.74/1.17  
% 1.74/1.17  %Foreground operators:
% 1.74/1.17  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.74/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.17  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.74/1.17  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 1.74/1.17  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.74/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.74/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.74/1.17  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.74/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.17  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.74/1.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.74/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.74/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.74/1.17  
% 1.74/1.18  tff(f_66, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & ~v7_struct_0(A)) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_tex_2)).
% 1.74/1.18  tff(f_52, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tex_2)).
% 1.74/1.18  tff(f_33, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.74/1.18  tff(f_41, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_struct_0)).
% 1.74/1.18  tff(c_14, plain, (~v7_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.74/1.18  tff(c_12, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.74/1.18  tff(c_16, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.74/1.18  tff(c_10, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.74/1.18  tff(c_19, plain, (![A_9, B_10]: (v1_subset_1(k6_domain_1(A_9, B_10), A_9) | ~m1_subset_1(B_10, A_9) | v1_zfmisc_1(A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.74/1.18  tff(c_8, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.74/1.18  tff(c_22, plain, (~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | v1_zfmisc_1(u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_19, c_8])).
% 1.74/1.18  tff(c_25, plain, (v1_zfmisc_1(u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_22])).
% 1.74/1.18  tff(c_26, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_25])).
% 1.74/1.18  tff(c_2, plain, (![A_1]: (~v1_xboole_0(u1_struct_0(A_1)) | ~l1_struct_0(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.74/1.18  tff(c_29, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_2])).
% 1.74/1.18  tff(c_32, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_29])).
% 1.74/1.18  tff(c_34, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_32])).
% 1.74/1.18  tff(c_35, plain, (v1_zfmisc_1(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_25])).
% 1.74/1.18  tff(c_4, plain, (![A_2]: (~v1_zfmisc_1(u1_struct_0(A_2)) | ~l1_struct_0(A_2) | v7_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.74/1.18  tff(c_39, plain, (~l1_struct_0('#skF_1') | v7_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_35, c_4])).
% 1.74/1.18  tff(c_42, plain, (v7_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_39])).
% 1.74/1.18  tff(c_44, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_42])).
% 1.74/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.18  
% 1.74/1.18  Inference rules
% 1.74/1.18  ----------------------
% 1.74/1.18  #Ref     : 0
% 1.74/1.18  #Sup     : 3
% 1.74/1.18  #Fact    : 0
% 1.74/1.18  #Define  : 0
% 1.74/1.18  #Split   : 1
% 1.74/1.18  #Chain   : 0
% 1.74/1.18  #Close   : 0
% 1.74/1.18  
% 1.74/1.18  Ordering : KBO
% 1.74/1.18  
% 1.74/1.18  Simplification rules
% 1.74/1.18  ----------------------
% 1.74/1.18  #Subsume      : 0
% 1.74/1.18  #Demod        : 3
% 1.74/1.18  #Tautology    : 0
% 1.74/1.18  #SimpNegUnit  : 2
% 1.74/1.18  #BackRed      : 0
% 1.74/1.18  
% 1.74/1.18  #Partial instantiations: 0
% 1.74/1.18  #Strategies tried      : 1
% 1.74/1.18  
% 1.74/1.18  Timing (in seconds)
% 1.74/1.18  ----------------------
% 1.74/1.18  Preprocessing        : 0.28
% 1.74/1.18  Parsing              : 0.16
% 1.74/1.18  CNF conversion       : 0.02
% 1.74/1.18  Main loop            : 0.08
% 1.74/1.18  Inferencing          : 0.03
% 1.74/1.18  Reduction            : 0.02
% 1.74/1.18  Demodulation         : 0.02
% 1.74/1.18  BG Simplification    : 0.01
% 1.74/1.18  Subsumption          : 0.01
% 1.74/1.18  Abstraction          : 0.00
% 1.74/1.18  MUC search           : 0.00
% 1.74/1.18  Cooper               : 0.00
% 1.74/1.18  Total                : 0.39
% 1.74/1.18  Index Insertion      : 0.00
% 1.74/1.18  Index Deletion       : 0.00
% 1.74/1.18  Index Matching       : 0.00
% 1.74/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
