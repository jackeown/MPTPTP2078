%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:50 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   37 (  53 expanded)
%              Number of leaves         :   18 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 ( 103 expanded)
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

tff(f_62,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & ~ v7_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tex_2)).

tff(f_48,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

tff(c_14,plain,(
    ~ v7_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( v1_subset_1(k6_domain_1(A_10,B_11),A_10)
      | ~ m1_subset_1(B_11,A_10)
      | v1_zfmisc_1(A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_27,plain,
    ( ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_zfmisc_1(u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_8])).

tff(c_30,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_27])).

tff(c_31,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_zfmisc_1(A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_8] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v7_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [A_8] :
      ( ~ l1_struct_0(A_8)
      | v7_struct_0(A_8)
      | ~ v1_xboole_0(u1_struct_0(A_8)) ) ),
    inference(resolution,[status(thm)],[c_2,c_18])).

tff(c_34,plain,
    ( ~ l1_struct_0('#skF_1')
    | v7_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_31,c_22])).

tff(c_37,plain,(
    v7_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_34])).

tff(c_39,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_37])).

tff(c_40,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_4,plain,(
    ! [A_2] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_2))
      | ~ l1_struct_0(A_2)
      | v7_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_44,plain,
    ( ~ l1_struct_0('#skF_1')
    | v7_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_4])).

tff(c_47,plain,(
    v7_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_44])).

tff(c_49,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:19:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.07  
% 1.59/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.07  %$ v1_subset_1 > m1_subset_1 > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > l1_struct_0 > k6_domain_1 > #nlpp > u1_struct_0 > #skF_2 > #skF_1
% 1.59/1.07  
% 1.59/1.07  %Foreground sorts:
% 1.59/1.07  
% 1.59/1.07  
% 1.59/1.07  %Background operators:
% 1.59/1.07  
% 1.59/1.07  
% 1.59/1.07  %Foreground operators:
% 1.59/1.07  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.59/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.07  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.59/1.07  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 1.59/1.07  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.59/1.07  tff('#skF_2', type, '#skF_2': $i).
% 1.59/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.07  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.59/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.07  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.59/1.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.59/1.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.59/1.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.59/1.07  
% 1.62/1.08  tff(f_62, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & ~v7_struct_0(A)) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_tex_2)).
% 1.62/1.08  tff(f_48, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tex_2)).
% 1.62/1.08  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 1.62/1.08  tff(f_37, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_struct_0)).
% 1.62/1.08  tff(c_14, plain, (~v7_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.62/1.08  tff(c_12, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.62/1.08  tff(c_10, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.62/1.08  tff(c_24, plain, (![A_10, B_11]: (v1_subset_1(k6_domain_1(A_10, B_11), A_10) | ~m1_subset_1(B_11, A_10) | v1_zfmisc_1(A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.62/1.08  tff(c_8, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.62/1.08  tff(c_27, plain, (~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | v1_zfmisc_1(u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_8])).
% 1.62/1.08  tff(c_30, plain, (v1_zfmisc_1(u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_27])).
% 1.62/1.08  tff(c_31, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_30])).
% 1.62/1.08  tff(c_2, plain, (![A_1]: (v1_zfmisc_1(A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.08  tff(c_18, plain, (![A_8]: (~v1_zfmisc_1(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | v7_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.62/1.08  tff(c_22, plain, (![A_8]: (~l1_struct_0(A_8) | v7_struct_0(A_8) | ~v1_xboole_0(u1_struct_0(A_8)))), inference(resolution, [status(thm)], [c_2, c_18])).
% 1.62/1.08  tff(c_34, plain, (~l1_struct_0('#skF_1') | v7_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_31, c_22])).
% 1.62/1.08  tff(c_37, plain, (v7_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_34])).
% 1.62/1.08  tff(c_39, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_37])).
% 1.62/1.08  tff(c_40, plain, (v1_zfmisc_1(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_30])).
% 1.62/1.08  tff(c_4, plain, (![A_2]: (~v1_zfmisc_1(u1_struct_0(A_2)) | ~l1_struct_0(A_2) | v7_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.62/1.08  tff(c_44, plain, (~l1_struct_0('#skF_1') | v7_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_4])).
% 1.62/1.08  tff(c_47, plain, (v7_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_44])).
% 1.62/1.08  tff(c_49, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_47])).
% 1.62/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.08  
% 1.62/1.08  Inference rules
% 1.62/1.08  ----------------------
% 1.62/1.08  #Ref     : 0
% 1.62/1.08  #Sup     : 4
% 1.62/1.08  #Fact    : 0
% 1.62/1.08  #Define  : 0
% 1.62/1.08  #Split   : 1
% 1.62/1.08  #Chain   : 0
% 1.62/1.08  #Close   : 0
% 1.62/1.08  
% 1.62/1.08  Ordering : KBO
% 1.62/1.08  
% 1.62/1.08  Simplification rules
% 1.62/1.08  ----------------------
% 1.62/1.08  #Subsume      : 0
% 1.62/1.08  #Demod        : 3
% 1.62/1.08  #Tautology    : 0
% 1.62/1.08  #SimpNegUnit  : 2
% 1.62/1.08  #BackRed      : 0
% 1.62/1.08  
% 1.62/1.08  #Partial instantiations: 0
% 1.62/1.08  #Strategies tried      : 1
% 1.62/1.08  
% 1.62/1.08  Timing (in seconds)
% 1.62/1.08  ----------------------
% 1.62/1.09  Preprocessing        : 0.24
% 1.62/1.09  Parsing              : 0.13
% 1.62/1.09  CNF conversion       : 0.02
% 1.62/1.09  Main loop            : 0.10
% 1.62/1.09  Inferencing          : 0.04
% 1.62/1.09  Reduction            : 0.02
% 1.62/1.09  Demodulation         : 0.02
% 1.62/1.09  BG Simplification    : 0.01
% 1.62/1.09  Subsumption          : 0.01
% 1.62/1.09  Abstraction          : 0.00
% 1.62/1.09  MUC search           : 0.00
% 1.62/1.09  Cooper               : 0.00
% 1.62/1.09  Total                : 0.36
% 1.62/1.09  Index Insertion      : 0.00
% 1.62/1.09  Index Deletion       : 0.00
% 1.62/1.09  Index Matching       : 0.00
% 1.62/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
