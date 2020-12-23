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
% DateTime   : Thu Dec  3 10:28:28 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   24 (  28 expanded)
%              Number of leaves         :   12 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  51 expanded)
%              Number of equality atoms :    2 (   6 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v7_struct_0 > v1_zfmisc_1 > l1_struct_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

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

tff(f_51,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_struct_0(B)
           => ( ( u1_struct_0(A) = u1_struct_0(B)
                & v7_struct_0(A) )
             => v7_struct_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tex_2)).

tff(f_39,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_33,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

tff(c_8,plain,(
    v7_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    ! [A_5] :
      ( v1_zfmisc_1(u1_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | ~ v7_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ~ v7_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_19,plain,(
    ! [A_4] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_4))
      | ~ l1_struct_0(A_4)
      | v7_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_19])).

tff(c_24,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_1'))
    | v7_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_22])).

tff(c_25,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_24])).

tff(c_29,plain,
    ( ~ l1_struct_0('#skF_1')
    | ~ v7_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_25])).

tff(c_39,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14,c_29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.52/1.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.06  
% 1.52/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.06  %$ v7_struct_0 > v1_zfmisc_1 > l1_struct_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_1
% 1.52/1.06  
% 1.52/1.06  %Foreground sorts:
% 1.52/1.06  
% 1.52/1.06  
% 1.52/1.06  %Background operators:
% 1.52/1.06  
% 1.52/1.06  
% 1.52/1.06  %Foreground operators:
% 1.52/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.52/1.06  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 1.52/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.52/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.52/1.06  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.52/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.52/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.52/1.06  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.52/1.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.52/1.06  
% 1.52/1.07  tff(f_51, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (((u1_struct_0(A) = u1_struct_0(B)) & v7_struct_0(A)) => v7_struct_0(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tex_2)).
% 1.52/1.07  tff(f_39, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 1.52/1.07  tff(f_33, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_struct_0)).
% 1.52/1.07  tff(c_8, plain, (v7_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.52/1.07  tff(c_14, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.52/1.07  tff(c_26, plain, (![A_5]: (v1_zfmisc_1(u1_struct_0(A_5)) | ~l1_struct_0(A_5) | ~v7_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.52/1.07  tff(c_6, plain, (~v7_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.52/1.07  tff(c_12, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.52/1.07  tff(c_10, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.52/1.07  tff(c_19, plain, (![A_4]: (~v1_zfmisc_1(u1_struct_0(A_4)) | ~l1_struct_0(A_4) | v7_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.52/1.07  tff(c_22, plain, (~v1_zfmisc_1(u1_struct_0('#skF_1')) | ~l1_struct_0('#skF_2') | v7_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10, c_19])).
% 1.52/1.07  tff(c_24, plain, (~v1_zfmisc_1(u1_struct_0('#skF_1')) | v7_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_22])).
% 1.52/1.07  tff(c_25, plain, (~v1_zfmisc_1(u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_6, c_24])).
% 1.52/1.07  tff(c_29, plain, (~l1_struct_0('#skF_1') | ~v7_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_25])).
% 1.52/1.07  tff(c_39, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_14, c_29])).
% 1.52/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.07  
% 1.52/1.07  Inference rules
% 1.52/1.07  ----------------------
% 1.52/1.07  #Ref     : 0
% 1.52/1.07  #Sup     : 6
% 1.52/1.07  #Fact    : 0
% 1.52/1.07  #Define  : 0
% 1.52/1.07  #Split   : 0
% 1.52/1.07  #Chain   : 0
% 1.52/1.07  #Close   : 0
% 1.52/1.07  
% 1.52/1.07  Ordering : KBO
% 1.52/1.07  
% 1.52/1.07  Simplification rules
% 1.52/1.07  ----------------------
% 1.52/1.07  #Subsume      : 0
% 1.52/1.07  #Demod        : 3
% 1.52/1.07  #Tautology    : 2
% 1.52/1.07  #SimpNegUnit  : 1
% 1.52/1.07  #BackRed      : 0
% 1.52/1.07  
% 1.52/1.07  #Partial instantiations: 0
% 1.52/1.07  #Strategies tried      : 1
% 1.52/1.07  
% 1.52/1.07  Timing (in seconds)
% 1.52/1.07  ----------------------
% 1.52/1.07  Preprocessing        : 0.25
% 1.52/1.07  Parsing              : 0.14
% 1.52/1.07  CNF conversion       : 0.01
% 1.52/1.07  Main loop            : 0.07
% 1.52/1.07  Inferencing          : 0.03
% 1.52/1.07  Reduction            : 0.02
% 1.52/1.07  Demodulation         : 0.02
% 1.52/1.07  BG Simplification    : 0.01
% 1.52/1.07  Subsumption          : 0.01
% 1.52/1.07  Abstraction          : 0.00
% 1.52/1.07  MUC search           : 0.00
% 1.52/1.07  Cooper               : 0.00
% 1.52/1.07  Total                : 0.34
% 1.52/1.08  Index Insertion      : 0.00
% 1.62/1.08  Index Deletion       : 0.00
% 1.62/1.08  Index Matching       : 0.00
% 1.62/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
