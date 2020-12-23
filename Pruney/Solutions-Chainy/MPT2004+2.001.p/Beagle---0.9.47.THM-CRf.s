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
% DateTime   : Thu Dec  3 10:31:06 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   19 (  22 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    3
%              Number of atoms          :   14 (  38 expanded)
%              Number of equality atoms :    4 (  10 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > m1_setfam_1 > l1_struct_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_45,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_struct_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
                   => ( ( u1_struct_0(A) = u1_struct_0(B)
                        & C = D
                        & m1_setfam_1(C,u1_struct_0(A)) )
                     => m1_setfam_1(D,u1_struct_0(B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_waybel_9)).

tff(c_6,plain,(
    '#skF_3' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    m1_setfam_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    m1_setfam_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4])).

tff(c_8,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ~ m1_setfam_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_8,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:21:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.09  
% 1.64/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.10  %$ m1_subset_1 > m1_setfam_1 > l1_struct_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.64/1.10  
% 1.64/1.10  %Foreground sorts:
% 1.64/1.10  
% 1.64/1.10  
% 1.64/1.10  %Background operators:
% 1.64/1.10  
% 1.64/1.10  
% 1.64/1.10  %Foreground operators:
% 1.64/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.10  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.10  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 1.64/1.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.64/1.10  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.64/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.10  tff('#skF_4', type, '#skF_4': $i).
% 1.64/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.10  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.64/1.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.64/1.10  
% 1.64/1.10  tff(f_45, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => ((((u1_struct_0(A) = u1_struct_0(B)) & (C = D)) & m1_setfam_1(C, u1_struct_0(A))) => m1_setfam_1(D, u1_struct_0(B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_waybel_9)).
% 1.64/1.10  tff(c_6, plain, ('#skF_3'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.64/1.10  tff(c_4, plain, (m1_setfam_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.64/1.10  tff(c_20, plain, (m1_setfam_1('#skF_4', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4])).
% 1.64/1.10  tff(c_8, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.64/1.10  tff(c_2, plain, (~m1_setfam_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.64/1.10  tff(c_22, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_8, c_2])).
% 1.64/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.10  
% 1.64/1.10  Inference rules
% 1.64/1.10  ----------------------
% 1.64/1.10  #Ref     : 0
% 1.64/1.10  #Sup     : 0
% 1.64/1.10  #Fact    : 0
% 1.64/1.10  #Define  : 0
% 1.64/1.10  #Split   : 0
% 1.64/1.10  #Chain   : 0
% 1.64/1.10  #Close   : 0
% 1.64/1.10  
% 1.64/1.10  Ordering : KBO
% 1.64/1.10  
% 1.64/1.10  Simplification rules
% 1.64/1.10  ----------------------
% 1.64/1.10  #Subsume      : 6
% 1.64/1.10  #Demod        : 6
% 1.64/1.10  #Tautology    : 1
% 1.64/1.10  #SimpNegUnit  : 0
% 1.64/1.10  #BackRed      : 0
% 1.64/1.10  
% 1.64/1.10  #Partial instantiations: 0
% 1.64/1.10  #Strategies tried      : 1
% 1.64/1.10  
% 1.64/1.10  Timing (in seconds)
% 1.64/1.10  ----------------------
% 1.64/1.11  Preprocessing        : 0.28
% 1.64/1.11  Parsing              : 0.15
% 1.64/1.11  CNF conversion       : 0.02
% 1.64/1.11  Main loop            : 0.03
% 1.64/1.11  Inferencing          : 0.00
% 1.64/1.11  Reduction            : 0.02
% 1.64/1.11  Demodulation         : 0.02
% 1.64/1.11  BG Simplification    : 0.01
% 1.64/1.11  Subsumption          : 0.01
% 1.64/1.11  Abstraction          : 0.00
% 1.64/1.11  MUC search           : 0.00
% 1.64/1.11  Cooper               : 0.00
% 1.64/1.11  Total                : 0.33
% 1.64/1.11  Index Insertion      : 0.00
% 1.64/1.11  Index Deletion       : 0.00
% 1.64/1.11  Index Matching       : 0.00
% 1.64/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
