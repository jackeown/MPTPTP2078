%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:39 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   33 (  53 expanded)
%              Number of leaves         :   13 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   46 ( 109 expanded)
%              Number of equality atoms :   30 (  81 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_setfam_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( ~ ( B != k1_xboole_0
              & k7_setfam_1(A,B) = k1_xboole_0 )
          & ~ ( k7_setfam_1(A,B) != k1_xboole_0
              & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tops_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ~ ( B != k1_xboole_0
          & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

tff(c_10,plain,
    ( k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_17,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_10])).

tff(c_16,plain,
    ( k1_xboole_0 != '#skF_2'
    | k7_setfam_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_23,plain,(
    k7_setfam_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17,c_17,c_16])).

tff(c_8,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30,plain,(
    ! [A_9,B_10] :
      ( k7_setfam_1(A_9,k7_setfam_1(A_9,B_10)) = B_10
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k1_zfmisc_1(A_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_33,plain,(
    k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_30])).

tff(c_38,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k7_setfam_1(A_11,B_12),k1_zfmisc_1(k1_zfmisc_1(A_11)))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(k1_zfmisc_1(A_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k7_setfam_1(A_5,B_6) != k1_xboole_0
      | k1_xboole_0 = B_6
      | ~ m1_subset_1(B_6,k1_zfmisc_1(k1_zfmisc_1(A_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24,plain,(
    ! [A_5,B_6] :
      ( k7_setfam_1(A_5,B_6) != '#skF_2'
      | B_6 = '#skF_2'
      | ~ m1_subset_1(B_6,k1_zfmisc_1(k1_zfmisc_1(A_5))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17,c_17,c_6])).

tff(c_58,plain,(
    ! [A_15,B_16] :
      ( k7_setfam_1(A_15,k7_setfam_1(A_15,B_16)) != '#skF_2'
      | k7_setfam_1(A_15,B_16) = '#skF_2'
      | ~ m1_subset_1(B_16,k1_zfmisc_1(k1_zfmisc_1(A_15))) ) ),
    inference(resolution,[status(thm)],[c_38,c_24])).

tff(c_62,plain,
    ( k7_setfam_1('#skF_1','#skF_2') = '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_58])).

tff(c_66,plain,(
    k7_setfam_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_62])).

tff(c_68,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23,c_66])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_69,plain,(
    k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_77,plain,(
    ! [A_17,B_18] :
      ( k7_setfam_1(A_17,B_18) != k1_xboole_0
      | k1_xboole_0 = B_18
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k1_zfmisc_1(A_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_80,plain,
    ( k7_setfam_1('#skF_1','#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_77])).

tff(c_83,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_80])).

tff(c_85,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_83])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 19:20:51 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.14  
% 1.81/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.14  %$ m1_subset_1 > k7_setfam_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.81/1.14  
% 1.81/1.14  %Foreground sorts:
% 1.81/1.14  
% 1.81/1.14  
% 1.81/1.14  %Background operators:
% 1.81/1.14  
% 1.81/1.14  
% 1.81/1.14  %Foreground operators:
% 1.81/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.14  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 1.81/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.81/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.81/1.14  
% 1.81/1.15  tff(f_56, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)) & ~(~(k7_setfam_1(A, B) = k1_xboole_0) & (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tops_2)).
% 1.81/1.15  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 1.81/1.15  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 1.81/1.15  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 1.81/1.15  tff(c_10, plain, (k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.81/1.15  tff(c_17, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_10])).
% 1.81/1.15  tff(c_16, plain, (k1_xboole_0!='#skF_2' | k7_setfam_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.81/1.15  tff(c_23, plain, (k7_setfam_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_17, c_17, c_16])).
% 1.81/1.15  tff(c_8, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.81/1.15  tff(c_30, plain, (![A_9, B_10]: (k7_setfam_1(A_9, k7_setfam_1(A_9, B_10))=B_10 | ~m1_subset_1(B_10, k1_zfmisc_1(k1_zfmisc_1(A_9))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.81/1.15  tff(c_33, plain, (k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_8, c_30])).
% 1.81/1.15  tff(c_38, plain, (![A_11, B_12]: (m1_subset_1(k7_setfam_1(A_11, B_12), k1_zfmisc_1(k1_zfmisc_1(A_11))) | ~m1_subset_1(B_12, k1_zfmisc_1(k1_zfmisc_1(A_11))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.81/1.15  tff(c_6, plain, (![A_5, B_6]: (k7_setfam_1(A_5, B_6)!=k1_xboole_0 | k1_xboole_0=B_6 | ~m1_subset_1(B_6, k1_zfmisc_1(k1_zfmisc_1(A_5))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.81/1.15  tff(c_24, plain, (![A_5, B_6]: (k7_setfam_1(A_5, B_6)!='#skF_2' | B_6='#skF_2' | ~m1_subset_1(B_6, k1_zfmisc_1(k1_zfmisc_1(A_5))))), inference(demodulation, [status(thm), theory('equality')], [c_17, c_17, c_6])).
% 1.81/1.15  tff(c_58, plain, (![A_15, B_16]: (k7_setfam_1(A_15, k7_setfam_1(A_15, B_16))!='#skF_2' | k7_setfam_1(A_15, B_16)='#skF_2' | ~m1_subset_1(B_16, k1_zfmisc_1(k1_zfmisc_1(A_15))))), inference(resolution, [status(thm)], [c_38, c_24])).
% 1.81/1.15  tff(c_62, plain, (k7_setfam_1('#skF_1', '#skF_2')='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_33, c_58])).
% 1.81/1.15  tff(c_66, plain, (k7_setfam_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_62])).
% 1.81/1.15  tff(c_68, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23, c_66])).
% 1.81/1.15  tff(c_70, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_10])).
% 1.81/1.15  tff(c_69, plain, (k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_10])).
% 1.81/1.15  tff(c_77, plain, (![A_17, B_18]: (k7_setfam_1(A_17, B_18)!=k1_xboole_0 | k1_xboole_0=B_18 | ~m1_subset_1(B_18, k1_zfmisc_1(k1_zfmisc_1(A_17))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.81/1.15  tff(c_80, plain, (k7_setfam_1('#skF_1', '#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_8, c_77])).
% 1.81/1.15  tff(c_83, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_69, c_80])).
% 1.81/1.15  tff(c_85, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_83])).
% 1.81/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.15  
% 1.81/1.15  Inference rules
% 1.81/1.15  ----------------------
% 1.81/1.15  #Ref     : 0
% 1.81/1.15  #Sup     : 16
% 1.81/1.15  #Fact    : 0
% 1.81/1.15  #Define  : 0
% 1.81/1.15  #Split   : 1
% 1.81/1.15  #Chain   : 0
% 1.81/1.15  #Close   : 0
% 1.81/1.15  
% 1.81/1.15  Ordering : KBO
% 1.81/1.15  
% 1.81/1.15  Simplification rules
% 1.81/1.15  ----------------------
% 1.81/1.15  #Subsume      : 3
% 1.81/1.15  #Demod        : 10
% 1.81/1.15  #Tautology    : 10
% 1.81/1.15  #SimpNegUnit  : 2
% 1.81/1.15  #BackRed      : 0
% 1.81/1.15  
% 1.81/1.15  #Partial instantiations: 0
% 1.81/1.15  #Strategies tried      : 1
% 1.81/1.15  
% 1.81/1.15  Timing (in seconds)
% 1.81/1.15  ----------------------
% 1.81/1.15  Preprocessing        : 0.28
% 1.81/1.15  Parsing              : 0.16
% 1.81/1.15  CNF conversion       : 0.02
% 1.81/1.15  Main loop            : 0.10
% 1.81/1.15  Inferencing          : 0.04
% 1.81/1.15  Reduction            : 0.03
% 1.81/1.15  Demodulation         : 0.02
% 1.81/1.15  BG Simplification    : 0.01
% 1.81/1.15  Subsumption          : 0.02
% 1.81/1.15  Abstraction          : 0.01
% 1.81/1.15  MUC search           : 0.00
% 1.81/1.15  Cooper               : 0.00
% 1.81/1.15  Total                : 0.40
% 1.81/1.15  Index Insertion      : 0.00
% 1.81/1.15  Index Deletion       : 0.00
% 1.81/1.15  Index Matching       : 0.00
% 1.81/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
