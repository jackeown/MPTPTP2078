%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:10 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   46 (  61 expanded)
%              Number of leaves         :   26 (  33 expanded)
%              Depth                    :    5
%              Number of atoms          :   50 (  82 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_55,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_75,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).

tff(f_73,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(c_34,plain,(
    ! [A_39,B_40] :
      ( r2_hidden(A_39,B_40)
      | v1_xboole_0(B_40)
      | ~ m1_subset_1(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_8,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_76,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r2_hidden(C_58,B_57)
      | ~ r2_hidden(C_58,A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_80,plain,(
    ! [C_59] : ~ r2_hidden(C_59,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_76])).

tff(c_95,plain,(
    ! [A_39] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_39,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_34,c_80])).

tff(c_126,plain,(
    ! [A_39] : ~ m1_subset_1(A_39,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_30,plain,(
    ! [A_36] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_127,plain,(
    ! [B_65,A_66] :
      ( m1_subset_1(k1_tarski(B_65),k1_zfmisc_1(A_66))
      | k1_xboole_0 = A_66
      | ~ m1_subset_1(B_65,A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_38,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_130,plain,
    ( k1_zfmisc_1('#skF_2') = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_127,c_38])).

tff(c_136,plain,(
    k1_zfmisc_1('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_130])).

tff(c_145,plain,(
    m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_30])).

tff(c_152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_145])).

tff(c_153,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_154,plain,(
    ! [B_67,A_68] :
      ( m1_subset_1(k1_tarski(B_67),k1_zfmisc_1(A_68))
      | k1_xboole_0 = A_68
      | ~ m1_subset_1(B_67,A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_157,plain,
    ( k1_zfmisc_1('#skF_2') = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_154,c_38])).

tff(c_163,plain,(
    k1_zfmisc_1('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_157])).

tff(c_28,plain,(
    ! [A_35] : ~ v1_xboole_0(k1_zfmisc_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_174,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_28])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_174])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:31:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.28  
% 2.04/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.28  %$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.04/1.28  
% 2.04/1.28  %Foreground sorts:
% 2.04/1.28  
% 2.04/1.28  
% 2.04/1.28  %Background operators:
% 2.04/1.28  
% 2.04/1.28  
% 2.04/1.28  %Foreground operators:
% 2.04/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.04/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.04/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.04/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.04/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.04/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.04/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.04/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.04/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.04/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.04/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.04/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.28  
% 2.04/1.29  tff(f_88, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.04/1.29  tff(f_55, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.04/1.29  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.04/1.29  tff(f_75, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.04/1.29  tff(f_82, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 2.04/1.29  tff(f_97, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_setfam_1)).
% 2.04/1.29  tff(f_73, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.04/1.29  tff(c_34, plain, (![A_39, B_40]: (r2_hidden(A_39, B_40) | v1_xboole_0(B_40) | ~m1_subset_1(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.04/1.29  tff(c_8, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.04/1.29  tff(c_76, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | ~r2_hidden(C_58, B_57) | ~r2_hidden(C_58, A_56))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.04/1.29  tff(c_80, plain, (![C_59]: (~r2_hidden(C_59, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_76])).
% 2.04/1.29  tff(c_95, plain, (![A_39]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_39, k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_80])).
% 2.04/1.29  tff(c_126, plain, (![A_39]: (~m1_subset_1(A_39, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_95])).
% 2.04/1.29  tff(c_30, plain, (![A_36]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.04/1.29  tff(c_127, plain, (![B_65, A_66]: (m1_subset_1(k1_tarski(B_65), k1_zfmisc_1(A_66)) | k1_xboole_0=A_66 | ~m1_subset_1(B_65, A_66))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.04/1.29  tff(c_38, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.04/1.29  tff(c_130, plain, (k1_zfmisc_1('#skF_2')=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_127, c_38])).
% 2.04/1.29  tff(c_136, plain, (k1_zfmisc_1('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_130])).
% 2.04/1.29  tff(c_145, plain, (m1_subset_1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_136, c_30])).
% 2.04/1.29  tff(c_152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_145])).
% 2.04/1.29  tff(c_153, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_95])).
% 2.04/1.29  tff(c_154, plain, (![B_67, A_68]: (m1_subset_1(k1_tarski(B_67), k1_zfmisc_1(A_68)) | k1_xboole_0=A_68 | ~m1_subset_1(B_67, A_68))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.04/1.29  tff(c_157, plain, (k1_zfmisc_1('#skF_2')=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_154, c_38])).
% 2.04/1.29  tff(c_163, plain, (k1_zfmisc_1('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_157])).
% 2.04/1.29  tff(c_28, plain, (![A_35]: (~v1_xboole_0(k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.04/1.29  tff(c_174, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_163, c_28])).
% 2.04/1.29  tff(c_179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_153, c_174])).
% 2.04/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.29  
% 2.04/1.29  Inference rules
% 2.04/1.29  ----------------------
% 2.04/1.29  #Ref     : 0
% 2.04/1.29  #Sup     : 33
% 2.04/1.29  #Fact    : 0
% 2.04/1.29  #Define  : 0
% 2.04/1.29  #Split   : 1
% 2.04/1.29  #Chain   : 0
% 2.04/1.29  #Close   : 0
% 2.04/1.29  
% 2.04/1.29  Ordering : KBO
% 2.04/1.29  
% 2.04/1.29  Simplification rules
% 2.04/1.29  ----------------------
% 2.04/1.29  #Subsume      : 2
% 2.04/1.29  #Demod        : 8
% 2.04/1.29  #Tautology    : 17
% 2.04/1.29  #SimpNegUnit  : 1
% 2.04/1.29  #BackRed      : 3
% 2.04/1.29  
% 2.04/1.29  #Partial instantiations: 0
% 2.04/1.29  #Strategies tried      : 1
% 2.04/1.29  
% 2.04/1.29  Timing (in seconds)
% 2.04/1.29  ----------------------
% 2.04/1.29  Preprocessing        : 0.34
% 2.04/1.29  Parsing              : 0.19
% 2.04/1.29  CNF conversion       : 0.02
% 2.04/1.29  Main loop            : 0.14
% 2.04/1.29  Inferencing          : 0.05
% 2.04/1.29  Reduction            : 0.05
% 2.04/1.29  Demodulation         : 0.03
% 2.04/1.29  BG Simplification    : 0.01
% 2.04/1.29  Subsumption          : 0.02
% 2.04/1.29  Abstraction          : 0.01
% 2.04/1.29  MUC search           : 0.00
% 2.04/1.29  Cooper               : 0.00
% 2.04/1.29  Total                : 0.51
% 2.04/1.29  Index Insertion      : 0.00
% 2.04/1.29  Index Deletion       : 0.00
% 2.04/1.29  Index Matching       : 0.00
% 2.04/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
