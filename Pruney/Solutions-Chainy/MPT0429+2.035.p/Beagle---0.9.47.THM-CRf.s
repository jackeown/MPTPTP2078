%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:10 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   37 (  41 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   42 (  46 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_65,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).

tff(f_47,axiom,(
    ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B)
        & ! [D] :
            ( ( r1_tarski(A,D)
              & r1_tarski(C,D) )
           => r1_tarski(B,D) ) )
     => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_35,plain,(
    ! [A_20,B_21] : k2_xboole_0(k1_tarski(A_20),B_21) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_39,plain,(
    ! [A_20] : k1_tarski(A_20) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_35])).

tff(c_16,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_46,plain,(
    ! [B_28,A_29] :
      ( m1_subset_1(k1_tarski(B_28),k1_zfmisc_1(A_29))
      | k1_xboole_0 = A_29
      | ~ m1_subset_1(B_28,A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_51,plain,
    ( k1_zfmisc_1('#skF_2') = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_22])).

tff(c_55,plain,(
    k1_zfmisc_1('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_51])).

tff(c_14,plain,(
    ! [A_9] : r1_tarski(k1_tarski(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_65,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_14])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_79,plain,(
    ! [B_32,A_33,C_34] :
      ( ~ r1_tarski(B_32,'#skF_1'(A_33,B_32,C_34))
      | k2_xboole_0(A_33,C_34) = B_32
      | ~ r1_tarski(C_34,B_32)
      | ~ r1_tarski(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_186,plain,(
    ! [A_58,C_59] :
      ( k2_xboole_0(A_58,C_59) = k1_xboole_0
      | ~ r1_tarski(C_59,k1_xboole_0)
      | ~ r1_tarski(A_58,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_79])).

tff(c_191,plain,(
    ! [A_58] :
      ( k2_xboole_0(A_58,k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(A_58,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_186])).

tff(c_195,plain,(
    ! [A_60] :
      ( k1_xboole_0 = A_60
      | ~ r1_tarski(A_60,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_191])).

tff(c_198,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_65,c_195])).

tff(c_206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:54:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.20  
% 1.94/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.21  %$ r2_hidden > r1_tarski > m1_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2
% 1.94/1.21  
% 1.94/1.21  %Foreground sorts:
% 1.94/1.21  
% 1.94/1.21  
% 1.94/1.21  %Background operators:
% 1.94/1.21  
% 1.94/1.21  
% 1.94/1.21  %Foreground operators:
% 1.94/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.94/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.94/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.94/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.21  
% 1.94/1.22  tff(f_40, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.94/1.22  tff(f_45, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.94/1.22  tff(f_49, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.94/1.22  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 1.94/1.22  tff(f_65, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_setfam_1)).
% 1.94/1.22  tff(f_47, axiom, (![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 1.94/1.22  tff(f_42, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.94/1.22  tff(f_38, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 1.94/1.22  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.94/1.22  tff(c_35, plain, (![A_20, B_21]: (k2_xboole_0(k1_tarski(A_20), B_21)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.94/1.22  tff(c_39, plain, (![A_20]: (k1_tarski(A_20)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_35])).
% 1.94/1.22  tff(c_16, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.94/1.22  tff(c_46, plain, (![B_28, A_29]: (m1_subset_1(k1_tarski(B_28), k1_zfmisc_1(A_29)) | k1_xboole_0=A_29 | ~m1_subset_1(B_28, A_29))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.94/1.22  tff(c_22, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.94/1.22  tff(c_51, plain, (k1_zfmisc_1('#skF_2')=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_22])).
% 1.94/1.22  tff(c_55, plain, (k1_zfmisc_1('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_51])).
% 1.94/1.22  tff(c_14, plain, (![A_9]: (r1_tarski(k1_tarski(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.94/1.22  tff(c_65, plain, (r1_tarski(k1_tarski('#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_55, c_14])).
% 1.94/1.22  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.94/1.22  tff(c_79, plain, (![B_32, A_33, C_34]: (~r1_tarski(B_32, '#skF_1'(A_33, B_32, C_34)) | k2_xboole_0(A_33, C_34)=B_32 | ~r1_tarski(C_34, B_32) | ~r1_tarski(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.94/1.22  tff(c_186, plain, (![A_58, C_59]: (k2_xboole_0(A_58, C_59)=k1_xboole_0 | ~r1_tarski(C_59, k1_xboole_0) | ~r1_tarski(A_58, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_79])).
% 1.94/1.22  tff(c_191, plain, (![A_58]: (k2_xboole_0(A_58, k1_xboole_0)=k1_xboole_0 | ~r1_tarski(A_58, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_186])).
% 1.94/1.22  tff(c_195, plain, (![A_60]: (k1_xboole_0=A_60 | ~r1_tarski(A_60, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_191])).
% 1.94/1.22  tff(c_198, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_65, c_195])).
% 1.94/1.22  tff(c_206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39, c_198])).
% 1.94/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.22  
% 1.94/1.22  Inference rules
% 1.94/1.22  ----------------------
% 1.94/1.22  #Ref     : 0
% 1.94/1.22  #Sup     : 37
% 1.94/1.22  #Fact    : 0
% 1.94/1.22  #Define  : 0
% 1.94/1.22  #Split   : 1
% 1.94/1.22  #Chain   : 0
% 1.94/1.22  #Close   : 0
% 1.94/1.22  
% 1.94/1.22  Ordering : KBO
% 1.94/1.22  
% 1.94/1.22  Simplification rules
% 1.94/1.22  ----------------------
% 1.94/1.22  #Subsume      : 3
% 1.94/1.22  #Demod        : 25
% 1.94/1.22  #Tautology    : 13
% 1.94/1.22  #SimpNegUnit  : 2
% 1.94/1.22  #BackRed      : 14
% 1.94/1.22  
% 1.94/1.22  #Partial instantiations: 0
% 1.94/1.22  #Strategies tried      : 1
% 1.94/1.22  
% 1.94/1.22  Timing (in seconds)
% 1.94/1.22  ----------------------
% 1.94/1.22  Preprocessing        : 0.27
% 1.94/1.22  Parsing              : 0.15
% 1.94/1.22  CNF conversion       : 0.02
% 1.94/1.22  Main loop            : 0.18
% 1.94/1.22  Inferencing          : 0.08
% 1.94/1.22  Reduction            : 0.05
% 1.94/1.22  Demodulation         : 0.04
% 1.94/1.22  BG Simplification    : 0.01
% 1.94/1.22  Subsumption          : 0.03
% 1.94/1.22  Abstraction          : 0.01
% 1.94/1.22  MUC search           : 0.00
% 1.94/1.22  Cooper               : 0.00
% 1.94/1.22  Total                : 0.48
% 1.94/1.22  Index Insertion      : 0.00
% 1.94/1.22  Index Deletion       : 0.00
% 1.94/1.22  Index Matching       : 0.00
% 1.94/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
