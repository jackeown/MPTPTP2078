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
% DateTime   : Thu Dec  3 10:04:37 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   54 (  73 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   80 ( 123 expanded)
%              Number of equality atoms :   27 (  39 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_32,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0
    | ~ r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_95,plain,(
    ~ r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_38,plain,
    ( r2_hidden('#skF_2',k2_relat_1('#skF_3'))
    | k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_113,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_38])).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_68,plain,(
    ! [A_24,B_25] :
      ( r1_xboole_0(k1_tarski(A_24),B_25)
      | r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    ! [B_25,A_24] :
      ( r1_xboole_0(B_25,k1_tarski(A_24))
      | r2_hidden(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_68,c_2])).

tff(c_176,plain,(
    ! [B_47,A_48] :
      ( k10_relat_1(B_47,A_48) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_47),A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_240,plain,(
    ! [B_59,A_60] :
      ( k10_relat_1(B_59,k1_tarski(A_60)) = k1_xboole_0
      | ~ v1_relat_1(B_59)
      | r2_hidden(A_60,k2_relat_1(B_59)) ) ),
    inference(resolution,[status(thm)],[c_75,c_176])).

tff(c_243,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_240,c_95])).

tff(c_246,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_243])).

tff(c_248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_246])).

tff(c_249,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_14,plain,(
    ! [A_9] :
      ( ~ r1_xboole_0(A_9,A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_76,plain,(
    ! [A_24] :
      ( k1_tarski(A_24) = k1_xboole_0
      | r2_hidden(A_24,k1_tarski(A_24)) ) ),
    inference(resolution,[status(thm)],[c_68,c_14])).

tff(c_250,plain,(
    r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_323,plain,(
    ! [B_76,A_77] :
      ( r1_xboole_0(k2_relat_1(B_76),A_77)
      | k10_relat_1(B_76,A_77) != k1_xboole_0
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_380,plain,(
    ! [A_86,B_87] :
      ( r1_xboole_0(A_86,k2_relat_1(B_87))
      | k10_relat_1(B_87,A_86) != k1_xboole_0
      | ~ v1_relat_1(B_87) ) ),
    inference(resolution,[status(thm)],[c_323,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_616,plain,(
    ! [C_115,B_116,A_117] :
      ( ~ r2_hidden(C_115,k2_relat_1(B_116))
      | ~ r2_hidden(C_115,A_117)
      | k10_relat_1(B_116,A_117) != k1_xboole_0
      | ~ v1_relat_1(B_116) ) ),
    inference(resolution,[status(thm)],[c_380,c_4])).

tff(c_626,plain,(
    ! [A_117] :
      ( ~ r2_hidden('#skF_2',A_117)
      | k10_relat_1('#skF_3',A_117) != k1_xboole_0
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_250,c_616])).

tff(c_633,plain,(
    ! [A_118] :
      ( ~ r2_hidden('#skF_2',A_118)
      | k10_relat_1('#skF_3',A_118) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_626])).

tff(c_653,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0
    | k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_76,c_633])).

tff(c_669,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_653])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( ~ r2_hidden(B_16,A_15)
      | k4_xboole_0(A_15,k1_tarski(B_16)) != A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_709,plain,(
    ! [A_15] :
      ( ~ r2_hidden('#skF_2',A_15)
      | k4_xboole_0(A_15,k1_xboole_0) != A_15 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_669,c_22])).

tff(c_740,plain,(
    ! [A_15] : ~ r2_hidden('#skF_2',A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_709])).

tff(c_748,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_740,c_250])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:47:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/2.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/2.09  
% 3.12/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/2.09  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.12/2.09  
% 3.12/2.09  %Foreground sorts:
% 3.12/2.09  
% 3.12/2.09  
% 3.12/2.09  %Background operators:
% 3.12/2.09  
% 3.12/2.09  
% 3.12/2.09  %Foreground operators:
% 3.12/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/2.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.12/2.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.12/2.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.12/2.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.12/2.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.12/2.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.12/2.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.12/2.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.12/2.09  tff('#skF_2', type, '#skF_2': $i).
% 3.12/2.09  tff('#skF_3', type, '#skF_3': $i).
% 3.12/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/2.09  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.12/2.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.12/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/2.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.12/2.09  
% 3.12/2.11  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.12/2.11  tff(f_89, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 3.12/2.11  tff(f_70, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.12/2.11  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.12/2.11  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 3.12/2.11  tff(f_61, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.12/2.11  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.12/2.11  tff(f_75, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.12/2.11  tff(c_10, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.12/2.11  tff(c_32, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0 | ~r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.12/2.11  tff(c_95, plain, (~r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_32])).
% 3.12/2.11  tff(c_38, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3')) | k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.12/2.11  tff(c_113, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_95, c_38])).
% 3.12/2.11  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.12/2.11  tff(c_68, plain, (![A_24, B_25]: (r1_xboole_0(k1_tarski(A_24), B_25) | r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.12/2.11  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.12/2.11  tff(c_75, plain, (![B_25, A_24]: (r1_xboole_0(B_25, k1_tarski(A_24)) | r2_hidden(A_24, B_25))), inference(resolution, [status(thm)], [c_68, c_2])).
% 3.12/2.11  tff(c_176, plain, (![B_47, A_48]: (k10_relat_1(B_47, A_48)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_47), A_48) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.12/2.11  tff(c_240, plain, (![B_59, A_60]: (k10_relat_1(B_59, k1_tarski(A_60))=k1_xboole_0 | ~v1_relat_1(B_59) | r2_hidden(A_60, k2_relat_1(B_59)))), inference(resolution, [status(thm)], [c_75, c_176])).
% 3.12/2.11  tff(c_243, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_240, c_95])).
% 3.12/2.11  tff(c_246, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_243])).
% 3.12/2.11  tff(c_248, plain, $false, inference(negUnitSimplification, [status(thm)], [c_113, c_246])).
% 3.12/2.11  tff(c_249, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 3.12/2.11  tff(c_14, plain, (![A_9]: (~r1_xboole_0(A_9, A_9) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.12/2.11  tff(c_76, plain, (![A_24]: (k1_tarski(A_24)=k1_xboole_0 | r2_hidden(A_24, k1_tarski(A_24)))), inference(resolution, [status(thm)], [c_68, c_14])).
% 3.12/2.11  tff(c_250, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_32])).
% 3.12/2.11  tff(c_323, plain, (![B_76, A_77]: (r1_xboole_0(k2_relat_1(B_76), A_77) | k10_relat_1(B_76, A_77)!=k1_xboole_0 | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.12/2.11  tff(c_380, plain, (![A_86, B_87]: (r1_xboole_0(A_86, k2_relat_1(B_87)) | k10_relat_1(B_87, A_86)!=k1_xboole_0 | ~v1_relat_1(B_87))), inference(resolution, [status(thm)], [c_323, c_2])).
% 3.12/2.11  tff(c_4, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.12/2.11  tff(c_616, plain, (![C_115, B_116, A_117]: (~r2_hidden(C_115, k2_relat_1(B_116)) | ~r2_hidden(C_115, A_117) | k10_relat_1(B_116, A_117)!=k1_xboole_0 | ~v1_relat_1(B_116))), inference(resolution, [status(thm)], [c_380, c_4])).
% 3.12/2.11  tff(c_626, plain, (![A_117]: (~r2_hidden('#skF_2', A_117) | k10_relat_1('#skF_3', A_117)!=k1_xboole_0 | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_250, c_616])).
% 3.12/2.11  tff(c_633, plain, (![A_118]: (~r2_hidden('#skF_2', A_118) | k10_relat_1('#skF_3', A_118)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_626])).
% 3.12/2.11  tff(c_653, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0 | k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_76, c_633])).
% 3.12/2.11  tff(c_669, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_249, c_653])).
% 3.12/2.11  tff(c_22, plain, (![B_16, A_15]: (~r2_hidden(B_16, A_15) | k4_xboole_0(A_15, k1_tarski(B_16))!=A_15)), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.12/2.11  tff(c_709, plain, (![A_15]: (~r2_hidden('#skF_2', A_15) | k4_xboole_0(A_15, k1_xboole_0)!=A_15)), inference(superposition, [status(thm), theory('equality')], [c_669, c_22])).
% 3.12/2.11  tff(c_740, plain, (![A_15]: (~r2_hidden('#skF_2', A_15))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_709])).
% 3.12/2.11  tff(c_748, plain, $false, inference(negUnitSimplification, [status(thm)], [c_740, c_250])).
% 3.12/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/2.11  
% 3.12/2.11  Inference rules
% 3.12/2.11  ----------------------
% 3.12/2.11  #Ref     : 0
% 3.12/2.11  #Sup     : 161
% 3.12/2.11  #Fact    : 0
% 3.12/2.11  #Define  : 0
% 3.12/2.12  #Split   : 1
% 3.12/2.12  #Chain   : 0
% 3.12/2.12  #Close   : 0
% 3.12/2.12  
% 3.12/2.12  Ordering : KBO
% 3.12/2.12  
% 3.12/2.12  Simplification rules
% 3.12/2.12  ----------------------
% 3.12/2.12  #Subsume      : 52
% 3.12/2.12  #Demod        : 40
% 3.12/2.12  #Tautology    : 57
% 3.12/2.12  #SimpNegUnit  : 11
% 3.12/2.12  #BackRed      : 3
% 3.12/2.12  
% 3.12/2.12  #Partial instantiations: 0
% 3.12/2.12  #Strategies tried      : 1
% 3.12/2.12  
% 3.12/2.12  Timing (in seconds)
% 3.12/2.12  ----------------------
% 3.12/2.12  Preprocessing        : 0.51
% 3.12/2.12  Parsing              : 0.28
% 3.12/2.12  CNF conversion       : 0.03
% 3.12/2.12  Main loop            : 0.56
% 3.12/2.12  Inferencing          : 0.22
% 3.12/2.12  Reduction            : 0.14
% 3.12/2.12  Demodulation         : 0.09
% 3.12/2.12  BG Simplification    : 0.03
% 3.12/2.12  Subsumption          : 0.12
% 3.25/2.12  Abstraction          : 0.04
% 3.25/2.12  MUC search           : 0.00
% 3.25/2.12  Cooper               : 0.00
% 3.25/2.12  Total                : 1.12
% 3.25/2.12  Index Insertion      : 0.00
% 3.25/2.12  Index Deletion       : 0.00
% 3.25/2.12  Index Matching       : 0.00
% 3.25/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
