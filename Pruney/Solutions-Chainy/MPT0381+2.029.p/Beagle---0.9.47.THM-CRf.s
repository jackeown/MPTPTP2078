%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:05 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   51 (  68 expanded)
%              Number of leaves         :   28 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   55 (  85 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_51,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_14,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_39,plain,(
    ! [B_30,A_31] :
      ( ~ r2_hidden(B_30,A_31)
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_43,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_39])).

tff(c_90,plain,(
    ! [B_43,A_44] :
      ( m1_subset_1(B_43,A_44)
      | ~ r2_hidden(B_43,A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_96,plain,
    ( m1_subset_1('#skF_3','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_90])).

tff(c_100,plain,(
    m1_subset_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_96])).

tff(c_188,plain,(
    ! [B_62,A_63] :
      ( m1_subset_1(k1_tarski(B_62),k1_zfmisc_1(A_63))
      | k1_xboole_0 = A_63
      | ~ m1_subset_1(B_62,A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_194,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_188,c_34])).

tff(c_198,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_194])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_73,plain,(
    ! [A_38,B_39] :
      ( k3_xboole_0(A_38,B_39) = A_38
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_77,plain,(
    ! [A_12] : k3_xboole_0(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_73])).

tff(c_119,plain,(
    ! [A_48,B_49,C_50] :
      ( ~ r1_xboole_0(A_48,B_49)
      | ~ r2_hidden(C_50,k3_xboole_0(A_48,B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_126,plain,(
    ! [A_12,C_50] :
      ( ~ r1_xboole_0(k1_xboole_0,A_12)
      | ~ r2_hidden(C_50,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_119])).

tff(c_134,plain,(
    ! [C_51] : ~ r2_hidden(C_51,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_144,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_134])).

tff(c_201,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_144])).

tff(c_207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_201])).

tff(c_209,plain,(
    ! [A_64] : ~ r1_xboole_0(k1_xboole_0,A_64) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_214,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_14,c_209])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.22  
% 2.15/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.23  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.15/1.23  
% 2.15/1.23  %Foreground sorts:
% 2.15/1.23  
% 2.15/1.23  
% 2.15/1.23  %Background operators:
% 2.15/1.23  
% 2.15/1.23  
% 2.15/1.23  %Foreground operators:
% 2.15/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.15/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.15/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.15/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.15/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.15/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.15/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.23  
% 2.23/1.24  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.23/1.24  tff(f_86, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.23/1.24  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.23/1.24  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.23/1.24  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 2.23/1.24  tff(f_51, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.23/1.24  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.23/1.24  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.23/1.24  tff(c_14, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.23/1.24  tff(c_36, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.23/1.24  tff(c_39, plain, (![B_30, A_31]: (~r2_hidden(B_30, A_31) | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.24  tff(c_43, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_39])).
% 2.23/1.24  tff(c_90, plain, (![B_43, A_44]: (m1_subset_1(B_43, A_44) | ~r2_hidden(B_43, A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.23/1.24  tff(c_96, plain, (m1_subset_1('#skF_3', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_90])).
% 2.23/1.24  tff(c_100, plain, (m1_subset_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_43, c_96])).
% 2.23/1.24  tff(c_188, plain, (![B_62, A_63]: (m1_subset_1(k1_tarski(B_62), k1_zfmisc_1(A_63)) | k1_xboole_0=A_63 | ~m1_subset_1(B_62, A_63))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.23/1.24  tff(c_34, plain, (~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.23/1.24  tff(c_194, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_188, c_34])).
% 2.23/1.24  tff(c_198, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_194])).
% 2.23/1.24  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.24  tff(c_12, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.23/1.24  tff(c_73, plain, (![A_38, B_39]: (k3_xboole_0(A_38, B_39)=A_38 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.23/1.24  tff(c_77, plain, (![A_12]: (k3_xboole_0(k1_xboole_0, A_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_73])).
% 2.23/1.24  tff(c_119, plain, (![A_48, B_49, C_50]: (~r1_xboole_0(A_48, B_49) | ~r2_hidden(C_50, k3_xboole_0(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.23/1.24  tff(c_126, plain, (![A_12, C_50]: (~r1_xboole_0(k1_xboole_0, A_12) | ~r2_hidden(C_50, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_77, c_119])).
% 2.23/1.24  tff(c_134, plain, (![C_51]: (~r2_hidden(C_51, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_126])).
% 2.23/1.24  tff(c_144, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_134])).
% 2.23/1.24  tff(c_201, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_144])).
% 2.23/1.24  tff(c_207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_201])).
% 2.23/1.24  tff(c_209, plain, (![A_64]: (~r1_xboole_0(k1_xboole_0, A_64))), inference(splitRight, [status(thm)], [c_126])).
% 2.23/1.24  tff(c_214, plain, $false, inference(resolution, [status(thm)], [c_14, c_209])).
% 2.23/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.24  
% 2.23/1.24  Inference rules
% 2.23/1.24  ----------------------
% 2.23/1.24  #Ref     : 0
% 2.23/1.24  #Sup     : 34
% 2.23/1.24  #Fact    : 0
% 2.23/1.24  #Define  : 0
% 2.23/1.24  #Split   : 2
% 2.23/1.24  #Chain   : 0
% 2.23/1.24  #Close   : 0
% 2.23/1.24  
% 2.23/1.24  Ordering : KBO
% 2.23/1.24  
% 2.23/1.24  Simplification rules
% 2.23/1.24  ----------------------
% 2.23/1.24  #Subsume      : 1
% 2.23/1.24  #Demod        : 13
% 2.23/1.24  #Tautology    : 18
% 2.23/1.24  #SimpNegUnit  : 3
% 2.23/1.24  #BackRed      : 7
% 2.23/1.24  
% 2.23/1.24  #Partial instantiations: 0
% 2.23/1.24  #Strategies tried      : 1
% 2.23/1.24  
% 2.23/1.24  Timing (in seconds)
% 2.23/1.24  ----------------------
% 2.23/1.24  Preprocessing        : 0.31
% 2.23/1.24  Parsing              : 0.16
% 2.23/1.24  CNF conversion       : 0.02
% 2.23/1.24  Main loop            : 0.16
% 2.23/1.24  Inferencing          : 0.06
% 2.23/1.24  Reduction            : 0.05
% 2.23/1.24  Demodulation         : 0.03
% 2.23/1.24  BG Simplification    : 0.02
% 2.23/1.24  Subsumption          : 0.03
% 2.23/1.24  Abstraction          : 0.01
% 2.23/1.24  MUC search           : 0.00
% 2.23/1.24  Cooper               : 0.00
% 2.23/1.24  Total                : 0.50
% 2.23/1.24  Index Insertion      : 0.00
% 2.23/1.24  Index Deletion       : 0.00
% 2.23/1.24  Index Matching       : 0.00
% 2.23/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
