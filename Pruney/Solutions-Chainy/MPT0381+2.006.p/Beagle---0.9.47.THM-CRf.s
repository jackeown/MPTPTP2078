%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:02 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   49 (  58 expanded)
%              Number of leaves         :   28 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   55 (  70 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
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

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_57,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
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

tff(c_40,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_44,plain,(
    ! [B_31,A_32] :
      ( ~ r2_hidden(B_31,A_32)
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_44])).

tff(c_144,plain,(
    ! [B_55,A_56] :
      ( m1_subset_1(B_55,A_56)
      | ~ r2_hidden(B_55,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_153,plain,
    ( m1_subset_1('#skF_3','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_144])).

tff(c_158,plain,(
    m1_subset_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_153])).

tff(c_184,plain,(
    ! [B_63,A_64] :
      ( m1_subset_1(k1_tarski(B_63),k1_zfmisc_1(A_64))
      | k1_xboole_0 = A_64
      | ~ m1_subset_1(B_63,A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_38,plain,(
    ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_190,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_184,c_38])).

tff(c_194,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_190])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_74,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(A_39,B_40) = A_39
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_78,plain,(
    ! [B_11] : k3_xboole_0(B_11,B_11) = B_11 ),
    inference(resolution,[status(thm)],[c_14,c_74])).

tff(c_97,plain,(
    ! [A_44,B_45,C_46] :
      ( ~ r1_xboole_0(A_44,B_45)
      | ~ r2_hidden(C_46,k3_xboole_0(A_44,B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_106,plain,(
    ! [B_47,C_48] :
      ( ~ r1_xboole_0(B_47,B_47)
      | ~ r2_hidden(C_48,B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_97])).

tff(c_111,plain,(
    ! [C_49] : ~ r2_hidden(C_49,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_106])).

tff(c_116,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_111])).

tff(c_196,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_116])).

tff(c_200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_196])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:52:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.21  
% 2.06/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.21  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.06/1.21  
% 2.06/1.21  %Foreground sorts:
% 2.06/1.21  
% 2.06/1.21  
% 2.06/1.21  %Background operators:
% 2.06/1.21  
% 2.06/1.21  
% 2.06/1.21  %Foreground operators:
% 2.06/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.21  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.06/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.06/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.06/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.06/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.21  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.06/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.06/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.06/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.22  
% 2.06/1.22  tff(f_90, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.06/1.22  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.06/1.22  tff(f_78, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.06/1.22  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 2.06/1.22  tff(f_57, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.06/1.22  tff(f_51, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.06/1.22  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.06/1.22  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.06/1.22  tff(c_40, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.06/1.22  tff(c_44, plain, (![B_31, A_32]: (~r2_hidden(B_31, A_32) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.22  tff(c_48, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_44])).
% 2.06/1.22  tff(c_144, plain, (![B_55, A_56]: (m1_subset_1(B_55, A_56) | ~r2_hidden(B_55, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.06/1.22  tff(c_153, plain, (m1_subset_1('#skF_3', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_144])).
% 2.06/1.22  tff(c_158, plain, (m1_subset_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_48, c_153])).
% 2.06/1.22  tff(c_184, plain, (![B_63, A_64]: (m1_subset_1(k1_tarski(B_63), k1_zfmisc_1(A_64)) | k1_xboole_0=A_64 | ~m1_subset_1(B_63, A_64))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.06/1.22  tff(c_38, plain, (~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.06/1.22  tff(c_190, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_184, c_38])).
% 2.06/1.22  tff(c_194, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_158, c_190])).
% 2.06/1.22  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.22  tff(c_18, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.06/1.22  tff(c_14, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.06/1.22  tff(c_74, plain, (![A_39, B_40]: (k3_xboole_0(A_39, B_40)=A_39 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.06/1.22  tff(c_78, plain, (![B_11]: (k3_xboole_0(B_11, B_11)=B_11)), inference(resolution, [status(thm)], [c_14, c_74])).
% 2.06/1.22  tff(c_97, plain, (![A_44, B_45, C_46]: (~r1_xboole_0(A_44, B_45) | ~r2_hidden(C_46, k3_xboole_0(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.06/1.22  tff(c_106, plain, (![B_47, C_48]: (~r1_xboole_0(B_47, B_47) | ~r2_hidden(C_48, B_47))), inference(superposition, [status(thm), theory('equality')], [c_78, c_97])).
% 2.06/1.22  tff(c_111, plain, (![C_49]: (~r2_hidden(C_49, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_106])).
% 2.06/1.22  tff(c_116, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_111])).
% 2.06/1.22  tff(c_196, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_116])).
% 2.06/1.22  tff(c_200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_196])).
% 2.06/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.22  
% 2.06/1.22  Inference rules
% 2.06/1.23  ----------------------
% 2.06/1.23  #Ref     : 0
% 2.06/1.23  #Sup     : 30
% 2.06/1.23  #Fact    : 0
% 2.06/1.23  #Define  : 0
% 2.06/1.23  #Split   : 1
% 2.06/1.23  #Chain   : 0
% 2.06/1.23  #Close   : 0
% 2.06/1.23  
% 2.06/1.23  Ordering : KBO
% 2.06/1.23  
% 2.06/1.23  Simplification rules
% 2.06/1.23  ----------------------
% 2.06/1.23  #Subsume      : 1
% 2.06/1.23  #Demod        : 9
% 2.06/1.23  #Tautology    : 17
% 2.06/1.23  #SimpNegUnit  : 2
% 2.06/1.23  #BackRed      : 4
% 2.06/1.23  
% 2.06/1.23  #Partial instantiations: 0
% 2.06/1.23  #Strategies tried      : 1
% 2.06/1.23  
% 2.06/1.23  Timing (in seconds)
% 2.06/1.23  ----------------------
% 2.06/1.23  Preprocessing        : 0.31
% 2.06/1.23  Parsing              : 0.16
% 2.06/1.23  CNF conversion       : 0.02
% 2.06/1.23  Main loop            : 0.16
% 2.06/1.23  Inferencing          : 0.06
% 2.06/1.23  Reduction            : 0.04
% 2.06/1.23  Demodulation         : 0.03
% 2.06/1.23  BG Simplification    : 0.02
% 2.06/1.23  Subsumption          : 0.03
% 2.06/1.23  Abstraction          : 0.01
% 2.06/1.23  MUC search           : 0.00
% 2.06/1.23  Cooper               : 0.00
% 2.06/1.23  Total                : 0.50
% 2.06/1.23  Index Insertion      : 0.00
% 2.06/1.23  Index Deletion       : 0.00
% 2.06/1.23  Index Matching       : 0.00
% 2.06/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
