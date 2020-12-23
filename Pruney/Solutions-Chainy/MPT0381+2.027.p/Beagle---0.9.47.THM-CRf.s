%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:04 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.26s
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

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

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

tff(c_38,plain,(
    ! [B_29,A_30] :
      ( ~ r2_hidden(B_29,A_30)
      | ~ v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_38])).

tff(c_136,plain,(
    ! [B_51,A_52] :
      ( m1_subset_1(B_51,A_52)
      | ~ r2_hidden(B_51,A_52)
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_145,plain,
    ( m1_subset_1('#skF_3','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_136])).

tff(c_150,plain,(
    m1_subset_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_145])).

tff(c_187,plain,(
    ! [B_60,A_61] :
      ( m1_subset_1(k1_tarski(B_60),k1_zfmisc_1(A_61))
      | k1_xboole_0 = A_61
      | ~ m1_subset_1(B_60,A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_193,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_187,c_34])).

tff(c_197,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_193])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_44,plain,(
    ! [A_33] :
      ( k1_xboole_0 = A_33
      | ~ r1_tarski(A_33,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_49,plain,(
    ! [B_11] : k3_xboole_0(k1_xboole_0,B_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_44])).

tff(c_99,plain,(
    ! [A_43,B_44,C_45] :
      ( ~ r1_xboole_0(A_43,B_44)
      | ~ r2_hidden(C_45,k3_xboole_0(A_43,B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_106,plain,(
    ! [B_11,C_45] :
      ( ~ r1_xboole_0(k1_xboole_0,B_11)
      | ~ r2_hidden(C_45,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_99])).

tff(c_109,plain,(
    ! [C_46] : ~ r2_hidden(C_46,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_114,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_109])).

tff(c_200,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_114])).

tff(c_207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_200])).

tff(c_209,plain,(
    ! [B_62] : ~ r1_xboole_0(k1_xboole_0,B_62) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_214,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_14,c_209])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:56:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.24  
% 2.20/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.24  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.26/1.24  
% 2.26/1.24  %Foreground sorts:
% 2.26/1.24  
% 2.26/1.24  
% 2.26/1.24  %Background operators:
% 2.26/1.24  
% 2.26/1.24  
% 2.26/1.24  %Foreground operators:
% 2.26/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.26/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.26/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.26/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.26/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.26/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.26/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.26/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.26/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.26/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.26/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.26/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.26/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.26/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.26/1.24  
% 2.26/1.25  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.26/1.25  tff(f_86, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.26/1.25  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.26/1.25  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.26/1.25  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 2.26/1.25  tff(f_47, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.26/1.25  tff(f_51, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.26/1.25  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.26/1.25  tff(c_14, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.26/1.25  tff(c_36, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.26/1.25  tff(c_38, plain, (![B_29, A_30]: (~r2_hidden(B_29, A_30) | ~v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.25  tff(c_42, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_38])).
% 2.26/1.25  tff(c_136, plain, (![B_51, A_52]: (m1_subset_1(B_51, A_52) | ~r2_hidden(B_51, A_52) | v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.26/1.25  tff(c_145, plain, (m1_subset_1('#skF_3', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_136])).
% 2.26/1.25  tff(c_150, plain, (m1_subset_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_42, c_145])).
% 2.26/1.25  tff(c_187, plain, (![B_60, A_61]: (m1_subset_1(k1_tarski(B_60), k1_zfmisc_1(A_61)) | k1_xboole_0=A_61 | ~m1_subset_1(B_60, A_61))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.26/1.25  tff(c_34, plain, (~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.26/1.25  tff(c_193, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_187, c_34])).
% 2.26/1.25  tff(c_197, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_150, c_193])).
% 2.26/1.25  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.25  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.26/1.25  tff(c_44, plain, (![A_33]: (k1_xboole_0=A_33 | ~r1_tarski(A_33, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.26/1.25  tff(c_49, plain, (![B_11]: (k3_xboole_0(k1_xboole_0, B_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_44])).
% 2.26/1.25  tff(c_99, plain, (![A_43, B_44, C_45]: (~r1_xboole_0(A_43, B_44) | ~r2_hidden(C_45, k3_xboole_0(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.26/1.25  tff(c_106, plain, (![B_11, C_45]: (~r1_xboole_0(k1_xboole_0, B_11) | ~r2_hidden(C_45, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_49, c_99])).
% 2.26/1.25  tff(c_109, plain, (![C_46]: (~r2_hidden(C_46, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_106])).
% 2.26/1.25  tff(c_114, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_109])).
% 2.26/1.25  tff(c_200, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_114])).
% 2.26/1.25  tff(c_207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_200])).
% 2.26/1.25  tff(c_209, plain, (![B_62]: (~r1_xboole_0(k1_xboole_0, B_62))), inference(splitRight, [status(thm)], [c_106])).
% 2.26/1.25  tff(c_214, plain, $false, inference(resolution, [status(thm)], [c_14, c_209])).
% 2.26/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.25  
% 2.26/1.25  Inference rules
% 2.26/1.25  ----------------------
% 2.26/1.25  #Ref     : 0
% 2.26/1.25  #Sup     : 34
% 2.26/1.25  #Fact    : 0
% 2.26/1.25  #Define  : 0
% 2.26/1.25  #Split   : 2
% 2.26/1.25  #Chain   : 0
% 2.26/1.25  #Close   : 0
% 2.26/1.25  
% 2.26/1.25  Ordering : KBO
% 2.26/1.25  
% 2.26/1.25  Simplification rules
% 2.26/1.25  ----------------------
% 2.26/1.25  #Subsume      : 1
% 2.26/1.25  #Demod        : 14
% 2.26/1.25  #Tautology    : 17
% 2.26/1.25  #SimpNegUnit  : 3
% 2.26/1.25  #BackRed      : 8
% 2.26/1.25  
% 2.26/1.25  #Partial instantiations: 0
% 2.26/1.25  #Strategies tried      : 1
% 2.26/1.25  
% 2.26/1.25  Timing (in seconds)
% 2.26/1.25  ----------------------
% 2.26/1.26  Preprocessing        : 0.29
% 2.26/1.26  Parsing              : 0.15
% 2.26/1.26  CNF conversion       : 0.02
% 2.26/1.26  Main loop            : 0.16
% 2.26/1.26  Inferencing          : 0.06
% 2.26/1.26  Reduction            : 0.05
% 2.26/1.26  Demodulation         : 0.03
% 2.26/1.26  BG Simplification    : 0.01
% 2.26/1.26  Subsumption          : 0.03
% 2.26/1.26  Abstraction          : 0.01
% 2.26/1.26  MUC search           : 0.00
% 2.26/1.26  Cooper               : 0.00
% 2.26/1.26  Total                : 0.48
% 2.26/1.26  Index Insertion      : 0.00
% 2.26/1.26  Index Deletion       : 0.00
% 2.26/1.26  Index Matching       : 0.00
% 2.26/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
