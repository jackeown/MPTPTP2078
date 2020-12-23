%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:01 EST 2020

% Result     : Theorem 5.13s
% Output     : CNFRefutation 5.13s
% Verified   : 
% Statistics : Number of formulae       :   53 (  60 expanded)
%              Number of leaves         :   31 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 (  74 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_66,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_8,plain,(
    ! [D_12,A_7,B_8] :
      ( r2_hidden(D_12,k3_xboole_0(A_7,B_8))
      | ~ r2_hidden(D_12,B_8)
      | ~ r2_hidden(D_12,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_77,plain,(
    ! [B_37,A_38] :
      ( ~ r2_hidden(B_37,A_38)
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_81,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_77])).

tff(c_164,plain,(
    ! [B_55,A_56] :
      ( m1_subset_1(B_55,A_56)
      | ~ r2_hidden(B_55,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_173,plain,
    ( m1_subset_1('#skF_4','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_164])).

tff(c_178,plain,(
    m1_subset_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_173])).

tff(c_274,plain,(
    ! [B_71,A_72] :
      ( m1_subset_1(k1_tarski(B_71),k1_zfmisc_1(A_72))
      | k1_xboole_0 = A_72
      | ~ m1_subset_1(B_71,A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_64,plain,(
    ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_280,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_274,c_64])).

tff(c_284,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_280])).

tff(c_40,plain,(
    ! [A_18] : r1_xboole_0(A_18,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_120,plain,(
    ! [A_42,B_43] :
      ( k4_xboole_0(A_42,B_43) = A_42
      | ~ r1_xboole_0(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_124,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(resolution,[status(thm)],[c_40,c_120])).

tff(c_286,plain,(
    ! [A_18] : k4_xboole_0(A_18,'#skF_5') = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_124])).

tff(c_38,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_503,plain,(
    ! [A_102,C_103,B_104] :
      ( ~ r2_hidden(A_102,C_103)
      | ~ r2_hidden(A_102,B_104)
      | ~ r2_hidden(A_102,k5_xboole_0(B_104,C_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2515,plain,(
    ! [A_257,A_258,B_259] :
      ( ~ r2_hidden(A_257,k3_xboole_0(A_258,B_259))
      | ~ r2_hidden(A_257,A_258)
      | ~ r2_hidden(A_257,k4_xboole_0(A_258,B_259)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_503])).

tff(c_2603,plain,(
    ! [A_260,A_261] :
      ( ~ r2_hidden(A_260,k3_xboole_0(A_261,'#skF_5'))
      | ~ r2_hidden(A_260,A_261)
      | ~ r2_hidden(A_260,A_261) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_2515])).

tff(c_2719,plain,(
    ! [D_262,A_263] :
      ( ~ r2_hidden(D_262,'#skF_5')
      | ~ r2_hidden(D_262,A_263) ) ),
    inference(resolution,[status(thm)],[c_8,c_2603])).

tff(c_2784,plain,(
    ! [A_263] : ~ r2_hidden('#skF_4',A_263) ),
    inference(resolution,[status(thm)],[c_66,c_2719])).

tff(c_2786,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2784,c_66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:23:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.13/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.13/1.96  
% 5.13/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.13/1.96  %$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 5.13/1.96  
% 5.13/1.96  %Foreground sorts:
% 5.13/1.96  
% 5.13/1.96  
% 5.13/1.96  %Background operators:
% 5.13/1.96  
% 5.13/1.96  
% 5.13/1.96  %Foreground operators:
% 5.13/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.13/1.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.13/1.96  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.13/1.96  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.13/1.96  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.13/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.13/1.96  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.13/1.96  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.13/1.96  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.13/1.96  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.13/1.96  tff('#skF_5', type, '#skF_5': $i).
% 5.13/1.96  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.13/1.96  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.13/1.96  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.13/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.13/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.13/1.96  tff('#skF_4', type, '#skF_4': $i).
% 5.13/1.96  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.13/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.13/1.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.13/1.96  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.13/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.13/1.96  
% 5.13/1.97  tff(f_90, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 5.13/1.97  tff(f_42, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 5.13/1.97  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.13/1.97  tff(f_78, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 5.13/1.97  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 5.13/1.97  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.13/1.97  tff(f_57, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.13/1.97  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.13/1.97  tff(f_49, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 5.13/1.97  tff(c_66, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.13/1.97  tff(c_8, plain, (![D_12, A_7, B_8]: (r2_hidden(D_12, k3_xboole_0(A_7, B_8)) | ~r2_hidden(D_12, B_8) | ~r2_hidden(D_12, A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.13/1.97  tff(c_77, plain, (![B_37, A_38]: (~r2_hidden(B_37, A_38) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.13/1.97  tff(c_81, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_66, c_77])).
% 5.13/1.97  tff(c_164, plain, (![B_55, A_56]: (m1_subset_1(B_55, A_56) | ~r2_hidden(B_55, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.13/1.97  tff(c_173, plain, (m1_subset_1('#skF_4', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_66, c_164])).
% 5.13/1.97  tff(c_178, plain, (m1_subset_1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_81, c_173])).
% 5.13/1.97  tff(c_274, plain, (![B_71, A_72]: (m1_subset_1(k1_tarski(B_71), k1_zfmisc_1(A_72)) | k1_xboole_0=A_72 | ~m1_subset_1(B_71, A_72))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.13/1.97  tff(c_64, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.13/1.97  tff(c_280, plain, (k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_274, c_64])).
% 5.13/1.97  tff(c_284, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_178, c_280])).
% 5.13/1.97  tff(c_40, plain, (![A_18]: (r1_xboole_0(A_18, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.13/1.97  tff(c_120, plain, (![A_42, B_43]: (k4_xboole_0(A_42, B_43)=A_42 | ~r1_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.13/1.97  tff(c_124, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(resolution, [status(thm)], [c_40, c_120])).
% 5.13/1.97  tff(c_286, plain, (![A_18]: (k4_xboole_0(A_18, '#skF_5')=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_284, c_124])).
% 5.13/1.97  tff(c_38, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.13/1.97  tff(c_503, plain, (![A_102, C_103, B_104]: (~r2_hidden(A_102, C_103) | ~r2_hidden(A_102, B_104) | ~r2_hidden(A_102, k5_xboole_0(B_104, C_103)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.13/1.97  tff(c_2515, plain, (![A_257, A_258, B_259]: (~r2_hidden(A_257, k3_xboole_0(A_258, B_259)) | ~r2_hidden(A_257, A_258) | ~r2_hidden(A_257, k4_xboole_0(A_258, B_259)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_503])).
% 5.13/1.97  tff(c_2603, plain, (![A_260, A_261]: (~r2_hidden(A_260, k3_xboole_0(A_261, '#skF_5')) | ~r2_hidden(A_260, A_261) | ~r2_hidden(A_260, A_261))), inference(superposition, [status(thm), theory('equality')], [c_286, c_2515])).
% 5.13/1.97  tff(c_2719, plain, (![D_262, A_263]: (~r2_hidden(D_262, '#skF_5') | ~r2_hidden(D_262, A_263))), inference(resolution, [status(thm)], [c_8, c_2603])).
% 5.13/1.97  tff(c_2784, plain, (![A_263]: (~r2_hidden('#skF_4', A_263))), inference(resolution, [status(thm)], [c_66, c_2719])).
% 5.13/1.97  tff(c_2786, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2784, c_66])).
% 5.13/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.13/1.97  
% 5.13/1.97  Inference rules
% 5.13/1.97  ----------------------
% 5.13/1.97  #Ref     : 0
% 5.13/1.97  #Sup     : 731
% 5.13/1.97  #Fact    : 0
% 5.13/1.97  #Define  : 0
% 5.13/1.97  #Split   : 1
% 5.13/1.97  #Chain   : 0
% 5.13/1.97  #Close   : 0
% 5.13/1.98  
% 5.13/1.98  Ordering : KBO
% 5.13/1.98  
% 5.13/1.98  Simplification rules
% 5.13/1.98  ----------------------
% 5.13/1.98  #Subsume      : 230
% 5.13/1.98  #Demod        : 11
% 5.13/1.98  #Tautology    : 63
% 5.13/1.98  #SimpNegUnit  : 4
% 5.13/1.98  #BackRed      : 4
% 5.13/1.98  
% 5.13/1.98  #Partial instantiations: 0
% 5.13/1.98  #Strategies tried      : 1
% 5.13/1.98  
% 5.13/1.98  Timing (in seconds)
% 5.13/1.98  ----------------------
% 5.13/1.98  Preprocessing        : 0.34
% 5.13/1.98  Parsing              : 0.17
% 5.13/1.98  CNF conversion       : 0.02
% 5.13/1.98  Main loop            : 0.89
% 5.13/1.98  Inferencing          : 0.28
% 5.13/1.98  Reduction            : 0.25
% 5.13/1.98  Demodulation         : 0.18
% 5.13/1.98  BG Simplification    : 0.04
% 5.13/1.98  Subsumption          : 0.26
% 5.13/1.98  Abstraction          : 0.04
% 5.13/1.98  MUC search           : 0.00
% 5.13/1.98  Cooper               : 0.00
% 5.13/1.98  Total                : 1.26
% 5.13/1.98  Index Insertion      : 0.00
% 5.13/1.98  Index Deletion       : 0.00
% 5.13/1.98  Index Matching       : 0.00
% 5.13/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
