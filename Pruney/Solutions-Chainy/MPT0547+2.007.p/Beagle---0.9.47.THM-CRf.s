%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:34 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   55 (  58 expanded)
%              Number of leaves         :   33 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :   57 (  61 expanded)
%              Number of equality atoms :   21 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k9_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).

tff(f_72,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(c_48,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_50,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_38,plain,(
    ! [A_36] : m1_subset_1('#skF_1'(A_36),A_36) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_32,plain,(
    ! [B_35,A_34] :
      ( r2_hidden(B_35,A_34)
      | ~ m1_subset_1(B_35,A_34)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_562,plain,(
    ! [A_102,B_103,C_104] :
      ( r2_hidden('#skF_2'(A_102,B_103,C_104),B_103)
      | ~ r2_hidden(A_102,k9_relat_1(C_104,B_103))
      | ~ v1_relat_1(C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_369,plain,(
    ! [A_85,B_86] : k4_xboole_0(A_85,k4_xboole_0(A_85,B_86)) = k3_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_399,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_369])).

tff(c_403,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_399])).

tff(c_22,plain,(
    ! [B_31] : k4_xboole_0(k1_tarski(B_31),k1_tarski(B_31)) != k1_tarski(B_31) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_404,plain,(
    ! [B_31] : k1_tarski(B_31) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_22])).

tff(c_137,plain,(
    ! [A_60,B_61] :
      ( k4_xboole_0(k1_tarski(A_60),B_61) = k1_xboole_0
      | ~ r2_hidden(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_148,plain,(
    ! [A_60] :
      ( k1_tarski(A_60) = k1_xboole_0
      | ~ r2_hidden(A_60,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_4])).

tff(c_441,plain,(
    ! [A_60] : ~ r2_hidden(A_60,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_404,c_148])).

tff(c_577,plain,(
    ! [A_105,C_106] :
      ( ~ r2_hidden(A_105,k9_relat_1(C_106,k1_xboole_0))
      | ~ v1_relat_1(C_106) ) ),
    inference(resolution,[status(thm)],[c_562,c_441])).

tff(c_1009,plain,(
    ! [C_160,B_161] :
      ( ~ v1_relat_1(C_160)
      | ~ m1_subset_1(B_161,k9_relat_1(C_160,k1_xboole_0))
      | v1_xboole_0(k9_relat_1(C_160,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_32,c_577])).

tff(c_1019,plain,(
    ! [C_162] :
      ( ~ v1_relat_1(C_162)
      | v1_xboole_0(k9_relat_1(C_162,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_38,c_1009])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1028,plain,(
    ! [C_163] :
      ( k9_relat_1(C_163,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(C_163) ) ),
    inference(resolution,[status(thm)],[c_1019,c_8])).

tff(c_1031,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_1028])).

tff(c_1035,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1031])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:11:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.51  
% 2.83/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.51  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.83/1.51  
% 2.83/1.51  %Foreground sorts:
% 2.83/1.51  
% 2.83/1.51  
% 2.83/1.51  %Background operators:
% 2.83/1.51  
% 2.83/1.51  
% 2.83/1.51  %Foreground operators:
% 2.83/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.83/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.83/1.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.83/1.51  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.83/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.83/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.83/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.83/1.51  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.83/1.51  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.83/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.83/1.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.83/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.83/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.83/1.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.83/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.83/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.83/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.51  
% 2.83/1.52  tff(f_88, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_relat_1)).
% 2.83/1.52  tff(f_72, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.83/1.52  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.83/1.52  tff(f_83, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.83/1.52  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.83/1.52  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.83/1.52  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.83/1.52  tff(f_52, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.83/1.52  tff(f_56, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 2.83/1.52  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_boole)).
% 2.83/1.52  tff(c_48, plain, (k9_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.83/1.52  tff(c_50, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.83/1.52  tff(c_38, plain, (![A_36]: (m1_subset_1('#skF_1'(A_36), A_36))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.83/1.52  tff(c_32, plain, (![B_35, A_34]: (r2_hidden(B_35, A_34) | ~m1_subset_1(B_35, A_34) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.83/1.52  tff(c_562, plain, (![A_102, B_103, C_104]: (r2_hidden('#skF_2'(A_102, B_103, C_104), B_103) | ~r2_hidden(A_102, k9_relat_1(C_104, B_103)) | ~v1_relat_1(C_104))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.83/1.52  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.83/1.52  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.83/1.52  tff(c_369, plain, (![A_85, B_86]: (k4_xboole_0(A_85, k4_xboole_0(A_85, B_86))=k3_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.83/1.52  tff(c_399, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_369])).
% 2.83/1.52  tff(c_403, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_399])).
% 2.83/1.52  tff(c_22, plain, (![B_31]: (k4_xboole_0(k1_tarski(B_31), k1_tarski(B_31))!=k1_tarski(B_31))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.83/1.52  tff(c_404, plain, (![B_31]: (k1_tarski(B_31)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_403, c_22])).
% 2.83/1.52  tff(c_137, plain, (![A_60, B_61]: (k4_xboole_0(k1_tarski(A_60), B_61)=k1_xboole_0 | ~r2_hidden(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.83/1.52  tff(c_148, plain, (![A_60]: (k1_tarski(A_60)=k1_xboole_0 | ~r2_hidden(A_60, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_137, c_4])).
% 2.83/1.52  tff(c_441, plain, (![A_60]: (~r2_hidden(A_60, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_404, c_148])).
% 2.83/1.52  tff(c_577, plain, (![A_105, C_106]: (~r2_hidden(A_105, k9_relat_1(C_106, k1_xboole_0)) | ~v1_relat_1(C_106))), inference(resolution, [status(thm)], [c_562, c_441])).
% 2.83/1.52  tff(c_1009, plain, (![C_160, B_161]: (~v1_relat_1(C_160) | ~m1_subset_1(B_161, k9_relat_1(C_160, k1_xboole_0)) | v1_xboole_0(k9_relat_1(C_160, k1_xboole_0)))), inference(resolution, [status(thm)], [c_32, c_577])).
% 2.83/1.52  tff(c_1019, plain, (![C_162]: (~v1_relat_1(C_162) | v1_xboole_0(k9_relat_1(C_162, k1_xboole_0)))), inference(resolution, [status(thm)], [c_38, c_1009])).
% 2.83/1.52  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.83/1.52  tff(c_1028, plain, (![C_163]: (k9_relat_1(C_163, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(C_163))), inference(resolution, [status(thm)], [c_1019, c_8])).
% 2.83/1.52  tff(c_1031, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_1028])).
% 2.83/1.52  tff(c_1035, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1031])).
% 2.83/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.52  
% 2.83/1.52  Inference rules
% 2.83/1.52  ----------------------
% 2.83/1.52  #Ref     : 0
% 2.83/1.52  #Sup     : 208
% 2.83/1.52  #Fact    : 0
% 2.83/1.52  #Define  : 0
% 2.83/1.52  #Split   : 2
% 2.83/1.52  #Chain   : 0
% 2.83/1.52  #Close   : 0
% 2.83/1.52  
% 2.83/1.52  Ordering : KBO
% 2.83/1.52  
% 2.83/1.52  Simplification rules
% 2.83/1.52  ----------------------
% 2.83/1.52  #Subsume      : 43
% 2.83/1.52  #Demod        : 59
% 2.83/1.52  #Tautology    : 96
% 2.83/1.52  #SimpNegUnit  : 27
% 2.83/1.52  #BackRed      : 5
% 2.83/1.52  
% 2.83/1.52  #Partial instantiations: 0
% 2.83/1.52  #Strategies tried      : 1
% 2.83/1.52  
% 2.83/1.52  Timing (in seconds)
% 2.83/1.52  ----------------------
% 3.09/1.52  Preprocessing        : 0.34
% 3.09/1.52  Parsing              : 0.18
% 3.09/1.52  CNF conversion       : 0.02
% 3.09/1.52  Main loop            : 0.36
% 3.09/1.52  Inferencing          : 0.14
% 3.09/1.52  Reduction            : 0.10
% 3.09/1.52  Demodulation         : 0.06
% 3.09/1.52  BG Simplification    : 0.02
% 3.09/1.53  Subsumption          : 0.07
% 3.09/1.53  Abstraction          : 0.02
% 3.09/1.53  MUC search           : 0.00
% 3.09/1.53  Cooper               : 0.00
% 3.09/1.53  Total                : 0.72
% 3.09/1.53  Index Insertion      : 0.00
% 3.09/1.53  Index Deletion       : 0.00
% 3.09/1.53  Index Matching       : 0.00
% 3.09/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
