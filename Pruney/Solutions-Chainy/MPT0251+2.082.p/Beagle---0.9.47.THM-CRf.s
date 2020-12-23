%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:57 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   60 (  66 expanded)
%              Number of leaves         :   30 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   59 (  67 expanded)
%              Number of equality atoms :   30 (  36 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_49,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_40,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_148,plain,(
    ! [B_38,A_39] :
      ( r1_xboole_0(B_38,A_39)
      | ~ r1_xboole_0(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_151,plain,(
    ! [A_14] : r1_xboole_0(k1_xboole_0,A_14) ),
    inference(resolution,[status(thm)],[c_20,c_148])).

tff(c_63,plain,(
    ! [B_35,A_36] : k2_xboole_0(B_35,A_36) = k2_xboole_0(A_36,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_79,plain,(
    ! [A_36] : k2_xboole_0(k1_xboole_0,A_36) = A_36 ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_14])).

tff(c_298,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(k2_xboole_0(A_65,B_66),B_66) = A_65
      | ~ r1_xboole_0(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_324,plain,(
    ! [A_36] :
      ( k4_xboole_0(A_36,A_36) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_298])).

tff(c_341,plain,(
    ! [A_36] : k4_xboole_0(A_36,A_36) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_324])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_159,plain,(
    ! [A_41,B_42] :
      ( k3_xboole_0(A_41,B_42) = A_41
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_163,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_159])).

tff(c_258,plain,(
    ! [A_57,B_58] : k5_xboole_0(A_57,k3_xboole_0(A_57,B_58)) = k4_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_267,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k4_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_258])).

tff(c_353,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_267])).

tff(c_173,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(k1_tarski(A_44),B_45)
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_495,plain,(
    ! [A_78,B_79] :
      ( k3_xboole_0(k1_tarski(A_78),B_79) = k1_tarski(A_78)
      | ~ r2_hidden(A_78,B_79) ) ),
    inference(resolution,[status(thm)],[c_173,c_16])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_501,plain,(
    ! [A_78,B_79] :
      ( k5_xboole_0(k1_tarski(A_78),k1_tarski(A_78)) = k4_xboole_0(k1_tarski(A_78),B_79)
      | ~ r2_hidden(A_78,B_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_495,c_12])).

tff(c_522,plain,(
    ! [A_80,B_81] :
      ( k4_xboole_0(k1_tarski(A_80),B_81) = k1_xboole_0
      | ~ r2_hidden(A_80,B_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_501])).

tff(c_18,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_536,plain,(
    ! [B_81,A_80] :
      ( k2_xboole_0(B_81,k1_tarski(A_80)) = k2_xboole_0(B_81,k1_xboole_0)
      | ~ r2_hidden(A_80,B_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_18])).

tff(c_558,plain,(
    ! [B_83,A_84] :
      ( k2_xboole_0(B_83,k1_tarski(A_84)) = B_83
      | ~ r2_hidden(A_84,B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_536])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_42,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_38])).

tff(c_584,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_42])).

tff(c_612,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_584])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n014.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 14:33:07 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.31  
% 2.19/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.31  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.19/1.31  
% 2.19/1.31  %Foreground sorts:
% 2.19/1.31  
% 2.19/1.31  
% 2.19/1.31  %Background operators:
% 2.19/1.31  
% 2.19/1.31  
% 2.19/1.31  %Foreground operators:
% 2.19/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.19/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.19/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.19/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.19/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.19/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.19/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.19/1.31  
% 2.45/1.33  tff(f_72, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 2.45/1.33  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.45/1.33  tff(f_49, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.45/1.33  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.45/1.33  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.45/1.33  tff(f_53, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 2.45/1.33  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.45/1.33  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.45/1.33  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.45/1.33  tff(f_65, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.45/1.33  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.45/1.33  tff(c_40, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.45/1.33  tff(c_14, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.45/1.33  tff(c_20, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.45/1.33  tff(c_148, plain, (![B_38, A_39]: (r1_xboole_0(B_38, A_39) | ~r1_xboole_0(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.45/1.33  tff(c_151, plain, (![A_14]: (r1_xboole_0(k1_xboole_0, A_14))), inference(resolution, [status(thm)], [c_20, c_148])).
% 2.45/1.33  tff(c_63, plain, (![B_35, A_36]: (k2_xboole_0(B_35, A_36)=k2_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.45/1.33  tff(c_79, plain, (![A_36]: (k2_xboole_0(k1_xboole_0, A_36)=A_36)), inference(superposition, [status(thm), theory('equality')], [c_63, c_14])).
% 2.45/1.33  tff(c_298, plain, (![A_65, B_66]: (k4_xboole_0(k2_xboole_0(A_65, B_66), B_66)=A_65 | ~r1_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.45/1.33  tff(c_324, plain, (![A_36]: (k4_xboole_0(A_36, A_36)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_36))), inference(superposition, [status(thm), theory('equality')], [c_79, c_298])).
% 2.45/1.33  tff(c_341, plain, (![A_36]: (k4_xboole_0(A_36, A_36)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_151, c_324])).
% 2.45/1.33  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.45/1.33  tff(c_159, plain, (![A_41, B_42]: (k3_xboole_0(A_41, B_42)=A_41 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.45/1.33  tff(c_163, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_159])).
% 2.45/1.33  tff(c_258, plain, (![A_57, B_58]: (k5_xboole_0(A_57, k3_xboole_0(A_57, B_58))=k4_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.45/1.33  tff(c_267, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k4_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_163, c_258])).
% 2.45/1.33  tff(c_353, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_341, c_267])).
% 2.45/1.33  tff(c_173, plain, (![A_44, B_45]: (r1_tarski(k1_tarski(A_44), B_45) | ~r2_hidden(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.45/1.33  tff(c_16, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.45/1.33  tff(c_495, plain, (![A_78, B_79]: (k3_xboole_0(k1_tarski(A_78), B_79)=k1_tarski(A_78) | ~r2_hidden(A_78, B_79))), inference(resolution, [status(thm)], [c_173, c_16])).
% 2.45/1.33  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.45/1.33  tff(c_501, plain, (![A_78, B_79]: (k5_xboole_0(k1_tarski(A_78), k1_tarski(A_78))=k4_xboole_0(k1_tarski(A_78), B_79) | ~r2_hidden(A_78, B_79))), inference(superposition, [status(thm), theory('equality')], [c_495, c_12])).
% 2.45/1.33  tff(c_522, plain, (![A_80, B_81]: (k4_xboole_0(k1_tarski(A_80), B_81)=k1_xboole_0 | ~r2_hidden(A_80, B_81))), inference(demodulation, [status(thm), theory('equality')], [c_353, c_501])).
% 2.45/1.33  tff(c_18, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.45/1.33  tff(c_536, plain, (![B_81, A_80]: (k2_xboole_0(B_81, k1_tarski(A_80))=k2_xboole_0(B_81, k1_xboole_0) | ~r2_hidden(A_80, B_81))), inference(superposition, [status(thm), theory('equality')], [c_522, c_18])).
% 2.45/1.33  tff(c_558, plain, (![B_83, A_84]: (k2_xboole_0(B_83, k1_tarski(A_84))=B_83 | ~r2_hidden(A_84, B_83))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_536])).
% 2.45/1.33  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.45/1.33  tff(c_38, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.45/1.33  tff(c_42, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_38])).
% 2.45/1.33  tff(c_584, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_558, c_42])).
% 2.45/1.33  tff(c_612, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_584])).
% 2.45/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.33  
% 2.45/1.33  Inference rules
% 2.45/1.33  ----------------------
% 2.45/1.33  #Ref     : 0
% 2.45/1.33  #Sup     : 126
% 2.45/1.33  #Fact    : 0
% 2.45/1.33  #Define  : 0
% 2.45/1.33  #Split   : 0
% 2.45/1.33  #Chain   : 0
% 2.45/1.33  #Close   : 0
% 2.45/1.33  
% 2.45/1.33  Ordering : KBO
% 2.45/1.33  
% 2.45/1.33  Simplification rules
% 2.45/1.33  ----------------------
% 2.45/1.33  #Subsume      : 8
% 2.45/1.33  #Demod        : 45
% 2.45/1.33  #Tautology    : 88
% 2.45/1.33  #SimpNegUnit  : 0
% 2.45/1.33  #BackRed      : 2
% 2.45/1.33  
% 2.45/1.33  #Partial instantiations: 0
% 2.45/1.33  #Strategies tried      : 1
% 2.45/1.33  
% 2.45/1.33  Timing (in seconds)
% 2.45/1.33  ----------------------
% 2.45/1.33  Preprocessing        : 0.33
% 2.45/1.33  Parsing              : 0.18
% 2.45/1.33  CNF conversion       : 0.02
% 2.45/1.33  Main loop            : 0.24
% 2.45/1.33  Inferencing          : 0.09
% 2.45/1.33  Reduction            : 0.08
% 2.45/1.33  Demodulation         : 0.06
% 2.45/1.33  BG Simplification    : 0.02
% 2.45/1.33  Subsumption          : 0.03
% 2.45/1.33  Abstraction          : 0.02
% 2.45/1.33  MUC search           : 0.00
% 2.45/1.33  Cooper               : 0.00
% 2.45/1.33  Total                : 0.60
% 2.45/1.33  Index Insertion      : 0.00
% 2.45/1.33  Index Deletion       : 0.00
% 2.45/1.33  Index Matching       : 0.00
% 2.45/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
