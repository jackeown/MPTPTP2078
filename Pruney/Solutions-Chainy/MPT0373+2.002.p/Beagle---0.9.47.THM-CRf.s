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
% DateTime   : Thu Dec  3 09:56:57 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   58 (  68 expanded)
%              Number of leaves         :   30 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 (  94 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ( A != k1_xboole_0
         => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_68,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_42,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_97,plain,(
    ! [B_37,A_38] :
      ( v1_xboole_0(B_37)
      | ~ m1_subset_1(B_37,A_38)
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_105,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_97])).

tff(c_106,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_28,plain,(
    ! [B_24,A_23] :
      ( r2_hidden(B_24,A_23)
      | ~ m1_subset_1(B_24,A_23)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_12,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_343,plain,(
    ! [A_90,B_91,C_92] :
      ( r1_tarski(k2_tarski(A_90,B_91),C_92)
      | ~ r2_hidden(B_91,C_92)
      | ~ r2_hidden(A_90,C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_359,plain,(
    ! [A_93,C_94] :
      ( r1_tarski(k1_tarski(A_93),C_94)
      | ~ r2_hidden(A_93,C_94)
      | ~ r2_hidden(A_93,C_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_343])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_419,plain,(
    ! [A_98,C_99] :
      ( k3_xboole_0(k1_tarski(A_98),C_99) = k1_tarski(A_98)
      | ~ r2_hidden(A_98,C_99) ) ),
    inference(resolution,[status(thm)],[c_359,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_134,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k4_xboole_0(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36,plain,(
    ! [A_27,B_28] : k6_subset_1(A_27,B_28) = k4_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_34,plain,(
    ! [A_25,B_26] : m1_subset_1(k6_subset_1(A_25,B_26),k1_zfmisc_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_43,plain,(
    ! [A_25,B_26] : m1_subset_1(k4_xboole_0(A_25,B_26),k1_zfmisc_1(A_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34])).

tff(c_155,plain,(
    ! [A_53,B_54] : m1_subset_1(k3_xboole_0(A_53,B_54),k1_zfmisc_1(A_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_43])).

tff(c_161,plain,(
    ! [B_2,A_1] : m1_subset_1(k3_xboole_0(B_2,A_1),k1_zfmisc_1(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_155])).

tff(c_466,plain,(
    ! [A_100,C_101] :
      ( m1_subset_1(k1_tarski(A_100),k1_zfmisc_1(C_101))
      | ~ r2_hidden(A_100,C_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_161])).

tff(c_38,plain,(
    ~ m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_474,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_466,c_38])).

tff(c_477,plain,
    ( ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_474])).

tff(c_480,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_477])).

tff(c_482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_480])).

tff(c_484,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_491,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_484,c_4])).

tff(c_495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_491])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:56:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.29  
% 2.34/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.29  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.34/1.29  
% 2.34/1.29  %Foreground sorts:
% 2.34/1.29  
% 2.34/1.29  
% 2.34/1.29  %Background operators:
% 2.34/1.29  
% 2.34/1.29  
% 2.34/1.29  %Foreground operators:
% 2.34/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.34/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.34/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.34/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.34/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.34/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.34/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.34/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.34/1.29  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.34/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.34/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.34/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.34/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.34/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.34/1.29  
% 2.34/1.30  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 2.34/1.30  tff(f_66, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.34/1.30  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.34/1.30  tff(f_53, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.34/1.30  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.34/1.30  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.34/1.30  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.34/1.30  tff(f_70, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.34/1.30  tff(f_68, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 2.34/1.30  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.34/1.30  tff(c_40, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.34/1.30  tff(c_42, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.34/1.30  tff(c_97, plain, (![B_37, A_38]: (v1_xboole_0(B_37) | ~m1_subset_1(B_37, A_38) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.34/1.30  tff(c_105, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_97])).
% 2.34/1.30  tff(c_106, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_105])).
% 2.34/1.30  tff(c_28, plain, (![B_24, A_23]: (r2_hidden(B_24, A_23) | ~m1_subset_1(B_24, A_23) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.34/1.30  tff(c_12, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.34/1.30  tff(c_343, plain, (![A_90, B_91, C_92]: (r1_tarski(k2_tarski(A_90, B_91), C_92) | ~r2_hidden(B_91, C_92) | ~r2_hidden(A_90, C_92))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.34/1.30  tff(c_359, plain, (![A_93, C_94]: (r1_tarski(k1_tarski(A_93), C_94) | ~r2_hidden(A_93, C_94) | ~r2_hidden(A_93, C_94))), inference(superposition, [status(thm), theory('equality')], [c_12, c_343])).
% 2.34/1.30  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.34/1.30  tff(c_419, plain, (![A_98, C_99]: (k3_xboole_0(k1_tarski(A_98), C_99)=k1_tarski(A_98) | ~r2_hidden(A_98, C_99))), inference(resolution, [status(thm)], [c_359, c_8])).
% 2.34/1.30  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.34/1.30  tff(c_134, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k4_xboole_0(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.34/1.30  tff(c_36, plain, (![A_27, B_28]: (k6_subset_1(A_27, B_28)=k4_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.34/1.30  tff(c_34, plain, (![A_25, B_26]: (m1_subset_1(k6_subset_1(A_25, B_26), k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.34/1.30  tff(c_43, plain, (![A_25, B_26]: (m1_subset_1(k4_xboole_0(A_25, B_26), k1_zfmisc_1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34])).
% 2.34/1.30  tff(c_155, plain, (![A_53, B_54]: (m1_subset_1(k3_xboole_0(A_53, B_54), k1_zfmisc_1(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_134, c_43])).
% 2.34/1.30  tff(c_161, plain, (![B_2, A_1]: (m1_subset_1(k3_xboole_0(B_2, A_1), k1_zfmisc_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_155])).
% 2.34/1.30  tff(c_466, plain, (![A_100, C_101]: (m1_subset_1(k1_tarski(A_100), k1_zfmisc_1(C_101)) | ~r2_hidden(A_100, C_101))), inference(superposition, [status(thm), theory('equality')], [c_419, c_161])).
% 2.34/1.30  tff(c_38, plain, (~m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.34/1.30  tff(c_474, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_466, c_38])).
% 2.34/1.30  tff(c_477, plain, (~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_474])).
% 2.34/1.30  tff(c_480, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_477])).
% 2.34/1.30  tff(c_482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_480])).
% 2.34/1.30  tff(c_484, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_105])).
% 2.34/1.30  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.34/1.30  tff(c_491, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_484, c_4])).
% 2.34/1.30  tff(c_495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_491])).
% 2.34/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.30  
% 2.34/1.30  Inference rules
% 2.34/1.30  ----------------------
% 2.34/1.30  #Ref     : 0
% 2.34/1.30  #Sup     : 110
% 2.34/1.30  #Fact    : 0
% 2.34/1.30  #Define  : 0
% 2.34/1.30  #Split   : 2
% 2.34/1.30  #Chain   : 0
% 2.34/1.30  #Close   : 0
% 2.34/1.30  
% 2.34/1.30  Ordering : KBO
% 2.34/1.30  
% 2.34/1.30  Simplification rules
% 2.34/1.30  ----------------------
% 2.34/1.30  #Subsume      : 8
% 2.34/1.30  #Demod        : 15
% 2.34/1.30  #Tautology    : 53
% 2.34/1.30  #SimpNegUnit  : 2
% 2.34/1.30  #BackRed      : 0
% 2.34/1.30  
% 2.34/1.30  #Partial instantiations: 0
% 2.34/1.30  #Strategies tried      : 1
% 2.34/1.30  
% 2.34/1.30  Timing (in seconds)
% 2.34/1.30  ----------------------
% 2.34/1.31  Preprocessing        : 0.30
% 2.34/1.31  Parsing              : 0.16
% 2.34/1.31  CNF conversion       : 0.02
% 2.34/1.31  Main loop            : 0.26
% 2.34/1.31  Inferencing          : 0.10
% 2.34/1.31  Reduction            : 0.08
% 2.34/1.31  Demodulation         : 0.06
% 2.34/1.31  BG Simplification    : 0.02
% 2.34/1.31  Subsumption          : 0.04
% 2.34/1.31  Abstraction          : 0.01
% 2.34/1.31  MUC search           : 0.00
% 2.34/1.31  Cooper               : 0.00
% 2.34/1.31  Total                : 0.58
% 2.34/1.31  Index Insertion      : 0.00
% 2.34/1.31  Index Deletion       : 0.00
% 2.34/1.31  Index Matching       : 0.00
% 2.34/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
