%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:59 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 100 expanded)
%              Number of leaves         :   29 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :   69 ( 168 expanded)
%              Number of equality atoms :   14 (  30 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ! [C] :
            ( m1_subset_1(C,A)
           => ( A != k1_xboole_0
             => m1_subset_1(k2_tarski(B,C),k1_zfmisc_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_70,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_44,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_96,plain,(
    ! [B_39,A_40] :
      ( v1_xboole_0(B_39)
      | ~ m1_subset_1(B_39,A_40)
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_107,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_96])).

tff(c_109,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_42,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28,plain,(
    ! [B_23,A_22] :
      ( r2_hidden(B_23,A_22)
      | ~ m1_subset_1(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_343,plain,(
    ! [A_87,B_88,C_89] :
      ( r1_tarski(k2_tarski(A_87,B_88),C_89)
      | ~ r2_hidden(B_88,C_89)
      | ~ r2_hidden(A_87,C_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_547,plain,(
    ! [A_96,B_97,C_98] :
      ( k3_xboole_0(k2_tarski(A_96,B_97),C_98) = k2_tarski(A_96,B_97)
      | ~ r2_hidden(B_97,C_98)
      | ~ r2_hidden(A_96,C_98) ) ),
    inference(resolution,[status(thm)],[c_343,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_155,plain,(
    ! [A_56,B_57] : k4_xboole_0(A_56,k4_xboole_0(A_56,B_57)) = k3_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_36,plain,(
    ! [A_26,B_27] : k6_subset_1(A_26,B_27) = k4_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_34,plain,(
    ! [A_24,B_25] : m1_subset_1(k6_subset_1(A_24,B_25),k1_zfmisc_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_45,plain,(
    ! [A_24,B_25] : m1_subset_1(k4_xboole_0(A_24,B_25),k1_zfmisc_1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34])).

tff(c_177,plain,(
    ! [A_61,B_62] : m1_subset_1(k3_xboole_0(A_61,B_62),k1_zfmisc_1(A_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_45])).

tff(c_183,plain,(
    ! [B_2,A_1] : m1_subset_1(k3_xboole_0(B_2,A_1),k1_zfmisc_1(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_177])).

tff(c_818,plain,(
    ! [A_114,B_115,C_116] :
      ( m1_subset_1(k2_tarski(A_114,B_115),k1_zfmisc_1(C_116))
      | ~ r2_hidden(B_115,C_116)
      | ~ r2_hidden(A_114,C_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_547,c_183])).

tff(c_38,plain,(
    ~ m1_subset_1(k2_tarski('#skF_3','#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_826,plain,
    ( ~ r2_hidden('#skF_4','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_818,c_38])).

tff(c_827,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_826])).

tff(c_830,plain,
    ( ~ m1_subset_1('#skF_3','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_827])).

tff(c_833,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_830])).

tff(c_835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_833])).

tff(c_836,plain,(
    ~ r2_hidden('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_826])).

tff(c_924,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_836])).

tff(c_927,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_924])).

tff(c_929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_927])).

tff(c_931,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_8,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_938,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_931,c_8])).

tff(c_942,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_938])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:58:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.73/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.99  
% 3.73/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.99  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.73/1.99  
% 3.73/1.99  %Foreground sorts:
% 3.73/1.99  
% 3.73/1.99  
% 3.73/1.99  %Background operators:
% 3.73/1.99  
% 3.73/1.99  
% 3.73/1.99  %Foreground operators:
% 3.73/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.73/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.73/1.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.73/1.99  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.73/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.73/1.99  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.73/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.73/1.99  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.73/1.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.73/1.99  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.73/1.99  tff('#skF_2', type, '#skF_2': $i).
% 3.73/1.99  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.73/1.99  tff('#skF_3', type, '#skF_3': $i).
% 3.73/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.73/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.73/1.99  tff('#skF_4', type, '#skF_4': $i).
% 3.73/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.73/1.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.73/1.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.73/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.73/1.99  
% 4.04/2.01  tff(f_83, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (~(A = k1_xboole_0) => m1_subset_1(k2_tarski(B, C), k1_zfmisc_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_subset_1)).
% 4.04/2.01  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.04/2.01  tff(f_55, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.04/2.01  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.04/2.01  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.04/2.01  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.04/2.01  tff(f_72, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 4.04/2.01  tff(f_70, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 4.04/2.01  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.04/2.01  tff(c_40, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.04/2.01  tff(c_44, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.04/2.01  tff(c_96, plain, (![B_39, A_40]: (v1_xboole_0(B_39) | ~m1_subset_1(B_39, A_40) | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.04/2.01  tff(c_107, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_96])).
% 4.04/2.01  tff(c_109, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_107])).
% 4.04/2.01  tff(c_42, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.04/2.01  tff(c_28, plain, (![B_23, A_22]: (r2_hidden(B_23, A_22) | ~m1_subset_1(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.04/2.01  tff(c_343, plain, (![A_87, B_88, C_89]: (r1_tarski(k2_tarski(A_87, B_88), C_89) | ~r2_hidden(B_88, C_89) | ~r2_hidden(A_87, C_89))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.04/2.01  tff(c_12, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.04/2.01  tff(c_547, plain, (![A_96, B_97, C_98]: (k3_xboole_0(k2_tarski(A_96, B_97), C_98)=k2_tarski(A_96, B_97) | ~r2_hidden(B_97, C_98) | ~r2_hidden(A_96, C_98))), inference(resolution, [status(thm)], [c_343, c_12])).
% 4.04/2.01  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.04/2.01  tff(c_155, plain, (![A_56, B_57]: (k4_xboole_0(A_56, k4_xboole_0(A_56, B_57))=k3_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.04/2.01  tff(c_36, plain, (![A_26, B_27]: (k6_subset_1(A_26, B_27)=k4_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.04/2.01  tff(c_34, plain, (![A_24, B_25]: (m1_subset_1(k6_subset_1(A_24, B_25), k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.04/2.01  tff(c_45, plain, (![A_24, B_25]: (m1_subset_1(k4_xboole_0(A_24, B_25), k1_zfmisc_1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34])).
% 4.04/2.01  tff(c_177, plain, (![A_61, B_62]: (m1_subset_1(k3_xboole_0(A_61, B_62), k1_zfmisc_1(A_61)))), inference(superposition, [status(thm), theory('equality')], [c_155, c_45])).
% 4.04/2.01  tff(c_183, plain, (![B_2, A_1]: (m1_subset_1(k3_xboole_0(B_2, A_1), k1_zfmisc_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_177])).
% 4.04/2.01  tff(c_818, plain, (![A_114, B_115, C_116]: (m1_subset_1(k2_tarski(A_114, B_115), k1_zfmisc_1(C_116)) | ~r2_hidden(B_115, C_116) | ~r2_hidden(A_114, C_116))), inference(superposition, [status(thm), theory('equality')], [c_547, c_183])).
% 4.04/2.01  tff(c_38, plain, (~m1_subset_1(k2_tarski('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.04/2.01  tff(c_826, plain, (~r2_hidden('#skF_4', '#skF_2') | ~r2_hidden('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_818, c_38])).
% 4.04/2.01  tff(c_827, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_826])).
% 4.04/2.01  tff(c_830, plain, (~m1_subset_1('#skF_3', '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_827])).
% 4.04/2.01  tff(c_833, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_830])).
% 4.04/2.01  tff(c_835, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_833])).
% 4.04/2.01  tff(c_836, plain, (~r2_hidden('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_826])).
% 4.04/2.01  tff(c_924, plain, (~m1_subset_1('#skF_4', '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_836])).
% 4.04/2.01  tff(c_927, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_924])).
% 4.04/2.01  tff(c_929, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_927])).
% 4.04/2.01  tff(c_931, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_107])).
% 4.04/2.01  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.04/2.01  tff(c_938, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_931, c_8])).
% 4.04/2.01  tff(c_942, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_938])).
% 4.04/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/2.01  
% 4.04/2.01  Inference rules
% 4.04/2.01  ----------------------
% 4.04/2.01  #Ref     : 0
% 4.04/2.01  #Sup     : 232
% 4.04/2.01  #Fact    : 0
% 4.04/2.01  #Define  : 0
% 4.04/2.01  #Split   : 3
% 4.04/2.01  #Chain   : 0
% 4.04/2.01  #Close   : 0
% 4.04/2.01  
% 4.04/2.01  Ordering : KBO
% 4.04/2.01  
% 4.04/2.01  Simplification rules
% 4.04/2.01  ----------------------
% 4.04/2.01  #Subsume      : 35
% 4.04/2.01  #Demod        : 61
% 4.04/2.01  #Tautology    : 81
% 4.04/2.01  #SimpNegUnit  : 3
% 4.04/2.01  #BackRed      : 0
% 4.04/2.01  
% 4.04/2.01  #Partial instantiations: 0
% 4.04/2.01  #Strategies tried      : 1
% 4.04/2.01  
% 4.04/2.01  Timing (in seconds)
% 4.04/2.01  ----------------------
% 4.04/2.01  Preprocessing        : 0.52
% 4.04/2.01  Parsing              : 0.27
% 4.04/2.01  CNF conversion       : 0.04
% 4.04/2.01  Main loop            : 0.66
% 4.04/2.01  Inferencing          : 0.23
% 4.04/2.01  Reduction            : 0.24
% 4.04/2.01  Demodulation         : 0.20
% 4.04/2.01  BG Simplification    : 0.04
% 4.04/2.01  Subsumption          : 0.10
% 4.04/2.02  Abstraction          : 0.03
% 4.04/2.02  MUC search           : 0.00
% 4.04/2.02  Cooper               : 0.00
% 4.04/2.02  Total                : 1.23
% 4.04/2.02  Index Insertion      : 0.00
% 4.04/2.02  Index Deletion       : 0.00
% 4.04/2.02  Index Matching       : 0.00
% 4.04/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
