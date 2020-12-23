%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:37 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   60 (  68 expanded)
%              Number of leaves         :   31 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   62 (  72 expanded)
%              Number of equality atoms :   28 (  35 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_46,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_66,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_63,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_34,plain,(
    ! [A_20] : k2_subset_1(A_20) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_42,plain,(
    k4_subset_1('#skF_3','#skF_4',k2_subset_1('#skF_3')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_45,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_42])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_178,plain,(
    ! [A_43,B_44] : k3_tarski(k2_tarski(A_43,B_44)) = k2_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_212,plain,(
    ! [A_51,B_52] : k3_tarski(k2_tarski(A_51,B_52)) = k2_xboole_0(B_52,A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_178])).

tff(c_24,plain,(
    ! [A_16,B_17] : k3_tarski(k2_tarski(A_16,B_17)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_218,plain,(
    ! [B_52,A_51] : k2_xboole_0(B_52,A_51) = k2_xboole_0(A_51,B_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_24])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_38,plain,(
    ! [A_22] : ~ v1_xboole_0(k1_zfmisc_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_281,plain,(
    ! [B_59,A_60] :
      ( r2_hidden(B_59,A_60)
      | ~ m1_subset_1(B_59,A_60)
      | v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [C_15,A_11] :
      ( r1_tarski(C_15,A_11)
      | ~ r2_hidden(C_15,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_288,plain,(
    ! [B_59,A_11] :
      ( r1_tarski(B_59,A_11)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_11))
      | v1_xboole_0(k1_zfmisc_1(A_11)) ) ),
    inference(resolution,[status(thm)],[c_281,c_12])).

tff(c_293,plain,(
    ! [B_61,A_62] :
      ( r1_tarski(B_61,A_62)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_62)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_288])).

tff(c_310,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_293])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_320,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_310,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_124,plain,(
    ! [A_33,B_34] : k2_xboole_0(A_33,k3_xboole_0(A_33,B_34)) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_133,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_124])).

tff(c_339,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_133])).

tff(c_366,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_339])).

tff(c_36,plain,(
    ! [A_21] : m1_subset_1(k2_subset_1(A_21),k1_zfmisc_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_46,plain,(
    ! [A_21] : m1_subset_1(A_21,k1_zfmisc_1(A_21)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36])).

tff(c_414,plain,(
    ! [A_74,B_75,C_76] :
      ( k4_subset_1(A_74,B_75,C_76) = k2_xboole_0(B_75,C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(A_74))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_428,plain,(
    ! [A_77,B_78] :
      ( k4_subset_1(A_77,B_78,A_77) = k2_xboole_0(B_78,A_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(resolution,[status(thm)],[c_46,c_414])).

tff(c_437,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_428])).

tff(c_443,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_437])).

tff(c_445,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_443])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:23:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.32  
% 2.25/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.32  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.25/1.32  
% 2.25/1.32  %Foreground sorts:
% 2.25/1.32  
% 2.25/1.32  
% 2.25/1.32  %Background operators:
% 2.25/1.32  
% 2.25/1.32  
% 2.25/1.32  %Foreground operators:
% 2.25/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.25/1.32  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.25/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.25/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.25/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.25/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.25/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.25/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.25/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.25/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.25/1.32  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.25/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.25/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.32  
% 2.39/1.34  tff(f_61, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.39/1.34  tff(f_77, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 2.39/1.34  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.39/1.34  tff(f_46, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.39/1.34  tff(f_66, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.39/1.34  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.39/1.34  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.39/1.34  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.39/1.34  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.39/1.34  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.39/1.34  tff(f_63, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.39/1.34  tff(f_72, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.39/1.34  tff(c_34, plain, (![A_20]: (k2_subset_1(A_20)=A_20)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.39/1.34  tff(c_42, plain, (k4_subset_1('#skF_3', '#skF_4', k2_subset_1('#skF_3'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.39/1.34  tff(c_45, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_42])).
% 2.39/1.34  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.39/1.34  tff(c_178, plain, (![A_43, B_44]: (k3_tarski(k2_tarski(A_43, B_44))=k2_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.39/1.34  tff(c_212, plain, (![A_51, B_52]: (k3_tarski(k2_tarski(A_51, B_52))=k2_xboole_0(B_52, A_51))), inference(superposition, [status(thm), theory('equality')], [c_8, c_178])).
% 2.39/1.34  tff(c_24, plain, (![A_16, B_17]: (k3_tarski(k2_tarski(A_16, B_17))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.39/1.34  tff(c_218, plain, (![B_52, A_51]: (k2_xboole_0(B_52, A_51)=k2_xboole_0(A_51, B_52))), inference(superposition, [status(thm), theory('equality')], [c_212, c_24])).
% 2.39/1.34  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.39/1.34  tff(c_38, plain, (![A_22]: (~v1_xboole_0(k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.39/1.34  tff(c_281, plain, (![B_59, A_60]: (r2_hidden(B_59, A_60) | ~m1_subset_1(B_59, A_60) | v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.39/1.34  tff(c_12, plain, (![C_15, A_11]: (r1_tarski(C_15, A_11) | ~r2_hidden(C_15, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.39/1.34  tff(c_288, plain, (![B_59, A_11]: (r1_tarski(B_59, A_11) | ~m1_subset_1(B_59, k1_zfmisc_1(A_11)) | v1_xboole_0(k1_zfmisc_1(A_11)))), inference(resolution, [status(thm)], [c_281, c_12])).
% 2.39/1.34  tff(c_293, plain, (![B_61, A_62]: (r1_tarski(B_61, A_62) | ~m1_subset_1(B_61, k1_zfmisc_1(A_62)))), inference(negUnitSimplification, [status(thm)], [c_38, c_288])).
% 2.39/1.34  tff(c_310, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_293])).
% 2.39/1.34  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.39/1.34  tff(c_320, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_310, c_6])).
% 2.39/1.34  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.39/1.34  tff(c_124, plain, (![A_33, B_34]: (k2_xboole_0(A_33, k3_xboole_0(A_33, B_34))=A_33)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.39/1.34  tff(c_133, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k3_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_124])).
% 2.39/1.34  tff(c_339, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_320, c_133])).
% 2.39/1.34  tff(c_366, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_218, c_339])).
% 2.39/1.34  tff(c_36, plain, (![A_21]: (m1_subset_1(k2_subset_1(A_21), k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.39/1.34  tff(c_46, plain, (![A_21]: (m1_subset_1(A_21, k1_zfmisc_1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36])).
% 2.39/1.34  tff(c_414, plain, (![A_74, B_75, C_76]: (k4_subset_1(A_74, B_75, C_76)=k2_xboole_0(B_75, C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(A_74)) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.39/1.34  tff(c_428, plain, (![A_77, B_78]: (k4_subset_1(A_77, B_78, A_77)=k2_xboole_0(B_78, A_77) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(resolution, [status(thm)], [c_46, c_414])).
% 2.39/1.34  tff(c_437, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')=k2_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_428])).
% 2.39/1.34  tff(c_443, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_366, c_437])).
% 2.39/1.34  tff(c_445, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_443])).
% 2.39/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.34  
% 2.39/1.34  Inference rules
% 2.39/1.34  ----------------------
% 2.39/1.34  #Ref     : 0
% 2.39/1.34  #Sup     : 95
% 2.39/1.34  #Fact    : 0
% 2.39/1.34  #Define  : 0
% 2.39/1.34  #Split   : 0
% 2.39/1.34  #Chain   : 0
% 2.39/1.34  #Close   : 0
% 2.39/1.34  
% 2.39/1.34  Ordering : KBO
% 2.39/1.34  
% 2.39/1.34  Simplification rules
% 2.39/1.34  ----------------------
% 2.39/1.34  #Subsume      : 7
% 2.39/1.34  #Demod        : 17
% 2.39/1.34  #Tautology    : 63
% 2.39/1.34  #SimpNegUnit  : 3
% 2.39/1.34  #BackRed      : 0
% 2.39/1.34  
% 2.39/1.34  #Partial instantiations: 0
% 2.39/1.34  #Strategies tried      : 1
% 2.39/1.34  
% 2.39/1.34  Timing (in seconds)
% 2.39/1.34  ----------------------
% 2.39/1.34  Preprocessing        : 0.32
% 2.39/1.34  Parsing              : 0.15
% 2.39/1.34  CNF conversion       : 0.02
% 2.39/1.34  Main loop            : 0.23
% 2.39/1.34  Inferencing          : 0.09
% 2.39/1.34  Reduction            : 0.08
% 2.39/1.34  Demodulation         : 0.06
% 2.39/1.34  BG Simplification    : 0.01
% 2.39/1.34  Subsumption          : 0.04
% 2.39/1.34  Abstraction          : 0.01
% 2.39/1.34  MUC search           : 0.00
% 2.39/1.34  Cooper               : 0.00
% 2.39/1.34  Total                : 0.58
% 2.39/1.34  Index Insertion      : 0.00
% 2.39/1.34  Index Deletion       : 0.00
% 2.39/1.34  Index Matching       : 0.00
% 2.39/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
