%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:58 EST 2020

% Result     : Theorem 9.76s
% Output     : CNFRefutation 9.76s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 159 expanded)
%              Number of leaves         :   26 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :   60 ( 211 expanded)
%              Number of equality atoms :   37 ( 136 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(c_32,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_30,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_145,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = A_40
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_173,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_36,c_145])).

tff(c_34,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_795,plain,(
    ! [A_64,B_65,C_66] : k3_xboole_0(k3_xboole_0(A_64,B_65),C_66) = k3_xboole_0(A_64,k3_xboole_0(B_65,C_66)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1995,plain,(
    ! [B_94,A_95,B_96] : k3_xboole_0(B_94,k3_xboole_0(A_95,B_96)) = k3_xboole_0(A_95,k3_xboole_0(B_96,B_94)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_795])).

tff(c_3106,plain,(
    ! [A_106] : k3_xboole_0(A_106,k1_tarski('#skF_4')) = k3_xboole_0('#skF_3',k3_xboole_0(A_106,'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1995])).

tff(c_3316,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_4')) = k3_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_3106])).

tff(c_3380,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_4')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3316])).

tff(c_56,plain,(
    ! [B_32,A_33] : k3_xboole_0(B_32,A_33) = k3_xboole_0(A_33,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_71,plain,(
    ! [B_32,A_33] : r1_tarski(k3_xboole_0(B_32,A_33),A_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_10])).

tff(c_3810,plain,(
    r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3380,c_71])).

tff(c_22,plain,(
    ! [B_23,A_22] :
      ( k1_tarski(B_23) = A_22
      | k1_xboole_0 = A_22
      | ~ r1_tarski(A_22,k1_tarski(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3836,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4')
    | k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3810,c_22])).

tff(c_3842,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_3836])).

tff(c_367,plain,(
    ! [A_53,B_54] : k3_xboole_0(k3_xboole_0(A_53,B_54),A_53) = k3_xboole_0(A_53,B_54) ),
    inference(resolution,[status(thm)],[c_10,c_145])).

tff(c_382,plain,(
    ! [A_53,B_54] : k3_xboole_0(A_53,k3_xboole_0(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_2])).

tff(c_3877,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3842,c_382])).

tff(c_3903,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3842,c_3877])).

tff(c_3845,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3842,c_3380])).

tff(c_11098,plain,(
    ! [B_169,A_170] : k3_xboole_0(k3_xboole_0(B_169,A_170),A_170) = k3_xboole_0(B_169,A_170) ),
    inference(resolution,[status(thm)],[c_71,c_145])).

tff(c_16089,plain,(
    ! [B_200,A_201] : k3_xboole_0(k3_xboole_0(B_200,A_201),B_200) = k3_xboole_0(A_201,B_200) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_11098])).

tff(c_16527,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),'#skF_1') = k3_xboole_0(k1_xboole_0,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3845,c_16089])).

tff(c_16765,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),'#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3903,c_2,c_16527])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_312,plain,(
    ! [A_45,C_46,B_47] :
      ( ~ r2_hidden(A_45,C_46)
      | ~ r1_xboole_0(k2_tarski(A_45,B_47),C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_361,plain,(
    ! [A_51,C_52] :
      ( ~ r2_hidden(A_51,C_52)
      | ~ r1_xboole_0(k1_tarski(A_51),C_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_312])).

tff(c_366,plain,(
    ! [A_51,B_4] :
      ( ~ r2_hidden(A_51,B_4)
      | k3_xboole_0(k1_tarski(A_51),B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_361])).

tff(c_17025,plain,(
    ~ r2_hidden('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16765,c_366])).

tff(c_17146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_17025])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:46:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.76/3.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.76/3.55  
% 9.76/3.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.76/3.55  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.76/3.55  
% 9.76/3.55  %Foreground sorts:
% 9.76/3.55  
% 9.76/3.55  
% 9.76/3.55  %Background operators:
% 9.76/3.55  
% 9.76/3.55  
% 9.76/3.55  %Foreground operators:
% 9.76/3.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.76/3.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.76/3.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.76/3.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.76/3.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.76/3.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.76/3.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.76/3.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.76/3.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.76/3.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.76/3.55  tff('#skF_2', type, '#skF_2': $i).
% 9.76/3.55  tff('#skF_3', type, '#skF_3': $i).
% 9.76/3.55  tff('#skF_1', type, '#skF_1': $i).
% 9.76/3.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.76/3.55  tff('#skF_4', type, '#skF_4': $i).
% 9.76/3.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.76/3.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.76/3.55  
% 9.76/3.57  tff(f_67, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 9.76/3.57  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.76/3.57  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.76/3.57  tff(f_33, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 9.76/3.57  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 9.76/3.57  tff(f_53, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 9.76/3.57  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 9.76/3.57  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 9.76/3.57  tff(f_58, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 9.76/3.57  tff(c_32, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.76/3.57  tff(c_30, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.76/3.57  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.76/3.57  tff(c_36, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.76/3.57  tff(c_145, plain, (![A_40, B_41]: (k3_xboole_0(A_40, B_41)=A_40 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.76/3.57  tff(c_173, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_36, c_145])).
% 9.76/3.57  tff(c_34, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.76/3.57  tff(c_795, plain, (![A_64, B_65, C_66]: (k3_xboole_0(k3_xboole_0(A_64, B_65), C_66)=k3_xboole_0(A_64, k3_xboole_0(B_65, C_66)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.76/3.57  tff(c_1995, plain, (![B_94, A_95, B_96]: (k3_xboole_0(B_94, k3_xboole_0(A_95, B_96))=k3_xboole_0(A_95, k3_xboole_0(B_96, B_94)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_795])).
% 9.76/3.57  tff(c_3106, plain, (![A_106]: (k3_xboole_0(A_106, k1_tarski('#skF_4'))=k3_xboole_0('#skF_3', k3_xboole_0(A_106, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1995])).
% 9.76/3.57  tff(c_3316, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_4'))=k3_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_173, c_3106])).
% 9.76/3.57  tff(c_3380, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_4'))=k3_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3316])).
% 9.76/3.57  tff(c_56, plain, (![B_32, A_33]: (k3_xboole_0(B_32, A_33)=k3_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.76/3.57  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.76/3.57  tff(c_71, plain, (![B_32, A_33]: (r1_tarski(k3_xboole_0(B_32, A_33), A_33))), inference(superposition, [status(thm), theory('equality')], [c_56, c_10])).
% 9.76/3.57  tff(c_3810, plain, (r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3380, c_71])).
% 9.76/3.57  tff(c_22, plain, (![B_23, A_22]: (k1_tarski(B_23)=A_22 | k1_xboole_0=A_22 | ~r1_tarski(A_22, k1_tarski(B_23)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.76/3.57  tff(c_3836, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4') | k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_3810, c_22])).
% 9.76/3.57  tff(c_3842, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_30, c_3836])).
% 9.76/3.57  tff(c_367, plain, (![A_53, B_54]: (k3_xboole_0(k3_xboole_0(A_53, B_54), A_53)=k3_xboole_0(A_53, B_54))), inference(resolution, [status(thm)], [c_10, c_145])).
% 9.76/3.57  tff(c_382, plain, (![A_53, B_54]: (k3_xboole_0(A_53, k3_xboole_0(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(superposition, [status(thm), theory('equality')], [c_367, c_2])).
% 9.76/3.57  tff(c_3877, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3842, c_382])).
% 9.76/3.57  tff(c_3903, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3842, c_3877])).
% 9.76/3.57  tff(c_3845, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3842, c_3380])).
% 9.76/3.57  tff(c_11098, plain, (![B_169, A_170]: (k3_xboole_0(k3_xboole_0(B_169, A_170), A_170)=k3_xboole_0(B_169, A_170))), inference(resolution, [status(thm)], [c_71, c_145])).
% 9.76/3.57  tff(c_16089, plain, (![B_200, A_201]: (k3_xboole_0(k3_xboole_0(B_200, A_201), B_200)=k3_xboole_0(A_201, B_200))), inference(superposition, [status(thm), theory('equality')], [c_2, c_11098])).
% 9.76/3.57  tff(c_16527, plain, (k3_xboole_0(k1_tarski('#skF_4'), '#skF_1')=k3_xboole_0(k1_xboole_0, '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3845, c_16089])).
% 9.76/3.57  tff(c_16765, plain, (k3_xboole_0(k1_tarski('#skF_4'), '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3903, c_2, c_16527])).
% 9.76/3.57  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.76/3.57  tff(c_14, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.76/3.57  tff(c_312, plain, (![A_45, C_46, B_47]: (~r2_hidden(A_45, C_46) | ~r1_xboole_0(k2_tarski(A_45, B_47), C_46))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.76/3.57  tff(c_361, plain, (![A_51, C_52]: (~r2_hidden(A_51, C_52) | ~r1_xboole_0(k1_tarski(A_51), C_52))), inference(superposition, [status(thm), theory('equality')], [c_14, c_312])).
% 9.76/3.57  tff(c_366, plain, (![A_51, B_4]: (~r2_hidden(A_51, B_4) | k3_xboole_0(k1_tarski(A_51), B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_361])).
% 9.76/3.57  tff(c_17025, plain, (~r2_hidden('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16765, c_366])).
% 9.76/3.57  tff(c_17146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_17025])).
% 9.76/3.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.76/3.57  
% 9.76/3.57  Inference rules
% 9.76/3.57  ----------------------
% 9.76/3.57  #Ref     : 0
% 9.76/3.57  #Sup     : 4173
% 9.76/3.57  #Fact    : 1
% 9.76/3.57  #Define  : 0
% 9.76/3.57  #Split   : 1
% 9.76/3.57  #Chain   : 0
% 9.76/3.57  #Close   : 0
% 9.76/3.57  
% 9.76/3.57  Ordering : KBO
% 9.76/3.57  
% 9.76/3.57  Simplification rules
% 9.76/3.57  ----------------------
% 9.76/3.57  #Subsume      : 93
% 9.76/3.57  #Demod        : 5383
% 9.76/3.57  #Tautology    : 2650
% 9.76/3.57  #SimpNegUnit  : 13
% 9.76/3.57  #BackRed      : 8
% 9.76/3.57  
% 9.76/3.57  #Partial instantiations: 0
% 9.76/3.57  #Strategies tried      : 1
% 9.76/3.57  
% 9.76/3.57  Timing (in seconds)
% 9.76/3.57  ----------------------
% 9.76/3.57  Preprocessing        : 0.31
% 9.76/3.57  Parsing              : 0.17
% 9.76/3.57  CNF conversion       : 0.02
% 9.76/3.57  Main loop            : 2.49
% 9.76/3.57  Inferencing          : 0.43
% 9.76/3.57  Reduction            : 1.53
% 9.76/3.57  Demodulation         : 1.38
% 9.76/3.57  BG Simplification    : 0.06
% 9.76/3.57  Subsumption          : 0.34
% 9.76/3.57  Abstraction          : 0.07
% 9.76/3.57  MUC search           : 0.00
% 9.76/3.57  Cooper               : 0.00
% 9.76/3.57  Total                : 2.83
% 9.76/3.57  Index Insertion      : 0.00
% 9.76/3.57  Index Deletion       : 0.00
% 9.76/3.57  Index Matching       : 0.00
% 9.76/3.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
