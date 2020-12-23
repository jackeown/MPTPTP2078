%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:51 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 105 expanded)
%              Number of leaves         :   26 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :   79 ( 171 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_66,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

tff(c_40,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_102,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_34,plain,(
    ! [A_21] : ~ v1_xboole_0(k1_zfmisc_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_130,plain,(
    ! [B_42,A_43] :
      ( r2_hidden(B_42,A_43)
      | ~ m1_subset_1(B_42,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [C_16,A_12] :
      ( r1_tarski(C_16,A_12)
      | ~ r2_hidden(C_16,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_137,plain,(
    ! [B_42,A_12] :
      ( r1_tarski(B_42,A_12)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_12))
      | v1_xboole_0(k1_zfmisc_1(A_12)) ) ),
    inference(resolution,[status(thm)],[c_130,c_12])).

tff(c_157,plain,(
    ! [B_46,A_47] :
      ( r1_tarski(B_46,A_47)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_137])).

tff(c_173,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_157])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_178,plain,(
    k3_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_173,c_6])).

tff(c_201,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_178])).

tff(c_223,plain,(
    ! [A_48,B_49] :
      ( k4_xboole_0(A_48,B_49) = k3_subset_1(A_48,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_239,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_223])).

tff(c_10,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_245,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')) = k3_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_10])).

tff(c_248,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_245])).

tff(c_46,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_183,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_46])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_174,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_157])).

tff(c_182,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_174,c_6])).

tff(c_240,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_223])).

tff(c_253,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_10])).

tff(c_256,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_2,c_253])).

tff(c_306,plain,(
    ! [C_50,B_51,A_52] :
      ( r1_tarski(k4_xboole_0(C_50,B_51),k4_xboole_0(C_50,A_52))
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_773,plain,(
    ! [A_71] :
      ( r1_tarski('#skF_4',k4_xboole_0('#skF_3',A_71))
      | ~ r1_tarski(A_71,k3_subset_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_306])).

tff(c_780,plain,(
    r1_tarski('#skF_4',k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_183,c_773])).

tff(c_785,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_780])).

tff(c_787,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_785])).

tff(c_788,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_789,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_943,plain,(
    ! [A_87,B_88] :
      ( k4_xboole_0(A_87,B_88) = k3_subset_1(A_87,B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_960,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_943])).

tff(c_959,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_943])).

tff(c_8,plain,(
    ! [C_9,B_8,A_7] :
      ( r1_tarski(k4_xboole_0(C_9,B_8),k4_xboole_0(C_9,A_7))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1121,plain,(
    ! [A_94] :
      ( r1_tarski(k3_subset_1('#skF_3','#skF_5'),k4_xboole_0('#skF_3',A_94))
      | ~ r1_tarski(A_94,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_959,c_8])).

tff(c_1133,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_1121])).

tff(c_1143,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_789,c_1133])).

tff(c_1145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_788,c_1143])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:49:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.46  
% 3.22/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.47  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.26/1.47  
% 3.26/1.47  %Foreground sorts:
% 3.26/1.47  
% 3.26/1.47  
% 3.26/1.47  %Background operators:
% 3.26/1.47  
% 3.26/1.47  
% 3.26/1.47  %Foreground operators:
% 3.26/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.26/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.26/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.26/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.47  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.26/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.26/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.26/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.26/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.26/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.26/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.26/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.26/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.26/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.26/1.47  
% 3.26/1.48  tff(f_76, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 3.26/1.48  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.26/1.48  tff(f_66, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.26/1.48  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.26/1.48  tff(f_46, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.26/1.48  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.26/1.48  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.26/1.48  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.26/1.48  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 3.26/1.48  tff(c_40, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.26/1.48  tff(c_102, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_40])).
% 3.26/1.48  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.26/1.48  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.26/1.48  tff(c_34, plain, (![A_21]: (~v1_xboole_0(k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.26/1.48  tff(c_130, plain, (![B_42, A_43]: (r2_hidden(B_42, A_43) | ~m1_subset_1(B_42, A_43) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.26/1.48  tff(c_12, plain, (![C_16, A_12]: (r1_tarski(C_16, A_12) | ~r2_hidden(C_16, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.26/1.48  tff(c_137, plain, (![B_42, A_12]: (r1_tarski(B_42, A_12) | ~m1_subset_1(B_42, k1_zfmisc_1(A_12)) | v1_xboole_0(k1_zfmisc_1(A_12)))), inference(resolution, [status(thm)], [c_130, c_12])).
% 3.26/1.48  tff(c_157, plain, (![B_46, A_47]: (r1_tarski(B_46, A_47) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)))), inference(negUnitSimplification, [status(thm)], [c_34, c_137])).
% 3.26/1.48  tff(c_173, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_157])).
% 3.26/1.48  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.26/1.48  tff(c_178, plain, (k3_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_173, c_6])).
% 3.26/1.48  tff(c_201, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2, c_178])).
% 3.26/1.48  tff(c_223, plain, (![A_48, B_49]: (k4_xboole_0(A_48, B_49)=k3_subset_1(A_48, B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.26/1.48  tff(c_239, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_36, c_223])).
% 3.26/1.48  tff(c_10, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.26/1.48  tff(c_245, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))=k3_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_239, c_10])).
% 3.26/1.48  tff(c_248, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_201, c_245])).
% 3.26/1.48  tff(c_46, plain, (r1_tarski('#skF_4', '#skF_5') | r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.26/1.48  tff(c_183, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_102, c_46])).
% 3.26/1.48  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.26/1.48  tff(c_174, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_157])).
% 3.26/1.48  tff(c_182, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_174, c_6])).
% 3.26/1.48  tff(c_240, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_223])).
% 3.26/1.48  tff(c_253, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_240, c_10])).
% 3.26/1.48  tff(c_256, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_182, c_2, c_253])).
% 3.26/1.48  tff(c_306, plain, (![C_50, B_51, A_52]: (r1_tarski(k4_xboole_0(C_50, B_51), k4_xboole_0(C_50, A_52)) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.26/1.48  tff(c_773, plain, (![A_71]: (r1_tarski('#skF_4', k4_xboole_0('#skF_3', A_71)) | ~r1_tarski(A_71, k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_256, c_306])).
% 3.26/1.48  tff(c_780, plain, (r1_tarski('#skF_4', k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5')))), inference(resolution, [status(thm)], [c_183, c_773])).
% 3.26/1.48  tff(c_785, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_248, c_780])).
% 3.26/1.48  tff(c_787, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_785])).
% 3.26/1.48  tff(c_788, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_40])).
% 3.26/1.48  tff(c_789, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_40])).
% 3.26/1.48  tff(c_943, plain, (![A_87, B_88]: (k4_xboole_0(A_87, B_88)=k3_subset_1(A_87, B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.26/1.48  tff(c_960, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_943])).
% 3.26/1.48  tff(c_959, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_36, c_943])).
% 3.26/1.48  tff(c_8, plain, (![C_9, B_8, A_7]: (r1_tarski(k4_xboole_0(C_9, B_8), k4_xboole_0(C_9, A_7)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.26/1.48  tff(c_1121, plain, (![A_94]: (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k4_xboole_0('#skF_3', A_94)) | ~r1_tarski(A_94, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_959, c_8])).
% 3.26/1.48  tff(c_1133, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_960, c_1121])).
% 3.26/1.48  tff(c_1143, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_789, c_1133])).
% 3.26/1.48  tff(c_1145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_788, c_1143])).
% 3.26/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.48  
% 3.26/1.48  Inference rules
% 3.26/1.48  ----------------------
% 3.26/1.48  #Ref     : 0
% 3.26/1.48  #Sup     : 312
% 3.26/1.48  #Fact    : 0
% 3.26/1.48  #Define  : 0
% 3.26/1.48  #Split   : 4
% 3.26/1.48  #Chain   : 0
% 3.26/1.48  #Close   : 0
% 3.26/1.48  
% 3.26/1.48  Ordering : KBO
% 3.26/1.48  
% 3.26/1.48  Simplification rules
% 3.26/1.48  ----------------------
% 3.26/1.48  #Subsume      : 13
% 3.26/1.48  #Demod        : 87
% 3.26/1.48  #Tautology    : 153
% 3.26/1.48  #SimpNegUnit  : 8
% 3.26/1.48  #BackRed      : 1
% 3.26/1.48  
% 3.26/1.48  #Partial instantiations: 0
% 3.26/1.48  #Strategies tried      : 1
% 3.26/1.48  
% 3.26/1.48  Timing (in seconds)
% 3.26/1.48  ----------------------
% 3.26/1.48  Preprocessing        : 0.31
% 3.26/1.48  Parsing              : 0.16
% 3.26/1.48  CNF conversion       : 0.02
% 3.26/1.48  Main loop            : 0.42
% 3.26/1.48  Inferencing          : 0.15
% 3.26/1.48  Reduction            : 0.14
% 3.26/1.48  Demodulation         : 0.10
% 3.26/1.48  BG Simplification    : 0.02
% 3.26/1.48  Subsumption          : 0.07
% 3.26/1.48  Abstraction          : 0.02
% 3.26/1.48  MUC search           : 0.00
% 3.26/1.48  Cooper               : 0.00
% 3.26/1.48  Total                : 0.77
% 3.26/1.48  Index Insertion      : 0.00
% 3.26/1.48  Index Deletion       : 0.00
% 3.26/1.48  Index Matching       : 0.00
% 3.26/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
