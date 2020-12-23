%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:40 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :   69 (  83 expanded)
%              Number of leaves         :   30 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   89 ( 128 expanded)
%              Number of equality atoms :   21 (  23 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,k3_subset_1(A,C))
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_78,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_54,plain,
    ( r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5'))
    | r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_70,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_448,plain,(
    ! [A_72,B_73] :
      ( k4_xboole_0(A_72,B_73) = k3_subset_1(A_72,B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_464,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_448])).

tff(c_18,plain,(
    ! [A_15,C_17,B_16] :
      ( r1_xboole_0(A_15,k4_xboole_0(C_17,B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_556,plain,(
    ! [A_75] :
      ( r1_xboole_0(A_75,k3_subset_1('#skF_3','#skF_5'))
      | ~ r1_tarski(A_75,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_464,c_18])).

tff(c_48,plain,
    ( ~ r1_tarski('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_141,plain,(
    ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_48])).

tff(c_561,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_556,c_141])).

tff(c_569,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_561])).

tff(c_571,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_575,plain,(
    k4_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_571])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_42,plain,(
    ! [A_27] : ~ v1_xboole_0(k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_624,plain,(
    ! [B_85,A_86] :
      ( r2_hidden(B_85,A_86)
      | ~ m1_subset_1(B_85,A_86)
      | v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [C_22,A_18] :
      ( r1_tarski(C_22,A_18)
      | ~ r2_hidden(C_22,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_628,plain,(
    ! [B_85,A_18] :
      ( r1_tarski(B_85,A_18)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_18))
      | v1_xboole_0(k1_zfmisc_1(A_18)) ) ),
    inference(resolution,[status(thm)],[c_624,c_20])).

tff(c_632,plain,(
    ! [B_87,A_88] :
      ( r1_tarski(B_87,A_88)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_88)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_628])).

tff(c_645,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_632])).

tff(c_570,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1204,plain,(
    ! [A_123,B_124] :
      ( k4_xboole_0(A_123,B_124) = k3_subset_1(A_123,B_124)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(A_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1220,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_1204])).

tff(c_16,plain,(
    ! [B_13,A_12,C_14] :
      ( r1_xboole_0(B_13,k4_xboole_0(A_12,C_14))
      | ~ r1_xboole_0(A_12,k4_xboole_0(B_13,C_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1402,plain,(
    ! [A_133] :
      ( r1_xboole_0('#skF_3',k4_xboole_0(A_133,'#skF_5'))
      | ~ r1_xboole_0(A_133,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1220,c_16])).

tff(c_1415,plain,(
    r1_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_570,c_1402])).

tff(c_14,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_xboole_0(A_9,C_11)
      | ~ r1_xboole_0(B_10,C_11)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1472,plain,(
    ! [A_137] :
      ( r1_xboole_0(A_137,k4_xboole_0('#skF_4','#skF_5'))
      | ~ r1_tarski(A_137,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1415,c_14])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2087,plain,(
    ! [A_163] :
      ( k3_xboole_0(A_163,k4_xboole_0('#skF_4','#skF_5')) = k1_xboole_0
      | ~ r1_tarski(A_163,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1472,c_2])).

tff(c_10,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_715,plain,(
    ! [A_95,B_96] : k4_xboole_0(A_95,k4_xboole_0(A_95,B_96)) = k3_xboole_0(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_718,plain,(
    ! [A_95,B_96] : k4_xboole_0(A_95,k3_xboole_0(A_95,B_96)) = k3_xboole_0(A_95,k4_xboole_0(A_95,B_96)) ),
    inference(superposition,[status(thm),theory(equality)],[c_715,c_12])).

tff(c_740,plain,(
    ! [A_95,B_96] : k3_xboole_0(A_95,k4_xboole_0(A_95,B_96)) = k4_xboole_0(A_95,B_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_718])).

tff(c_2113,plain,
    ( k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2087,c_740])).

tff(c_2146,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_2113])).

tff(c_2148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_575,c_2146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:58:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.88/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.79  
% 3.88/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.79  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.88/1.79  
% 3.88/1.79  %Foreground sorts:
% 3.88/1.79  
% 3.88/1.79  
% 3.88/1.79  %Background operators:
% 3.88/1.79  
% 3.88/1.79  
% 3.88/1.79  %Foreground operators:
% 3.88/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.88/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.88/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.88/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.88/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.88/1.79  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.88/1.79  tff('#skF_5', type, '#skF_5': $i).
% 3.88/1.79  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.88/1.79  tff('#skF_3', type, '#skF_3': $i).
% 3.88/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.88/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.88/1.79  tff('#skF_4', type, '#skF_4': $i).
% 3.88/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.88/1.79  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.88/1.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.88/1.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.88/1.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.88/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.88/1.79  
% 3.88/1.81  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.88/1.81  tff(f_88, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 3.88/1.81  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.88/1.81  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.88/1.81  tff(f_78, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.88/1.81  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.88/1.81  tff(f_58, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.88/1.81  tff(f_47, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 3.88/1.81  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.88/1.81  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.88/1.81  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.88/1.81  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.88/1.81  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.88/1.81  tff(c_54, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5')) | r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.88/1.81  tff(c_70, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_54])).
% 3.88/1.81  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.88/1.81  tff(c_448, plain, (![A_72, B_73]: (k4_xboole_0(A_72, B_73)=k3_subset_1(A_72, B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.88/1.81  tff(c_464, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_448])).
% 3.88/1.81  tff(c_18, plain, (![A_15, C_17, B_16]: (r1_xboole_0(A_15, k4_xboole_0(C_17, B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.88/1.81  tff(c_556, plain, (![A_75]: (r1_xboole_0(A_75, k3_subset_1('#skF_3', '#skF_5')) | ~r1_tarski(A_75, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_464, c_18])).
% 3.88/1.81  tff(c_48, plain, (~r1_tarski('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.88/1.81  tff(c_141, plain, (~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_48])).
% 3.88/1.81  tff(c_561, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_556, c_141])).
% 3.88/1.81  tff(c_569, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_561])).
% 3.88/1.81  tff(c_571, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_54])).
% 3.88/1.81  tff(c_575, plain, (k4_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_571])).
% 3.88/1.81  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.88/1.81  tff(c_42, plain, (![A_27]: (~v1_xboole_0(k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.88/1.81  tff(c_624, plain, (![B_85, A_86]: (r2_hidden(B_85, A_86) | ~m1_subset_1(B_85, A_86) | v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.88/1.81  tff(c_20, plain, (![C_22, A_18]: (r1_tarski(C_22, A_18) | ~r2_hidden(C_22, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.88/1.81  tff(c_628, plain, (![B_85, A_18]: (r1_tarski(B_85, A_18) | ~m1_subset_1(B_85, k1_zfmisc_1(A_18)) | v1_xboole_0(k1_zfmisc_1(A_18)))), inference(resolution, [status(thm)], [c_624, c_20])).
% 3.88/1.81  tff(c_632, plain, (![B_87, A_88]: (r1_tarski(B_87, A_88) | ~m1_subset_1(B_87, k1_zfmisc_1(A_88)))), inference(negUnitSimplification, [status(thm)], [c_42, c_628])).
% 3.88/1.81  tff(c_645, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_632])).
% 3.88/1.81  tff(c_570, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_54])).
% 3.88/1.81  tff(c_1204, plain, (![A_123, B_124]: (k4_xboole_0(A_123, B_124)=k3_subset_1(A_123, B_124) | ~m1_subset_1(B_124, k1_zfmisc_1(A_123)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.88/1.81  tff(c_1220, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_1204])).
% 3.88/1.81  tff(c_16, plain, (![B_13, A_12, C_14]: (r1_xboole_0(B_13, k4_xboole_0(A_12, C_14)) | ~r1_xboole_0(A_12, k4_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.88/1.81  tff(c_1402, plain, (![A_133]: (r1_xboole_0('#skF_3', k4_xboole_0(A_133, '#skF_5')) | ~r1_xboole_0(A_133, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1220, c_16])).
% 3.88/1.81  tff(c_1415, plain, (r1_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_570, c_1402])).
% 3.88/1.81  tff(c_14, plain, (![A_9, C_11, B_10]: (r1_xboole_0(A_9, C_11) | ~r1_xboole_0(B_10, C_11) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.88/1.81  tff(c_1472, plain, (![A_137]: (r1_xboole_0(A_137, k4_xboole_0('#skF_4', '#skF_5')) | ~r1_tarski(A_137, '#skF_3'))), inference(resolution, [status(thm)], [c_1415, c_14])).
% 3.88/1.81  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.88/1.81  tff(c_2087, plain, (![A_163]: (k3_xboole_0(A_163, k4_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0 | ~r1_tarski(A_163, '#skF_3'))), inference(resolution, [status(thm)], [c_1472, c_2])).
% 3.88/1.81  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.88/1.81  tff(c_715, plain, (![A_95, B_96]: (k4_xboole_0(A_95, k4_xboole_0(A_95, B_96))=k3_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.88/1.81  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.88/1.81  tff(c_718, plain, (![A_95, B_96]: (k4_xboole_0(A_95, k3_xboole_0(A_95, B_96))=k3_xboole_0(A_95, k4_xboole_0(A_95, B_96)))), inference(superposition, [status(thm), theory('equality')], [c_715, c_12])).
% 3.88/1.81  tff(c_740, plain, (![A_95, B_96]: (k3_xboole_0(A_95, k4_xboole_0(A_95, B_96))=k4_xboole_0(A_95, B_96))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_718])).
% 3.88/1.81  tff(c_2113, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | ~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2087, c_740])).
% 3.88/1.81  tff(c_2146, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_645, c_2113])).
% 3.88/1.81  tff(c_2148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_575, c_2146])).
% 3.88/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.81  
% 3.88/1.81  Inference rules
% 3.88/1.81  ----------------------
% 3.88/1.81  #Ref     : 0
% 3.88/1.81  #Sup     : 562
% 3.88/1.81  #Fact    : 0
% 3.88/1.81  #Define  : 0
% 3.88/1.81  #Split   : 5
% 3.88/1.81  #Chain   : 0
% 3.88/1.81  #Close   : 0
% 3.88/1.81  
% 3.88/1.81  Ordering : KBO
% 3.88/1.81  
% 3.88/1.81  Simplification rules
% 3.88/1.81  ----------------------
% 3.88/1.81  #Subsume      : 60
% 3.88/1.81  #Demod        : 269
% 3.88/1.81  #Tautology    : 287
% 3.88/1.81  #SimpNegUnit  : 14
% 3.88/1.81  #BackRed      : 2
% 3.88/1.81  
% 3.88/1.81  #Partial instantiations: 0
% 3.88/1.81  #Strategies tried      : 1
% 3.88/1.81  
% 3.88/1.81  Timing (in seconds)
% 3.88/1.81  ----------------------
% 4.13/1.81  Preprocessing        : 0.40
% 4.13/1.81  Parsing              : 0.23
% 4.13/1.81  CNF conversion       : 0.03
% 4.13/1.81  Main loop            : 0.62
% 4.13/1.81  Inferencing          : 0.23
% 4.13/1.81  Reduction            : 0.20
% 4.13/1.81  Demodulation         : 0.14
% 4.13/1.81  BG Simplification    : 0.03
% 4.13/1.81  Subsumption          : 0.10
% 4.13/1.81  Abstraction          : 0.03
% 4.13/1.81  MUC search           : 0.00
% 4.13/1.81  Cooper               : 0.00
% 4.13/1.81  Total                : 1.06
% 4.13/1.81  Index Insertion      : 0.00
% 4.13/1.81  Index Deletion       : 0.00
% 4.13/1.81  Index Matching       : 0.00
% 4.13/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
