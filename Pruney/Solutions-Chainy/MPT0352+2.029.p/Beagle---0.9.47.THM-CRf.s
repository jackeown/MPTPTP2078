%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:50 EST 2020

% Result     : Theorem 17.83s
% Output     : CNFRefutation 17.83s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 116 expanded)
%              Number of leaves         :   28 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :   88 ( 185 expanded)
%              Number of equality atoms :   23 (  40 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_68,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

tff(c_44,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_102,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_50,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_182,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_50])).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_38,plain,(
    ! [A_22] : ~ v1_xboole_0(k1_zfmisc_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_152,plain,(
    ! [B_46,A_47] :
      ( r2_hidden(B_46,A_47)
      | ~ m1_subset_1(B_46,A_47)
      | v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [C_17,A_13] :
      ( r1_tarski(C_17,A_13)
      | ~ r2_hidden(C_17,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_159,plain,(
    ! [B_46,A_13] :
      ( r1_tarski(B_46,A_13)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_13))
      | v1_xboole_0(k1_zfmisc_1(A_13)) ) ),
    inference(resolution,[status(thm)],[c_152,c_16])).

tff(c_164,plain,(
    ! [B_48,A_49] :
      ( r1_tarski(B_48,A_49)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_159])).

tff(c_181,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_164])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_194,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_181,c_6])).

tff(c_203,plain,(
    ! [A_50,B_51] : k4_xboole_0(A_50,k4_xboole_0(A_50,B_51)) = k3_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_218,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_203])).

tff(c_227,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_218])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_334,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(A_56,B_57) = k3_subset_1(A_56,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_351,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_334])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_180,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_164])).

tff(c_190,plain,(
    k4_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_180,c_6])).

tff(c_221,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k3_xboole_0('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_203])).

tff(c_228,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12,c_221])).

tff(c_350,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_334])).

tff(c_14,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_229,plain,(
    ! [C_52,B_53,A_54] :
      ( r1_tarski(k4_xboole_0(C_52,B_53),k4_xboole_0(C_52,A_54))
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2124,plain,(
    ! [A_111,B_112,B_113] :
      ( r1_tarski(k4_xboole_0(A_111,B_112),k3_xboole_0(A_111,B_113))
      | ~ r1_tarski(k4_xboole_0(A_111,B_113),B_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_229])).

tff(c_21442,plain,(
    ! [A_385,B_386,B_387] :
      ( r1_tarski(k3_xboole_0(A_385,B_386),k3_xboole_0(A_385,B_387))
      | ~ r1_tarski(k4_xboole_0(A_385,B_387),k4_xboole_0(A_385,B_386)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2124])).

tff(c_21578,plain,(
    ! [B_386] :
      ( r1_tarski(k3_xboole_0('#skF_3',B_386),k3_xboole_0('#skF_3','#skF_5'))
      | ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k4_xboole_0('#skF_3',B_386)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_21442])).

tff(c_60864,plain,(
    ! [B_694] :
      ( r1_tarski(k3_xboole_0('#skF_3',B_694),'#skF_5')
      | ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k4_xboole_0('#skF_3',B_694)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_21578])).

tff(c_60938,plain,
    ( r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_5')
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_60864])).

tff(c_60975,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_227,c_2,c_60938])).

tff(c_60977,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_60975])).

tff(c_60978,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_60979,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_61307,plain,(
    ! [A_718,B_719] :
      ( k4_xboole_0(A_718,B_719) = k3_subset_1(A_718,B_719)
      | ~ m1_subset_1(B_719,k1_zfmisc_1(A_718)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_61323,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_61307])).

tff(c_61324,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_61307])).

tff(c_10,plain,(
    ! [C_9,B_8,A_7] :
      ( r1_tarski(k4_xboole_0(C_9,B_8),k4_xboole_0(C_9,A_7))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_61770,plain,(
    ! [B_738] :
      ( r1_tarski(k4_xboole_0('#skF_3',B_738),k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_tarski('#skF_4',B_738) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61324,c_10])).

tff(c_61789,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_61323,c_61770])).

tff(c_61804,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60979,c_61789])).

tff(c_61806,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60978,c_61804])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:59:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.83/9.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.83/9.43  
% 17.83/9.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.83/9.43  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 17.83/9.43  
% 17.83/9.43  %Foreground sorts:
% 17.83/9.43  
% 17.83/9.43  
% 17.83/9.43  %Background operators:
% 17.83/9.43  
% 17.83/9.43  
% 17.83/9.43  %Foreground operators:
% 17.83/9.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.83/9.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.83/9.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.83/9.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.83/9.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 17.83/9.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.83/9.43  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 17.83/9.43  tff('#skF_5', type, '#skF_5': $i).
% 17.83/9.43  tff('#skF_3', type, '#skF_3': $i).
% 17.83/9.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.83/9.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.83/9.43  tff('#skF_4', type, '#skF_4': $i).
% 17.83/9.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.83/9.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 17.83/9.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.83/9.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.83/9.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 17.83/9.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.83/9.43  
% 17.83/9.44  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 17.83/9.44  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 17.83/9.44  tff(f_68, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 17.83/9.44  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 17.83/9.44  tff(f_48, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 17.83/9.44  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 17.83/9.45  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 17.83/9.45  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 17.83/9.45  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 17.83/9.45  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 17.83/9.45  tff(c_44, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_78])).
% 17.83/9.45  tff(c_102, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_44])).
% 17.83/9.45  tff(c_50, plain, (r1_tarski('#skF_4', '#skF_5') | r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 17.83/9.45  tff(c_182, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_102, c_50])).
% 17.83/9.45  tff(c_12, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 17.83/9.45  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 17.83/9.45  tff(c_38, plain, (![A_22]: (~v1_xboole_0(k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 17.83/9.45  tff(c_152, plain, (![B_46, A_47]: (r2_hidden(B_46, A_47) | ~m1_subset_1(B_46, A_47) | v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_61])).
% 17.83/9.45  tff(c_16, plain, (![C_17, A_13]: (r1_tarski(C_17, A_13) | ~r2_hidden(C_17, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 17.83/9.45  tff(c_159, plain, (![B_46, A_13]: (r1_tarski(B_46, A_13) | ~m1_subset_1(B_46, k1_zfmisc_1(A_13)) | v1_xboole_0(k1_zfmisc_1(A_13)))), inference(resolution, [status(thm)], [c_152, c_16])).
% 17.83/9.45  tff(c_164, plain, (![B_48, A_49]: (r1_tarski(B_48, A_49) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)))), inference(negUnitSimplification, [status(thm)], [c_38, c_159])).
% 17.83/9.45  tff(c_181, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_164])).
% 17.83/9.45  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.83/9.45  tff(c_194, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_181, c_6])).
% 17.83/9.45  tff(c_203, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k4_xboole_0(A_50, B_51))=k3_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_41])).
% 17.83/9.45  tff(c_218, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_194, c_203])).
% 17.83/9.45  tff(c_227, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_218])).
% 17.83/9.45  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 17.83/9.45  tff(c_334, plain, (![A_56, B_57]: (k4_xboole_0(A_56, B_57)=k3_subset_1(A_56, B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 17.83/9.45  tff(c_351, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_334])).
% 17.83/9.45  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 17.83/9.45  tff(c_180, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_164])).
% 17.83/9.45  tff(c_190, plain, (k4_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_180, c_6])).
% 17.83/9.45  tff(c_221, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k3_xboole_0('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_190, c_203])).
% 17.83/9.45  tff(c_228, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12, c_221])).
% 17.83/9.45  tff(c_350, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_334])).
% 17.83/9.45  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 17.83/9.45  tff(c_229, plain, (![C_52, B_53, A_54]: (r1_tarski(k4_xboole_0(C_52, B_53), k4_xboole_0(C_52, A_54)) | ~r1_tarski(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_37])).
% 17.83/9.45  tff(c_2124, plain, (![A_111, B_112, B_113]: (r1_tarski(k4_xboole_0(A_111, B_112), k3_xboole_0(A_111, B_113)) | ~r1_tarski(k4_xboole_0(A_111, B_113), B_112))), inference(superposition, [status(thm), theory('equality')], [c_14, c_229])).
% 17.83/9.45  tff(c_21442, plain, (![A_385, B_386, B_387]: (r1_tarski(k3_xboole_0(A_385, B_386), k3_xboole_0(A_385, B_387)) | ~r1_tarski(k4_xboole_0(A_385, B_387), k4_xboole_0(A_385, B_386)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2124])).
% 17.83/9.45  tff(c_21578, plain, (![B_386]: (r1_tarski(k3_xboole_0('#skF_3', B_386), k3_xboole_0('#skF_3', '#skF_5')) | ~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k4_xboole_0('#skF_3', B_386)))), inference(superposition, [status(thm), theory('equality')], [c_350, c_21442])).
% 17.83/9.45  tff(c_60864, plain, (![B_694]: (r1_tarski(k3_xboole_0('#skF_3', B_694), '#skF_5') | ~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k4_xboole_0('#skF_3', B_694)))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_21578])).
% 17.83/9.45  tff(c_60938, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_5') | ~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_351, c_60864])).
% 17.83/9.45  tff(c_60975, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_227, c_2, c_60938])).
% 17.83/9.45  tff(c_60977, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_60975])).
% 17.83/9.45  tff(c_60978, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_44])).
% 17.83/9.45  tff(c_60979, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_44])).
% 17.83/9.45  tff(c_61307, plain, (![A_718, B_719]: (k4_xboole_0(A_718, B_719)=k3_subset_1(A_718, B_719) | ~m1_subset_1(B_719, k1_zfmisc_1(A_718)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 17.83/9.45  tff(c_61323, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_61307])).
% 17.83/9.45  tff(c_61324, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_61307])).
% 17.83/9.45  tff(c_10, plain, (![C_9, B_8, A_7]: (r1_tarski(k4_xboole_0(C_9, B_8), k4_xboole_0(C_9, A_7)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 17.83/9.45  tff(c_61770, plain, (![B_738]: (r1_tarski(k4_xboole_0('#skF_3', B_738), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', B_738))), inference(superposition, [status(thm), theory('equality')], [c_61324, c_10])).
% 17.83/9.45  tff(c_61789, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_61323, c_61770])).
% 17.83/9.45  tff(c_61804, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60979, c_61789])).
% 17.83/9.45  tff(c_61806, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60978, c_61804])).
% 17.83/9.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.83/9.45  
% 17.83/9.45  Inference rules
% 17.83/9.45  ----------------------
% 17.83/9.45  #Ref     : 1
% 17.83/9.45  #Sup     : 15417
% 17.83/9.45  #Fact    : 0
% 17.83/9.45  #Define  : 0
% 17.83/9.45  #Split   : 17
% 17.83/9.45  #Chain   : 0
% 17.83/9.45  #Close   : 0
% 17.83/9.45  
% 17.83/9.45  Ordering : KBO
% 17.83/9.45  
% 17.83/9.45  Simplification rules
% 17.83/9.45  ----------------------
% 17.83/9.45  #Subsume      : 7437
% 17.83/9.45  #Demod        : 8853
% 17.83/9.45  #Tautology    : 3794
% 17.83/9.45  #SimpNegUnit  : 916
% 17.83/9.45  #BackRed      : 57
% 17.83/9.45  
% 17.83/9.45  #Partial instantiations: 0
% 17.83/9.45  #Strategies tried      : 1
% 17.83/9.45  
% 17.83/9.45  Timing (in seconds)
% 17.83/9.45  ----------------------
% 17.83/9.45  Preprocessing        : 0.30
% 17.83/9.45  Parsing              : 0.15
% 17.83/9.45  CNF conversion       : 0.02
% 17.83/9.45  Main loop            : 8.33
% 17.83/9.45  Inferencing          : 1.25
% 17.83/9.45  Reduction            : 3.82
% 17.83/9.45  Demodulation         : 3.01
% 17.83/9.45  BG Simplification    : 0.12
% 17.83/9.45  Subsumption          : 2.65
% 17.83/9.45  Abstraction          : 0.19
% 17.83/9.45  MUC search           : 0.00
% 17.83/9.45  Cooper               : 0.00
% 17.83/9.45  Total                : 8.66
% 17.83/9.45  Index Insertion      : 0.00
% 17.83/9.45  Index Deletion       : 0.00
% 17.83/9.45  Index Matching       : 0.00
% 17.83/9.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
