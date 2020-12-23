%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:32 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :   62 (  76 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :   83 ( 112 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k1_zfmisc_1(k3_xboole_0(A,B)) = k3_xboole_0(k1_zfmisc_1(A),k1_zfmisc_1(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_22,plain,(
    ! [A_9,B_10] : r1_tarski(k3_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,(
    ! [C_17,A_13] :
      ( r2_hidden(C_17,k1_zfmisc_1(A_13))
      | ~ r1_tarski(C_17,A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_48,plain,(
    ! [A_22] : ~ v1_xboole_0(k1_zfmisc_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_155,plain,(
    ! [B_53,A_54] :
      ( r2_hidden(B_53,A_54)
      | ~ m1_subset_1(B_53,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_26,plain,(
    ! [C_17,A_13] :
      ( r1_tarski(C_17,A_13)
      | ~ r2_hidden(C_17,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_166,plain,(
    ! [B_53,A_13] :
      ( r1_tarski(B_53,A_13)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_13))
      | v1_xboole_0(k1_zfmisc_1(A_13)) ) ),
    inference(resolution,[status(thm)],[c_155,c_26])).

tff(c_177,plain,(
    ! [B_57,A_58] :
      ( r1_tarski(B_57,A_58)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_166])).

tff(c_193,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_177])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_198,plain,(
    k3_xboole_0('#skF_6','#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_193,c_24])).

tff(c_337,plain,(
    ! [A_64,B_65] : k3_xboole_0(k1_zfmisc_1(A_64),k1_zfmisc_1(B_65)) = k1_zfmisc_1(k3_xboole_0(A_64,B_65)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_63,plain,(
    ! [B_34,A_35] : k3_xboole_0(B_34,A_35) = k3_xboole_0(A_35,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_78,plain,(
    ! [B_34,A_35] : r1_tarski(k3_xboole_0(B_34,A_35),A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_22])).

tff(c_413,plain,(
    ! [A_68,B_69] : r1_tarski(k1_zfmisc_1(k3_xboole_0(A_68,B_69)),k1_zfmisc_1(B_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_78])).

tff(c_434,plain,(
    r1_tarski(k1_zfmisc_1('#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_413])).

tff(c_451,plain,(
    k3_xboole_0(k1_zfmisc_1('#skF_6'),k1_zfmisc_1('#skF_5')) = k1_zfmisc_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_434,c_24])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2469,plain,(
    ! [D_117] :
      ( r2_hidden(D_117,k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(D_117,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_451,c_6])).

tff(c_40,plain,(
    ! [B_21,A_20] :
      ( m1_subset_1(B_21,A_20)
      | ~ r2_hidden(B_21,A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2483,plain,(
    ! [D_117] :
      ( m1_subset_1(D_117,k1_zfmisc_1('#skF_5'))
      | v1_xboole_0(k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(D_117,k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_2469,c_40])).

tff(c_2605,plain,(
    ! [D_124] :
      ( m1_subset_1(D_124,k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(D_124,k1_zfmisc_1('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2483])).

tff(c_2637,plain,(
    ! [C_17] :
      ( m1_subset_1(C_17,k1_zfmisc_1('#skF_5'))
      | ~ r1_tarski(C_17,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_28,c_2605])).

tff(c_2946,plain,(
    ! [A_136,C_137,B_138] :
      ( r1_tarski(k3_subset_1(A_136,C_137),k3_subset_1(A_136,B_138))
      | ~ r1_tarski(B_138,C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(A_136))
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_58,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_453,plain,(
    ! [A_70,B_71,C_72] :
      ( k9_subset_1(A_70,B_71,C_72) = k3_xboole_0(B_71,C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_466,plain,(
    ! [B_71] : k9_subset_1('#skF_5',B_71,'#skF_7') = k3_xboole_0(B_71,'#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_453])).

tff(c_56,plain,(
    ~ r1_tarski(k3_subset_1('#skF_5','#skF_6'),k3_subset_1('#skF_5',k9_subset_1('#skF_5','#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_476,plain,(
    ~ r1_tarski(k3_subset_1('#skF_5','#skF_6'),k3_subset_1('#skF_5',k3_xboole_0('#skF_6','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_56])).

tff(c_2949,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_6','#skF_7'),'#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2946,c_476])).

tff(c_2955,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_22,c_2949])).

tff(c_2961,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_6','#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_2637,c_2955])).

tff(c_2971,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2961])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:45:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.07/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.07/1.76  
% 4.07/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.07/1.76  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 4.07/1.76  
% 4.07/1.76  %Foreground sorts:
% 4.07/1.76  
% 4.07/1.76  
% 4.07/1.76  %Background operators:
% 4.07/1.76  
% 4.07/1.76  
% 4.07/1.76  %Foreground operators:
% 4.07/1.76  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.07/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.07/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.07/1.76  tff('#skF_7', type, '#skF_7': $i).
% 4.07/1.76  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.07/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.07/1.76  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.07/1.76  tff('#skF_5', type, '#skF_5': $i).
% 4.07/1.76  tff('#skF_6', type, '#skF_6': $i).
% 4.07/1.76  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.07/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.07/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.07/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.07/1.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.07/1.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.07/1.76  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.07/1.76  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.07/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.07/1.76  
% 4.07/1.77  tff(f_38, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.07/1.77  tff(f_49, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.07/1.77  tff(f_67, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.07/1.77  tff(f_88, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_subset_1)).
% 4.07/1.77  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.07/1.77  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.07/1.77  tff(f_51, axiom, (![A, B]: (k1_zfmisc_1(k3_xboole_0(A, B)) = k3_xboole_0(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_zfmisc_1)).
% 4.07/1.77  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.07/1.77  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.07/1.77  tff(f_80, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 4.07/1.77  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.07/1.77  tff(c_22, plain, (![A_9, B_10]: (r1_tarski(k3_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.07/1.77  tff(c_28, plain, (![C_17, A_13]: (r2_hidden(C_17, k1_zfmisc_1(A_13)) | ~r1_tarski(C_17, A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.07/1.77  tff(c_48, plain, (![A_22]: (~v1_xboole_0(k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.07/1.77  tff(c_60, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.07/1.77  tff(c_155, plain, (![B_53, A_54]: (r2_hidden(B_53, A_54) | ~m1_subset_1(B_53, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.07/1.77  tff(c_26, plain, (![C_17, A_13]: (r1_tarski(C_17, A_13) | ~r2_hidden(C_17, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.07/1.77  tff(c_166, plain, (![B_53, A_13]: (r1_tarski(B_53, A_13) | ~m1_subset_1(B_53, k1_zfmisc_1(A_13)) | v1_xboole_0(k1_zfmisc_1(A_13)))), inference(resolution, [status(thm)], [c_155, c_26])).
% 4.07/1.77  tff(c_177, plain, (![B_57, A_58]: (r1_tarski(B_57, A_58) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)))), inference(negUnitSimplification, [status(thm)], [c_48, c_166])).
% 4.07/1.77  tff(c_193, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_177])).
% 4.07/1.77  tff(c_24, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.07/1.77  tff(c_198, plain, (k3_xboole_0('#skF_6', '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_193, c_24])).
% 4.07/1.77  tff(c_337, plain, (![A_64, B_65]: (k3_xboole_0(k1_zfmisc_1(A_64), k1_zfmisc_1(B_65))=k1_zfmisc_1(k3_xboole_0(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.07/1.77  tff(c_63, plain, (![B_34, A_35]: (k3_xboole_0(B_34, A_35)=k3_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.07/1.77  tff(c_78, plain, (![B_34, A_35]: (r1_tarski(k3_xboole_0(B_34, A_35), A_35))), inference(superposition, [status(thm), theory('equality')], [c_63, c_22])).
% 4.07/1.77  tff(c_413, plain, (![A_68, B_69]: (r1_tarski(k1_zfmisc_1(k3_xboole_0(A_68, B_69)), k1_zfmisc_1(B_69)))), inference(superposition, [status(thm), theory('equality')], [c_337, c_78])).
% 4.07/1.77  tff(c_434, plain, (r1_tarski(k1_zfmisc_1('#skF_6'), k1_zfmisc_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_198, c_413])).
% 4.07/1.77  tff(c_451, plain, (k3_xboole_0(k1_zfmisc_1('#skF_6'), k1_zfmisc_1('#skF_5'))=k1_zfmisc_1('#skF_6')), inference(resolution, [status(thm)], [c_434, c_24])).
% 4.07/1.77  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.07/1.77  tff(c_2469, plain, (![D_117]: (r2_hidden(D_117, k1_zfmisc_1('#skF_5')) | ~r2_hidden(D_117, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_451, c_6])).
% 4.07/1.77  tff(c_40, plain, (![B_21, A_20]: (m1_subset_1(B_21, A_20) | ~r2_hidden(B_21, A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.07/1.77  tff(c_2483, plain, (![D_117]: (m1_subset_1(D_117, k1_zfmisc_1('#skF_5')) | v1_xboole_0(k1_zfmisc_1('#skF_5')) | ~r2_hidden(D_117, k1_zfmisc_1('#skF_6')))), inference(resolution, [status(thm)], [c_2469, c_40])).
% 4.07/1.77  tff(c_2605, plain, (![D_124]: (m1_subset_1(D_124, k1_zfmisc_1('#skF_5')) | ~r2_hidden(D_124, k1_zfmisc_1('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_48, c_2483])).
% 4.07/1.77  tff(c_2637, plain, (![C_17]: (m1_subset_1(C_17, k1_zfmisc_1('#skF_5')) | ~r1_tarski(C_17, '#skF_6'))), inference(resolution, [status(thm)], [c_28, c_2605])).
% 4.07/1.77  tff(c_2946, plain, (![A_136, C_137, B_138]: (r1_tarski(k3_subset_1(A_136, C_137), k3_subset_1(A_136, B_138)) | ~r1_tarski(B_138, C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(A_136)) | ~m1_subset_1(B_138, k1_zfmisc_1(A_136)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.07/1.77  tff(c_58, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.07/1.77  tff(c_453, plain, (![A_70, B_71, C_72]: (k9_subset_1(A_70, B_71, C_72)=k3_xboole_0(B_71, C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.07/1.77  tff(c_466, plain, (![B_71]: (k9_subset_1('#skF_5', B_71, '#skF_7')=k3_xboole_0(B_71, '#skF_7'))), inference(resolution, [status(thm)], [c_58, c_453])).
% 4.07/1.77  tff(c_56, plain, (~r1_tarski(k3_subset_1('#skF_5', '#skF_6'), k3_subset_1('#skF_5', k9_subset_1('#skF_5', '#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.07/1.77  tff(c_476, plain, (~r1_tarski(k3_subset_1('#skF_5', '#skF_6'), k3_subset_1('#skF_5', k3_xboole_0('#skF_6', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_466, c_56])).
% 4.07/1.77  tff(c_2949, plain, (~r1_tarski(k3_xboole_0('#skF_6', '#skF_7'), '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5')) | ~m1_subset_1(k3_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_2946, c_476])).
% 4.07/1.77  tff(c_2955, plain, (~m1_subset_1(k3_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_22, c_2949])).
% 4.07/1.77  tff(c_2961, plain, (~r1_tarski(k3_xboole_0('#skF_6', '#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_2637, c_2955])).
% 4.07/1.77  tff(c_2971, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_2961])).
% 4.07/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.07/1.77  
% 4.07/1.77  Inference rules
% 4.07/1.77  ----------------------
% 4.07/1.77  #Ref     : 0
% 4.07/1.77  #Sup     : 717
% 4.07/1.77  #Fact    : 0
% 4.07/1.77  #Define  : 0
% 4.07/1.77  #Split   : 2
% 4.07/1.77  #Chain   : 0
% 4.07/1.77  #Close   : 0
% 4.07/1.77  
% 4.07/1.77  Ordering : KBO
% 4.07/1.77  
% 4.07/1.77  Simplification rules
% 4.07/1.77  ----------------------
% 4.07/1.77  #Subsume      : 53
% 4.07/1.77  #Demod        : 651
% 4.07/1.77  #Tautology    : 417
% 4.07/1.77  #SimpNegUnit  : 7
% 4.07/1.77  #BackRed      : 1
% 4.07/1.77  
% 4.07/1.77  #Partial instantiations: 0
% 4.07/1.77  #Strategies tried      : 1
% 4.07/1.77  
% 4.07/1.77  Timing (in seconds)
% 4.07/1.77  ----------------------
% 4.07/1.78  Preprocessing        : 0.31
% 4.07/1.78  Parsing              : 0.15
% 4.07/1.78  CNF conversion       : 0.02
% 4.07/1.78  Main loop            : 0.70
% 4.07/1.78  Inferencing          : 0.20
% 4.07/1.78  Reduction            : 0.30
% 4.07/1.78  Demodulation         : 0.23
% 4.07/1.78  BG Simplification    : 0.03
% 4.07/1.78  Subsumption          : 0.12
% 4.07/1.78  Abstraction          : 0.03
% 4.07/1.78  MUC search           : 0.00
% 4.07/1.78  Cooper               : 0.00
% 4.07/1.78  Total                : 1.04
% 4.07/1.78  Index Insertion      : 0.00
% 4.07/1.78  Index Deletion       : 0.00
% 4.07/1.78  Index Matching       : 0.00
% 4.07/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
