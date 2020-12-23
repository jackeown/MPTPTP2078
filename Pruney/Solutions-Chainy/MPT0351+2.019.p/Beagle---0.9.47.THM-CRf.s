%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:39 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   79 (  97 expanded)
%              Number of leaves         :   37 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :   81 ( 102 expanded)
%              Number of equality atoms :   43 (  60 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_71,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_56,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_76,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_73,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_44,plain,(
    ! [A_26] : k2_subset_1(A_26) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_52,plain,(
    k4_subset_1('#skF_3','#skF_4',k2_subset_1('#skF_3')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_55,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_52])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_79,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k2_xboole_0(A_37,B_38)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_86,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_79])).

tff(c_285,plain,(
    ! [A_65,B_66] : k5_xboole_0(A_65,k4_xboole_0(B_66,A_65)) = k2_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_297,plain,(
    ! [A_1] : k5_xboole_0(A_1,k1_xboole_0) = k2_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_285])).

tff(c_303,plain,(
    ! [A_1] : k5_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_297])).

tff(c_18,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_153,plain,(
    ! [A_50,B_51] : k3_tarski(k2_tarski(A_50,B_51)) = k2_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_187,plain,(
    ! [B_57,A_58] : k3_tarski(k2_tarski(B_57,A_58)) = k2_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_153])).

tff(c_34,plain,(
    ! [A_22,B_23] : k3_tarski(k2_tarski(A_22,B_23)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_193,plain,(
    ! [B_57,A_58] : k2_xboole_0(B_57,A_58) = k2_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_34])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_168,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_172,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_168])).

tff(c_318,plain,(
    ! [A_70,B_71] : k5_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k4_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_327,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_318])).

tff(c_330,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_327])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_48,plain,(
    ! [A_28] : ~ v1_xboole_0(k1_zfmisc_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_355,plain,(
    ! [B_75,A_76] :
      ( r2_hidden(B_75,A_76)
      | ~ m1_subset_1(B_75,A_76)
      | v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [C_21,A_17] :
      ( r1_tarski(C_21,A_17)
      | ~ r2_hidden(C_21,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_362,plain,(
    ! [B_75,A_17] :
      ( r1_tarski(B_75,A_17)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_17))
      | v1_xboole_0(k1_zfmisc_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_355,c_22])).

tff(c_367,plain,(
    ! [B_77,A_78] :
      ( r1_tarski(B_77,A_78)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_78)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_362])).

tff(c_385,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_367])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_392,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_385,c_12])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_396,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_10])).

tff(c_399,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_396])).

tff(c_16,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_414,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_16])).

tff(c_417,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_193,c_414])).

tff(c_46,plain,(
    ! [A_27] : m1_subset_1(k2_subset_1(A_27),k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_56,plain,(
    ! [A_27] : m1_subset_1(A_27,k1_zfmisc_1(A_27)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46])).

tff(c_807,plain,(
    ! [A_97,B_98,C_99] :
      ( k4_subset_1(A_97,B_98,C_99) = k2_xboole_0(B_98,C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(A_97))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_966,plain,(
    ! [A_102,B_103] :
      ( k4_subset_1(A_102,B_103,A_102) = k2_xboole_0(B_103,A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_102)) ) ),
    inference(resolution,[status(thm)],[c_56,c_807])).

tff(c_975,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_966])).

tff(c_981,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_975])).

tff(c_983,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_981])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:53:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.46  
% 2.97/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.47  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.97/1.47  
% 2.97/1.47  %Foreground sorts:
% 2.97/1.47  
% 2.97/1.47  
% 2.97/1.47  %Background operators:
% 2.97/1.47  
% 2.97/1.47  
% 2.97/1.47  %Foreground operators:
% 2.97/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.97/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.97/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.97/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.97/1.47  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.97/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.97/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.97/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.97/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.47  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.97/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.97/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.97/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.97/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.97/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.97/1.47  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.97/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.97/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.97/1.47  
% 3.13/1.48  tff(f_71, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.13/1.48  tff(f_87, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 3.13/1.48  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.13/1.48  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.13/1.48  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.13/1.48  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.13/1.48  tff(f_56, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.13/1.48  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.13/1.48  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.13/1.48  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.13/1.48  tff(f_76, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.13/1.48  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.13/1.48  tff(f_54, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.13/1.48  tff(f_73, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.13/1.48  tff(f_82, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.13/1.48  tff(c_44, plain, (![A_26]: (k2_subset_1(A_26)=A_26)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.13/1.48  tff(c_52, plain, (k4_subset_1('#skF_3', '#skF_4', k2_subset_1('#skF_3'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.13/1.48  tff(c_55, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_52])).
% 3.13/1.48  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.13/1.48  tff(c_79, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k2_xboole_0(A_37, B_38))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.13/1.48  tff(c_86, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_79])).
% 3.13/1.48  tff(c_285, plain, (![A_65, B_66]: (k5_xboole_0(A_65, k4_xboole_0(B_66, A_65))=k2_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.13/1.48  tff(c_297, plain, (![A_1]: (k5_xboole_0(A_1, k1_xboole_0)=k2_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_86, c_285])).
% 3.13/1.48  tff(c_303, plain, (![A_1]: (k5_xboole_0(A_1, k1_xboole_0)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_297])).
% 3.13/1.48  tff(c_18, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.13/1.48  tff(c_153, plain, (![A_50, B_51]: (k3_tarski(k2_tarski(A_50, B_51))=k2_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.13/1.48  tff(c_187, plain, (![B_57, A_58]: (k3_tarski(k2_tarski(B_57, A_58))=k2_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_18, c_153])).
% 3.13/1.48  tff(c_34, plain, (![A_22, B_23]: (k3_tarski(k2_tarski(A_22, B_23))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.13/1.48  tff(c_193, plain, (![B_57, A_58]: (k2_xboole_0(B_57, A_58)=k2_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_187, c_34])).
% 3.13/1.48  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.13/1.48  tff(c_168, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.13/1.48  tff(c_172, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_168])).
% 3.13/1.48  tff(c_318, plain, (![A_70, B_71]: (k5_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k4_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.13/1.48  tff(c_327, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_172, c_318])).
% 3.13/1.48  tff(c_330, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_327])).
% 3.13/1.48  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.13/1.48  tff(c_48, plain, (![A_28]: (~v1_xboole_0(k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.13/1.48  tff(c_355, plain, (![B_75, A_76]: (r2_hidden(B_75, A_76) | ~m1_subset_1(B_75, A_76) | v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.13/1.48  tff(c_22, plain, (![C_21, A_17]: (r1_tarski(C_21, A_17) | ~r2_hidden(C_21, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.13/1.48  tff(c_362, plain, (![B_75, A_17]: (r1_tarski(B_75, A_17) | ~m1_subset_1(B_75, k1_zfmisc_1(A_17)) | v1_xboole_0(k1_zfmisc_1(A_17)))), inference(resolution, [status(thm)], [c_355, c_22])).
% 3.13/1.48  tff(c_367, plain, (![B_77, A_78]: (r1_tarski(B_77, A_78) | ~m1_subset_1(B_77, k1_zfmisc_1(A_78)))), inference(negUnitSimplification, [status(thm)], [c_48, c_362])).
% 3.13/1.48  tff(c_385, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_367])).
% 3.13/1.48  tff(c_12, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.13/1.48  tff(c_392, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_385, c_12])).
% 3.13/1.48  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.13/1.48  tff(c_396, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_392, c_10])).
% 3.13/1.48  tff(c_399, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_330, c_396])).
% 3.13/1.48  tff(c_16, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.13/1.48  tff(c_414, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_399, c_16])).
% 3.13/1.48  tff(c_417, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_303, c_193, c_414])).
% 3.13/1.48  tff(c_46, plain, (![A_27]: (m1_subset_1(k2_subset_1(A_27), k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.13/1.48  tff(c_56, plain, (![A_27]: (m1_subset_1(A_27, k1_zfmisc_1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46])).
% 3.13/1.48  tff(c_807, plain, (![A_97, B_98, C_99]: (k4_subset_1(A_97, B_98, C_99)=k2_xboole_0(B_98, C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(A_97)) | ~m1_subset_1(B_98, k1_zfmisc_1(A_97)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.13/1.48  tff(c_966, plain, (![A_102, B_103]: (k4_subset_1(A_102, B_103, A_102)=k2_xboole_0(B_103, A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(A_102)))), inference(resolution, [status(thm)], [c_56, c_807])).
% 3.13/1.48  tff(c_975, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')=k2_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_966])).
% 3.13/1.48  tff(c_981, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_417, c_975])).
% 3.13/1.48  tff(c_983, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_981])).
% 3.13/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.48  
% 3.13/1.48  Inference rules
% 3.13/1.48  ----------------------
% 3.13/1.48  #Ref     : 0
% 3.13/1.48  #Sup     : 225
% 3.13/1.48  #Fact    : 0
% 3.13/1.48  #Define  : 0
% 3.13/1.48  #Split   : 1
% 3.13/1.48  #Chain   : 0
% 3.13/1.48  #Close   : 0
% 3.13/1.48  
% 3.13/1.48  Ordering : KBO
% 3.13/1.48  
% 3.13/1.48  Simplification rules
% 3.13/1.48  ----------------------
% 3.13/1.48  #Subsume      : 11
% 3.13/1.48  #Demod        : 208
% 3.13/1.48  #Tautology    : 169
% 3.13/1.48  #SimpNegUnit  : 3
% 3.13/1.49  #BackRed      : 0
% 3.13/1.49  
% 3.13/1.49  #Partial instantiations: 0
% 3.13/1.49  #Strategies tried      : 1
% 3.13/1.49  
% 3.13/1.49  Timing (in seconds)
% 3.13/1.49  ----------------------
% 3.13/1.49  Preprocessing        : 0.33
% 3.13/1.49  Parsing              : 0.17
% 3.13/1.49  CNF conversion       : 0.02
% 3.13/1.49  Main loop            : 0.36
% 3.13/1.49  Inferencing          : 0.12
% 3.13/1.49  Reduction            : 0.15
% 3.13/1.49  Demodulation         : 0.12
% 3.13/1.49  BG Simplification    : 0.02
% 3.13/1.49  Subsumption          : 0.06
% 3.13/1.49  Abstraction          : 0.02
% 3.13/1.49  MUC search           : 0.00
% 3.13/1.49  Cooper               : 0.00
% 3.13/1.49  Total                : 0.72
% 3.13/1.49  Index Insertion      : 0.00
% 3.13/1.49  Index Deletion       : 0.00
% 3.13/1.49  Index Matching       : 0.00
% 3.13/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
