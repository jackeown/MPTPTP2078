%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:18 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 101 expanded)
%              Number of leaves         :   32 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :   89 ( 150 expanded)
%              Number of equality atoms :   38 (  53 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_75,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

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
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_489,plain,(
    ! [A_63,B_64] :
      ( k4_xboole_0(A_63,B_64) = k3_subset_1(A_63,B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_498,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_489])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_24] : ~ v1_xboole_0(k1_zfmisc_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_313,plain,(
    ! [B_53,A_54] :
      ( r2_hidden(B_53,A_54)
      | ~ m1_subset_1(B_53,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    ! [A_19] : k3_tarski(k1_zfmisc_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_222,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,k3_tarski(B_46))
      | ~ r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_228,plain,(
    ! [A_45,A_19] :
      ( r1_tarski(A_45,A_19)
      | ~ r2_hidden(A_45,k1_zfmisc_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_222])).

tff(c_317,plain,(
    ! [B_53,A_19] :
      ( r1_tarski(B_53,A_19)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_19))
      | v1_xboole_0(k1_zfmisc_1(A_19)) ) ),
    inference(resolution,[status(thm)],[c_313,c_228])).

tff(c_354,plain,(
    ! [B_55,A_56] :
      ( r1_tarski(B_55,A_56)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_317])).

tff(c_363,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_354])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_372,plain,(
    k3_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_363,c_10])).

tff(c_392,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_372])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_407,plain,(
    k5_xboole_0('#skF_1','#skF_3') = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_8])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_xboole_0(k3_xboole_0(A_5,B_6),k5_xboole_0(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_382,plain,(
    r1_xboole_0('#skF_3',k5_xboole_0('#skF_3','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_6])).

tff(c_398,plain,(
    r1_xboole_0('#skF_3',k5_xboole_0('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_382])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = A_14
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_424,plain,(
    k4_xboole_0('#skF_3',k5_xboole_0('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_398,c_14])).

tff(c_462,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_424])).

tff(c_499,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_462])).

tff(c_40,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_426,plain,(
    ! [A_59,C_60,B_61] :
      ( r1_xboole_0(A_59,C_60)
      | ~ r1_xboole_0(B_61,C_60)
      | ~ r1_tarski(A_59,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_908,plain,(
    ! [A_88,B_89,A_90] :
      ( r1_xboole_0(A_88,B_89)
      | ~ r1_tarski(A_88,A_90)
      | k4_xboole_0(A_90,B_89) != A_90 ) ),
    inference(resolution,[status(thm)],[c_16,c_426])).

tff(c_921,plain,(
    ! [B_91] :
      ( r1_xboole_0('#skF_2',B_91)
      | k4_xboole_0('#skF_3',B_91) != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_40,c_908])).

tff(c_953,plain,(
    ! [B_96] :
      ( k4_xboole_0('#skF_2',B_96) = '#skF_2'
      | k4_xboole_0('#skF_3',B_96) != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_921,c_14])).

tff(c_18,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_38,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_162,plain,(
    ! [A_41,B_42] :
      ( k3_xboole_0(A_41,B_42) = A_41
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_169,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_162])).

tff(c_276,plain,(
    ! [A_51,B_52] : k5_xboole_0(A_51,k3_xboole_0(A_51,B_52)) = k4_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_291,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) = k5_xboole_0('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_276])).

tff(c_307,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_291])).

tff(c_969,plain,
    ( k1_xboole_0 = '#skF_2'
    | k4_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_3')) != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_953,c_307])).

tff(c_993,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_969])).

tff(c_995,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_993])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:24:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.63  
% 3.32/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.63  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.32/1.63  
% 3.32/1.63  %Foreground sorts:
% 3.32/1.63  
% 3.32/1.63  
% 3.32/1.63  %Background operators:
% 3.32/1.63  
% 3.32/1.63  
% 3.32/1.63  %Foreground operators:
% 3.32/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.32/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.32/1.63  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.32/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.63  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.32/1.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.32/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.32/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.32/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.32/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.32/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.63  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.32/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.32/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.32/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.32/1.63  
% 3.32/1.65  tff(f_84, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 3.32/1.65  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.32/1.65  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.32/1.65  tff(f_75, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.32/1.65  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.32/1.65  tff(f_55, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 3.32/1.65  tff(f_53, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.32/1.65  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.32/1.65  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.32/1.65  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.32/1.65  tff(f_31, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 3.32/1.65  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.32/1.65  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.32/1.65  tff(f_49, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.32/1.65  tff(c_36, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.32/1.65  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.32/1.65  tff(c_489, plain, (![A_63, B_64]: (k4_xboole_0(A_63, B_64)=k3_subset_1(A_63, B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.32/1.65  tff(c_498, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_489])).
% 3.32/1.65  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.32/1.65  tff(c_34, plain, (![A_24]: (~v1_xboole_0(k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.32/1.65  tff(c_313, plain, (![B_53, A_54]: (r2_hidden(B_53, A_54) | ~m1_subset_1(B_53, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.32/1.65  tff(c_22, plain, (![A_19]: (k3_tarski(k1_zfmisc_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.32/1.65  tff(c_222, plain, (![A_45, B_46]: (r1_tarski(A_45, k3_tarski(B_46)) | ~r2_hidden(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.32/1.65  tff(c_228, plain, (![A_45, A_19]: (r1_tarski(A_45, A_19) | ~r2_hidden(A_45, k1_zfmisc_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_222])).
% 3.32/1.65  tff(c_317, plain, (![B_53, A_19]: (r1_tarski(B_53, A_19) | ~m1_subset_1(B_53, k1_zfmisc_1(A_19)) | v1_xboole_0(k1_zfmisc_1(A_19)))), inference(resolution, [status(thm)], [c_313, c_228])).
% 3.32/1.65  tff(c_354, plain, (![B_55, A_56]: (r1_tarski(B_55, A_56) | ~m1_subset_1(B_55, k1_zfmisc_1(A_56)))), inference(negUnitSimplification, [status(thm)], [c_34, c_317])).
% 3.32/1.65  tff(c_363, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_354])).
% 3.32/1.65  tff(c_10, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.32/1.65  tff(c_372, plain, (k3_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_363, c_10])).
% 3.32/1.65  tff(c_392, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2, c_372])).
% 3.32/1.65  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.32/1.65  tff(c_407, plain, (k5_xboole_0('#skF_1', '#skF_3')=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_392, c_8])).
% 3.32/1.65  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.32/1.65  tff(c_6, plain, (![A_5, B_6]: (r1_xboole_0(k3_xboole_0(A_5, B_6), k5_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.32/1.65  tff(c_382, plain, (r1_xboole_0('#skF_3', k5_xboole_0('#skF_3', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_372, c_6])).
% 3.32/1.65  tff(c_398, plain, (r1_xboole_0('#skF_3', k5_xboole_0('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_382])).
% 3.32/1.65  tff(c_14, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=A_14 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.32/1.65  tff(c_424, plain, (k4_xboole_0('#skF_3', k5_xboole_0('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_398, c_14])).
% 3.32/1.65  tff(c_462, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_407, c_424])).
% 3.32/1.65  tff(c_499, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_498, c_462])).
% 3.32/1.65  tff(c_40, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.32/1.65  tff(c_16, plain, (![A_14, B_15]: (r1_xboole_0(A_14, B_15) | k4_xboole_0(A_14, B_15)!=A_14)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.32/1.65  tff(c_426, plain, (![A_59, C_60, B_61]: (r1_xboole_0(A_59, C_60) | ~r1_xboole_0(B_61, C_60) | ~r1_tarski(A_59, B_61))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.32/1.65  tff(c_908, plain, (![A_88, B_89, A_90]: (r1_xboole_0(A_88, B_89) | ~r1_tarski(A_88, A_90) | k4_xboole_0(A_90, B_89)!=A_90)), inference(resolution, [status(thm)], [c_16, c_426])).
% 3.32/1.65  tff(c_921, plain, (![B_91]: (r1_xboole_0('#skF_2', B_91) | k4_xboole_0('#skF_3', B_91)!='#skF_3')), inference(resolution, [status(thm)], [c_40, c_908])).
% 3.32/1.65  tff(c_953, plain, (![B_96]: (k4_xboole_0('#skF_2', B_96)='#skF_2' | k4_xboole_0('#skF_3', B_96)!='#skF_3')), inference(resolution, [status(thm)], [c_921, c_14])).
% 3.32/1.65  tff(c_18, plain, (![A_16]: (k5_xboole_0(A_16, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.32/1.65  tff(c_38, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.32/1.65  tff(c_162, plain, (![A_41, B_42]: (k3_xboole_0(A_41, B_42)=A_41 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.32/1.65  tff(c_169, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))='#skF_2'), inference(resolution, [status(thm)], [c_38, c_162])).
% 3.32/1.65  tff(c_276, plain, (![A_51, B_52]: (k5_xboole_0(A_51, k3_xboole_0(A_51, B_52))=k4_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.32/1.65  tff(c_291, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))=k5_xboole_0('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_169, c_276])).
% 3.32/1.65  tff(c_307, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_291])).
% 3.32/1.65  tff(c_969, plain, (k1_xboole_0='#skF_2' | k4_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_3'))!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_953, c_307])).
% 3.32/1.65  tff(c_993, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_499, c_969])).
% 3.32/1.65  tff(c_995, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_993])).
% 3.32/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.65  
% 3.32/1.65  Inference rules
% 3.32/1.65  ----------------------
% 3.32/1.65  #Ref     : 0
% 3.32/1.65  #Sup     : 252
% 3.32/1.65  #Fact    : 0
% 3.32/1.65  #Define  : 0
% 3.32/1.65  #Split   : 0
% 3.32/1.65  #Chain   : 0
% 3.32/1.65  #Close   : 0
% 3.32/1.65  
% 3.32/1.65  Ordering : KBO
% 3.32/1.65  
% 3.32/1.65  Simplification rules
% 3.32/1.65  ----------------------
% 3.32/1.65  #Subsume      : 15
% 3.32/1.65  #Demod        : 109
% 3.32/1.65  #Tautology    : 132
% 3.32/1.65  #SimpNegUnit  : 7
% 3.32/1.65  #BackRed      : 11
% 3.32/1.65  
% 3.32/1.65  #Partial instantiations: 0
% 3.32/1.65  #Strategies tried      : 1
% 3.32/1.65  
% 3.32/1.65  Timing (in seconds)
% 3.32/1.65  ----------------------
% 3.32/1.65  Preprocessing        : 0.37
% 3.32/1.65  Parsing              : 0.19
% 3.32/1.65  CNF conversion       : 0.02
% 3.32/1.65  Main loop            : 0.47
% 3.32/1.65  Inferencing          : 0.16
% 3.32/1.65  Reduction            : 0.17
% 3.32/1.65  Demodulation         : 0.13
% 3.32/1.65  BG Simplification    : 0.02
% 3.32/1.65  Subsumption          : 0.08
% 3.32/1.65  Abstraction          : 0.02
% 3.32/1.65  MUC search           : 0.00
% 3.32/1.65  Cooper               : 0.00
% 3.32/1.65  Total                : 0.88
% 3.32/1.66  Index Insertion      : 0.00
% 3.32/1.66  Index Deletion       : 0.00
% 3.32/1.66  Index Matching       : 0.00
% 3.32/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
