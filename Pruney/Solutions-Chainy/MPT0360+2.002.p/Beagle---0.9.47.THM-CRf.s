%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:18 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :   69 (  95 expanded)
%              Number of leaves         :   31 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :   84 ( 144 expanded)
%              Number of equality atoms :   33 (  47 expanded)
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

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_73,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_53,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_503,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = k3_subset_1(A_59,B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_512,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_503])).

tff(c_32,plain,(
    ! [A_23] : ~ v1_xboole_0(k1_zfmisc_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_24,plain,(
    ! [B_20,A_19] :
      ( r2_hidden(B_20,A_19)
      | ~ m1_subset_1(B_20,A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    ! [A_18] : k3_tarski(k1_zfmisc_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_203,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,k3_tarski(B_41))
      | ~ r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_256,plain,(
    ! [A_48,A_49] :
      ( r1_tarski(A_48,A_49)
      | ~ r2_hidden(A_48,k1_zfmisc_1(A_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_203])).

tff(c_260,plain,(
    ! [B_20,A_49] :
      ( r1_tarski(B_20,A_49)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_49))
      | v1_xboole_0(k1_zfmisc_1(A_49)) ) ),
    inference(resolution,[status(thm)],[c_24,c_256])).

tff(c_270,plain,(
    ! [B_50,A_51] :
      ( r1_tarski(B_50,A_51)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_260])).

tff(c_279,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_270])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_283,plain,(
    k3_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_279,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_293,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_2])).

tff(c_12,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_347,plain,(
    k5_xboole_0('#skF_1','#skF_3') = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_12])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_xboole_0(k3_xboole_0(A_7,B_8),k5_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_290,plain,(
    r1_xboole_0('#skF_3',k5_xboole_0('#skF_3','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_10])).

tff(c_305,plain,(
    r1_xboole_0('#skF_3',k5_xboole_0('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_290])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_374,plain,(
    k3_xboole_0('#skF_3',k5_xboole_0('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_305,c_6])).

tff(c_478,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_374])).

tff(c_513,plain,(
    k3_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_478])).

tff(c_38,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k3_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_446,plain,(
    ! [A_56,C_57,B_58] :
      ( r1_xboole_0(A_56,C_57)
      | ~ r1_xboole_0(B_58,C_57)
      | ~ r1_tarski(A_56,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1189,plain,(
    ! [A_81,B_82,A_83] :
      ( r1_xboole_0(A_81,B_82)
      | ~ r1_tarski(A_81,A_83)
      | k3_xboole_0(A_83,B_82) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_446])).

tff(c_1202,plain,(
    ! [B_84] :
      ( r1_xboole_0('#skF_2',B_84)
      | k3_xboole_0('#skF_3',B_84) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_1189])).

tff(c_1239,plain,(
    ! [B_89] :
      ( k3_xboole_0('#skF_2',B_89) = k1_xboole_0
      | k3_xboole_0('#skF_3',B_89) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1202,c_6])).

tff(c_36,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_140,plain,(
    ! [A_36,B_37] :
      ( k3_xboole_0(A_36,B_37) = A_36
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_147,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_140])).

tff(c_1286,plain,
    ( k1_xboole_0 = '#skF_2'
    | k3_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_3')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1239,c_147])).

tff(c_1337,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_1286])).

tff(c_1339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1337])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:43:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.65  
% 3.48/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.66  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.48/1.66  
% 3.48/1.66  %Foreground sorts:
% 3.48/1.66  
% 3.48/1.66  
% 3.48/1.66  %Background operators:
% 3.48/1.66  
% 3.48/1.66  
% 3.48/1.66  %Foreground operators:
% 3.48/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.48/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.48/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.48/1.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.48/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.48/1.66  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.48/1.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.48/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.48/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.48/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.48/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.48/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.66  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.48/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.48/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.48/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.48/1.66  
% 3.48/1.67  tff(f_82, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 3.48/1.67  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.48/1.67  tff(f_73, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.48/1.67  tff(f_66, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.48/1.67  tff(f_53, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 3.48/1.67  tff(f_51, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.48/1.67  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.48/1.67  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.48/1.67  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.48/1.67  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.48/1.67  tff(f_35, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 3.48/1.67  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.48/1.67  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.48/1.67  tff(c_34, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.48/1.67  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.48/1.67  tff(c_503, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=k3_subset_1(A_59, B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.48/1.67  tff(c_512, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_503])).
% 3.48/1.67  tff(c_32, plain, (![A_23]: (~v1_xboole_0(k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.48/1.67  tff(c_24, plain, (![B_20, A_19]: (r2_hidden(B_20, A_19) | ~m1_subset_1(B_20, A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.48/1.67  tff(c_20, plain, (![A_18]: (k3_tarski(k1_zfmisc_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.48/1.67  tff(c_203, plain, (![A_40, B_41]: (r1_tarski(A_40, k3_tarski(B_41)) | ~r2_hidden(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.48/1.67  tff(c_256, plain, (![A_48, A_49]: (r1_tarski(A_48, A_49) | ~r2_hidden(A_48, k1_zfmisc_1(A_49)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_203])).
% 3.48/1.67  tff(c_260, plain, (![B_20, A_49]: (r1_tarski(B_20, A_49) | ~m1_subset_1(B_20, k1_zfmisc_1(A_49)) | v1_xboole_0(k1_zfmisc_1(A_49)))), inference(resolution, [status(thm)], [c_24, c_256])).
% 3.48/1.67  tff(c_270, plain, (![B_50, A_51]: (r1_tarski(B_50, A_51) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)))), inference(negUnitSimplification, [status(thm)], [c_32, c_260])).
% 3.48/1.67  tff(c_279, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_270])).
% 3.48/1.67  tff(c_14, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.48/1.67  tff(c_283, plain, (k3_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_279, c_14])).
% 3.48/1.67  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.48/1.67  tff(c_293, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_283, c_2])).
% 3.48/1.67  tff(c_12, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.48/1.67  tff(c_347, plain, (k5_xboole_0('#skF_1', '#skF_3')=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_293, c_12])).
% 3.48/1.67  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.48/1.67  tff(c_10, plain, (![A_7, B_8]: (r1_xboole_0(k3_xboole_0(A_7, B_8), k5_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.48/1.67  tff(c_290, plain, (r1_xboole_0('#skF_3', k5_xboole_0('#skF_3', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_283, c_10])).
% 3.48/1.67  tff(c_305, plain, (r1_xboole_0('#skF_3', k5_xboole_0('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_290])).
% 3.48/1.67  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.48/1.67  tff(c_374, plain, (k3_xboole_0('#skF_3', k5_xboole_0('#skF_1', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_305, c_6])).
% 3.48/1.67  tff(c_478, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_1', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_347, c_374])).
% 3.48/1.67  tff(c_513, plain, (k3_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_512, c_478])).
% 3.48/1.67  tff(c_38, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.48/1.67  tff(c_8, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k3_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.48/1.67  tff(c_446, plain, (![A_56, C_57, B_58]: (r1_xboole_0(A_56, C_57) | ~r1_xboole_0(B_58, C_57) | ~r1_tarski(A_56, B_58))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.48/1.67  tff(c_1189, plain, (![A_81, B_82, A_83]: (r1_xboole_0(A_81, B_82) | ~r1_tarski(A_81, A_83) | k3_xboole_0(A_83, B_82)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_446])).
% 3.48/1.67  tff(c_1202, plain, (![B_84]: (r1_xboole_0('#skF_2', B_84) | k3_xboole_0('#skF_3', B_84)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_1189])).
% 3.48/1.67  tff(c_1239, plain, (![B_89]: (k3_xboole_0('#skF_2', B_89)=k1_xboole_0 | k3_xboole_0('#skF_3', B_89)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1202, c_6])).
% 3.48/1.67  tff(c_36, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.48/1.67  tff(c_140, plain, (![A_36, B_37]: (k3_xboole_0(A_36, B_37)=A_36 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.48/1.67  tff(c_147, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))='#skF_2'), inference(resolution, [status(thm)], [c_36, c_140])).
% 3.48/1.67  tff(c_1286, plain, (k1_xboole_0='#skF_2' | k3_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_3'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1239, c_147])).
% 3.48/1.67  tff(c_1337, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_513, c_1286])).
% 3.48/1.67  tff(c_1339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1337])).
% 3.48/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.67  
% 3.48/1.67  Inference rules
% 3.48/1.67  ----------------------
% 3.48/1.67  #Ref     : 0
% 3.48/1.67  #Sup     : 356
% 3.48/1.67  #Fact    : 0
% 3.48/1.67  #Define  : 0
% 3.48/1.67  #Split   : 0
% 3.48/1.67  #Chain   : 0
% 3.48/1.67  #Close   : 0
% 3.48/1.67  
% 3.48/1.67  Ordering : KBO
% 3.48/1.67  
% 3.48/1.67  Simplification rules
% 3.48/1.67  ----------------------
% 3.48/1.67  #Subsume      : 13
% 3.48/1.67  #Demod        : 177
% 3.48/1.67  #Tautology    : 158
% 3.48/1.67  #SimpNegUnit  : 5
% 3.48/1.67  #BackRed      : 6
% 3.48/1.67  
% 3.48/1.67  #Partial instantiations: 0
% 3.48/1.67  #Strategies tried      : 1
% 3.48/1.67  
% 3.48/1.67  Timing (in seconds)
% 3.48/1.67  ----------------------
% 3.48/1.67  Preprocessing        : 0.38
% 3.48/1.67  Parsing              : 0.21
% 3.65/1.67  CNF conversion       : 0.02
% 3.65/1.67  Main loop            : 0.48
% 3.65/1.67  Inferencing          : 0.16
% 3.65/1.67  Reduction            : 0.19
% 3.65/1.67  Demodulation         : 0.15
% 3.65/1.67  BG Simplification    : 0.02
% 3.65/1.67  Subsumption          : 0.08
% 3.65/1.67  Abstraction          : 0.02
% 3.65/1.67  MUC search           : 0.00
% 3.65/1.67  Cooper               : 0.00
% 3.65/1.67  Total                : 0.89
% 3.65/1.67  Index Insertion      : 0.00
% 3.65/1.67  Index Deletion       : 0.00
% 3.65/1.67  Index Matching       : 0.00
% 3.65/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
