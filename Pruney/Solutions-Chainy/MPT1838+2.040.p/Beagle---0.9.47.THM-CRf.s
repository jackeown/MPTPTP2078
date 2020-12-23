%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:19 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 190 expanded)
%              Number of leaves         :   27 (  75 expanded)
%              Depth                    :   12
%              Number of atoms          :  130 ( 433 expanded)
%              Number of equality atoms :   64 ( 225 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_32,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_34,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & ~ ( B = k1_tarski(A)
            & C = k1_tarski(A) )
        & ~ ( B = k1_xboole_0
            & C = k1_tarski(A) )
        & ~ ( B = k1_tarski(A)
            & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_4] : k4_xboole_0(k1_xboole_0,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_89,plain,(
    ! [A_28,B_29] : k5_xboole_0(A_28,k4_xboole_0(B_29,A_28)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_101,plain,(
    ! [A_4] : k5_xboole_0(A_4,k1_xboole_0) = k2_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_89])).

tff(c_104,plain,(
    ! [A_4] : k5_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_101])).

tff(c_42,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_66,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_74,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_66])).

tff(c_98,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_89])).

tff(c_123,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_98])).

tff(c_38,plain,(
    ! [A_14] :
      ( m1_subset_1('#skF_1'(A_14),A_14)
      | ~ v1_zfmisc_1(A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_128,plain,(
    ! [A_32,B_33] :
      ( k6_domain_1(A_32,B_33) = k1_tarski(B_33)
      | ~ m1_subset_1(B_33,A_32)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_174,plain,(
    ! [A_46] :
      ( k6_domain_1(A_46,'#skF_1'(A_46)) = k1_tarski('#skF_1'(A_46))
      | ~ v1_zfmisc_1(A_46)
      | v1_xboole_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_38,c_128])).

tff(c_36,plain,(
    ! [A_14] :
      ( k6_domain_1(A_14,'#skF_1'(A_14)) = A_14
      | ~ v1_zfmisc_1(A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_189,plain,(
    ! [A_47] :
      ( k1_tarski('#skF_1'(A_47)) = A_47
      | ~ v1_zfmisc_1(A_47)
      | v1_xboole_0(A_47)
      | ~ v1_zfmisc_1(A_47)
      | v1_xboole_0(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_36])).

tff(c_30,plain,(
    ! [B_10,A_9,C_11] :
      ( k1_xboole_0 = B_10
      | k1_tarski(A_9) = B_10
      | k2_xboole_0(B_10,C_11) != k1_tarski(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_242,plain,(
    ! [B_49,A_50,C_51] :
      ( k1_xboole_0 = B_49
      | k1_tarski('#skF_1'(A_50)) = B_49
      | k2_xboole_0(B_49,C_51) != A_50
      | ~ v1_zfmisc_1(A_50)
      | v1_xboole_0(A_50)
      | ~ v1_zfmisc_1(A_50)
      | v1_xboole_0(A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_30])).

tff(c_244,plain,(
    ! [A_50] :
      ( k1_xboole_0 = '#skF_3'
      | k1_tarski('#skF_1'(A_50)) = '#skF_3'
      | A_50 != '#skF_3'
      | ~ v1_zfmisc_1(A_50)
      | v1_xboole_0(A_50)
      | ~ v1_zfmisc_1(A_50)
      | v1_xboole_0(A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_242])).

tff(c_327,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_244])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_340,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_2])).

tff(c_342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_340])).

tff(c_344,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_44,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_40,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_358,plain,(
    ! [A_57] :
      ( k1_tarski('#skF_1'(A_57)) = '#skF_3'
      | A_57 != '#skF_3'
      | ~ v1_zfmisc_1(A_57)
      | v1_xboole_0(A_57)
      | ~ v1_zfmisc_1(A_57)
      | v1_xboole_0(A_57) ) ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_249,plain,(
    ! [A_52] :
      ( k1_xboole_0 = A_52
      | k1_tarski('#skF_1'(A_52)) = A_52
      | ~ v1_zfmisc_1(A_52)
      | v1_xboole_0(A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_242])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_133,plain,(
    ! [A_34,C_35,B_36] :
      ( k1_tarski(A_34) = C_35
      | k1_xboole_0 = C_35
      | k2_xboole_0(B_36,C_35) != k1_tarski(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_136,plain,(
    ! [A_34] :
      ( k1_tarski(A_34) = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k1_tarski(A_34) != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_133])).

tff(c_141,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_149,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_2])).

tff(c_151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_149])).

tff(c_152,plain,(
    ! [A_34] :
      ( k1_tarski(A_34) = '#skF_2'
      | k1_tarski(A_34) != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_267,plain,(
    ! [A_52] :
      ( k1_tarski('#skF_1'(A_52)) = '#skF_2'
      | A_52 != '#skF_3'
      | k1_xboole_0 = A_52
      | ~ v1_zfmisc_1(A_52)
      | v1_xboole_0(A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_152])).

tff(c_364,plain,(
    ! [A_57] :
      ( '#skF_2' = '#skF_3'
      | A_57 != '#skF_3'
      | k1_xboole_0 = A_57
      | ~ v1_zfmisc_1(A_57)
      | v1_xboole_0(A_57)
      | A_57 != '#skF_3'
      | ~ v1_zfmisc_1(A_57)
      | v1_xboole_0(A_57)
      | ~ v1_zfmisc_1(A_57)
      | v1_xboole_0(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_267])).

tff(c_421,plain,(
    ! [A_61] :
      ( A_61 != '#skF_3'
      | k1_xboole_0 = A_61
      | ~ v1_zfmisc_1(A_61)
      | v1_xboole_0(A_61)
      | A_61 != '#skF_3'
      | ~ v1_zfmisc_1(A_61)
      | v1_xboole_0(A_61)
      | ~ v1_zfmisc_1(A_61)
      | v1_xboole_0(A_61) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_364])).

tff(c_423,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_421])).

tff(c_426,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_423])).

tff(c_428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_344,c_426])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:22:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.30  
% 2.46/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.31  %$ r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.46/1.31  
% 2.46/1.31  %Foreground sorts:
% 2.46/1.31  
% 2.46/1.31  
% 2.46/1.31  %Background operators:
% 2.46/1.31  
% 2.46/1.31  
% 2.46/1.31  %Foreground operators:
% 2.46/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.46/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.46/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.46/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.46/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.46/1.31  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.46/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.46/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.46/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.46/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.46/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.31  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.46/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.46/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.46/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.46/1.31  
% 2.46/1.32  tff(f_87, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.46/1.32  tff(f_32, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.46/1.32  tff(f_34, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.46/1.32  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.46/1.32  tff(f_30, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.46/1.32  tff(f_73, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 2.46/1.32  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.46/1.32  tff(f_56, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.46/1.32  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.46/1.32  tff(c_46, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.46/1.32  tff(c_8, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.46/1.32  tff(c_10, plain, (![A_4]: (k4_xboole_0(k1_xboole_0, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.46/1.32  tff(c_89, plain, (![A_28, B_29]: (k5_xboole_0(A_28, k4_xboole_0(B_29, A_28))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.46/1.32  tff(c_101, plain, (![A_4]: (k5_xboole_0(A_4, k1_xboole_0)=k2_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_89])).
% 2.46/1.32  tff(c_104, plain, (![A_4]: (k5_xboole_0(A_4, k1_xboole_0)=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_101])).
% 2.46/1.32  tff(c_42, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.46/1.32  tff(c_66, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.46/1.32  tff(c_74, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_66])).
% 2.46/1.32  tff(c_98, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_74, c_89])).
% 2.46/1.32  tff(c_123, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_98])).
% 2.46/1.32  tff(c_38, plain, (![A_14]: (m1_subset_1('#skF_1'(A_14), A_14) | ~v1_zfmisc_1(A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.46/1.32  tff(c_128, plain, (![A_32, B_33]: (k6_domain_1(A_32, B_33)=k1_tarski(B_33) | ~m1_subset_1(B_33, A_32) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.46/1.32  tff(c_174, plain, (![A_46]: (k6_domain_1(A_46, '#skF_1'(A_46))=k1_tarski('#skF_1'(A_46)) | ~v1_zfmisc_1(A_46) | v1_xboole_0(A_46))), inference(resolution, [status(thm)], [c_38, c_128])).
% 2.46/1.32  tff(c_36, plain, (![A_14]: (k6_domain_1(A_14, '#skF_1'(A_14))=A_14 | ~v1_zfmisc_1(A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.46/1.32  tff(c_189, plain, (![A_47]: (k1_tarski('#skF_1'(A_47))=A_47 | ~v1_zfmisc_1(A_47) | v1_xboole_0(A_47) | ~v1_zfmisc_1(A_47) | v1_xboole_0(A_47))), inference(superposition, [status(thm), theory('equality')], [c_174, c_36])).
% 2.46/1.32  tff(c_30, plain, (![B_10, A_9, C_11]: (k1_xboole_0=B_10 | k1_tarski(A_9)=B_10 | k2_xboole_0(B_10, C_11)!=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.46/1.32  tff(c_242, plain, (![B_49, A_50, C_51]: (k1_xboole_0=B_49 | k1_tarski('#skF_1'(A_50))=B_49 | k2_xboole_0(B_49, C_51)!=A_50 | ~v1_zfmisc_1(A_50) | v1_xboole_0(A_50) | ~v1_zfmisc_1(A_50) | v1_xboole_0(A_50))), inference(superposition, [status(thm), theory('equality')], [c_189, c_30])).
% 2.46/1.32  tff(c_244, plain, (![A_50]: (k1_xboole_0='#skF_3' | k1_tarski('#skF_1'(A_50))='#skF_3' | A_50!='#skF_3' | ~v1_zfmisc_1(A_50) | v1_xboole_0(A_50) | ~v1_zfmisc_1(A_50) | v1_xboole_0(A_50))), inference(superposition, [status(thm), theory('equality')], [c_123, c_242])).
% 2.46/1.32  tff(c_327, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_244])).
% 2.46/1.32  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.46/1.32  tff(c_340, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_327, c_2])).
% 2.46/1.32  tff(c_342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_340])).
% 2.46/1.32  tff(c_344, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_244])).
% 2.46/1.32  tff(c_44, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.46/1.32  tff(c_40, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.46/1.32  tff(c_358, plain, (![A_57]: (k1_tarski('#skF_1'(A_57))='#skF_3' | A_57!='#skF_3' | ~v1_zfmisc_1(A_57) | v1_xboole_0(A_57) | ~v1_zfmisc_1(A_57) | v1_xboole_0(A_57))), inference(splitRight, [status(thm)], [c_244])).
% 2.46/1.32  tff(c_249, plain, (![A_52]: (k1_xboole_0=A_52 | k1_tarski('#skF_1'(A_52))=A_52 | ~v1_zfmisc_1(A_52) | v1_xboole_0(A_52))), inference(superposition, [status(thm), theory('equality')], [c_8, c_242])).
% 2.46/1.32  tff(c_48, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.46/1.32  tff(c_133, plain, (![A_34, C_35, B_36]: (k1_tarski(A_34)=C_35 | k1_xboole_0=C_35 | k2_xboole_0(B_36, C_35)!=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.46/1.32  tff(c_136, plain, (![A_34]: (k1_tarski(A_34)='#skF_2' | k1_xboole_0='#skF_2' | k1_tarski(A_34)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_123, c_133])).
% 2.46/1.32  tff(c_141, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_136])).
% 2.46/1.32  tff(c_149, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_2])).
% 2.46/1.32  tff(c_151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_149])).
% 2.46/1.32  tff(c_152, plain, (![A_34]: (k1_tarski(A_34)='#skF_2' | k1_tarski(A_34)!='#skF_3')), inference(splitRight, [status(thm)], [c_136])).
% 2.46/1.32  tff(c_267, plain, (![A_52]: (k1_tarski('#skF_1'(A_52))='#skF_2' | A_52!='#skF_3' | k1_xboole_0=A_52 | ~v1_zfmisc_1(A_52) | v1_xboole_0(A_52))), inference(superposition, [status(thm), theory('equality')], [c_249, c_152])).
% 2.46/1.32  tff(c_364, plain, (![A_57]: ('#skF_2'='#skF_3' | A_57!='#skF_3' | k1_xboole_0=A_57 | ~v1_zfmisc_1(A_57) | v1_xboole_0(A_57) | A_57!='#skF_3' | ~v1_zfmisc_1(A_57) | v1_xboole_0(A_57) | ~v1_zfmisc_1(A_57) | v1_xboole_0(A_57))), inference(superposition, [status(thm), theory('equality')], [c_358, c_267])).
% 2.46/1.32  tff(c_421, plain, (![A_61]: (A_61!='#skF_3' | k1_xboole_0=A_61 | ~v1_zfmisc_1(A_61) | v1_xboole_0(A_61) | A_61!='#skF_3' | ~v1_zfmisc_1(A_61) | v1_xboole_0(A_61) | ~v1_zfmisc_1(A_61) | v1_xboole_0(A_61))), inference(negUnitSimplification, [status(thm)], [c_40, c_364])).
% 2.46/1.32  tff(c_423, plain, (k1_xboole_0='#skF_3' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_421])).
% 2.46/1.32  tff(c_426, plain, (k1_xboole_0='#skF_3' | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_423])).
% 2.46/1.32  tff(c_428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_344, c_426])).
% 2.46/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.32  
% 2.46/1.32  Inference rules
% 2.46/1.32  ----------------------
% 2.46/1.32  #Ref     : 3
% 2.46/1.32  #Sup     : 89
% 2.46/1.32  #Fact    : 0
% 2.46/1.32  #Define  : 0
% 2.46/1.32  #Split   : 2
% 2.46/1.32  #Chain   : 0
% 2.46/1.32  #Close   : 0
% 2.46/1.32  
% 2.46/1.32  Ordering : KBO
% 2.46/1.32  
% 2.46/1.32  Simplification rules
% 2.46/1.32  ----------------------
% 2.46/1.32  #Subsume      : 13
% 2.46/1.32  #Demod        : 26
% 2.46/1.32  #Tautology    : 45
% 2.46/1.32  #SimpNegUnit  : 9
% 2.46/1.32  #BackRed      : 20
% 2.46/1.32  
% 2.46/1.32  #Partial instantiations: 0
% 2.46/1.32  #Strategies tried      : 1
% 2.46/1.32  
% 2.46/1.32  Timing (in seconds)
% 2.46/1.32  ----------------------
% 2.46/1.32  Preprocessing        : 0.30
% 2.46/1.32  Parsing              : 0.15
% 2.46/1.32  CNF conversion       : 0.02
% 2.46/1.32  Main loop            : 0.27
% 2.46/1.32  Inferencing          : 0.09
% 2.46/1.32  Reduction            : 0.07
% 2.46/1.32  Demodulation         : 0.05
% 2.46/1.32  BG Simplification    : 0.02
% 2.46/1.32  Subsumption          : 0.07
% 2.46/1.32  Abstraction          : 0.01
% 2.46/1.32  MUC search           : 0.00
% 2.46/1.32  Cooper               : 0.00
% 2.46/1.32  Total                : 0.59
% 2.46/1.32  Index Insertion      : 0.00
% 2.46/1.32  Index Deletion       : 0.00
% 2.46/1.32  Index Matching       : 0.00
% 2.46/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
