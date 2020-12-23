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
% DateTime   : Thu Dec  3 09:55:34 EST 2020

% Result     : Theorem 7.44s
% Output     : CNFRefutation 7.44s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 116 expanded)
%              Number of leaves         :   38 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :   87 ( 158 expanded)
%              Number of equality atoms :   40 (  63 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_84,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_77,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_575,plain,(
    ! [A_89,B_90] :
      ( k4_xboole_0(A_89,B_90) = k3_subset_1(A_89,B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_591,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_575])).

tff(c_52,plain,(
    ! [A_36] : ~ v1_xboole_0(k1_zfmisc_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_303,plain,(
    ! [B_79,A_80] :
      ( r2_hidden(B_79,A_80)
      | ~ m1_subset_1(B_79,A_80)
      | v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26,plain,(
    ! [C_28,A_24] :
      ( r1_tarski(C_28,A_24)
      | ~ r2_hidden(C_28,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_307,plain,(
    ! [B_79,A_24] :
      ( r1_tarski(B_79,A_24)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_24))
      | v1_xboole_0(k1_zfmisc_1(A_24)) ) ),
    inference(resolution,[status(thm)],[c_303,c_26])).

tff(c_315,plain,(
    ! [B_81,A_82] :
      ( r1_tarski(B_81,A_82)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_82)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_307])).

tff(c_324,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_315])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_332,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_324,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_363,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_2])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_600,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_4','#skF_5')) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_18])).

tff(c_604,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_4','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_600])).

tff(c_620,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_4','#skF_5')) = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_604,c_18])).

tff(c_623,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_4','#skF_5')) = k3_subset_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_620])).

tff(c_224,plain,(
    ! [A_73,B_74] : k2_xboole_0(k3_xboole_0(A_73,B_74),k4_xboole_0(A_73,B_74)) = A_73 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_230,plain,(
    ! [A_73,B_74] : k4_xboole_0(k3_xboole_0(A_73,B_74),A_73) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_16])).

tff(c_1283,plain,(
    k4_xboole_0(k3_subset_1('#skF_4','#skF_5'),'#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_230])).

tff(c_20,plain,(
    ! [A_17,B_18] : k2_xboole_0(k3_xboole_0(A_17,B_18),k4_xboole_0(A_17,B_18)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_597,plain,(
    k2_xboole_0(k3_xboole_0('#skF_4','#skF_5'),k3_subset_1('#skF_4','#skF_5')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_20])).

tff(c_603,plain,(
    k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_597])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    ! [C_28,A_24] :
      ( r2_hidden(C_28,k1_zfmisc_1(A_24))
      | ~ r1_tarski(C_28,A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_414,plain,(
    ! [B_83,A_84] :
      ( m1_subset_1(B_83,A_84)
      | ~ r2_hidden(B_83,A_84)
      | v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_420,plain,(
    ! [C_28,A_24] :
      ( m1_subset_1(C_28,k1_zfmisc_1(A_24))
      | v1_xboole_0(k1_zfmisc_1(A_24))
      | ~ r1_tarski(C_28,A_24) ) ),
    inference(resolution,[status(thm)],[c_28,c_414])).

tff(c_427,plain,(
    ! [C_28,A_24] :
      ( m1_subset_1(C_28,k1_zfmisc_1(A_24))
      | ~ r1_tarski(C_28,A_24) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_420])).

tff(c_1304,plain,(
    ! [A_115,B_116,C_117] :
      ( k4_subset_1(A_115,B_116,C_117) = k2_xboole_0(B_116,C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(A_115))
      | ~ m1_subset_1(B_116,k1_zfmisc_1(A_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10298,plain,(
    ! [A_273,B_274,C_275] :
      ( k4_subset_1(A_273,B_274,C_275) = k2_xboole_0(B_274,C_275)
      | ~ m1_subset_1(B_274,k1_zfmisc_1(A_273))
      | ~ r1_tarski(C_275,A_273) ) ),
    inference(resolution,[status(thm)],[c_427,c_1304])).

tff(c_10410,plain,(
    ! [C_278] :
      ( k4_subset_1('#skF_4','#skF_5',C_278) = k2_xboole_0('#skF_5',C_278)
      | ~ r1_tarski(C_278,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_10298])).

tff(c_10864,plain,(
    ! [A_285] :
      ( k4_subset_1('#skF_4','#skF_5',A_285) = k2_xboole_0('#skF_5',A_285)
      | k4_xboole_0(A_285,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_10410])).

tff(c_48,plain,(
    ! [A_33] : k2_subset_1(A_33) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_56,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) != k2_subset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_59,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_56])).

tff(c_10884,plain,
    ( k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) != '#skF_4'
    | k4_xboole_0(k3_subset_1('#skF_4','#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10864,c_59])).

tff(c_10917,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1283,c_603,c_10884])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:29:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.44/2.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.44/2.60  
% 7.44/2.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.44/2.60  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 7.44/2.60  
% 7.44/2.60  %Foreground sorts:
% 7.44/2.60  
% 7.44/2.60  
% 7.44/2.60  %Background operators:
% 7.44/2.60  
% 7.44/2.60  
% 7.44/2.60  %Foreground operators:
% 7.44/2.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.44/2.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.44/2.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.44/2.60  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.44/2.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.44/2.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.44/2.60  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.44/2.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.44/2.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.44/2.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.44/2.60  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 7.44/2.60  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.44/2.60  tff('#skF_5', type, '#skF_5': $i).
% 7.44/2.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.44/2.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.44/2.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.44/2.60  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.44/2.60  tff('#skF_4', type, '#skF_4': $i).
% 7.44/2.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.44/2.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.44/2.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.44/2.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.44/2.60  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 7.44/2.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.44/2.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.44/2.60  
% 7.44/2.61  tff(f_95, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 7.44/2.61  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 7.44/2.61  tff(f_84, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 7.44/2.61  tff(f_75, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 7.44/2.61  tff(f_60, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 7.44/2.61  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.44/2.61  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.44/2.61  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.44/2.61  tff(f_49, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 7.44/2.61  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 7.44/2.61  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.44/2.61  tff(f_90, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 7.44/2.61  tff(f_77, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 7.44/2.61  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.44/2.61  tff(c_575, plain, (![A_89, B_90]: (k4_xboole_0(A_89, B_90)=k3_subset_1(A_89, B_90) | ~m1_subset_1(B_90, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.44/2.61  tff(c_591, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_575])).
% 7.44/2.61  tff(c_52, plain, (![A_36]: (~v1_xboole_0(k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.44/2.61  tff(c_303, plain, (![B_79, A_80]: (r2_hidden(B_79, A_80) | ~m1_subset_1(B_79, A_80) | v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.44/2.61  tff(c_26, plain, (![C_28, A_24]: (r1_tarski(C_28, A_24) | ~r2_hidden(C_28, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.44/2.61  tff(c_307, plain, (![B_79, A_24]: (r1_tarski(B_79, A_24) | ~m1_subset_1(B_79, k1_zfmisc_1(A_24)) | v1_xboole_0(k1_zfmisc_1(A_24)))), inference(resolution, [status(thm)], [c_303, c_26])).
% 7.44/2.61  tff(c_315, plain, (![B_81, A_82]: (r1_tarski(B_81, A_82) | ~m1_subset_1(B_81, k1_zfmisc_1(A_82)))), inference(negUnitSimplification, [status(thm)], [c_52, c_307])).
% 7.44/2.61  tff(c_324, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_315])).
% 7.44/2.61  tff(c_14, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.44/2.61  tff(c_332, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_324, c_14])).
% 7.44/2.61  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.44/2.61  tff(c_363, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_332, c_2])).
% 7.44/2.61  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.44/2.61  tff(c_600, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_4', '#skF_5'))=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_591, c_18])).
% 7.44/2.61  tff(c_604, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_4', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_363, c_600])).
% 7.44/2.61  tff(c_620, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_4', '#skF_5'))=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_604, c_18])).
% 7.44/2.61  tff(c_623, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_4', '#skF_5'))=k3_subset_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_591, c_620])).
% 7.44/2.61  tff(c_224, plain, (![A_73, B_74]: (k2_xboole_0(k3_xboole_0(A_73, B_74), k4_xboole_0(A_73, B_74))=A_73)), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.44/2.61  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k2_xboole_0(A_13, B_14))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.44/2.61  tff(c_230, plain, (![A_73, B_74]: (k4_xboole_0(k3_xboole_0(A_73, B_74), A_73)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_224, c_16])).
% 7.44/2.61  tff(c_1283, plain, (k4_xboole_0(k3_subset_1('#skF_4', '#skF_5'), '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_623, c_230])).
% 7.44/2.61  tff(c_20, plain, (![A_17, B_18]: (k2_xboole_0(k3_xboole_0(A_17, B_18), k4_xboole_0(A_17, B_18))=A_17)), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.44/2.61  tff(c_597, plain, (k2_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), k3_subset_1('#skF_4', '#skF_5'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_591, c_20])).
% 7.44/2.61  tff(c_603, plain, (k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_363, c_597])).
% 7.44/2.61  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | k4_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.44/2.61  tff(c_28, plain, (![C_28, A_24]: (r2_hidden(C_28, k1_zfmisc_1(A_24)) | ~r1_tarski(C_28, A_24))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.44/2.61  tff(c_414, plain, (![B_83, A_84]: (m1_subset_1(B_83, A_84) | ~r2_hidden(B_83, A_84) | v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.44/2.61  tff(c_420, plain, (![C_28, A_24]: (m1_subset_1(C_28, k1_zfmisc_1(A_24)) | v1_xboole_0(k1_zfmisc_1(A_24)) | ~r1_tarski(C_28, A_24))), inference(resolution, [status(thm)], [c_28, c_414])).
% 7.44/2.61  tff(c_427, plain, (![C_28, A_24]: (m1_subset_1(C_28, k1_zfmisc_1(A_24)) | ~r1_tarski(C_28, A_24))), inference(negUnitSimplification, [status(thm)], [c_52, c_420])).
% 7.44/2.61  tff(c_1304, plain, (![A_115, B_116, C_117]: (k4_subset_1(A_115, B_116, C_117)=k2_xboole_0(B_116, C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(A_115)) | ~m1_subset_1(B_116, k1_zfmisc_1(A_115)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.44/2.61  tff(c_10298, plain, (![A_273, B_274, C_275]: (k4_subset_1(A_273, B_274, C_275)=k2_xboole_0(B_274, C_275) | ~m1_subset_1(B_274, k1_zfmisc_1(A_273)) | ~r1_tarski(C_275, A_273))), inference(resolution, [status(thm)], [c_427, c_1304])).
% 7.44/2.61  tff(c_10410, plain, (![C_278]: (k4_subset_1('#skF_4', '#skF_5', C_278)=k2_xboole_0('#skF_5', C_278) | ~r1_tarski(C_278, '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_10298])).
% 7.44/2.61  tff(c_10864, plain, (![A_285]: (k4_subset_1('#skF_4', '#skF_5', A_285)=k2_xboole_0('#skF_5', A_285) | k4_xboole_0(A_285, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_10410])).
% 7.44/2.61  tff(c_48, plain, (![A_33]: (k2_subset_1(A_33)=A_33)), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.44/2.61  tff(c_56, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))!=k2_subset_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.44/2.61  tff(c_59, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_56])).
% 7.44/2.61  tff(c_10884, plain, (k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))!='#skF_4' | k4_xboole_0(k3_subset_1('#skF_4', '#skF_5'), '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_10864, c_59])).
% 7.44/2.61  tff(c_10917, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1283, c_603, c_10884])).
% 7.44/2.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.44/2.61  
% 7.44/2.61  Inference rules
% 7.44/2.61  ----------------------
% 7.44/2.61  #Ref     : 0
% 7.44/2.61  #Sup     : 2611
% 7.44/2.61  #Fact    : 0
% 7.44/2.61  #Define  : 0
% 7.44/2.61  #Split   : 5
% 7.44/2.61  #Chain   : 0
% 7.44/2.61  #Close   : 0
% 7.44/2.61  
% 7.44/2.61  Ordering : KBO
% 7.44/2.61  
% 7.44/2.61  Simplification rules
% 7.44/2.61  ----------------------
% 7.44/2.61  #Subsume      : 270
% 7.44/2.61  #Demod        : 3252
% 7.44/2.61  #Tautology    : 1798
% 7.44/2.61  #SimpNegUnit  : 56
% 7.44/2.61  #BackRed      : 12
% 7.44/2.61  
% 7.44/2.61  #Partial instantiations: 0
% 7.44/2.61  #Strategies tried      : 1
% 7.44/2.61  
% 7.44/2.61  Timing (in seconds)
% 7.44/2.61  ----------------------
% 7.44/2.62  Preprocessing        : 0.33
% 7.44/2.62  Parsing              : 0.18
% 7.44/2.62  CNF conversion       : 0.02
% 7.44/2.62  Main loop            : 1.52
% 7.44/2.62  Inferencing          : 0.41
% 7.44/2.62  Reduction            : 0.74
% 7.44/2.62  Demodulation         : 0.60
% 7.44/2.62  BG Simplification    : 0.05
% 7.44/2.62  Subsumption          : 0.23
% 7.44/2.62  Abstraction          : 0.08
% 7.44/2.62  MUC search           : 0.00
% 7.44/2.62  Cooper               : 0.00
% 7.44/2.62  Total                : 1.88
% 7.44/2.62  Index Insertion      : 0.00
% 7.44/2.62  Index Deletion       : 0.00
% 7.44/2.62  Index Matching       : 0.00
% 7.44/2.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
