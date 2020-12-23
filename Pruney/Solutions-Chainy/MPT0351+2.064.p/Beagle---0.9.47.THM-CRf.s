%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:45 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 106 expanded)
%              Number of leaves         :   37 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :   71 ( 122 expanded)
%              Number of equality atoms :   33 (  54 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_66,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_68,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_36,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_44,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34,plain,(
    ! [A_46] : k2_subset_1(A_46) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_36,plain,(
    ! [A_47] : m1_subset_1(k2_subset_1(A_47),k1_zfmisc_1(A_47)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_45,plain,(
    ! [A_47] : m1_subset_1(A_47,k1_zfmisc_1(A_47)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36])).

tff(c_258,plain,(
    ! [A_103,B_104,C_105] :
      ( k4_subset_1(A_103,B_104,C_105) = k2_xboole_0(B_104,C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(A_103))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_265,plain,(
    ! [A_106,B_107] :
      ( k4_subset_1(A_106,B_107,A_106) = k2_xboole_0(B_107,A_106)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(A_106)) ) ),
    inference(resolution,[status(thm)],[c_45,c_258])).

tff(c_272,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_265])).

tff(c_42,plain,(
    k4_subset_1('#skF_2','#skF_3',k2_subset_1('#skF_2')) != k2_subset_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_46,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_42])).

tff(c_282,plain,(
    k2_xboole_0('#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_46])).

tff(c_10,plain,(
    ! [A_8] : k2_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_178,plain,(
    ! [C_83,A_84,B_85] :
      ( r2_hidden(C_83,A_84)
      | ~ r2_hidden(C_83,B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_203,plain,(
    ! [A_93,B_94,A_95] :
      ( r2_hidden('#skF_1'(A_93,B_94),A_95)
      | ~ m1_subset_1(A_93,k1_zfmisc_1(A_95))
      | r1_tarski(A_93,B_94) ) ),
    inference(resolution,[status(thm)],[c_6,c_178])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_215,plain,(
    ! [A_96,A_97] :
      ( ~ m1_subset_1(A_96,k1_zfmisc_1(A_97))
      | r1_tarski(A_96,A_97) ) ),
    inference(resolution,[status(thm)],[c_203,c_4])).

tff(c_224,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_215])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_228,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_224,c_12])).

tff(c_8,plain,(
    ! [A_6,B_7] : k5_xboole_0(A_6,k3_xboole_0(A_6,B_7)) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_241,plain,(
    k5_xboole_0('#skF_3','#skF_3') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_8])).

tff(c_244,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_241])).

tff(c_14,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_249,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_14])).

tff(c_252,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_249])).

tff(c_287,plain,(
    ! [B_109] :
      ( k4_subset_1('#skF_2',B_109,'#skF_3') = k2_xboole_0(B_109,'#skF_3')
      | ~ m1_subset_1(B_109,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_44,c_258])).

tff(c_291,plain,(
    k4_subset_1('#skF_2','#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_45,c_287])).

tff(c_296,plain,(
    k4_subset_1('#skF_2','#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_291])).

tff(c_381,plain,(
    ! [A_132,C_133,B_134] :
      ( k4_subset_1(A_132,C_133,B_134) = k4_subset_1(A_132,B_134,C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(A_132))
      | ~ m1_subset_1(B_134,k1_zfmisc_1(A_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_389,plain,(
    ! [A_135,B_136] :
      ( k4_subset_1(A_135,B_136,A_135) = k4_subset_1(A_135,A_135,B_136)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(A_135)) ) ),
    inference(resolution,[status(thm)],[c_45,c_381])).

tff(c_393,plain,(
    k4_subset_1('#skF_2','#skF_2','#skF_3') = k4_subset_1('#skF_2','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_389])).

tff(c_397,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_272,c_393])).

tff(c_399,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_282,c_397])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:01:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.31  
% 2.37/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.31  %$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.37/1.31  
% 2.37/1.31  %Foreground sorts:
% 2.37/1.31  
% 2.37/1.31  
% 2.37/1.31  %Background operators:
% 2.37/1.31  
% 2.37/1.31  
% 2.37/1.31  %Foreground operators:
% 2.37/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.37/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.37/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.37/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.37/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.37/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.37/1.31  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.37/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.37/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.37/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.37/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.37/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.37/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.37/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.37/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.37/1.31  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.37/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.31  
% 2.37/1.33  tff(f_86, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 2.37/1.33  tff(f_66, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.37/1.33  tff(f_68, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.37/1.33  tff(f_81, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.37/1.33  tff(f_36, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.37/1.33  tff(f_44, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.37/1.33  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.37/1.33  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.37/1.33  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.37/1.33  tff(f_34, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.37/1.33  tff(f_42, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.37/1.33  tff(f_64, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k4_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 2.37/1.33  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.37/1.33  tff(c_34, plain, (![A_46]: (k2_subset_1(A_46)=A_46)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.37/1.33  tff(c_36, plain, (![A_47]: (m1_subset_1(k2_subset_1(A_47), k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.37/1.33  tff(c_45, plain, (![A_47]: (m1_subset_1(A_47, k1_zfmisc_1(A_47)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36])).
% 2.37/1.33  tff(c_258, plain, (![A_103, B_104, C_105]: (k4_subset_1(A_103, B_104, C_105)=k2_xboole_0(B_104, C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(A_103)) | ~m1_subset_1(B_104, k1_zfmisc_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.37/1.33  tff(c_265, plain, (![A_106, B_107]: (k4_subset_1(A_106, B_107, A_106)=k2_xboole_0(B_107, A_106) | ~m1_subset_1(B_107, k1_zfmisc_1(A_106)))), inference(resolution, [status(thm)], [c_45, c_258])).
% 2.37/1.33  tff(c_272, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')=k2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_265])).
% 2.37/1.33  tff(c_42, plain, (k4_subset_1('#skF_2', '#skF_3', k2_subset_1('#skF_2'))!=k2_subset_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.37/1.33  tff(c_46, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_42])).
% 2.37/1.33  tff(c_282, plain, (k2_xboole_0('#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_272, c_46])).
% 2.37/1.33  tff(c_10, plain, (![A_8]: (k2_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.37/1.33  tff(c_16, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.37/1.33  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.37/1.33  tff(c_178, plain, (![C_83, A_84, B_85]: (r2_hidden(C_83, A_84) | ~r2_hidden(C_83, B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.37/1.33  tff(c_203, plain, (![A_93, B_94, A_95]: (r2_hidden('#skF_1'(A_93, B_94), A_95) | ~m1_subset_1(A_93, k1_zfmisc_1(A_95)) | r1_tarski(A_93, B_94))), inference(resolution, [status(thm)], [c_6, c_178])).
% 2.37/1.33  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.37/1.33  tff(c_215, plain, (![A_96, A_97]: (~m1_subset_1(A_96, k1_zfmisc_1(A_97)) | r1_tarski(A_96, A_97))), inference(resolution, [status(thm)], [c_203, c_4])).
% 2.37/1.33  tff(c_224, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_215])).
% 2.37/1.33  tff(c_12, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.37/1.33  tff(c_228, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_224, c_12])).
% 2.37/1.33  tff(c_8, plain, (![A_6, B_7]: (k5_xboole_0(A_6, k3_xboole_0(A_6, B_7))=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.37/1.33  tff(c_241, plain, (k5_xboole_0('#skF_3', '#skF_3')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_228, c_8])).
% 2.37/1.33  tff(c_244, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_241])).
% 2.37/1.33  tff(c_14, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.37/1.33  tff(c_249, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_244, c_14])).
% 2.37/1.33  tff(c_252, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_249])).
% 2.37/1.33  tff(c_287, plain, (![B_109]: (k4_subset_1('#skF_2', B_109, '#skF_3')=k2_xboole_0(B_109, '#skF_3') | ~m1_subset_1(B_109, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_44, c_258])).
% 2.37/1.33  tff(c_291, plain, (k4_subset_1('#skF_2', '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_45, c_287])).
% 2.37/1.33  tff(c_296, plain, (k4_subset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_252, c_291])).
% 2.37/1.33  tff(c_381, plain, (![A_132, C_133, B_134]: (k4_subset_1(A_132, C_133, B_134)=k4_subset_1(A_132, B_134, C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(A_132)) | ~m1_subset_1(B_134, k1_zfmisc_1(A_132)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.37/1.33  tff(c_389, plain, (![A_135, B_136]: (k4_subset_1(A_135, B_136, A_135)=k4_subset_1(A_135, A_135, B_136) | ~m1_subset_1(B_136, k1_zfmisc_1(A_135)))), inference(resolution, [status(thm)], [c_45, c_381])).
% 2.37/1.33  tff(c_393, plain, (k4_subset_1('#skF_2', '#skF_2', '#skF_3')=k4_subset_1('#skF_2', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_389])).
% 2.37/1.33  tff(c_397, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_296, c_272, c_393])).
% 2.37/1.33  tff(c_399, plain, $false, inference(negUnitSimplification, [status(thm)], [c_282, c_397])).
% 2.37/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.33  
% 2.37/1.33  Inference rules
% 2.37/1.33  ----------------------
% 2.37/1.33  #Ref     : 0
% 2.37/1.33  #Sup     : 87
% 2.37/1.33  #Fact    : 0
% 2.37/1.33  #Define  : 0
% 2.37/1.33  #Split   : 1
% 2.37/1.33  #Chain   : 0
% 2.37/1.33  #Close   : 0
% 2.37/1.33  
% 2.37/1.33  Ordering : KBO
% 2.37/1.33  
% 2.37/1.33  Simplification rules
% 2.37/1.33  ----------------------
% 2.37/1.33  #Subsume      : 5
% 2.37/1.33  #Demod        : 17
% 2.37/1.33  #Tautology    : 48
% 2.37/1.33  #SimpNegUnit  : 1
% 2.37/1.33  #BackRed      : 1
% 2.37/1.33  
% 2.37/1.33  #Partial instantiations: 0
% 2.37/1.33  #Strategies tried      : 1
% 2.37/1.33  
% 2.37/1.33  Timing (in seconds)
% 2.37/1.33  ----------------------
% 2.37/1.33  Preprocessing        : 0.32
% 2.37/1.33  Parsing              : 0.18
% 2.37/1.33  CNF conversion       : 0.02
% 2.37/1.33  Main loop            : 0.24
% 2.37/1.33  Inferencing          : 0.09
% 2.37/1.33  Reduction            : 0.07
% 2.37/1.33  Demodulation         : 0.05
% 2.37/1.33  BG Simplification    : 0.02
% 2.37/1.33  Subsumption          : 0.05
% 2.37/1.33  Abstraction          : 0.01
% 2.37/1.33  MUC search           : 0.00
% 2.37/1.33  Cooper               : 0.00
% 2.37/1.33  Total                : 0.58
% 2.37/1.33  Index Insertion      : 0.00
% 2.37/1.33  Index Deletion       : 0.00
% 2.37/1.33  Index Matching       : 0.00
% 2.37/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
