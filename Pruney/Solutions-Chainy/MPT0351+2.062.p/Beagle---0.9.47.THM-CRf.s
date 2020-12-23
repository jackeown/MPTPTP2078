%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:45 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 118 expanded)
%              Number of leaves         :   38 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :   78 ( 134 expanded)
%              Number of equality atoms :   40 (  66 expanded)
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

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_68,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_70,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_34,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_46,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_36,plain,(
    ! [A_49] : k2_subset_1(A_49) = A_49 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_38,plain,(
    ! [A_50] : m1_subset_1(k2_subset_1(A_50),k1_zfmisc_1(A_50)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_47,plain,(
    ! [A_50] : m1_subset_1(A_50,k1_zfmisc_1(A_50)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38])).

tff(c_261,plain,(
    ! [A_106,B_107,C_108] :
      ( k4_subset_1(A_106,B_107,C_108) = k2_xboole_0(B_107,C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(A_106))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(A_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_268,plain,(
    ! [A_109,B_110] :
      ( k4_subset_1(A_109,B_110,A_109) = k2_xboole_0(B_110,A_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_109)) ) ),
    inference(resolution,[status(thm)],[c_47,c_261])).

tff(c_275,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_268])).

tff(c_44,plain,(
    k4_subset_1('#skF_2','#skF_3',k2_subset_1('#skF_2')) != k2_subset_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_48,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_44])).

tff(c_285,plain,(
    k2_xboole_0('#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_48])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_18,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [A_8] : k3_xboole_0(A_8,A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_113,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = k4_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_122,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k4_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_113])).

tff(c_126,plain,(
    ! [A_75] : k4_xboole_0(A_75,A_75) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_122])).

tff(c_16,plain,(
    ! [A_14,B_15] : k2_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_131,plain,(
    ! [A_75] : k2_xboole_0(A_75,k1_xboole_0) = k2_xboole_0(A_75,A_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_16])).

tff(c_135,plain,(
    ! [A_75] : k2_xboole_0(A_75,k1_xboole_0) = A_75 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_131])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_181,plain,(
    ! [C_86,A_87,B_88] :
      ( r2_hidden(C_86,A_87)
      | ~ r2_hidden(C_86,B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_206,plain,(
    ! [A_96,B_97,A_98] :
      ( r2_hidden('#skF_1'(A_96,B_97),A_98)
      | ~ m1_subset_1(A_96,k1_zfmisc_1(A_98))
      | r1_tarski(A_96,B_97) ) ),
    inference(resolution,[status(thm)],[c_6,c_181])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_218,plain,(
    ! [A_99,A_100] :
      ( ~ m1_subset_1(A_99,k1_zfmisc_1(A_100))
      | r1_tarski(A_99,A_100) ) ),
    inference(resolution,[status(thm)],[c_206,c_4])).

tff(c_227,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_218])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_231,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_227,c_14])).

tff(c_12,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_244,plain,(
    k5_xboole_0('#skF_3','#skF_3') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_12])).

tff(c_247,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_244])).

tff(c_252,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_16])).

tff(c_255,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_252])).

tff(c_290,plain,(
    ! [B_112] :
      ( k4_subset_1('#skF_2',B_112,'#skF_3') = k2_xboole_0(B_112,'#skF_3')
      | ~ m1_subset_1(B_112,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_46,c_261])).

tff(c_294,plain,(
    k4_subset_1('#skF_2','#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_47,c_290])).

tff(c_299,plain,(
    k4_subset_1('#skF_2','#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_294])).

tff(c_384,plain,(
    ! [A_135,C_136,B_137] :
      ( k4_subset_1(A_135,C_136,B_137) = k4_subset_1(A_135,B_137,C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(A_135))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(A_135)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_392,plain,(
    ! [A_138,B_139] :
      ( k4_subset_1(A_138,B_139,A_138) = k4_subset_1(A_138,A_138,B_139)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(A_138)) ) ),
    inference(resolution,[status(thm)],[c_47,c_384])).

tff(c_396,plain,(
    k4_subset_1('#skF_2','#skF_2','#skF_3') = k4_subset_1('#skF_2','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_392])).

tff(c_400,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_275,c_396])).

tff(c_402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_285,c_400])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:55 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.31  
% 2.19/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.31  %$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.19/1.31  
% 2.19/1.31  %Foreground sorts:
% 2.19/1.31  
% 2.19/1.31  
% 2.19/1.31  %Background operators:
% 2.19/1.31  
% 2.19/1.31  
% 2.19/1.31  %Foreground operators:
% 2.19/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.19/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.19/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.19/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.31  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.19/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.19/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.19/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.19/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.19/1.31  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.19/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.31  
% 2.19/1.33  tff(f_88, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 2.19/1.33  tff(f_68, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.19/1.33  tff(f_70, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.19/1.33  tff(f_83, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.19/1.33  tff(f_34, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.19/1.33  tff(f_46, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.19/1.33  tff(f_36, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.19/1.33  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.19/1.33  tff(f_44, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.19/1.33  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.19/1.33  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.19/1.33  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.19/1.33  tff(f_66, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k4_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 2.19/1.33  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.19/1.33  tff(c_36, plain, (![A_49]: (k2_subset_1(A_49)=A_49)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.19/1.33  tff(c_38, plain, (![A_50]: (m1_subset_1(k2_subset_1(A_50), k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.19/1.33  tff(c_47, plain, (![A_50]: (m1_subset_1(A_50, k1_zfmisc_1(A_50)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38])).
% 2.19/1.33  tff(c_261, plain, (![A_106, B_107, C_108]: (k4_subset_1(A_106, B_107, C_108)=k2_xboole_0(B_107, C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(A_106)) | ~m1_subset_1(B_107, k1_zfmisc_1(A_106)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.19/1.33  tff(c_268, plain, (![A_109, B_110]: (k4_subset_1(A_109, B_110, A_109)=k2_xboole_0(B_110, A_109) | ~m1_subset_1(B_110, k1_zfmisc_1(A_109)))), inference(resolution, [status(thm)], [c_47, c_261])).
% 2.19/1.33  tff(c_275, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')=k2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_268])).
% 2.19/1.33  tff(c_44, plain, (k4_subset_1('#skF_2', '#skF_3', k2_subset_1('#skF_2'))!=k2_subset_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.19/1.33  tff(c_48, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_44])).
% 2.19/1.33  tff(c_285, plain, (k2_xboole_0('#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_275, c_48])).
% 2.19/1.33  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.19/1.33  tff(c_18, plain, (![A_16]: (k5_xboole_0(A_16, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.19/1.33  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.19/1.33  tff(c_113, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k3_xboole_0(A_73, B_74))=k4_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.19/1.33  tff(c_122, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k4_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_113])).
% 2.19/1.33  tff(c_126, plain, (![A_75]: (k4_xboole_0(A_75, A_75)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_122])).
% 2.19/1.33  tff(c_16, plain, (![A_14, B_15]: (k2_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.19/1.33  tff(c_131, plain, (![A_75]: (k2_xboole_0(A_75, k1_xboole_0)=k2_xboole_0(A_75, A_75))), inference(superposition, [status(thm), theory('equality')], [c_126, c_16])).
% 2.19/1.33  tff(c_135, plain, (![A_75]: (k2_xboole_0(A_75, k1_xboole_0)=A_75)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_131])).
% 2.19/1.33  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.19/1.33  tff(c_181, plain, (![C_86, A_87, B_88]: (r2_hidden(C_86, A_87) | ~r2_hidden(C_86, B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.19/1.33  tff(c_206, plain, (![A_96, B_97, A_98]: (r2_hidden('#skF_1'(A_96, B_97), A_98) | ~m1_subset_1(A_96, k1_zfmisc_1(A_98)) | r1_tarski(A_96, B_97))), inference(resolution, [status(thm)], [c_6, c_181])).
% 2.19/1.33  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.19/1.33  tff(c_218, plain, (![A_99, A_100]: (~m1_subset_1(A_99, k1_zfmisc_1(A_100)) | r1_tarski(A_99, A_100))), inference(resolution, [status(thm)], [c_206, c_4])).
% 2.19/1.33  tff(c_227, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_218])).
% 2.19/1.33  tff(c_14, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.19/1.33  tff(c_231, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_227, c_14])).
% 2.19/1.33  tff(c_12, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.19/1.33  tff(c_244, plain, (k5_xboole_0('#skF_3', '#skF_3')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_231, c_12])).
% 2.19/1.33  tff(c_247, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_244])).
% 2.19/1.33  tff(c_252, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_247, c_16])).
% 2.19/1.33  tff(c_255, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_252])).
% 2.19/1.33  tff(c_290, plain, (![B_112]: (k4_subset_1('#skF_2', B_112, '#skF_3')=k2_xboole_0(B_112, '#skF_3') | ~m1_subset_1(B_112, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_46, c_261])).
% 2.19/1.33  tff(c_294, plain, (k4_subset_1('#skF_2', '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_47, c_290])).
% 2.19/1.33  tff(c_299, plain, (k4_subset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_255, c_294])).
% 2.19/1.33  tff(c_384, plain, (![A_135, C_136, B_137]: (k4_subset_1(A_135, C_136, B_137)=k4_subset_1(A_135, B_137, C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(A_135)) | ~m1_subset_1(B_137, k1_zfmisc_1(A_135)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.19/1.33  tff(c_392, plain, (![A_138, B_139]: (k4_subset_1(A_138, B_139, A_138)=k4_subset_1(A_138, A_138, B_139) | ~m1_subset_1(B_139, k1_zfmisc_1(A_138)))), inference(resolution, [status(thm)], [c_47, c_384])).
% 2.19/1.33  tff(c_396, plain, (k4_subset_1('#skF_2', '#skF_2', '#skF_3')=k4_subset_1('#skF_2', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_392])).
% 2.19/1.33  tff(c_400, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_299, c_275, c_396])).
% 2.19/1.33  tff(c_402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_285, c_400])).
% 2.19/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.33  
% 2.19/1.33  Inference rules
% 2.19/1.33  ----------------------
% 2.19/1.33  #Ref     : 0
% 2.19/1.33  #Sup     : 87
% 2.19/1.33  #Fact    : 0
% 2.19/1.33  #Define  : 0
% 2.19/1.33  #Split   : 1
% 2.19/1.33  #Chain   : 0
% 2.19/1.33  #Close   : 0
% 2.19/1.33  
% 2.19/1.33  Ordering : KBO
% 2.19/1.33  
% 2.19/1.33  Simplification rules
% 2.19/1.33  ----------------------
% 2.19/1.33  #Subsume      : 5
% 2.19/1.33  #Demod        : 18
% 2.19/1.33  #Tautology    : 49
% 2.19/1.33  #SimpNegUnit  : 1
% 2.19/1.33  #BackRed      : 1
% 2.19/1.33  
% 2.19/1.33  #Partial instantiations: 0
% 2.19/1.33  #Strategies tried      : 1
% 2.19/1.33  
% 2.19/1.33  Timing (in seconds)
% 2.19/1.33  ----------------------
% 2.62/1.33  Preprocessing        : 0.32
% 2.62/1.33  Parsing              : 0.18
% 2.62/1.33  CNF conversion       : 0.02
% 2.62/1.33  Main loop            : 0.24
% 2.62/1.33  Inferencing          : 0.09
% 2.62/1.33  Reduction            : 0.07
% 2.62/1.33  Demodulation         : 0.05
% 2.62/1.33  BG Simplification    : 0.02
% 2.62/1.33  Subsumption          : 0.05
% 2.62/1.33  Abstraction          : 0.02
% 2.62/1.33  MUC search           : 0.00
% 2.62/1.33  Cooper               : 0.00
% 2.62/1.33  Total                : 0.60
% 2.62/1.33  Index Insertion      : 0.00
% 2.62/1.33  Index Deletion       : 0.00
% 2.62/1.33  Index Matching       : 0.00
% 2.62/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
