%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:44 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 119 expanded)
%              Number of leaves         :   32 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :   83 ( 186 expanded)
%              Number of equality atoms :   27 (  52 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_55,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_57,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_24,plain,(
    ! [A_39] : k2_subset_1(A_39) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_40] : m1_subset_1(k2_subset_1(A_40),k1_zfmisc_1(A_40)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_41,plain,(
    ! [A_40] : m1_subset_1(A_40,k1_zfmisc_1(A_40)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26])).

tff(c_176,plain,(
    ! [A_84,B_85,C_86] :
      ( k4_subset_1(A_84,B_85,C_86) = k2_xboole_0(B_85,C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(A_84))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_210,plain,(
    ! [A_94,B_95] :
      ( k4_subset_1(A_94,B_95,A_94) = k2_xboole_0(B_95,A_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94)) ) ),
    inference(resolution,[status(thm)],[c_41,c_176])).

tff(c_215,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_210])).

tff(c_38,plain,(
    k4_subset_1('#skF_2','#skF_3',k2_subset_1('#skF_2')) != k2_subset_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_42,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_38])).

tff(c_217,plain,(
    k2_xboole_0('#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_42])).

tff(c_260,plain,(
    ! [A_104,B_105,C_106] :
      ( r2_hidden('#skF_1'(A_104,B_105,C_106),B_105)
      | r1_tarski(B_105,C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(A_104))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_28,plain,(
    ! [C_44,A_41,B_42] :
      ( r2_hidden(C_44,A_41)
      | ~ r2_hidden(C_44,B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_389,plain,(
    ! [A_125,B_126,C_127,A_128] :
      ( r2_hidden('#skF_1'(A_125,B_126,C_127),A_128)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_128))
      | r1_tarski(B_126,C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(A_125))
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_125)) ) ),
    inference(resolution,[status(thm)],[c_260,c_28])).

tff(c_32,plain,(
    ! [A_48,B_49,C_53] :
      ( ~ r2_hidden('#skF_1'(A_48,B_49,C_53),C_53)
      | r1_tarski(B_49,C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(A_48))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_407,plain,(
    ! [B_133,A_134,A_135] :
      ( ~ m1_subset_1(B_133,k1_zfmisc_1(A_134))
      | r1_tarski(B_133,A_134)
      | ~ m1_subset_1(A_134,k1_zfmisc_1(A_135))
      | ~ m1_subset_1(B_133,k1_zfmisc_1(A_135)) ) ),
    inference(resolution,[status(thm)],[c_389,c_32])).

tff(c_416,plain,(
    ! [A_135] :
      ( r1_tarski('#skF_3','#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(A_135))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_135)) ) ),
    inference(resolution,[status(thm)],[c_40,c_407])).

tff(c_420,plain,(
    ! [A_136] :
      ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(A_136))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_136)) ) ),
    inference(splitLeft,[status(thm)],[c_416])).

tff(c_424,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_41,c_420])).

tff(c_428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_424])).

tff(c_429,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_416])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_433,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_429,c_6])).

tff(c_62,plain,(
    ! [B_59,A_60] : k3_xboole_0(B_59,A_60) = k3_xboole_0(A_60,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_77,plain,(
    ! [A_60,B_59] : k2_xboole_0(A_60,k3_xboole_0(B_59,A_60)) = A_60 ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_4])).

tff(c_437,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_77])).

tff(c_183,plain,(
    ! [B_87] :
      ( k4_subset_1('#skF_2',B_87,'#skF_3') = k2_xboole_0(B_87,'#skF_3')
      | ~ m1_subset_1(B_87,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_40,c_176])).

tff(c_192,plain,(
    k4_subset_1('#skF_2','#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_41,c_183])).

tff(c_231,plain,(
    ! [A_97,C_98,B_99] :
      ( k4_subset_1(A_97,C_98,B_99) = k4_subset_1(A_97,B_99,C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(A_97))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_239,plain,(
    ! [B_103] :
      ( k4_subset_1('#skF_2',B_103,'#skF_3') = k4_subset_1('#skF_2','#skF_3',B_103)
      | ~ m1_subset_1(B_103,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_40,c_231])).

tff(c_246,plain,(
    k4_subset_1('#skF_2','#skF_2','#skF_3') = k4_subset_1('#skF_2','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_41,c_239])).

tff(c_250,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_192,c_246])).

tff(c_445,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_250])).

tff(c_447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_445])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:23:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.42  
% 2.63/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.43  %$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 2.63/1.43  
% 2.63/1.43  %Foreground sorts:
% 2.63/1.43  
% 2.63/1.43  
% 2.63/1.43  %Background operators:
% 2.63/1.43  
% 2.63/1.43  
% 2.63/1.43  %Foreground operators:
% 2.63/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.63/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.63/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.63/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.63/1.43  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.63/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.63/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.63/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.63/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.63/1.43  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.63/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.63/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.63/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.63/1.43  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.63/1.43  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.63/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.63/1.43  
% 2.63/1.44  tff(f_89, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 2.63/1.44  tff(f_55, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.63/1.44  tff(f_57, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.63/1.44  tff(f_70, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.63/1.44  tff(f_84, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 2.63/1.44  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.63/1.44  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.63/1.44  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.63/1.44  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.63/1.44  tff(f_53, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k4_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 2.63/1.44  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.63/1.44  tff(c_24, plain, (![A_39]: (k2_subset_1(A_39)=A_39)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.63/1.44  tff(c_26, plain, (![A_40]: (m1_subset_1(k2_subset_1(A_40), k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.63/1.44  tff(c_41, plain, (![A_40]: (m1_subset_1(A_40, k1_zfmisc_1(A_40)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26])).
% 2.63/1.44  tff(c_176, plain, (![A_84, B_85, C_86]: (k4_subset_1(A_84, B_85, C_86)=k2_xboole_0(B_85, C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(A_84)) | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.63/1.44  tff(c_210, plain, (![A_94, B_95]: (k4_subset_1(A_94, B_95, A_94)=k2_xboole_0(B_95, A_94) | ~m1_subset_1(B_95, k1_zfmisc_1(A_94)))), inference(resolution, [status(thm)], [c_41, c_176])).
% 2.63/1.44  tff(c_215, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')=k2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_210])).
% 2.63/1.44  tff(c_38, plain, (k4_subset_1('#skF_2', '#skF_3', k2_subset_1('#skF_2'))!=k2_subset_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.63/1.44  tff(c_42, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_38])).
% 2.63/1.44  tff(c_217, plain, (k2_xboole_0('#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_215, c_42])).
% 2.63/1.44  tff(c_260, plain, (![A_104, B_105, C_106]: (r2_hidden('#skF_1'(A_104, B_105, C_106), B_105) | r1_tarski(B_105, C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(A_104)) | ~m1_subset_1(B_105, k1_zfmisc_1(A_104)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.63/1.44  tff(c_28, plain, (![C_44, A_41, B_42]: (r2_hidden(C_44, A_41) | ~r2_hidden(C_44, B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.63/1.44  tff(c_389, plain, (![A_125, B_126, C_127, A_128]: (r2_hidden('#skF_1'(A_125, B_126, C_127), A_128) | ~m1_subset_1(B_126, k1_zfmisc_1(A_128)) | r1_tarski(B_126, C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(A_125)) | ~m1_subset_1(B_126, k1_zfmisc_1(A_125)))), inference(resolution, [status(thm)], [c_260, c_28])).
% 2.63/1.44  tff(c_32, plain, (![A_48, B_49, C_53]: (~r2_hidden('#skF_1'(A_48, B_49, C_53), C_53) | r1_tarski(B_49, C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(A_48)) | ~m1_subset_1(B_49, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.63/1.44  tff(c_407, plain, (![B_133, A_134, A_135]: (~m1_subset_1(B_133, k1_zfmisc_1(A_134)) | r1_tarski(B_133, A_134) | ~m1_subset_1(A_134, k1_zfmisc_1(A_135)) | ~m1_subset_1(B_133, k1_zfmisc_1(A_135)))), inference(resolution, [status(thm)], [c_389, c_32])).
% 2.63/1.44  tff(c_416, plain, (![A_135]: (r1_tarski('#skF_3', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(A_135)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_135)))), inference(resolution, [status(thm)], [c_40, c_407])).
% 2.63/1.44  tff(c_420, plain, (![A_136]: (~m1_subset_1('#skF_2', k1_zfmisc_1(A_136)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_136)))), inference(splitLeft, [status(thm)], [c_416])).
% 2.63/1.44  tff(c_424, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_41, c_420])).
% 2.63/1.44  tff(c_428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_424])).
% 2.63/1.44  tff(c_429, plain, (r1_tarski('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_416])).
% 2.63/1.44  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.63/1.44  tff(c_433, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_429, c_6])).
% 2.63/1.44  tff(c_62, plain, (![B_59, A_60]: (k3_xboole_0(B_59, A_60)=k3_xboole_0(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.63/1.44  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.63/1.44  tff(c_77, plain, (![A_60, B_59]: (k2_xboole_0(A_60, k3_xboole_0(B_59, A_60))=A_60)), inference(superposition, [status(thm), theory('equality')], [c_62, c_4])).
% 2.63/1.44  tff(c_437, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_433, c_77])).
% 2.63/1.44  tff(c_183, plain, (![B_87]: (k4_subset_1('#skF_2', B_87, '#skF_3')=k2_xboole_0(B_87, '#skF_3') | ~m1_subset_1(B_87, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_40, c_176])).
% 2.63/1.44  tff(c_192, plain, (k4_subset_1('#skF_2', '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_41, c_183])).
% 2.63/1.44  tff(c_231, plain, (![A_97, C_98, B_99]: (k4_subset_1(A_97, C_98, B_99)=k4_subset_1(A_97, B_99, C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(A_97)) | ~m1_subset_1(B_99, k1_zfmisc_1(A_97)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.63/1.44  tff(c_239, plain, (![B_103]: (k4_subset_1('#skF_2', B_103, '#skF_3')=k4_subset_1('#skF_2', '#skF_3', B_103) | ~m1_subset_1(B_103, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_40, c_231])).
% 2.63/1.44  tff(c_246, plain, (k4_subset_1('#skF_2', '#skF_2', '#skF_3')=k4_subset_1('#skF_2', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_41, c_239])).
% 2.63/1.44  tff(c_250, plain, (k2_xboole_0('#skF_2', '#skF_3')=k2_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_192, c_246])).
% 2.63/1.44  tff(c_445, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_437, c_250])).
% 2.63/1.44  tff(c_447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_217, c_445])).
% 2.63/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.44  
% 2.63/1.44  Inference rules
% 2.63/1.44  ----------------------
% 2.63/1.44  #Ref     : 0
% 2.63/1.44  #Sup     : 99
% 2.63/1.44  #Fact    : 0
% 2.63/1.44  #Define  : 0
% 2.63/1.44  #Split   : 1
% 2.63/1.44  #Chain   : 0
% 2.63/1.44  #Close   : 0
% 2.63/1.44  
% 2.63/1.44  Ordering : KBO
% 2.63/1.44  
% 2.63/1.44  Simplification rules
% 2.63/1.44  ----------------------
% 2.63/1.44  #Subsume      : 0
% 2.63/1.44  #Demod        : 28
% 2.63/1.44  #Tautology    : 70
% 2.63/1.44  #SimpNegUnit  : 1
% 2.63/1.44  #BackRed      : 5
% 2.63/1.44  
% 2.63/1.44  #Partial instantiations: 0
% 2.63/1.44  #Strategies tried      : 1
% 2.63/1.44  
% 2.63/1.44  Timing (in seconds)
% 2.63/1.44  ----------------------
% 2.63/1.44  Preprocessing        : 0.33
% 2.63/1.44  Parsing              : 0.19
% 2.63/1.44  CNF conversion       : 0.02
% 2.63/1.44  Main loop            : 0.26
% 2.63/1.44  Inferencing          : 0.10
% 2.63/1.44  Reduction            : 0.08
% 2.63/1.44  Demodulation         : 0.06
% 2.63/1.44  BG Simplification    : 0.02
% 2.63/1.44  Subsumption          : 0.05
% 2.63/1.44  Abstraction          : 0.02
% 2.63/1.44  MUC search           : 0.00
% 2.63/1.44  Cooper               : 0.00
% 2.63/1.44  Total                : 0.62
% 2.63/1.44  Index Insertion      : 0.00
% 2.63/1.44  Index Deletion       : 0.00
% 2.63/1.44  Index Matching       : 0.00
% 2.63/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
