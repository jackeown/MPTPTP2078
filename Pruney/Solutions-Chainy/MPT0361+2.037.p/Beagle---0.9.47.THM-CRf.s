%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:32 EST 2020

% Result     : Theorem 4.74s
% Output     : CNFRefutation 4.74s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 110 expanded)
%              Number of leaves         :   29 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   85 ( 188 expanded)
%              Number of equality atoms :   15 (  26 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(k3_subset_1(A,B),C)
           => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_subset_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_285,plain,(
    ! [A_74,B_75,C_76] :
      ( k4_subset_1(A_74,B_75,C_76) = k2_xboole_0(B_75,C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(A_74))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_318,plain,(
    ! [B_78] :
      ( k4_subset_1('#skF_1',B_78,'#skF_3') = k2_xboole_0(B_78,'#skF_3')
      | ~ m1_subset_1(B_78,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_30,c_285])).

tff(c_330,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_318])).

tff(c_390,plain,(
    ! [A_81,B_82,C_83] :
      ( m1_subset_1(k4_subset_1(A_81,B_82,C_83),k1_zfmisc_1(A_81))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(A_81))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_405,plain,
    ( m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_390])).

tff(c_420,plain,(
    m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_405])).

tff(c_8,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_52,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k2_xboole_0(A_35,B_36)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_59,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_52])).

tff(c_107,plain,(
    ! [A_45,B_46,C_47] :
      ( r1_tarski(A_45,k2_xboole_0(B_46,C_47))
      | ~ r1_tarski(k4_xboole_0(A_45,B_46),C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_110,plain,(
    ! [A_1,C_47] :
      ( r1_tarski(A_1,k2_xboole_0(A_1,C_47))
      | ~ r1_tarski(k1_xboole_0,C_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_107])).

tff(c_115,plain,(
    ! [A_1,C_47] : r1_tarski(A_1,k2_xboole_0(A_1,C_47)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_110])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k3_subset_1(A_17,B_18),k1_zfmisc_1(A_17))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_589,plain,(
    ! [A_87,B_88,B_89] :
      ( k4_subset_1(A_87,B_88,k3_subset_1(A_87,B_89)) = k2_xboole_0(B_88,k3_subset_1(A_87,B_89))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_87)) ) ),
    inference(resolution,[status(thm)],[c_18,c_285])).

tff(c_657,plain,(
    ! [B_90] :
      ( k4_subset_1('#skF_1','#skF_3',k3_subset_1('#skF_1',B_90)) = k2_xboole_0('#skF_3',k3_subset_1('#skF_1',B_90))
      | ~ m1_subset_1(B_90,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_30,c_589])).

tff(c_698,plain,(
    k4_subset_1('#skF_1','#skF_3',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_657])).

tff(c_20,plain,(
    ! [A_19,B_20,C_21] :
      ( m1_subset_1(k4_subset_1(A_19,B_20,C_21),k1_zfmisc_1(A_19))
      | ~ m1_subset_1(C_21,k1_zfmisc_1(A_19))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_703,plain,
    ( m1_subset_1(k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_698,c_20])).

tff(c_707,plain,
    ( m1_subset_1(k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_703])).

tff(c_718,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_707])).

tff(c_721,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_718])).

tff(c_725,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_721])).

tff(c_727,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_707])).

tff(c_182,plain,(
    ! [A_61,B_62] :
      ( k3_subset_1(A_61,k3_subset_1(A_61,B_62)) = B_62
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_190,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_182])).

tff(c_427,plain,(
    ! [A_84,C_85,B_86] :
      ( r1_tarski(k3_subset_1(A_84,C_85),B_86)
      | ~ r1_tarski(k3_subset_1(A_84,B_86),C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(A_84))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_442,plain,(
    ! [C_85] :
      ( r1_tarski(k3_subset_1('#skF_1',C_85),k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_427])).

tff(c_2200,plain,(
    ! [C_108] :
      ( r1_tarski(k3_subset_1('#skF_1',C_108),k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_727,c_442])).

tff(c_28,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1',k4_subset_1('#skF_1','#skF_2','#skF_3')),k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_337,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1',k2_xboole_0('#skF_2','#skF_3')),k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_28])).

tff(c_2205,plain,
    ( ~ r1_tarski('#skF_2',k2_xboole_0('#skF_2','#skF_3'))
    | ~ m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2200,c_337])).

tff(c_2271,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_115,c_2205])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:05:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.74/1.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.89  
% 4.74/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.89  %$ r1_tarski > m1_subset_1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.74/1.89  
% 4.74/1.89  %Foreground sorts:
% 4.74/1.89  
% 4.74/1.89  
% 4.74/1.89  %Background operators:
% 4.74/1.89  
% 4.74/1.89  
% 4.74/1.89  %Foreground operators:
% 4.74/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.74/1.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.74/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.74/1.89  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.74/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.74/1.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.74/1.89  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.74/1.89  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.74/1.89  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.74/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.74/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.74/1.89  tff('#skF_1', type, '#skF_1': $i).
% 4.74/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.74/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.74/1.89  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.74/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.74/1.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.74/1.89  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.74/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.74/1.89  
% 4.74/1.90  tff(f_80, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_subset_1)).
% 4.74/1.90  tff(f_63, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.74/1.90  tff(f_53, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 4.74/1.90  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.74/1.90  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.74/1.90  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.74/1.90  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 4.74/1.90  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.74/1.90  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.74/1.90  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_subset_1)).
% 4.74/1.90  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.74/1.90  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.74/1.90  tff(c_285, plain, (![A_74, B_75, C_76]: (k4_subset_1(A_74, B_75, C_76)=k2_xboole_0(B_75, C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(A_74)) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.74/1.90  tff(c_318, plain, (![B_78]: (k4_subset_1('#skF_1', B_78, '#skF_3')=k2_xboole_0(B_78, '#skF_3') | ~m1_subset_1(B_78, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_30, c_285])).
% 4.74/1.90  tff(c_330, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_318])).
% 4.74/1.90  tff(c_390, plain, (![A_81, B_82, C_83]: (m1_subset_1(k4_subset_1(A_81, B_82, C_83), k1_zfmisc_1(A_81)) | ~m1_subset_1(C_83, k1_zfmisc_1(A_81)) | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.74/1.90  tff(c_405, plain, (m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_330, c_390])).
% 4.74/1.90  tff(c_420, plain, (m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_405])).
% 4.74/1.90  tff(c_8, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.74/1.90  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.74/1.90  tff(c_52, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k2_xboole_0(A_35, B_36))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.74/1.90  tff(c_59, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_52])).
% 4.74/1.90  tff(c_107, plain, (![A_45, B_46, C_47]: (r1_tarski(A_45, k2_xboole_0(B_46, C_47)) | ~r1_tarski(k4_xboole_0(A_45, B_46), C_47))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.74/1.90  tff(c_110, plain, (![A_1, C_47]: (r1_tarski(A_1, k2_xboole_0(A_1, C_47)) | ~r1_tarski(k1_xboole_0, C_47))), inference(superposition, [status(thm), theory('equality')], [c_59, c_107])).
% 4.74/1.90  tff(c_115, plain, (![A_1, C_47]: (r1_tarski(A_1, k2_xboole_0(A_1, C_47)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_110])).
% 4.74/1.90  tff(c_18, plain, (![A_17, B_18]: (m1_subset_1(k3_subset_1(A_17, B_18), k1_zfmisc_1(A_17)) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.74/1.90  tff(c_589, plain, (![A_87, B_88, B_89]: (k4_subset_1(A_87, B_88, k3_subset_1(A_87, B_89))=k2_xboole_0(B_88, k3_subset_1(A_87, B_89)) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)) | ~m1_subset_1(B_89, k1_zfmisc_1(A_87)))), inference(resolution, [status(thm)], [c_18, c_285])).
% 4.74/1.90  tff(c_657, plain, (![B_90]: (k4_subset_1('#skF_1', '#skF_3', k3_subset_1('#skF_1', B_90))=k2_xboole_0('#skF_3', k3_subset_1('#skF_1', B_90)) | ~m1_subset_1(B_90, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_30, c_589])).
% 4.74/1.90  tff(c_698, plain, (k4_subset_1('#skF_1', '#skF_3', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_657])).
% 4.74/1.90  tff(c_20, plain, (![A_19, B_20, C_21]: (m1_subset_1(k4_subset_1(A_19, B_20, C_21), k1_zfmisc_1(A_19)) | ~m1_subset_1(C_21, k1_zfmisc_1(A_19)) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.74/1.90  tff(c_703, plain, (m1_subset_1(k2_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2')), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_698, c_20])).
% 4.74/1.90  tff(c_707, plain, (m1_subset_1(k2_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2')), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_703])).
% 4.74/1.91  tff(c_718, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_707])).
% 4.74/1.91  tff(c_721, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_718])).
% 4.74/1.91  tff(c_725, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_721])).
% 4.74/1.91  tff(c_727, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_707])).
% 4.74/1.91  tff(c_182, plain, (![A_61, B_62]: (k3_subset_1(A_61, k3_subset_1(A_61, B_62))=B_62 | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.74/1.91  tff(c_190, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_32, c_182])).
% 4.74/1.91  tff(c_427, plain, (![A_84, C_85, B_86]: (r1_tarski(k3_subset_1(A_84, C_85), B_86) | ~r1_tarski(k3_subset_1(A_84, B_86), C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(A_84)) | ~m1_subset_1(B_86, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.74/1.91  tff(c_442, plain, (![C_85]: (r1_tarski(k3_subset_1('#skF_1', C_85), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', C_85) | ~m1_subset_1(C_85, k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_190, c_427])).
% 4.74/1.91  tff(c_2200, plain, (![C_108]: (r1_tarski(k3_subset_1('#skF_1', C_108), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', C_108) | ~m1_subset_1(C_108, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_727, c_442])).
% 4.74/1.91  tff(c_28, plain, (~r1_tarski(k3_subset_1('#skF_1', k4_subset_1('#skF_1', '#skF_2', '#skF_3')), k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.74/1.91  tff(c_337, plain, (~r1_tarski(k3_subset_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3')), k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_330, c_28])).
% 4.74/1.91  tff(c_2205, plain, (~r1_tarski('#skF_2', k2_xboole_0('#skF_2', '#skF_3')) | ~m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_2200, c_337])).
% 4.74/1.91  tff(c_2271, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_420, c_115, c_2205])).
% 4.74/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.91  
% 4.74/1.91  Inference rules
% 4.74/1.91  ----------------------
% 4.74/1.91  #Ref     : 0
% 4.74/1.91  #Sup     : 596
% 4.74/1.91  #Fact    : 0
% 4.74/1.91  #Define  : 0
% 4.74/1.91  #Split   : 3
% 4.74/1.91  #Chain   : 0
% 4.74/1.91  #Close   : 0
% 4.74/1.91  
% 4.74/1.91  Ordering : KBO
% 4.74/1.91  
% 4.74/1.91  Simplification rules
% 4.74/1.91  ----------------------
% 4.74/1.91  #Subsume      : 2
% 4.74/1.91  #Demod        : 263
% 4.74/1.91  #Tautology    : 196
% 4.74/1.91  #SimpNegUnit  : 0
% 4.74/1.91  #BackRed      : 1
% 4.74/1.91  
% 4.74/1.91  #Partial instantiations: 0
% 4.74/1.91  #Strategies tried      : 1
% 4.74/1.91  
% 4.74/1.91  Timing (in seconds)
% 4.74/1.91  ----------------------
% 4.74/1.91  Preprocessing        : 0.34
% 4.74/1.91  Parsing              : 0.19
% 4.74/1.91  CNF conversion       : 0.02
% 4.74/1.91  Main loop            : 0.75
% 4.74/1.91  Inferencing          : 0.23
% 4.74/1.91  Reduction            : 0.26
% 4.74/1.91  Demodulation         : 0.20
% 4.74/1.91  BG Simplification    : 0.03
% 4.74/1.91  Subsumption          : 0.17
% 4.74/1.91  Abstraction          : 0.04
% 4.74/1.91  MUC search           : 0.00
% 4.74/1.91  Cooper               : 0.00
% 4.74/1.91  Total                : 1.12
% 4.74/1.91  Index Insertion      : 0.00
% 4.74/1.91  Index Deletion       : 0.00
% 4.74/1.91  Index Matching       : 0.00
% 4.74/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
