%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:32 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 4.16s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 110 expanded)
%              Number of leaves         :   29 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   81 ( 186 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(k3_subset_1(A,B),C)
           => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_246,plain,(
    ! [A_68,B_69,C_70] :
      ( k4_subset_1(A_68,B_69,C_70) = k2_xboole_0(B_69,C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(A_68))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_297,plain,(
    ! [B_72] :
      ( k4_subset_1('#skF_1',B_72,'#skF_3') = k2_xboole_0(B_72,'#skF_3')
      | ~ m1_subset_1(B_72,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_30,c_246])).

tff(c_314,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_297])).

tff(c_20,plain,(
    ! [A_19,B_20,C_21] :
      ( m1_subset_1(k4_subset_1(A_19,B_20,C_21),k1_zfmisc_1(A_19))
      | ~ m1_subset_1(C_21,k1_zfmisc_1(A_19))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_344,plain,
    ( m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_20])).

tff(c_348,plain,(
    m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_344])).

tff(c_8,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    ! [A_36,B_37] : k2_xboole_0(A_36,k3_xboole_0(A_36,B_37)) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_56,plain,(
    ! [A_36] : k4_xboole_0(A_36,A_36) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_12])).

tff(c_150,plain,(
    ! [A_51,B_52,C_53] :
      ( r1_tarski(A_51,k2_xboole_0(B_52,C_53))
      | ~ r1_tarski(k4_xboole_0(A_51,B_52),C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_153,plain,(
    ! [A_36,C_53] :
      ( r1_tarski(A_36,k2_xboole_0(A_36,C_53))
      | ~ r1_tarski(k1_xboole_0,C_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_150])).

tff(c_158,plain,(
    ! [A_36,C_53] : r1_tarski(A_36,k2_xboole_0(A_36,C_53)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_153])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k3_subset_1(A_17,B_18),k1_zfmisc_1(A_17))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_259,plain,(
    ! [B_71] :
      ( k4_subset_1('#skF_1',B_71,'#skF_2') = k2_xboole_0(B_71,'#skF_2')
      | ~ m1_subset_1(B_71,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_32,c_246])).

tff(c_637,plain,(
    ! [B_85] :
      ( k4_subset_1('#skF_1',k3_subset_1('#skF_1',B_85),'#skF_2') = k2_xboole_0(k3_subset_1('#skF_1',B_85),'#skF_2')
      | ~ m1_subset_1(B_85,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_18,c_259])).

tff(c_678,plain,(
    k4_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2'),'#skF_2') = k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_637])).

tff(c_683,plain,
    ( m1_subset_1(k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_678,c_20])).

tff(c_687,plain,
    ( m1_subset_1(k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_683])).

tff(c_736,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_687])).

tff(c_739,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_736])).

tff(c_743,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_739])).

tff(c_745,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_687])).

tff(c_123,plain,(
    ! [A_47,B_48] :
      ( k3_subset_1(A_47,k3_subset_1(A_47,B_48)) = B_48
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_128,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_123])).

tff(c_364,plain,(
    ! [A_73,C_74,B_75] :
      ( r1_tarski(k3_subset_1(A_73,C_74),B_75)
      | ~ r1_tarski(k3_subset_1(A_73,B_75),C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(A_73))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_383,plain,(
    ! [C_74] :
      ( r1_tarski(k3_subset_1('#skF_1',C_74),k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_364])).

tff(c_1833,plain,(
    ! [C_108] :
      ( r1_tarski(k3_subset_1('#skF_1',C_108),k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_745,c_383])).

tff(c_28,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1',k4_subset_1('#skF_1','#skF_2','#skF_3')),k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_340,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1',k2_xboole_0('#skF_2','#skF_3')),k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_28])).

tff(c_1838,plain,
    ( ~ r1_tarski('#skF_2',k2_xboole_0('#skF_2','#skF_3'))
    | ~ m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1833,c_340])).

tff(c_1895,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_158,c_1838])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:44:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.92/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/1.68  
% 3.92/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/1.68  %$ r1_tarski > m1_subset_1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.92/1.68  
% 3.92/1.68  %Foreground sorts:
% 3.92/1.68  
% 3.92/1.68  
% 3.92/1.68  %Background operators:
% 3.92/1.68  
% 3.92/1.68  
% 3.92/1.68  %Foreground operators:
% 3.92/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.92/1.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.92/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.92/1.68  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.92/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.92/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.92/1.68  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.92/1.68  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.92/1.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.92/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.92/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.92/1.68  tff('#skF_1', type, '#skF_1': $i).
% 3.92/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.92/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.92/1.68  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.92/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.92/1.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.92/1.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.92/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.92/1.68  
% 4.16/1.69  tff(f_80, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_subset_1)).
% 4.16/1.69  tff(f_63, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.16/1.69  tff(f_53, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 4.16/1.69  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.16/1.69  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 4.16/1.69  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.16/1.69  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 4.16/1.69  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.16/1.69  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.16/1.69  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_subset_1)).
% 4.16/1.69  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.16/1.69  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.16/1.69  tff(c_246, plain, (![A_68, B_69, C_70]: (k4_subset_1(A_68, B_69, C_70)=k2_xboole_0(B_69, C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(A_68)) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.16/1.69  tff(c_297, plain, (![B_72]: (k4_subset_1('#skF_1', B_72, '#skF_3')=k2_xboole_0(B_72, '#skF_3') | ~m1_subset_1(B_72, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_30, c_246])).
% 4.16/1.69  tff(c_314, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_297])).
% 4.16/1.69  tff(c_20, plain, (![A_19, B_20, C_21]: (m1_subset_1(k4_subset_1(A_19, B_20, C_21), k1_zfmisc_1(A_19)) | ~m1_subset_1(C_21, k1_zfmisc_1(A_19)) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.16/1.69  tff(c_344, plain, (m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_314, c_20])).
% 4.16/1.69  tff(c_348, plain, (m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_344])).
% 4.16/1.69  tff(c_8, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.16/1.69  tff(c_50, plain, (![A_36, B_37]: (k2_xboole_0(A_36, k3_xboole_0(A_36, B_37))=A_36)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.16/1.69  tff(c_12, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.16/1.69  tff(c_56, plain, (![A_36]: (k4_xboole_0(A_36, A_36)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_12])).
% 4.16/1.69  tff(c_150, plain, (![A_51, B_52, C_53]: (r1_tarski(A_51, k2_xboole_0(B_52, C_53)) | ~r1_tarski(k4_xboole_0(A_51, B_52), C_53))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.16/1.69  tff(c_153, plain, (![A_36, C_53]: (r1_tarski(A_36, k2_xboole_0(A_36, C_53)) | ~r1_tarski(k1_xboole_0, C_53))), inference(superposition, [status(thm), theory('equality')], [c_56, c_150])).
% 4.16/1.69  tff(c_158, plain, (![A_36, C_53]: (r1_tarski(A_36, k2_xboole_0(A_36, C_53)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_153])).
% 4.16/1.69  tff(c_18, plain, (![A_17, B_18]: (m1_subset_1(k3_subset_1(A_17, B_18), k1_zfmisc_1(A_17)) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.16/1.69  tff(c_259, plain, (![B_71]: (k4_subset_1('#skF_1', B_71, '#skF_2')=k2_xboole_0(B_71, '#skF_2') | ~m1_subset_1(B_71, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_32, c_246])).
% 4.16/1.69  tff(c_637, plain, (![B_85]: (k4_subset_1('#skF_1', k3_subset_1('#skF_1', B_85), '#skF_2')=k2_xboole_0(k3_subset_1('#skF_1', B_85), '#skF_2') | ~m1_subset_1(B_85, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_259])).
% 4.16/1.69  tff(c_678, plain, (k4_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'), '#skF_2')=k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_32, c_637])).
% 4.16/1.69  tff(c_683, plain, (m1_subset_1(k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_678, c_20])).
% 4.16/1.69  tff(c_687, plain, (m1_subset_1(k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_683])).
% 4.16/1.69  tff(c_736, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_687])).
% 4.16/1.69  tff(c_739, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_736])).
% 4.16/1.69  tff(c_743, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_739])).
% 4.16/1.69  tff(c_745, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_687])).
% 4.16/1.69  tff(c_123, plain, (![A_47, B_48]: (k3_subset_1(A_47, k3_subset_1(A_47, B_48))=B_48 | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.16/1.69  tff(c_128, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_32, c_123])).
% 4.16/1.69  tff(c_364, plain, (![A_73, C_74, B_75]: (r1_tarski(k3_subset_1(A_73, C_74), B_75) | ~r1_tarski(k3_subset_1(A_73, B_75), C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(A_73)) | ~m1_subset_1(B_75, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.16/1.69  tff(c_383, plain, (![C_74]: (r1_tarski(k3_subset_1('#skF_1', C_74), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', C_74) | ~m1_subset_1(C_74, k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_128, c_364])).
% 4.16/1.69  tff(c_1833, plain, (![C_108]: (r1_tarski(k3_subset_1('#skF_1', C_108), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', C_108) | ~m1_subset_1(C_108, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_745, c_383])).
% 4.16/1.69  tff(c_28, plain, (~r1_tarski(k3_subset_1('#skF_1', k4_subset_1('#skF_1', '#skF_2', '#skF_3')), k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.16/1.69  tff(c_340, plain, (~r1_tarski(k3_subset_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3')), k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_28])).
% 4.16/1.69  tff(c_1838, plain, (~r1_tarski('#skF_2', k2_xboole_0('#skF_2', '#skF_3')) | ~m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_1833, c_340])).
% 4.16/1.69  tff(c_1895, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_348, c_158, c_1838])).
% 4.16/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.69  
% 4.16/1.69  Inference rules
% 4.16/1.69  ----------------------
% 4.16/1.69  #Ref     : 0
% 4.16/1.69  #Sup     : 489
% 4.16/1.69  #Fact    : 0
% 4.16/1.69  #Define  : 0
% 4.16/1.69  #Split   : 2
% 4.16/1.69  #Chain   : 0
% 4.16/1.69  #Close   : 0
% 4.16/1.69  
% 4.16/1.69  Ordering : KBO
% 4.16/1.69  
% 4.16/1.69  Simplification rules
% 4.16/1.69  ----------------------
% 4.16/1.69  #Subsume      : 3
% 4.16/1.69  #Demod        : 259
% 4.16/1.69  #Tautology    : 191
% 4.16/1.69  #SimpNegUnit  : 0
% 4.16/1.69  #BackRed      : 1
% 4.16/1.69  
% 4.16/1.69  #Partial instantiations: 0
% 4.16/1.69  #Strategies tried      : 1
% 4.16/1.69  
% 4.16/1.69  Timing (in seconds)
% 4.16/1.69  ----------------------
% 4.16/1.70  Preprocessing        : 0.31
% 4.16/1.70  Parsing              : 0.17
% 4.16/1.70  CNF conversion       : 0.02
% 4.16/1.70  Main loop            : 0.62
% 4.16/1.70  Inferencing          : 0.20
% 4.16/1.70  Reduction            : 0.21
% 4.16/1.70  Demodulation         : 0.16
% 4.16/1.70  BG Simplification    : 0.03
% 4.16/1.70  Subsumption          : 0.13
% 4.16/1.70  Abstraction          : 0.04
% 4.16/1.70  MUC search           : 0.00
% 4.16/1.70  Cooper               : 0.00
% 4.16/1.70  Total                : 0.96
% 4.16/1.70  Index Insertion      : 0.00
% 4.16/1.70  Index Deletion       : 0.00
% 4.16/1.70  Index Matching       : 0.00
% 4.16/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
