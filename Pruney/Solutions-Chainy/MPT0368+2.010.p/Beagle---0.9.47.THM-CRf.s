%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:49 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   65 (  80 expanded)
%              Number of leaves         :   36 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   78 ( 107 expanded)
%              Number of equality atoms :   19 (  26 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( ! [C] :
              ( m1_subset_1(C,A)
             => r2_hidden(C,B) )
         => A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_61,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_67,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_52,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_36,plain,(
    ! [A_45] : k2_subset_1(A_45) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_40,plain,(
    ! [A_48] : m1_subset_1(k2_subset_1(A_48),k1_zfmisc_1(A_48)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_57,plain,(
    ! [A_48] : m1_subset_1(A_48,k1_zfmisc_1(A_48)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_40])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_50,plain,(
    ! [A_53,B_54,C_58] :
      ( m1_subset_1('#skF_1'(A_53,B_54,C_58),A_53)
      | r1_tarski(B_54,C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(A_53))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_54,plain,(
    ! [C_61] :
      ( r2_hidden(C_61,'#skF_3')
      | ~ m1_subset_1(C_61,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1923,plain,(
    ! [A_152,B_153,C_154] :
      ( ~ r2_hidden('#skF_1'(A_152,B_153,C_154),C_154)
      | r1_tarski(B_153,C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(A_152))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(A_152)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1938,plain,(
    ! [B_155,A_156] :
      ( r1_tarski(B_155,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_156))
      | ~ m1_subset_1(B_155,k1_zfmisc_1(A_156))
      | ~ m1_subset_1('#skF_1'(A_156,B_155,'#skF_3'),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_54,c_1923])).

tff(c_1942,plain,(
    ! [B_54] :
      ( r1_tarski(B_54,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_54,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_50,c_1938])).

tff(c_1946,plain,(
    ! [B_157] :
      ( r1_tarski(B_157,'#skF_3')
      | ~ m1_subset_1(B_157,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1942])).

tff(c_1959,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_57,c_1946])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1963,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1959,c_6])).

tff(c_1966,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1963])).

tff(c_14,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_115,plain,(
    ! [A_74,B_75] : k5_xboole_0(A_74,k3_xboole_0(A_74,B_75)) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_124,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_115])).

tff(c_127,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_124])).

tff(c_424,plain,(
    ! [A_93,B_94] :
      ( k4_xboole_0(A_93,B_94) = k3_subset_1(A_93,B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_427,plain,(
    ! [A_48] : k4_xboole_0(A_48,A_48) = k3_subset_1(A_48,A_48) ),
    inference(resolution,[status(thm)],[c_57,c_424])).

tff(c_432,plain,(
    ! [A_48] : k3_subset_1(A_48,A_48) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_427])).

tff(c_1969,plain,(
    ! [B_158,C_159,A_160] :
      ( r1_tarski(B_158,C_159)
      | ~ r1_tarski(k3_subset_1(A_160,C_159),k3_subset_1(A_160,B_158))
      | ~ m1_subset_1(C_159,k1_zfmisc_1(A_160))
      | ~ m1_subset_1(B_158,k1_zfmisc_1(A_160)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1972,plain,(
    ! [B_158,A_48] :
      ( r1_tarski(B_158,A_48)
      | ~ r1_tarski(k1_xboole_0,k3_subset_1(A_48,B_158))
      | ~ m1_subset_1(A_48,k1_zfmisc_1(A_48))
      | ~ m1_subset_1(B_158,k1_zfmisc_1(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_1969])).

tff(c_1986,plain,(
    ! [B_161,A_162] :
      ( r1_tarski(B_161,A_162)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(A_162)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_14,c_1972])).

tff(c_1996,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_1986])).

tff(c_2003,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1966,c_1996])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:53:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.57  
% 3.42/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.57  %$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 3.42/1.57  
% 3.42/1.57  %Foreground sorts:
% 3.42/1.57  
% 3.42/1.57  
% 3.42/1.57  %Background operators:
% 3.42/1.57  
% 3.42/1.57  
% 3.42/1.57  %Foreground operators:
% 3.42/1.57  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.42/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.42/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.42/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.42/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.42/1.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.42/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.42/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.42/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.42/1.57  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.42/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.42/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.42/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.42/1.57  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.42/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.42/1.57  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.42/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.57  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.42/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.42/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.42/1.57  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.42/1.57  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.42/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.42/1.57  
% 3.42/1.58  tff(f_100, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_subset_1)).
% 3.42/1.58  tff(f_61, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.42/1.58  tff(f_67, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.42/1.58  tff(f_90, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 3.42/1.58  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.42/1.58  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.42/1.58  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.42/1.58  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.42/1.58  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.42/1.58  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.42/1.58  tff(f_76, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 3.42/1.58  tff(c_52, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.42/1.58  tff(c_36, plain, (![A_45]: (k2_subset_1(A_45)=A_45)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.42/1.58  tff(c_40, plain, (![A_48]: (m1_subset_1(k2_subset_1(A_48), k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.42/1.58  tff(c_57, plain, (![A_48]: (m1_subset_1(A_48, k1_zfmisc_1(A_48)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_40])).
% 3.42/1.58  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.42/1.58  tff(c_50, plain, (![A_53, B_54, C_58]: (m1_subset_1('#skF_1'(A_53, B_54, C_58), A_53) | r1_tarski(B_54, C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(A_53)) | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.42/1.58  tff(c_54, plain, (![C_61]: (r2_hidden(C_61, '#skF_3') | ~m1_subset_1(C_61, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.42/1.58  tff(c_1923, plain, (![A_152, B_153, C_154]: (~r2_hidden('#skF_1'(A_152, B_153, C_154), C_154) | r1_tarski(B_153, C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(A_152)) | ~m1_subset_1(B_153, k1_zfmisc_1(A_152)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.42/1.58  tff(c_1938, plain, (![B_155, A_156]: (r1_tarski(B_155, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_156)) | ~m1_subset_1(B_155, k1_zfmisc_1(A_156)) | ~m1_subset_1('#skF_1'(A_156, B_155, '#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_1923])).
% 3.42/1.58  tff(c_1942, plain, (![B_54]: (r1_tarski(B_54, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_54, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_50, c_1938])).
% 3.42/1.58  tff(c_1946, plain, (![B_157]: (r1_tarski(B_157, '#skF_3') | ~m1_subset_1(B_157, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1942])).
% 3.42/1.58  tff(c_1959, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_57, c_1946])).
% 3.42/1.58  tff(c_6, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.42/1.58  tff(c_1963, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1959, c_6])).
% 3.42/1.58  tff(c_1966, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_1963])).
% 3.42/1.58  tff(c_14, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.42/1.58  tff(c_18, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.42/1.58  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.42/1.58  tff(c_115, plain, (![A_74, B_75]: (k5_xboole_0(A_74, k3_xboole_0(A_74, B_75))=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.42/1.58  tff(c_124, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_115])).
% 3.42/1.58  tff(c_127, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_124])).
% 3.42/1.58  tff(c_424, plain, (![A_93, B_94]: (k4_xboole_0(A_93, B_94)=k3_subset_1(A_93, B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(A_93)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.42/1.58  tff(c_427, plain, (![A_48]: (k4_xboole_0(A_48, A_48)=k3_subset_1(A_48, A_48))), inference(resolution, [status(thm)], [c_57, c_424])).
% 3.42/1.58  tff(c_432, plain, (![A_48]: (k3_subset_1(A_48, A_48)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_127, c_427])).
% 3.42/1.58  tff(c_1969, plain, (![B_158, C_159, A_160]: (r1_tarski(B_158, C_159) | ~r1_tarski(k3_subset_1(A_160, C_159), k3_subset_1(A_160, B_158)) | ~m1_subset_1(C_159, k1_zfmisc_1(A_160)) | ~m1_subset_1(B_158, k1_zfmisc_1(A_160)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.42/1.58  tff(c_1972, plain, (![B_158, A_48]: (r1_tarski(B_158, A_48) | ~r1_tarski(k1_xboole_0, k3_subset_1(A_48, B_158)) | ~m1_subset_1(A_48, k1_zfmisc_1(A_48)) | ~m1_subset_1(B_158, k1_zfmisc_1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_432, c_1969])).
% 3.42/1.58  tff(c_1986, plain, (![B_161, A_162]: (r1_tarski(B_161, A_162) | ~m1_subset_1(B_161, k1_zfmisc_1(A_162)))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_14, c_1972])).
% 3.42/1.58  tff(c_1996, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_1986])).
% 3.42/1.58  tff(c_2003, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1966, c_1996])).
% 3.42/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.58  
% 3.42/1.58  Inference rules
% 3.42/1.58  ----------------------
% 3.42/1.58  #Ref     : 0
% 3.42/1.58  #Sup     : 483
% 3.42/1.58  #Fact    : 0
% 3.42/1.58  #Define  : 0
% 3.42/1.58  #Split   : 0
% 3.42/1.58  #Chain   : 0
% 3.42/1.58  #Close   : 0
% 3.42/1.58  
% 3.42/1.58  Ordering : KBO
% 3.42/1.58  
% 3.42/1.58  Simplification rules
% 3.42/1.58  ----------------------
% 3.42/1.58  #Subsume      : 3
% 3.42/1.58  #Demod        : 280
% 3.42/1.58  #Tautology    : 314
% 3.42/1.58  #SimpNegUnit  : 2
% 3.42/1.58  #BackRed      : 1
% 3.42/1.58  
% 3.42/1.58  #Partial instantiations: 0
% 3.42/1.58  #Strategies tried      : 1
% 3.42/1.58  
% 3.42/1.58  Timing (in seconds)
% 3.42/1.58  ----------------------
% 3.42/1.58  Preprocessing        : 0.33
% 3.42/1.58  Parsing              : 0.18
% 3.42/1.58  CNF conversion       : 0.02
% 3.42/1.58  Main loop            : 0.50
% 3.42/1.58  Inferencing          : 0.18
% 3.42/1.59  Reduction            : 0.19
% 3.42/1.59  Demodulation         : 0.15
% 3.42/1.59  BG Simplification    : 0.03
% 3.42/1.59  Subsumption          : 0.07
% 3.42/1.59  Abstraction          : 0.03
% 3.42/1.59  MUC search           : 0.00
% 3.42/1.59  Cooper               : 0.00
% 3.42/1.59  Total                : 0.86
% 3.42/1.59  Index Insertion      : 0.00
% 3.42/1.59  Index Deletion       : 0.00
% 3.42/1.59  Index Matching       : 0.00
% 3.42/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
