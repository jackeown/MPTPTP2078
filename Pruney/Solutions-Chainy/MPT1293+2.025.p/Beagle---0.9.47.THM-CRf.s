%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:38 EST 2020

% Result     : Theorem 5.10s
% Output     : CNFRefutation 5.10s
% Verified   : 
% Statistics : Number of formulae       :   63 (  85 expanded)
%              Number of leaves         :   28 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 118 expanded)
%              Number of equality atoms :   19 (  27 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_47,axiom,(
    ! [A,B] : k3_tarski(k2_xboole_0(A,B)) = k2_xboole_0(k3_tarski(A),k3_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => r1_tarski(k7_subset_1(u1_struct_0(A),k5_setfam_1(u1_struct_0(A),B),k5_setfam_1(u1_struct_0(A),C)),k5_setfam_1(u1_struct_0(A),k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tops_2)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_14,plain,(
    ! [A_16,B_17] : k2_xboole_0(k3_tarski(A_16),k3_tarski(B_17)) = k3_tarski(k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_159,plain,(
    ! [A_59,B_60,C_61] :
      ( r1_tarski(A_59,k2_xboole_0(B_60,C_61))
      | ~ r1_tarski(k4_xboole_0(A_59,B_60),C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_172,plain,(
    ! [A_62,B_63] : r1_tarski(A_62,k2_xboole_0(B_63,A_62)) ),
    inference(resolution,[status(thm)],[c_4,c_159])).

tff(c_183,plain,(
    ! [B_17,A_16] : r1_tarski(k3_tarski(B_17),k3_tarski(k2_xboole_0(A_16,B_17))) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_172])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_44,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | ~ m1_subset_1(A_35,k1_zfmisc_1(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_56,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_30,c_44])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(k4_xboole_0(A_1,C_3),B_2)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,k1_zfmisc_1(B_25))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_244,plain,(
    ! [A_70,B_71] :
      ( k5_setfam_1(A_70,B_71) = k3_tarski(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k1_zfmisc_1(A_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_285,plain,(
    ! [A_75,A_76] :
      ( k5_setfam_1(A_75,A_76) = k3_tarski(A_76)
      | ~ r1_tarski(A_76,k1_zfmisc_1(A_75)) ) ),
    inference(resolution,[status(thm)],[c_24,c_244])).

tff(c_2921,plain,(
    ! [A_327,A_328,C_329] :
      ( k5_setfam_1(A_327,k4_xboole_0(A_328,C_329)) = k3_tarski(k4_xboole_0(A_328,C_329))
      | ~ r1_tarski(A_328,k1_zfmisc_1(A_327)) ) ),
    inference(resolution,[status(thm)],[c_2,c_285])).

tff(c_2941,plain,(
    ! [C_329] : k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2',C_329)) = k3_tarski(k4_xboole_0('#skF_2',C_329)) ),
    inference(resolution,[status(thm)],[c_56,c_2921])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] :
      ( r1_tarski(k4_xboole_0(A_8,B_9),C_10)
      | ~ r1_tarski(A_8,k2_xboole_0(B_9,C_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_18] : k3_tarski(k1_zfmisc_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_57,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(k3_tarski(A_37),k3_tarski(B_38))
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_63,plain,(
    ! [A_37,A_18] :
      ( r1_tarski(k3_tarski(A_37),A_18)
      | ~ r1_tarski(A_37,k1_zfmisc_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_57])).

tff(c_380,plain,(
    ! [A_86,B_87,C_88] :
      ( k7_subset_1(A_86,B_87,C_88) = k4_xboole_0(B_87,C_88)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_479,plain,(
    ! [B_99,A_100,C_101] :
      ( k7_subset_1(B_99,A_100,C_101) = k4_xboole_0(A_100,C_101)
      | ~ r1_tarski(A_100,B_99) ) ),
    inference(resolution,[status(thm)],[c_24,c_380])).

tff(c_2388,plain,(
    ! [A_277,A_278,C_279] :
      ( k7_subset_1(A_277,k3_tarski(A_278),C_279) = k4_xboole_0(k3_tarski(A_278),C_279)
      | ~ r1_tarski(A_278,k1_zfmisc_1(A_277)) ) ),
    inference(resolution,[status(thm)],[c_63,c_479])).

tff(c_2408,plain,(
    ! [C_279] : k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),C_279) = k4_xboole_0(k3_tarski('#skF_2'),C_279) ),
    inference(resolution,[status(thm)],[c_56,c_2388])).

tff(c_389,plain,(
    ! [C_88] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_88) = k4_xboole_0('#skF_2',C_88) ),
    inference(resolution,[status(thm)],[c_30,c_380])).

tff(c_257,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_244])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_256,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_244])).

tff(c_26,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_258,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_26])).

tff(c_284,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_258])).

tff(c_399,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_284])).

tff(c_2411,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2408,c_399])).

tff(c_2436,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_8,c_2411])).

tff(c_2946,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k3_tarski(k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2941,c_2436])).

tff(c_2953,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_6,c_14,c_2946])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.30  % Computer   : n009.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % DateTime   : Tue Dec  1 17:42:26 EST 2020
% 0.11/0.30  % CPUTime    : 
% 0.11/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.10/1.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.10/1.92  
% 5.10/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.10/1.93  %$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 5.10/1.93  
% 5.10/1.93  %Foreground sorts:
% 5.10/1.93  
% 5.10/1.93  
% 5.10/1.93  %Background operators:
% 5.10/1.93  
% 5.10/1.93  
% 5.10/1.93  %Foreground operators:
% 5.10/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.10/1.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.10/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.10/1.93  tff('#skF_2', type, '#skF_2': $i).
% 5.10/1.93  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.10/1.93  tff('#skF_3', type, '#skF_3': $i).
% 5.10/1.93  tff('#skF_1', type, '#skF_1': $i).
% 5.10/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.10/1.93  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.10/1.93  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 5.10/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.10/1.93  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.10/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.10/1.93  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.10/1.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.10/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.10/1.93  
% 5.10/1.94  tff(f_47, axiom, (![A, B]: (k3_tarski(k2_xboole_0(A, B)) = k2_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 5.10/1.94  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.10/1.94  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 5.10/1.94  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.10/1.94  tff(f_72, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k7_subset_1(u1_struct_0(A), k5_setfam_1(u1_struct_0(A), B), k5_setfam_1(u1_struct_0(A), C)), k5_setfam_1(u1_struct_0(A), k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tops_2)).
% 5.10/1.94  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.10/1.94  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 5.10/1.94  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 5.10/1.94  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 5.10/1.94  tff(f_49, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 5.10/1.94  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 5.10/1.94  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.10/1.94  tff(c_14, plain, (![A_16, B_17]: (k2_xboole_0(k3_tarski(A_16), k3_tarski(B_17))=k3_tarski(k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.10/1.94  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.10/1.94  tff(c_159, plain, (![A_59, B_60, C_61]: (r1_tarski(A_59, k2_xboole_0(B_60, C_61)) | ~r1_tarski(k4_xboole_0(A_59, B_60), C_61))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.10/1.94  tff(c_172, plain, (![A_62, B_63]: (r1_tarski(A_62, k2_xboole_0(B_63, A_62)))), inference(resolution, [status(thm)], [c_4, c_159])).
% 5.10/1.94  tff(c_183, plain, (![B_17, A_16]: (r1_tarski(k3_tarski(B_17), k3_tarski(k2_xboole_0(A_16, B_17))))), inference(superposition, [status(thm), theory('equality')], [c_14, c_172])).
% 5.10/1.94  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.10/1.94  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.10/1.94  tff(c_44, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | ~m1_subset_1(A_35, k1_zfmisc_1(B_36)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.10/1.94  tff(c_56, plain, (r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_30, c_44])).
% 5.10/1.94  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(k4_xboole_0(A_1, C_3), B_2) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.10/1.94  tff(c_24, plain, (![A_24, B_25]: (m1_subset_1(A_24, k1_zfmisc_1(B_25)) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.10/1.94  tff(c_244, plain, (![A_70, B_71]: (k5_setfam_1(A_70, B_71)=k3_tarski(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(k1_zfmisc_1(A_70))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.10/1.94  tff(c_285, plain, (![A_75, A_76]: (k5_setfam_1(A_75, A_76)=k3_tarski(A_76) | ~r1_tarski(A_76, k1_zfmisc_1(A_75)))), inference(resolution, [status(thm)], [c_24, c_244])).
% 5.10/1.94  tff(c_2921, plain, (![A_327, A_328, C_329]: (k5_setfam_1(A_327, k4_xboole_0(A_328, C_329))=k3_tarski(k4_xboole_0(A_328, C_329)) | ~r1_tarski(A_328, k1_zfmisc_1(A_327)))), inference(resolution, [status(thm)], [c_2, c_285])).
% 5.10/1.94  tff(c_2941, plain, (![C_329]: (k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', C_329))=k3_tarski(k4_xboole_0('#skF_2', C_329)))), inference(resolution, [status(thm)], [c_56, c_2921])).
% 5.10/1.94  tff(c_8, plain, (![A_8, B_9, C_10]: (r1_tarski(k4_xboole_0(A_8, B_9), C_10) | ~r1_tarski(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.10/1.94  tff(c_16, plain, (![A_18]: (k3_tarski(k1_zfmisc_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.10/1.94  tff(c_57, plain, (![A_37, B_38]: (r1_tarski(k3_tarski(A_37), k3_tarski(B_38)) | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.10/1.94  tff(c_63, plain, (![A_37, A_18]: (r1_tarski(k3_tarski(A_37), A_18) | ~r1_tarski(A_37, k1_zfmisc_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_57])).
% 5.10/1.94  tff(c_380, plain, (![A_86, B_87, C_88]: (k7_subset_1(A_86, B_87, C_88)=k4_xboole_0(B_87, C_88) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.10/1.94  tff(c_479, plain, (![B_99, A_100, C_101]: (k7_subset_1(B_99, A_100, C_101)=k4_xboole_0(A_100, C_101) | ~r1_tarski(A_100, B_99))), inference(resolution, [status(thm)], [c_24, c_380])).
% 5.10/1.94  tff(c_2388, plain, (![A_277, A_278, C_279]: (k7_subset_1(A_277, k3_tarski(A_278), C_279)=k4_xboole_0(k3_tarski(A_278), C_279) | ~r1_tarski(A_278, k1_zfmisc_1(A_277)))), inference(resolution, [status(thm)], [c_63, c_479])).
% 5.10/1.94  tff(c_2408, plain, (![C_279]: (k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), C_279)=k4_xboole_0(k3_tarski('#skF_2'), C_279))), inference(resolution, [status(thm)], [c_56, c_2388])).
% 5.10/1.94  tff(c_389, plain, (![C_88]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_88)=k4_xboole_0('#skF_2', C_88))), inference(resolution, [status(thm)], [c_30, c_380])).
% 5.10/1.94  tff(c_257, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_30, c_244])).
% 5.10/1.94  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.10/1.94  tff(c_256, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')=k3_tarski('#skF_3')), inference(resolution, [status(thm)], [c_28, c_244])).
% 5.10/1.94  tff(c_26, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.10/1.94  tff(c_258, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_256, c_26])).
% 5.10/1.94  tff(c_284, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_257, c_258])).
% 5.10/1.94  tff(c_399, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_389, c_284])).
% 5.10/1.94  tff(c_2411, plain, (~r1_tarski(k4_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2408, c_399])).
% 5.10/1.94  tff(c_2436, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_8, c_2411])).
% 5.10/1.94  tff(c_2946, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k3_tarski(k4_xboole_0('#skF_2', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2941, c_2436])).
% 5.10/1.94  tff(c_2953, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_183, c_6, c_14, c_2946])).
% 5.10/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.10/1.94  
% 5.10/1.94  Inference rules
% 5.10/1.94  ----------------------
% 5.10/1.94  #Ref     : 0
% 5.10/1.94  #Sup     : 781
% 5.10/1.94  #Fact    : 0
% 5.10/1.94  #Define  : 0
% 5.10/1.94  #Split   : 0
% 5.10/1.94  #Chain   : 0
% 5.10/1.94  #Close   : 0
% 5.10/1.94  
% 5.10/1.94  Ordering : KBO
% 5.10/1.94  
% 5.10/1.94  Simplification rules
% 5.10/1.94  ----------------------
% 5.10/1.94  #Subsume      : 18
% 5.10/1.94  #Demod        : 221
% 5.10/1.94  #Tautology    : 146
% 5.10/1.94  #SimpNegUnit  : 0
% 5.10/1.94  #BackRed      : 9
% 5.10/1.94  
% 5.10/1.94  #Partial instantiations: 0
% 5.10/1.94  #Strategies tried      : 1
% 5.10/1.94  
% 5.10/1.94  Timing (in seconds)
% 5.10/1.94  ----------------------
% 5.10/1.94  Preprocessing        : 0.31
% 5.10/1.94  Parsing              : 0.17
% 5.10/1.94  CNF conversion       : 0.02
% 5.10/1.94  Main loop            : 0.91
% 5.10/1.94  Inferencing          : 0.29
% 5.10/1.94  Reduction            : 0.32
% 5.10/1.94  Demodulation         : 0.25
% 5.10/1.94  BG Simplification    : 0.04
% 5.10/1.94  Subsumption          : 0.19
% 5.10/1.94  Abstraction          : 0.04
% 5.10/1.94  MUC search           : 0.00
% 5.10/1.94  Cooper               : 0.00
% 5.10/1.94  Total                : 1.25
% 5.10/1.94  Index Insertion      : 0.00
% 5.10/1.94  Index Deletion       : 0.00
% 5.10/1.94  Index Matching       : 0.00
% 5.10/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
