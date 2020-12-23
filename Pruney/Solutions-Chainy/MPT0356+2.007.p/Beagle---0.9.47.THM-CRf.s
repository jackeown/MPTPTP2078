%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:56 EST 2020

% Result     : Theorem 30.60s
% Output     : CNFRefutation 30.67s
% Verified   : 
% Statistics : Number of formulae       :   74 (  93 expanded)
%              Number of leaves         :   34 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :   95 ( 142 expanded)
%              Number of equality atoms :   16 (  25 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k9_subset_1 > k8_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k8_subset_1,type,(
    k8_subset_1: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_161,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,k3_subset_1(A,C))
             => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_120,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_76,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_137,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_76,plain,(
    r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_189,plain,(
    ! [A_91,B_92] :
      ( k3_xboole_0(A_91,B_92) = A_91
      | ~ r1_tarski(A_91,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_211,plain,(
    k3_xboole_0('#skF_3',k3_subset_1('#skF_2','#skF_4')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_76,c_189])).

tff(c_78,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_3541,plain,(
    ! [A_240,B_241] :
      ( k4_xboole_0(A_240,B_241) = k3_subset_1(A_240,B_241)
      | ~ m1_subset_1(B_241,k1_zfmisc_1(A_240)) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3548,plain,(
    k4_xboole_0('#skF_2','#skF_4') = k3_subset_1('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_3541])).

tff(c_455,plain,(
    ! [A_105,B_106] :
      ( k2_xboole_0(A_105,B_106) = B_106
      | ~ r1_tarski(A_105,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_487,plain,(
    ! [B_7] : k2_xboole_0(B_7,B_7) = B_7 ),
    inference(resolution,[status(thm)],[c_12,c_455])).

tff(c_4548,plain,(
    ! [A_256,B_257,C_258] : r1_tarski(k2_xboole_0(k3_xboole_0(A_256,B_257),k3_xboole_0(A_256,C_258)),k2_xboole_0(B_257,C_258)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4622,plain,(
    ! [A_256,B_257] : r1_tarski(k3_xboole_0(A_256,B_257),k2_xboole_0(B_257,B_257)) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_4548])).

tff(c_4667,plain,(
    ! [A_259,B_260] : r1_tarski(k3_xboole_0(A_259,B_260),B_260) ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_4622])).

tff(c_14,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_xboole_0(A_8,C_10)
      | ~ r1_tarski(A_8,k4_xboole_0(B_9,C_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10227,plain,(
    ! [A_361,B_362,C_363] : r1_xboole_0(k3_xboole_0(A_361,k4_xboole_0(B_362,C_363)),C_363) ),
    inference(resolution,[status(thm)],[c_4667,c_14])).

tff(c_11290,plain,(
    ! [A_385] : r1_xboole_0(k3_xboole_0(A_385,k3_subset_1('#skF_2','#skF_4')),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3548,c_10227])).

tff(c_11300,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_11290])).

tff(c_52,plain,(
    ! [A_45,B_46,C_47] :
      ( r1_tarski(A_45,k4_xboole_0(B_46,C_47))
      | ~ r1_xboole_0(A_45,C_47)
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_38,plain,(
    ! [A_32,B_33] : r1_tarski(k4_xboole_0(A_32,B_33),A_32) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_976,plain,(
    ! [B_137,A_138] :
      ( B_137 = A_138
      | ~ r1_tarski(B_137,A_138)
      | ~ r1_tarski(A_138,B_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12036,plain,(
    ! [A_401,B_402] :
      ( k4_xboole_0(A_401,B_402) = A_401
      | ~ r1_tarski(A_401,k4_xboole_0(A_401,B_402)) ) ),
    inference(resolution,[status(thm)],[c_38,c_976])).

tff(c_12061,plain,(
    ! [B_46,C_47] :
      ( k4_xboole_0(B_46,C_47) = B_46
      | ~ r1_xboole_0(B_46,C_47)
      | ~ r1_tarski(B_46,B_46) ) ),
    inference(resolution,[status(thm)],[c_52,c_12036])).

tff(c_12312,plain,(
    ! [B_403,C_404] :
      ( k4_xboole_0(B_403,C_404) = B_403
      | ~ r1_xboole_0(B_403,C_404) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12061])).

tff(c_12370,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_11300,c_12312])).

tff(c_50,plain,(
    ! [A_42,C_44,B_43] :
      ( r1_xboole_0(A_42,k4_xboole_0(C_44,B_43))
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_12859,plain,(
    ! [A_42] :
      ( r1_xboole_0(A_42,'#skF_3')
      | ~ r1_tarski(A_42,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12370,c_50])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4074,plain,(
    ! [C_246,A_247,B_248] :
      ( r2_hidden(C_246,A_247)
      | ~ r2_hidden(C_246,B_248)
      | ~ m1_subset_1(B_248,k1_zfmisc_1(A_247)) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_21922,plain,(
    ! [A_504,B_505,A_506] :
      ( r2_hidden('#skF_1'(A_504,B_505),A_506)
      | ~ m1_subset_1(A_504,k1_zfmisc_1(A_506))
      | r1_tarski(A_504,B_505) ) ),
    inference(resolution,[status(thm)],[c_6,c_4074])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_21934,plain,(
    ! [A_507,A_508] :
      ( ~ m1_subset_1(A_507,k1_zfmisc_1(A_508))
      | r1_tarski(A_507,A_508) ) ),
    inference(resolution,[status(thm)],[c_21922,c_4])).

tff(c_21941,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_21934])).

tff(c_80,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_3549,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k3_subset_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_3541])).

tff(c_5917,plain,(
    ! [A_280,B_281,C_282] :
      ( r1_tarski(A_280,k4_xboole_0(B_281,C_282))
      | ~ r1_xboole_0(A_280,C_282)
      | ~ r1_tarski(A_280,B_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_103947,plain,(
    ! [A_1132] :
      ( r1_tarski(A_1132,k3_subset_1('#skF_2','#skF_3'))
      | ~ r1_xboole_0(A_1132,'#skF_3')
      | ~ r1_tarski(A_1132,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3549,c_5917])).

tff(c_74,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_104055,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_3')
    | ~ r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_103947,c_74])).

tff(c_104116,plain,(
    ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21941,c_104055])).

tff(c_104122,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_12859,c_104116])).

tff(c_104133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_104122])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:53:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 30.60/22.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.67/22.05  
% 30.67/22.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.67/22.06  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k9_subset_1 > k8_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 30.67/22.06  
% 30.67/22.06  %Foreground sorts:
% 30.67/22.06  
% 30.67/22.06  
% 30.67/22.06  %Background operators:
% 30.67/22.06  
% 30.67/22.06  
% 30.67/22.06  %Foreground operators:
% 30.67/22.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 30.67/22.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 30.67/22.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 30.67/22.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 30.67/22.06  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 30.67/22.06  tff(k8_subset_1, type, k8_subset_1: ($i * $i * $i) > $i).
% 30.67/22.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 30.67/22.06  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 30.67/22.06  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 30.67/22.06  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 30.67/22.06  tff('#skF_2', type, '#skF_2': $i).
% 30.67/22.06  tff('#skF_3', type, '#skF_3': $i).
% 30.67/22.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 30.67/22.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 30.67/22.06  tff(k3_tarski, type, k3_tarski: $i > $i).
% 30.67/22.06  tff('#skF_4', type, '#skF_4': $i).
% 30.67/22.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 30.67/22.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 30.67/22.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 30.67/22.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 30.67/22.06  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 30.67/22.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 30.67/22.06  
% 30.67/22.07  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 30.67/22.07  tff(f_161, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 30.67/22.07  tff(f_74, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 30.67/22.07  tff(f_120, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 30.67/22.07  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 30.67/22.07  tff(f_76, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 30.67/22.07  tff(f_44, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 30.67/22.07  tff(f_108, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 30.67/22.07  tff(f_78, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 30.67/22.07  tff(f_102, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 30.67/22.07  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 30.67/22.07  tff(f_137, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 30.67/22.07  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 30.67/22.07  tff(c_76, plain, (r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 30.67/22.07  tff(c_189, plain, (![A_91, B_92]: (k3_xboole_0(A_91, B_92)=A_91 | ~r1_tarski(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_74])).
% 30.67/22.07  tff(c_211, plain, (k3_xboole_0('#skF_3', k3_subset_1('#skF_2', '#skF_4'))='#skF_3'), inference(resolution, [status(thm)], [c_76, c_189])).
% 30.67/22.07  tff(c_78, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 30.67/22.07  tff(c_3541, plain, (![A_240, B_241]: (k4_xboole_0(A_240, B_241)=k3_subset_1(A_240, B_241) | ~m1_subset_1(B_241, k1_zfmisc_1(A_240)))), inference(cnfTransformation, [status(thm)], [f_120])).
% 30.67/22.07  tff(c_3548, plain, (k4_xboole_0('#skF_2', '#skF_4')=k3_subset_1('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_78, c_3541])).
% 30.67/22.07  tff(c_455, plain, (![A_105, B_106]: (k2_xboole_0(A_105, B_106)=B_106 | ~r1_tarski(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_58])).
% 30.67/22.07  tff(c_487, plain, (![B_7]: (k2_xboole_0(B_7, B_7)=B_7)), inference(resolution, [status(thm)], [c_12, c_455])).
% 30.67/22.07  tff(c_4548, plain, (![A_256, B_257, C_258]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_256, B_257), k3_xboole_0(A_256, C_258)), k2_xboole_0(B_257, C_258)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 30.67/22.07  tff(c_4622, plain, (![A_256, B_257]: (r1_tarski(k3_xboole_0(A_256, B_257), k2_xboole_0(B_257, B_257)))), inference(superposition, [status(thm), theory('equality')], [c_487, c_4548])).
% 30.67/22.07  tff(c_4667, plain, (![A_259, B_260]: (r1_tarski(k3_xboole_0(A_259, B_260), B_260))), inference(demodulation, [status(thm), theory('equality')], [c_487, c_4622])).
% 30.67/22.07  tff(c_14, plain, (![A_8, C_10, B_9]: (r1_xboole_0(A_8, C_10) | ~r1_tarski(A_8, k4_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 30.67/22.07  tff(c_10227, plain, (![A_361, B_362, C_363]: (r1_xboole_0(k3_xboole_0(A_361, k4_xboole_0(B_362, C_363)), C_363))), inference(resolution, [status(thm)], [c_4667, c_14])).
% 30.67/22.07  tff(c_11290, plain, (![A_385]: (r1_xboole_0(k3_xboole_0(A_385, k3_subset_1('#skF_2', '#skF_4')), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3548, c_10227])).
% 30.67/22.07  tff(c_11300, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_211, c_11290])).
% 30.67/22.07  tff(c_52, plain, (![A_45, B_46, C_47]: (r1_tarski(A_45, k4_xboole_0(B_46, C_47)) | ~r1_xboole_0(A_45, C_47) | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_108])).
% 30.67/22.07  tff(c_38, plain, (![A_32, B_33]: (r1_tarski(k4_xboole_0(A_32, B_33), A_32))), inference(cnfTransformation, [status(thm)], [f_78])).
% 30.67/22.07  tff(c_976, plain, (![B_137, A_138]: (B_137=A_138 | ~r1_tarski(B_137, A_138) | ~r1_tarski(A_138, B_137))), inference(cnfTransformation, [status(thm)], [f_38])).
% 30.67/22.07  tff(c_12036, plain, (![A_401, B_402]: (k4_xboole_0(A_401, B_402)=A_401 | ~r1_tarski(A_401, k4_xboole_0(A_401, B_402)))), inference(resolution, [status(thm)], [c_38, c_976])).
% 30.67/22.07  tff(c_12061, plain, (![B_46, C_47]: (k4_xboole_0(B_46, C_47)=B_46 | ~r1_xboole_0(B_46, C_47) | ~r1_tarski(B_46, B_46))), inference(resolution, [status(thm)], [c_52, c_12036])).
% 30.67/22.07  tff(c_12312, plain, (![B_403, C_404]: (k4_xboole_0(B_403, C_404)=B_403 | ~r1_xboole_0(B_403, C_404))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12061])).
% 30.67/22.07  tff(c_12370, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_11300, c_12312])).
% 30.67/22.07  tff(c_50, plain, (![A_42, C_44, B_43]: (r1_xboole_0(A_42, k4_xboole_0(C_44, B_43)) | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_102])).
% 30.67/22.07  tff(c_12859, plain, (![A_42]: (r1_xboole_0(A_42, '#skF_3') | ~r1_tarski(A_42, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_12370, c_50])).
% 30.67/22.07  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 30.67/22.07  tff(c_4074, plain, (![C_246, A_247, B_248]: (r2_hidden(C_246, A_247) | ~r2_hidden(C_246, B_248) | ~m1_subset_1(B_248, k1_zfmisc_1(A_247)))), inference(cnfTransformation, [status(thm)], [f_137])).
% 30.67/22.07  tff(c_21922, plain, (![A_504, B_505, A_506]: (r2_hidden('#skF_1'(A_504, B_505), A_506) | ~m1_subset_1(A_504, k1_zfmisc_1(A_506)) | r1_tarski(A_504, B_505))), inference(resolution, [status(thm)], [c_6, c_4074])).
% 30.67/22.07  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 30.67/22.07  tff(c_21934, plain, (![A_507, A_508]: (~m1_subset_1(A_507, k1_zfmisc_1(A_508)) | r1_tarski(A_507, A_508))), inference(resolution, [status(thm)], [c_21922, c_4])).
% 30.67/22.07  tff(c_21941, plain, (r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_78, c_21934])).
% 30.67/22.07  tff(c_80, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 30.67/22.07  tff(c_3549, plain, (k4_xboole_0('#skF_2', '#skF_3')=k3_subset_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_80, c_3541])).
% 30.67/22.07  tff(c_5917, plain, (![A_280, B_281, C_282]: (r1_tarski(A_280, k4_xboole_0(B_281, C_282)) | ~r1_xboole_0(A_280, C_282) | ~r1_tarski(A_280, B_281))), inference(cnfTransformation, [status(thm)], [f_108])).
% 30.67/22.07  tff(c_103947, plain, (![A_1132]: (r1_tarski(A_1132, k3_subset_1('#skF_2', '#skF_3')) | ~r1_xboole_0(A_1132, '#skF_3') | ~r1_tarski(A_1132, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3549, c_5917])).
% 30.67/22.07  tff(c_74, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 30.67/22.07  tff(c_104055, plain, (~r1_xboole_0('#skF_4', '#skF_3') | ~r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_103947, c_74])).
% 30.67/22.07  tff(c_104116, plain, (~r1_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_21941, c_104055])).
% 30.67/22.07  tff(c_104122, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_12859, c_104116])).
% 30.67/22.07  tff(c_104133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_104122])).
% 30.67/22.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.67/22.07  
% 30.67/22.07  Inference rules
% 30.67/22.07  ----------------------
% 30.67/22.07  #Ref     : 1
% 30.67/22.07  #Sup     : 26111
% 30.67/22.07  #Fact    : 0
% 30.67/22.07  #Define  : 0
% 30.67/22.07  #Split   : 8
% 30.67/22.07  #Chain   : 0
% 30.67/22.07  #Close   : 0
% 30.67/22.07  
% 30.67/22.07  Ordering : KBO
% 30.67/22.07  
% 30.67/22.07  Simplification rules
% 30.67/22.07  ----------------------
% 30.67/22.07  #Subsume      : 4316
% 30.67/22.07  #Demod        : 16572
% 30.67/22.07  #Tautology    : 12771
% 30.67/22.07  #SimpNegUnit  : 422
% 30.67/22.07  #BackRed      : 28
% 30.67/22.07  
% 30.67/22.07  #Partial instantiations: 0
% 30.67/22.07  #Strategies tried      : 1
% 30.67/22.07  
% 30.67/22.07  Timing (in seconds)
% 30.67/22.07  ----------------------
% 30.79/22.07  Preprocessing        : 0.35
% 30.79/22.07  Parsing              : 0.19
% 30.79/22.07  CNF conversion       : 0.03
% 30.79/22.07  Main loop            : 20.91
% 30.79/22.07  Inferencing          : 2.10
% 30.79/22.07  Reduction            : 12.57
% 30.79/22.08  Demodulation         : 10.76
% 30.79/22.08  BG Simplification    : 0.19
% 30.79/22.08  Subsumption          : 5.08
% 30.79/22.08  Abstraction          : 0.29
% 30.79/22.08  MUC search           : 0.00
% 30.79/22.08  Cooper               : 0.00
% 30.79/22.08  Total                : 21.29
% 30.79/22.08  Index Insertion      : 0.00
% 30.79/22.08  Index Deletion       : 0.00
% 30.79/22.08  Index Matching       : 0.00
% 30.79/22.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
