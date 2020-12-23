%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:09 EST 2020

% Result     : Theorem 16.35s
% Output     : CNFRefutation 16.35s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 132 expanded)
%              Number of leaves         :   32 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  100 ( 189 expanded)
%              Number of equality atoms :   26 (  49 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_85,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_89,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
        & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_91,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,k3_xboole_0(A,B)),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_30,plain,(
    ! [A_25,B_26] : r1_xboole_0(k4_xboole_0(A_25,B_26),B_26) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_66,plain,(
    ! [B_42,A_43] :
      ( r1_xboole_0(B_42,A_43)
      | ~ r1_xboole_0(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_71,plain,(
    ! [B_26,A_25] : r1_xboole_0(B_26,k4_xboole_0(A_25,B_26)) ),
    inference(resolution,[status(thm)],[c_30,c_66])).

tff(c_371,plain,(
    ! [A_64,B_65] :
      ( k4_xboole_0(A_64,B_65) = A_64
      | ~ r1_xboole_0(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_412,plain,(
    ! [B_26,A_25] : k4_xboole_0(B_26,k4_xboole_0(A_25,B_26)) = B_26 ),
    inference(resolution,[status(thm)],[c_71,c_371])).

tff(c_969,plain,(
    ! [A_99,B_100] : k4_xboole_0(A_99,k4_xboole_0(A_99,B_100)) = k3_xboole_0(A_99,B_100) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1028,plain,(
    ! [A_25] : k3_xboole_0(A_25,A_25) = A_25 ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_969])).

tff(c_125,plain,(
    ! [A_50,B_51] :
      ( k3_xboole_0(A_50,B_51) = k1_xboole_0
      | ~ r1_xboole_0(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_142,plain,(
    ! [B_26,A_25] : k3_xboole_0(B_26,k4_xboole_0(A_25,B_26)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_71,c_125])).

tff(c_1024,plain,(
    ! [B_26,A_25] : k3_xboole_0(B_26,k4_xboole_0(A_25,B_26)) = k4_xboole_0(B_26,B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_969])).

tff(c_1366,plain,(
    ! [B_106] : k4_xboole_0(B_106,B_106) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_1024])).

tff(c_20,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1371,plain,(
    ! [B_106] : k4_xboole_0(B_106,k1_xboole_0) = k3_xboole_0(B_106,B_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_1366,c_20])).

tff(c_1420,plain,(
    ! [B_106] : k4_xboole_0(B_106,k1_xboole_0) = B_106 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1028,c_1371])).

tff(c_52,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1465,plain,(
    ! [A_109,B_110] :
      ( k4_xboole_0(A_109,k1_tarski(B_110)) = A_109
      | r2_hidden(B_110,A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2780,plain,(
    ! [A_146,B_147] :
      ( r1_xboole_0(A_146,k1_tarski(B_147))
      | r2_hidden(B_147,A_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1465,c_30])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2794,plain,(
    ! [B_147,A_146] :
      ( r1_xboole_0(k1_tarski(B_147),A_146)
      | r2_hidden(B_147,A_146) ) ),
    inference(resolution,[status(thm)],[c_2780,c_8])).

tff(c_1240,plain,(
    ! [A_102,B_103,C_104] :
      ( ~ r1_xboole_0(A_102,B_103)
      | r1_xboole_0(A_102,k3_xboole_0(B_103,C_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6909,plain,(
    ! [A_232,B_233,C_234] :
      ( k3_xboole_0(A_232,k3_xboole_0(B_233,C_234)) = k1_xboole_0
      | ~ r1_xboole_0(A_232,B_233) ) ),
    inference(resolution,[status(thm)],[c_1240,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_54,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_55,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_54])).

tff(c_183,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_187,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_55,c_183])).

tff(c_217,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k3_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_2])).

tff(c_7076,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0
    | ~ r1_xboole_0(k1_tarski('#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6909,c_217])).

tff(c_7351,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_7076])).

tff(c_7375,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_2794,c_7351])).

tff(c_50,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2061,plain,(
    ! [A_124,B_125,C_126] :
      ( ~ r1_xboole_0(A_124,B_125)
      | ~ r2_hidden(C_126,B_125)
      | ~ r2_hidden(C_126,A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2112,plain,(
    ! [C_126] :
      ( ~ r2_hidden(C_126,'#skF_3')
      | ~ r2_hidden(C_126,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_2061])).

tff(c_7383,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_7375,c_2112])).

tff(c_7387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_7383])).

tff(c_7388,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7076])).

tff(c_115,plain,(
    ! [A_48,B_49] : r1_xboole_0(k4_xboole_0(A_48,k3_xboole_0(A_48,B_49)),B_49) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_558,plain,(
    ! [B_72,A_73] : r1_xboole_0(k4_xboole_0(B_72,k3_xboole_0(A_73,B_72)),A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_115])).

tff(c_605,plain,(
    ! [A_73,B_72] : r1_xboole_0(A_73,k4_xboole_0(B_72,k3_xboole_0(A_73,B_72))) ),
    inference(resolution,[status(thm)],[c_558,c_8])).

tff(c_7458,plain,(
    r1_xboole_0('#skF_3',k4_xboole_0('#skF_2',k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7388,c_605])).

tff(c_7488,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1420,c_7458])).

tff(c_72,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_66])).

tff(c_2259,plain,(
    ! [A_131,C_132,B_133] :
      ( ~ r1_xboole_0(A_131,C_132)
      | ~ r1_xboole_0(A_131,B_133)
      | r1_xboole_0(A_131,k2_xboole_0(B_133,C_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_18597,plain,(
    ! [B_344,C_345,A_346] :
      ( r1_xboole_0(k2_xboole_0(B_344,C_345),A_346)
      | ~ r1_xboole_0(A_346,C_345)
      | ~ r1_xboole_0(A_346,B_344) ) ),
    inference(resolution,[status(thm)],[c_2259,c_8])).

tff(c_48,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_18627,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_18597,c_48])).

tff(c_18640,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7488,c_72,c_18627])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 13:09:37 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.35/5.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.35/5.56  
% 16.35/5.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.35/5.56  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 16.35/5.56  
% 16.35/5.56  %Foreground sorts:
% 16.35/5.56  
% 16.35/5.56  
% 16.35/5.56  %Background operators:
% 16.35/5.56  
% 16.35/5.56  
% 16.35/5.56  %Foreground operators:
% 16.35/5.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.35/5.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.35/5.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 16.35/5.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.35/5.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.35/5.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.35/5.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 16.35/5.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.35/5.56  tff('#skF_5', type, '#skF_5': $i).
% 16.35/5.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 16.35/5.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 16.35/5.56  tff('#skF_2', type, '#skF_2': $i).
% 16.35/5.56  tff('#skF_3', type, '#skF_3': $i).
% 16.35/5.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.35/5.56  tff('#skF_4', type, '#skF_4': $i).
% 16.35/5.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.35/5.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.35/5.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.35/5.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.35/5.56  
% 16.35/5.59  tff(f_85, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 16.35/5.59  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 16.35/5.59  tff(f_89, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 16.35/5.59  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 16.35/5.59  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 16.35/5.59  tff(f_111, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 16.35/5.59  tff(f_102, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 16.35/5.59  tff(f_83, axiom, (![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_xboole_1)).
% 16.35/5.59  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 16.35/5.59  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 16.35/5.59  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 16.35/5.59  tff(f_91, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, k3_xboole_0(A, B)), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_xboole_1)).
% 16.35/5.59  tff(f_77, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 16.35/5.59  tff(c_30, plain, (![A_25, B_26]: (r1_xboole_0(k4_xboole_0(A_25, B_26), B_26))), inference(cnfTransformation, [status(thm)], [f_85])).
% 16.35/5.59  tff(c_66, plain, (![B_42, A_43]: (r1_xboole_0(B_42, A_43) | ~r1_xboole_0(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.35/5.59  tff(c_71, plain, (![B_26, A_25]: (r1_xboole_0(B_26, k4_xboole_0(A_25, B_26)))), inference(resolution, [status(thm)], [c_30, c_66])).
% 16.35/5.59  tff(c_371, plain, (![A_64, B_65]: (k4_xboole_0(A_64, B_65)=A_64 | ~r1_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_89])).
% 16.35/5.59  tff(c_412, plain, (![B_26, A_25]: (k4_xboole_0(B_26, k4_xboole_0(A_25, B_26))=B_26)), inference(resolution, [status(thm)], [c_71, c_371])).
% 16.35/5.59  tff(c_969, plain, (![A_99, B_100]: (k4_xboole_0(A_99, k4_xboole_0(A_99, B_100))=k3_xboole_0(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_61])).
% 16.35/5.59  tff(c_1028, plain, (![A_25]: (k3_xboole_0(A_25, A_25)=A_25)), inference(superposition, [status(thm), theory('equality')], [c_412, c_969])).
% 16.35/5.59  tff(c_125, plain, (![A_50, B_51]: (k3_xboole_0(A_50, B_51)=k1_xboole_0 | ~r1_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.35/5.59  tff(c_142, plain, (![B_26, A_25]: (k3_xboole_0(B_26, k4_xboole_0(A_25, B_26))=k1_xboole_0)), inference(resolution, [status(thm)], [c_71, c_125])).
% 16.35/5.59  tff(c_1024, plain, (![B_26, A_25]: (k3_xboole_0(B_26, k4_xboole_0(A_25, B_26))=k4_xboole_0(B_26, B_26))), inference(superposition, [status(thm), theory('equality')], [c_412, c_969])).
% 16.35/5.59  tff(c_1366, plain, (![B_106]: (k4_xboole_0(B_106, B_106)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_142, c_1024])).
% 16.35/5.59  tff(c_20, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 16.35/5.59  tff(c_1371, plain, (![B_106]: (k4_xboole_0(B_106, k1_xboole_0)=k3_xboole_0(B_106, B_106))), inference(superposition, [status(thm), theory('equality')], [c_1366, c_20])).
% 16.35/5.59  tff(c_1420, plain, (![B_106]: (k4_xboole_0(B_106, k1_xboole_0)=B_106)), inference(demodulation, [status(thm), theory('equality')], [c_1028, c_1371])).
% 16.35/5.59  tff(c_52, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 16.35/5.59  tff(c_1465, plain, (![A_109, B_110]: (k4_xboole_0(A_109, k1_tarski(B_110))=A_109 | r2_hidden(B_110, A_109))), inference(cnfTransformation, [status(thm)], [f_102])).
% 16.35/5.59  tff(c_2780, plain, (![A_146, B_147]: (r1_xboole_0(A_146, k1_tarski(B_147)) | r2_hidden(B_147, A_146))), inference(superposition, [status(thm), theory('equality')], [c_1465, c_30])).
% 16.35/5.59  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.35/5.59  tff(c_2794, plain, (![B_147, A_146]: (r1_xboole_0(k1_tarski(B_147), A_146) | r2_hidden(B_147, A_146))), inference(resolution, [status(thm)], [c_2780, c_8])).
% 16.35/5.59  tff(c_1240, plain, (![A_102, B_103, C_104]: (~r1_xboole_0(A_102, B_103) | r1_xboole_0(A_102, k3_xboole_0(B_103, C_104)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 16.35/5.59  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.35/5.59  tff(c_6909, plain, (![A_232, B_233, C_234]: (k3_xboole_0(A_232, k3_xboole_0(B_233, C_234))=k1_xboole_0 | ~r1_xboole_0(A_232, B_233))), inference(resolution, [status(thm)], [c_1240, c_4])).
% 16.35/5.59  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.35/5.59  tff(c_54, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 16.35/5.59  tff(c_55, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_54])).
% 16.35/5.59  tff(c_183, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_59])).
% 16.35/5.59  tff(c_187, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))=k3_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_55, c_183])).
% 16.35/5.59  tff(c_217, plain, (k3_xboole_0(k1_tarski('#skF_5'), k3_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_187, c_2])).
% 16.35/5.59  tff(c_7076, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0 | ~r1_xboole_0(k1_tarski('#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6909, c_217])).
% 16.35/5.59  tff(c_7351, plain, (~r1_xboole_0(k1_tarski('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_7076])).
% 16.35/5.59  tff(c_7375, plain, (r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_2794, c_7351])).
% 16.35/5.59  tff(c_50, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 16.35/5.59  tff(c_2061, plain, (![A_124, B_125, C_126]: (~r1_xboole_0(A_124, B_125) | ~r2_hidden(C_126, B_125) | ~r2_hidden(C_126, A_124))), inference(cnfTransformation, [status(thm)], [f_53])).
% 16.35/5.59  tff(c_2112, plain, (![C_126]: (~r2_hidden(C_126, '#skF_3') | ~r2_hidden(C_126, '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_2061])).
% 16.35/5.59  tff(c_7383, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_7375, c_2112])).
% 16.35/5.59  tff(c_7387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_7383])).
% 16.35/5.59  tff(c_7388, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_7076])).
% 16.35/5.59  tff(c_115, plain, (![A_48, B_49]: (r1_xboole_0(k4_xboole_0(A_48, k3_xboole_0(A_48, B_49)), B_49))), inference(cnfTransformation, [status(thm)], [f_91])).
% 16.35/5.59  tff(c_558, plain, (![B_72, A_73]: (r1_xboole_0(k4_xboole_0(B_72, k3_xboole_0(A_73, B_72)), A_73))), inference(superposition, [status(thm), theory('equality')], [c_2, c_115])).
% 16.35/5.59  tff(c_605, plain, (![A_73, B_72]: (r1_xboole_0(A_73, k4_xboole_0(B_72, k3_xboole_0(A_73, B_72))))), inference(resolution, [status(thm)], [c_558, c_8])).
% 16.35/5.59  tff(c_7458, plain, (r1_xboole_0('#skF_3', k4_xboole_0('#skF_2', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_7388, c_605])).
% 16.35/5.59  tff(c_7488, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1420, c_7458])).
% 16.35/5.59  tff(c_72, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_66])).
% 16.35/5.59  tff(c_2259, plain, (![A_131, C_132, B_133]: (~r1_xboole_0(A_131, C_132) | ~r1_xboole_0(A_131, B_133) | r1_xboole_0(A_131, k2_xboole_0(B_133, C_132)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 16.35/5.59  tff(c_18597, plain, (![B_344, C_345, A_346]: (r1_xboole_0(k2_xboole_0(B_344, C_345), A_346) | ~r1_xboole_0(A_346, C_345) | ~r1_xboole_0(A_346, B_344))), inference(resolution, [status(thm)], [c_2259, c_8])).
% 16.35/5.59  tff(c_48, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 16.35/5.59  tff(c_18627, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_18597, c_48])).
% 16.35/5.59  tff(c_18640, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7488, c_72, c_18627])).
% 16.35/5.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.35/5.59  
% 16.35/5.59  Inference rules
% 16.35/5.59  ----------------------
% 16.35/5.59  #Ref     : 1
% 16.35/5.59  #Sup     : 4662
% 16.35/5.59  #Fact    : 0
% 16.35/5.59  #Define  : 0
% 16.35/5.59  #Split   : 2
% 16.35/5.59  #Chain   : 0
% 16.35/5.59  #Close   : 0
% 16.35/5.59  
% 16.35/5.59  Ordering : KBO
% 16.35/5.59  
% 16.35/5.59  Simplification rules
% 16.35/5.59  ----------------------
% 16.35/5.59  #Subsume      : 532
% 16.35/5.59  #Demod        : 3768
% 16.35/5.59  #Tautology    : 3018
% 16.35/5.59  #SimpNegUnit  : 56
% 16.35/5.59  #BackRed      : 30
% 16.35/5.59  
% 16.35/5.59  #Partial instantiations: 0
% 16.35/5.59  #Strategies tried      : 1
% 16.35/5.59  
% 16.35/5.59  Timing (in seconds)
% 16.35/5.59  ----------------------
% 16.35/5.59  Preprocessing        : 0.50
% 16.35/5.59  Parsing              : 0.26
% 16.35/5.59  CNF conversion       : 0.04
% 16.35/5.59  Main loop            : 4.12
% 16.35/5.59  Inferencing          : 0.88
% 16.35/5.59  Reduction            : 2.19
% 16.35/5.59  Demodulation         : 1.84
% 16.35/5.59  BG Simplification    : 0.10
% 16.35/5.60  Subsumption          : 0.70
% 16.35/5.60  Abstraction          : 0.12
% 16.35/5.60  MUC search           : 0.00
% 16.35/5.60  Cooper               : 0.00
% 16.35/5.60  Total                : 4.68
% 16.35/5.60  Index Insertion      : 0.00
% 16.35/5.60  Index Deletion       : 0.00
% 16.35/5.60  Index Matching       : 0.00
% 16.35/5.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
