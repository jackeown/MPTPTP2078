%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:46 EST 2020

% Result     : Theorem 5.06s
% Output     : CNFRefutation 5.06s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 166 expanded)
%              Number of leaves         :   30 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          :  108 ( 280 expanded)
%              Number of equality atoms :   46 ( 119 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_83,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_69,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_58,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_46,plain,(
    ! [A_33] : k5_xboole_0(A_33,k1_xboole_0) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k4_xboole_0(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_10] : k3_xboole_0(A_10,A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_83,plain,(
    ! [A_42,B_43] : r1_tarski(k3_xboole_0(A_42,B_43),A_42) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_86,plain,(
    ! [A_10] : r1_tarski(A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_83])).

tff(c_158,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,B_59) = k1_xboole_0
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_173,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_86,c_158])).

tff(c_50,plain,(
    ! [A_34,B_35] :
      ( r1_xboole_0(A_34,B_35)
      | k4_xboole_0(A_34,B_35) != A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_301,plain,(
    ! [A_70,B_71,C_72] :
      ( ~ r1_xboole_0(A_70,B_71)
      | ~ r2_hidden(C_72,k3_xboole_0(A_70,B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_535,plain,(
    ! [A_84,C_85] :
      ( ~ r1_xboole_0(A_84,A_84)
      | ~ r2_hidden(C_85,A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_301])).

tff(c_538,plain,(
    ! [C_85,B_35] :
      ( ~ r2_hidden(C_85,B_35)
      | k4_xboole_0(B_35,B_35) != B_35 ) ),
    inference(resolution,[status(thm)],[c_50,c_535])).

tff(c_547,plain,(
    ! [C_86,B_87] :
      ( ~ r2_hidden(C_86,B_87)
      | k1_xboole_0 != B_87 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_538])).

tff(c_565,plain,(
    ! [A_91,B_92] :
      ( k1_xboole_0 != A_91
      | r1_tarski(A_91,B_92) ) ),
    inference(resolution,[status(thm)],[c_8,c_547])).

tff(c_36,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = k1_xboole_0
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_572,plain,(
    ! [A_93,B_94] :
      ( k4_xboole_0(A_93,B_94) = k1_xboole_0
      | k1_xboole_0 != A_93 ) ),
    inference(resolution,[status(thm)],[c_565,c_36])).

tff(c_646,plain,(
    ! [A_100,B_101] :
      ( k3_xboole_0(A_100,B_101) = k1_xboole_0
      | k1_xboole_0 != A_100 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_572])).

tff(c_835,plain,(
    ! [A_111,B_112] :
      ( k3_xboole_0(A_111,B_112) = k1_xboole_0
      | k1_xboole_0 != B_112 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_646])).

tff(c_38,plain,(
    ! [A_24,B_25] : k5_xboole_0(A_24,k3_xboole_0(A_24,B_25)) = k4_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_850,plain,(
    ! [A_111,B_112] :
      ( k5_xboole_0(A_111,k1_xboole_0) = k4_xboole_0(A_111,B_112)
      | k1_xboole_0 != B_112 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_835,c_38])).

tff(c_1053,plain,(
    ! [A_111] : k4_xboole_0(A_111,k1_xboole_0) = A_111 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_850])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_32,plain,(
    ! [A_20] :
      ( r2_hidden('#skF_3'(A_20),A_20)
      | k1_xboole_0 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_64,plain,(
    k2_zfmisc_1('#skF_5','#skF_4') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1898,plain,(
    ! [A_176,B_177,C_178,D_179] :
      ( r2_hidden(k4_tarski(A_176,B_177),k2_zfmisc_1(C_178,D_179))
      | ~ r2_hidden(B_177,D_179)
      | ~ r2_hidden(A_176,C_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2434,plain,(
    ! [A_190,B_191] :
      ( r2_hidden(k4_tarski(A_190,B_191),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(B_191,'#skF_4')
      | ~ r2_hidden(A_190,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1898])).

tff(c_54,plain,(
    ! [B_37,D_39,A_36,C_38] :
      ( r2_hidden(B_37,D_39)
      | ~ r2_hidden(k4_tarski(A_36,B_37),k2_zfmisc_1(C_38,D_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2455,plain,(
    ! [B_191,A_190] :
      ( r2_hidden(B_191,'#skF_5')
      | ~ r2_hidden(B_191,'#skF_4')
      | ~ r2_hidden(A_190,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2434,c_54])).

tff(c_2857,plain,(
    ! [A_205] : ~ r2_hidden(A_205,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2455])).

tff(c_2873,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_32,c_2857])).

tff(c_2880,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2873])).

tff(c_2882,plain,(
    ! [B_206] :
      ( r2_hidden(B_206,'#skF_5')
      | ~ r2_hidden(B_206,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_2455])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3720,plain,(
    ! [A_232] :
      ( r1_tarski(A_232,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_232,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2882,c_6])).

tff(c_3725,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_3720])).

tff(c_3739,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3725,c_36])).

tff(c_3800,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3739,c_44])).

tff(c_3832,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1053,c_3800])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_56,plain,(
    ! [A_36,C_38,B_37,D_39] :
      ( r2_hidden(A_36,C_38)
      | ~ r2_hidden(k4_tarski(A_36,B_37),k2_zfmisc_1(C_38,D_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2453,plain,(
    ! [A_190,B_191] :
      ( r2_hidden(A_190,'#skF_4')
      | ~ r2_hidden(B_191,'#skF_4')
      | ~ r2_hidden(A_190,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2434,c_56])).

tff(c_3446,plain,(
    ! [B_223] : ~ r2_hidden(B_223,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2453])).

tff(c_3462,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_3446])).

tff(c_3469,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_3462])).

tff(c_3471,plain,(
    ! [A_224] :
      ( r2_hidden(A_224,'#skF_4')
      | ~ r2_hidden(A_224,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_2453])).

tff(c_5048,plain,(
    ! [B_256] :
      ( r2_hidden('#skF_1'('#skF_5',B_256),'#skF_4')
      | r1_tarski('#skF_5',B_256) ) ),
    inference(resolution,[status(thm)],[c_8,c_3471])).

tff(c_5066,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_5048,c_6])).

tff(c_5080,plain,(
    k4_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5066,c_36])).

tff(c_5142,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k3_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5080,c_44])).

tff(c_5177,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1053,c_3832,c_2,c_5142])).

tff(c_5179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5177])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:09:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.06/1.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.06/1.93  
% 5.06/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.06/1.94  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 5.06/1.94  
% 5.06/1.94  %Foreground sorts:
% 5.06/1.94  
% 5.06/1.94  
% 5.06/1.94  %Background operators:
% 5.06/1.94  
% 5.06/1.94  
% 5.06/1.94  %Foreground operators:
% 5.06/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.06/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.06/1.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.06/1.94  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.06/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.06/1.94  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.06/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.06/1.94  tff('#skF_5', type, '#skF_5': $i).
% 5.06/1.94  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.06/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.06/1.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.06/1.94  tff('#skF_4', type, '#skF_4': $i).
% 5.06/1.94  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.06/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.06/1.94  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.06/1.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.06/1.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.06/1.94  
% 5.06/1.95  tff(f_102, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 5.06/1.95  tff(f_83, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.06/1.95  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.06/1.95  tff(f_81, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.06/1.95  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.06/1.95  tff(f_40, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.06/1.95  tff(f_79, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.06/1.95  tff(f_73, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.06/1.95  tff(f_87, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.06/1.95  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.06/1.95  tff(f_75, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.06/1.95  tff(f_69, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.06/1.95  tff(f_93, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 5.06/1.95  tff(c_58, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.06/1.95  tff(c_46, plain, (![A_33]: (k5_xboole_0(A_33, k1_xboole_0)=A_33)), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.06/1.95  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.06/1.95  tff(c_44, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k4_xboole_0(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.06/1.95  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.06/1.95  tff(c_14, plain, (![A_10]: (k3_xboole_0(A_10, A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.06/1.95  tff(c_83, plain, (![A_42, B_43]: (r1_tarski(k3_xboole_0(A_42, B_43), A_42))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.06/1.95  tff(c_86, plain, (![A_10]: (r1_tarski(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_14, c_83])).
% 5.06/1.95  tff(c_158, plain, (![A_58, B_59]: (k4_xboole_0(A_58, B_59)=k1_xboole_0 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.06/1.95  tff(c_173, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_86, c_158])).
% 5.06/1.95  tff(c_50, plain, (![A_34, B_35]: (r1_xboole_0(A_34, B_35) | k4_xboole_0(A_34, B_35)!=A_34)), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.06/1.95  tff(c_301, plain, (![A_70, B_71, C_72]: (~r1_xboole_0(A_70, B_71) | ~r2_hidden(C_72, k3_xboole_0(A_70, B_71)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.06/1.95  tff(c_535, plain, (![A_84, C_85]: (~r1_xboole_0(A_84, A_84) | ~r2_hidden(C_85, A_84))), inference(superposition, [status(thm), theory('equality')], [c_14, c_301])).
% 5.06/1.95  tff(c_538, plain, (![C_85, B_35]: (~r2_hidden(C_85, B_35) | k4_xboole_0(B_35, B_35)!=B_35)), inference(resolution, [status(thm)], [c_50, c_535])).
% 5.06/1.95  tff(c_547, plain, (![C_86, B_87]: (~r2_hidden(C_86, B_87) | k1_xboole_0!=B_87)), inference(demodulation, [status(thm), theory('equality')], [c_173, c_538])).
% 5.06/1.95  tff(c_565, plain, (![A_91, B_92]: (k1_xboole_0!=A_91 | r1_tarski(A_91, B_92))), inference(resolution, [status(thm)], [c_8, c_547])).
% 5.06/1.95  tff(c_36, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=k1_xboole_0 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.06/1.95  tff(c_572, plain, (![A_93, B_94]: (k4_xboole_0(A_93, B_94)=k1_xboole_0 | k1_xboole_0!=A_93)), inference(resolution, [status(thm)], [c_565, c_36])).
% 5.06/1.95  tff(c_646, plain, (![A_100, B_101]: (k3_xboole_0(A_100, B_101)=k1_xboole_0 | k1_xboole_0!=A_100)), inference(superposition, [status(thm), theory('equality')], [c_44, c_572])).
% 5.06/1.95  tff(c_835, plain, (![A_111, B_112]: (k3_xboole_0(A_111, B_112)=k1_xboole_0 | k1_xboole_0!=B_112)), inference(superposition, [status(thm), theory('equality')], [c_2, c_646])).
% 5.06/1.95  tff(c_38, plain, (![A_24, B_25]: (k5_xboole_0(A_24, k3_xboole_0(A_24, B_25))=k4_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.06/1.95  tff(c_850, plain, (![A_111, B_112]: (k5_xboole_0(A_111, k1_xboole_0)=k4_xboole_0(A_111, B_112) | k1_xboole_0!=B_112)), inference(superposition, [status(thm), theory('equality')], [c_835, c_38])).
% 5.06/1.95  tff(c_1053, plain, (![A_111]: (k4_xboole_0(A_111, k1_xboole_0)=A_111)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_850])).
% 5.06/1.95  tff(c_60, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.06/1.95  tff(c_32, plain, (![A_20]: (r2_hidden('#skF_3'(A_20), A_20) | k1_xboole_0=A_20)), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.06/1.95  tff(c_64, plain, (k2_zfmisc_1('#skF_5', '#skF_4')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.06/1.95  tff(c_1898, plain, (![A_176, B_177, C_178, D_179]: (r2_hidden(k4_tarski(A_176, B_177), k2_zfmisc_1(C_178, D_179)) | ~r2_hidden(B_177, D_179) | ~r2_hidden(A_176, C_178))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.06/1.95  tff(c_2434, plain, (![A_190, B_191]: (r2_hidden(k4_tarski(A_190, B_191), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(B_191, '#skF_4') | ~r2_hidden(A_190, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_1898])).
% 5.06/1.95  tff(c_54, plain, (![B_37, D_39, A_36, C_38]: (r2_hidden(B_37, D_39) | ~r2_hidden(k4_tarski(A_36, B_37), k2_zfmisc_1(C_38, D_39)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.06/1.95  tff(c_2455, plain, (![B_191, A_190]: (r2_hidden(B_191, '#skF_5') | ~r2_hidden(B_191, '#skF_4') | ~r2_hidden(A_190, '#skF_5'))), inference(resolution, [status(thm)], [c_2434, c_54])).
% 5.06/1.95  tff(c_2857, plain, (![A_205]: (~r2_hidden(A_205, '#skF_5'))), inference(splitLeft, [status(thm)], [c_2455])).
% 5.06/1.95  tff(c_2873, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_32, c_2857])).
% 5.06/1.95  tff(c_2880, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_2873])).
% 5.06/1.95  tff(c_2882, plain, (![B_206]: (r2_hidden(B_206, '#skF_5') | ~r2_hidden(B_206, '#skF_4'))), inference(splitRight, [status(thm)], [c_2455])).
% 5.06/1.95  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.06/1.95  tff(c_3720, plain, (![A_232]: (r1_tarski(A_232, '#skF_5') | ~r2_hidden('#skF_1'(A_232, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_2882, c_6])).
% 5.06/1.95  tff(c_3725, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_8, c_3720])).
% 5.06/1.95  tff(c_3739, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_3725, c_36])).
% 5.06/1.95  tff(c_3800, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3739, c_44])).
% 5.06/1.95  tff(c_3832, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1053, c_3800])).
% 5.06/1.95  tff(c_62, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.06/1.95  tff(c_56, plain, (![A_36, C_38, B_37, D_39]: (r2_hidden(A_36, C_38) | ~r2_hidden(k4_tarski(A_36, B_37), k2_zfmisc_1(C_38, D_39)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.06/1.95  tff(c_2453, plain, (![A_190, B_191]: (r2_hidden(A_190, '#skF_4') | ~r2_hidden(B_191, '#skF_4') | ~r2_hidden(A_190, '#skF_5'))), inference(resolution, [status(thm)], [c_2434, c_56])).
% 5.06/1.95  tff(c_3446, plain, (![B_223]: (~r2_hidden(B_223, '#skF_4'))), inference(splitLeft, [status(thm)], [c_2453])).
% 5.06/1.95  tff(c_3462, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_32, c_3446])).
% 5.06/1.95  tff(c_3469, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_3462])).
% 5.06/1.95  tff(c_3471, plain, (![A_224]: (r2_hidden(A_224, '#skF_4') | ~r2_hidden(A_224, '#skF_5'))), inference(splitRight, [status(thm)], [c_2453])).
% 5.06/1.95  tff(c_5048, plain, (![B_256]: (r2_hidden('#skF_1'('#skF_5', B_256), '#skF_4') | r1_tarski('#skF_5', B_256))), inference(resolution, [status(thm)], [c_8, c_3471])).
% 5.06/1.95  tff(c_5066, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_5048, c_6])).
% 5.06/1.95  tff(c_5080, plain, (k4_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_5066, c_36])).
% 5.06/1.95  tff(c_5142, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k3_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5080, c_44])).
% 5.06/1.95  tff(c_5177, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1053, c_3832, c_2, c_5142])).
% 5.06/1.95  tff(c_5179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_5177])).
% 5.06/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.06/1.95  
% 5.06/1.95  Inference rules
% 5.06/1.95  ----------------------
% 5.06/1.95  #Ref     : 1
% 5.06/1.95  #Sup     : 1282
% 5.06/1.95  #Fact    : 0
% 5.06/1.95  #Define  : 0
% 5.06/1.95  #Split   : 6
% 5.06/1.95  #Chain   : 0
% 5.06/1.95  #Close   : 0
% 5.06/1.95  
% 5.06/1.95  Ordering : KBO
% 5.06/1.95  
% 5.06/1.95  Simplification rules
% 5.06/1.95  ----------------------
% 5.06/1.95  #Subsume      : 308
% 5.06/1.95  #Demod        : 603
% 5.06/1.95  #Tautology    : 598
% 5.06/1.95  #SimpNegUnit  : 37
% 5.06/1.95  #BackRed      : 5
% 5.06/1.95  
% 5.06/1.95  #Partial instantiations: 0
% 5.06/1.95  #Strategies tried      : 1
% 5.06/1.95  
% 5.06/1.95  Timing (in seconds)
% 5.06/1.95  ----------------------
% 5.06/1.95  Preprocessing        : 0.31
% 5.06/1.95  Parsing              : 0.16
% 5.06/1.95  CNF conversion       : 0.02
% 5.06/1.95  Main loop            : 0.86
% 5.06/1.95  Inferencing          : 0.27
% 5.06/1.95  Reduction            : 0.34
% 5.06/1.95  Demodulation         : 0.27
% 5.06/1.95  BG Simplification    : 0.03
% 5.06/1.95  Subsumption          : 0.16
% 5.06/1.95  Abstraction          : 0.04
% 5.06/1.95  MUC search           : 0.00
% 5.06/1.95  Cooper               : 0.00
% 5.06/1.95  Total                : 1.20
% 5.06/1.95  Index Insertion      : 0.00
% 5.06/1.95  Index Deletion       : 0.00
% 5.06/1.95  Index Matching       : 0.00
% 5.06/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
