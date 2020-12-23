%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:26 EST 2020

% Result     : Theorem 4.53s
% Output     : CNFRefutation 4.53s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 133 expanded)
%              Number of leaves         :   21 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  116 ( 289 expanded)
%              Number of equality atoms :   78 ( 186 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_53,negated_conjecture,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_38,plain,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_112,plain,(
    ! [A_44,B_45] :
      ( r1_tarski('#skF_3'(A_44,B_45),A_44)
      | ~ r1_tarski('#skF_4'(A_44,B_45),A_44)
      | k1_zfmisc_1(A_44) = B_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_177,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0('#skF_3'(A_56,B_57),A_56) = k1_xboole_0
      | ~ r1_tarski('#skF_4'(A_56,B_57),A_56)
      | k1_zfmisc_1(A_56) = B_57 ) ),
    inference(resolution,[status(thm)],[c_112,c_4])).

tff(c_234,plain,(
    ! [B_68,B_69] :
      ( k4_xboole_0('#skF_3'(B_68,B_69),B_68) = k1_xboole_0
      | k1_zfmisc_1(B_68) = B_69
      | k4_xboole_0('#skF_4'(B_68,B_69),B_68) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_177])).

tff(c_244,plain,(
    ! [B_69] :
      ( '#skF_3'(k1_xboole_0,B_69) = k1_xboole_0
      | k1_zfmisc_1(k1_xboole_0) = B_69
      | k4_xboole_0('#skF_4'(k1_xboole_0,B_69),k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_6])).

tff(c_263,plain,(
    ! [B_70] :
      ( '#skF_3'(k1_xboole_0,B_70) = k1_xboole_0
      | k1_zfmisc_1(k1_xboole_0) = B_70
      | '#skF_4'(k1_xboole_0,B_70) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_244])).

tff(c_32,plain,(
    ! [A_15,B_16] :
      ( r1_tarski('#skF_3'(A_15,B_16),A_15)
      | ~ r1_tarski('#skF_4'(A_15,B_16),A_15)
      | k1_zfmisc_1(A_15) = B_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_287,plain,(
    ! [B_70] :
      ( r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ r1_tarski('#skF_4'(k1_xboole_0,B_70),k1_xboole_0)
      | k1_zfmisc_1(k1_xboole_0) = B_70
      | k1_zfmisc_1(k1_xboole_0) = B_70
      | '#skF_4'(k1_xboole_0,B_70) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_32])).

tff(c_1827,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_287])).

tff(c_28,plain,(
    ! [C_19,A_15] :
      ( r2_hidden(C_19,k1_zfmisc_1(A_15))
      | ~ r1_tarski(C_19,A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_101,plain,(
    ! [A_42,B_43] :
      ( '#skF_1'(A_42,B_43) = A_42
      | r2_hidden('#skF_2'(A_42,B_43),B_43)
      | k1_tarski(A_42) = B_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_26,plain,(
    ! [C_19,A_15] :
      ( r1_tarski(C_19,A_15)
      | ~ r2_hidden(C_19,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_206,plain,(
    ! [A_60,A_61] :
      ( r1_tarski('#skF_2'(A_60,k1_zfmisc_1(A_61)),A_61)
      | '#skF_1'(A_60,k1_zfmisc_1(A_61)) = A_60
      | k1_zfmisc_1(A_61) = k1_tarski(A_60) ) ),
    inference(resolution,[status(thm)],[c_101,c_26])).

tff(c_750,plain,(
    ! [A_959,A_960] :
      ( k4_xboole_0('#skF_2'(A_959,k1_zfmisc_1(A_960)),A_960) = k1_xboole_0
      | '#skF_1'(A_959,k1_zfmisc_1(A_960)) = A_959
      | k1_zfmisc_1(A_960) = k1_tarski(A_959) ) ),
    inference(resolution,[status(thm)],[c_206,c_4])).

tff(c_803,plain,(
    ! [A_982] :
      ( '#skF_2'(A_982,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
      | '#skF_1'(A_982,k1_zfmisc_1(k1_xboole_0)) = A_982
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_982) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_6])).

tff(c_14,plain,(
    ! [A_4,B_5] :
      ( '#skF_1'(A_4,B_5) = A_4
      | '#skF_2'(A_4,B_5) != A_4
      | k1_tarski(A_4) = B_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_823,plain,(
    ! [A_982] :
      ( '#skF_1'(A_982,k1_zfmisc_1(k1_xboole_0)) = A_982
      | k1_xboole_0 != A_982
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_982)
      | '#skF_1'(A_982,k1_zfmisc_1(k1_xboole_0)) = A_982
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_982) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_803,c_14])).

tff(c_2241,plain,(
    ! [A_1655] :
      ( k1_xboole_0 != A_1655
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_1655)
      | '#skF_1'(A_1655,k1_zfmisc_1(k1_xboole_0)) = A_1655 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_823])).

tff(c_132,plain,(
    ! [A_48,B_49] :
      ( ~ r2_hidden('#skF_1'(A_48,B_49),B_49)
      | r2_hidden('#skF_2'(A_48,B_49),B_49)
      | k1_tarski(A_48) = B_49 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_141,plain,(
    ! [A_48,A_15] :
      ( r1_tarski('#skF_2'(A_48,k1_zfmisc_1(A_15)),A_15)
      | ~ r2_hidden('#skF_1'(A_48,k1_zfmisc_1(A_15)),k1_zfmisc_1(A_15))
      | k1_zfmisc_1(A_15) = k1_tarski(A_48) ) ),
    inference(resolution,[status(thm)],[c_132,c_26])).

tff(c_3742,plain,(
    ! [A_3600] :
      ( r1_tarski('#skF_2'(A_3600,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
      | ~ r2_hidden(A_3600,k1_zfmisc_1(k1_xboole_0))
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_3600)
      | k1_xboole_0 != A_3600
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_3600) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2241,c_141])).

tff(c_3747,plain,(
    ! [A_3600] :
      ( k4_xboole_0('#skF_2'(A_3600,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) = k1_xboole_0
      | ~ r2_hidden(A_3600,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != A_3600
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_3600) ) ),
    inference(resolution,[status(thm)],[c_3742,c_4])).

tff(c_3818,plain,(
    ! [A_3643] :
      ( '#skF_2'(A_3643,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
      | ~ r2_hidden(A_3643,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != A_3643
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_3643) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3747])).

tff(c_3882,plain,(
    ! [C_3686] :
      ( '#skF_2'(C_3686,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
      | k1_xboole_0 != C_3686
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(C_3686)
      | ~ r1_tarski(C_3686,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_3818])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( ~ r2_hidden('#skF_1'(A_4,B_5),B_5)
      | '#skF_2'(A_4,B_5) != A_4
      | k1_tarski(A_4) = B_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2309,plain,(
    ! [A_1699] :
      ( ~ r2_hidden(A_1699,k1_zfmisc_1(k1_xboole_0))
      | '#skF_2'(A_1699,k1_zfmisc_1(k1_xboole_0)) != A_1699
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_1699)
      | k1_xboole_0 != A_1699
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_1699) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2241,c_12])).

tff(c_2359,plain,(
    ! [C_19] :
      ( '#skF_2'(C_19,k1_zfmisc_1(k1_xboole_0)) != C_19
      | k1_xboole_0 != C_19
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(C_19)
      | ~ r1_tarski(C_19,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_2309])).

tff(c_4063,plain,(
    ! [C_3815] :
      ( k1_xboole_0 != C_3815
      | k1_xboole_0 != C_3815
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(C_3815)
      | ~ r1_tarski(C_3815,k1_xboole_0)
      | k1_xboole_0 != C_3815
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(C_3815)
      | ~ r1_tarski(C_3815,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3882,c_2359])).

tff(c_4094,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1827,c_4063])).

tff(c_4143,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1827,c_4094])).

tff(c_4145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_4143])).

tff(c_4147,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_287])).

tff(c_4150,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_4147])).

tff(c_4154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4150])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:48:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.53/1.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/1.83  
% 4.53/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/1.84  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1 > #skF_4
% 4.53/1.84  
% 4.53/1.84  %Foreground sorts:
% 4.53/1.84  
% 4.53/1.84  
% 4.53/1.84  %Background operators:
% 4.53/1.84  
% 4.53/1.84  
% 4.53/1.84  %Foreground operators:
% 4.53/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.53/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.53/1.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.53/1.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.53/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.53/1.84  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.53/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.53/1.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.53/1.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.53/1.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.53/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.53/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.53/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.53/1.84  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.53/1.84  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.53/1.84  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.53/1.84  
% 4.53/1.85  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.53/1.85  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.53/1.85  tff(f_53, negated_conjecture, ~(k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 4.53/1.85  tff(f_51, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.53/1.85  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.53/1.85  tff(c_6, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.53/1.85  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.53/1.85  tff(c_38, plain, (k1_zfmisc_1(k1_xboole_0)!=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.53/1.85  tff(c_112, plain, (![A_44, B_45]: (r1_tarski('#skF_3'(A_44, B_45), A_44) | ~r1_tarski('#skF_4'(A_44, B_45), A_44) | k1_zfmisc_1(A_44)=B_45)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.53/1.85  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.53/1.85  tff(c_177, plain, (![A_56, B_57]: (k4_xboole_0('#skF_3'(A_56, B_57), A_56)=k1_xboole_0 | ~r1_tarski('#skF_4'(A_56, B_57), A_56) | k1_zfmisc_1(A_56)=B_57)), inference(resolution, [status(thm)], [c_112, c_4])).
% 4.53/1.85  tff(c_234, plain, (![B_68, B_69]: (k4_xboole_0('#skF_3'(B_68, B_69), B_68)=k1_xboole_0 | k1_zfmisc_1(B_68)=B_69 | k4_xboole_0('#skF_4'(B_68, B_69), B_68)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_177])).
% 4.53/1.85  tff(c_244, plain, (![B_69]: ('#skF_3'(k1_xboole_0, B_69)=k1_xboole_0 | k1_zfmisc_1(k1_xboole_0)=B_69 | k4_xboole_0('#skF_4'(k1_xboole_0, B_69), k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_234, c_6])).
% 4.53/1.85  tff(c_263, plain, (![B_70]: ('#skF_3'(k1_xboole_0, B_70)=k1_xboole_0 | k1_zfmisc_1(k1_xboole_0)=B_70 | '#skF_4'(k1_xboole_0, B_70)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_244])).
% 4.53/1.85  tff(c_32, plain, (![A_15, B_16]: (r1_tarski('#skF_3'(A_15, B_16), A_15) | ~r1_tarski('#skF_4'(A_15, B_16), A_15) | k1_zfmisc_1(A_15)=B_16)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.53/1.85  tff(c_287, plain, (![B_70]: (r1_tarski(k1_xboole_0, k1_xboole_0) | ~r1_tarski('#skF_4'(k1_xboole_0, B_70), k1_xboole_0) | k1_zfmisc_1(k1_xboole_0)=B_70 | k1_zfmisc_1(k1_xboole_0)=B_70 | '#skF_4'(k1_xboole_0, B_70)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_263, c_32])).
% 4.53/1.85  tff(c_1827, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(splitLeft, [status(thm)], [c_287])).
% 4.53/1.85  tff(c_28, plain, (![C_19, A_15]: (r2_hidden(C_19, k1_zfmisc_1(A_15)) | ~r1_tarski(C_19, A_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.53/1.85  tff(c_101, plain, (![A_42, B_43]: ('#skF_1'(A_42, B_43)=A_42 | r2_hidden('#skF_2'(A_42, B_43), B_43) | k1_tarski(A_42)=B_43)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.53/1.85  tff(c_26, plain, (![C_19, A_15]: (r1_tarski(C_19, A_15) | ~r2_hidden(C_19, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.53/1.85  tff(c_206, plain, (![A_60, A_61]: (r1_tarski('#skF_2'(A_60, k1_zfmisc_1(A_61)), A_61) | '#skF_1'(A_60, k1_zfmisc_1(A_61))=A_60 | k1_zfmisc_1(A_61)=k1_tarski(A_60))), inference(resolution, [status(thm)], [c_101, c_26])).
% 4.53/1.85  tff(c_750, plain, (![A_959, A_960]: (k4_xboole_0('#skF_2'(A_959, k1_zfmisc_1(A_960)), A_960)=k1_xboole_0 | '#skF_1'(A_959, k1_zfmisc_1(A_960))=A_959 | k1_zfmisc_1(A_960)=k1_tarski(A_959))), inference(resolution, [status(thm)], [c_206, c_4])).
% 4.53/1.85  tff(c_803, plain, (![A_982]: ('#skF_2'(A_982, k1_zfmisc_1(k1_xboole_0))=k1_xboole_0 | '#skF_1'(A_982, k1_zfmisc_1(k1_xboole_0))=A_982 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_982))), inference(superposition, [status(thm), theory('equality')], [c_750, c_6])).
% 4.53/1.85  tff(c_14, plain, (![A_4, B_5]: ('#skF_1'(A_4, B_5)=A_4 | '#skF_2'(A_4, B_5)!=A_4 | k1_tarski(A_4)=B_5)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.53/1.85  tff(c_823, plain, (![A_982]: ('#skF_1'(A_982, k1_zfmisc_1(k1_xboole_0))=A_982 | k1_xboole_0!=A_982 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_982) | '#skF_1'(A_982, k1_zfmisc_1(k1_xboole_0))=A_982 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_982))), inference(superposition, [status(thm), theory('equality')], [c_803, c_14])).
% 4.53/1.85  tff(c_2241, plain, (![A_1655]: (k1_xboole_0!=A_1655 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_1655) | '#skF_1'(A_1655, k1_zfmisc_1(k1_xboole_0))=A_1655)), inference(factorization, [status(thm), theory('equality')], [c_823])).
% 4.53/1.85  tff(c_132, plain, (![A_48, B_49]: (~r2_hidden('#skF_1'(A_48, B_49), B_49) | r2_hidden('#skF_2'(A_48, B_49), B_49) | k1_tarski(A_48)=B_49)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.53/1.85  tff(c_141, plain, (![A_48, A_15]: (r1_tarski('#skF_2'(A_48, k1_zfmisc_1(A_15)), A_15) | ~r2_hidden('#skF_1'(A_48, k1_zfmisc_1(A_15)), k1_zfmisc_1(A_15)) | k1_zfmisc_1(A_15)=k1_tarski(A_48))), inference(resolution, [status(thm)], [c_132, c_26])).
% 4.53/1.85  tff(c_3742, plain, (![A_3600]: (r1_tarski('#skF_2'(A_3600, k1_zfmisc_1(k1_xboole_0)), k1_xboole_0) | ~r2_hidden(A_3600, k1_zfmisc_1(k1_xboole_0)) | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_3600) | k1_xboole_0!=A_3600 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_3600))), inference(superposition, [status(thm), theory('equality')], [c_2241, c_141])).
% 4.53/1.85  tff(c_3747, plain, (![A_3600]: (k4_xboole_0('#skF_2'(A_3600, k1_zfmisc_1(k1_xboole_0)), k1_xboole_0)=k1_xboole_0 | ~r2_hidden(A_3600, k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0!=A_3600 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_3600))), inference(resolution, [status(thm)], [c_3742, c_4])).
% 4.53/1.85  tff(c_3818, plain, (![A_3643]: ('#skF_2'(A_3643, k1_zfmisc_1(k1_xboole_0))=k1_xboole_0 | ~r2_hidden(A_3643, k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0!=A_3643 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_3643))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3747])).
% 4.53/1.85  tff(c_3882, plain, (![C_3686]: ('#skF_2'(C_3686, k1_zfmisc_1(k1_xboole_0))=k1_xboole_0 | k1_xboole_0!=C_3686 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(C_3686) | ~r1_tarski(C_3686, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_3818])).
% 4.53/1.85  tff(c_12, plain, (![A_4, B_5]: (~r2_hidden('#skF_1'(A_4, B_5), B_5) | '#skF_2'(A_4, B_5)!=A_4 | k1_tarski(A_4)=B_5)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.53/1.85  tff(c_2309, plain, (![A_1699]: (~r2_hidden(A_1699, k1_zfmisc_1(k1_xboole_0)) | '#skF_2'(A_1699, k1_zfmisc_1(k1_xboole_0))!=A_1699 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_1699) | k1_xboole_0!=A_1699 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_1699))), inference(superposition, [status(thm), theory('equality')], [c_2241, c_12])).
% 4.53/1.85  tff(c_2359, plain, (![C_19]: ('#skF_2'(C_19, k1_zfmisc_1(k1_xboole_0))!=C_19 | k1_xboole_0!=C_19 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(C_19) | ~r1_tarski(C_19, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_2309])).
% 4.53/1.85  tff(c_4063, plain, (![C_3815]: (k1_xboole_0!=C_3815 | k1_xboole_0!=C_3815 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(C_3815) | ~r1_tarski(C_3815, k1_xboole_0) | k1_xboole_0!=C_3815 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(C_3815) | ~r1_tarski(C_3815, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3882, c_2359])).
% 4.53/1.85  tff(c_4094, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_1827, c_4063])).
% 4.53/1.85  tff(c_4143, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1827, c_4094])).
% 4.53/1.85  tff(c_4145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_4143])).
% 4.53/1.85  tff(c_4147, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(splitRight, [status(thm)], [c_287])).
% 4.53/1.85  tff(c_4150, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_4147])).
% 4.53/1.85  tff(c_4154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_4150])).
% 4.53/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/1.85  
% 4.53/1.85  Inference rules
% 4.53/1.85  ----------------------
% 4.53/1.85  #Ref     : 1
% 4.53/1.85  #Sup     : 491
% 4.53/1.85  #Fact    : 2
% 4.53/1.85  #Define  : 0
% 4.53/1.85  #Split   : 4
% 4.53/1.85  #Chain   : 0
% 4.53/1.85  #Close   : 0
% 4.53/1.85  
% 4.53/1.85  Ordering : KBO
% 4.53/1.85  
% 4.53/1.85  Simplification rules
% 4.53/1.85  ----------------------
% 4.53/1.85  #Subsume      : 132
% 4.53/1.85  #Demod        : 111
% 4.53/1.85  #Tautology    : 176
% 4.53/1.85  #SimpNegUnit  : 14
% 4.53/1.85  #BackRed      : 0
% 4.53/1.85  
% 4.53/1.85  #Partial instantiations: 1580
% 4.53/1.85  #Strategies tried      : 1
% 4.53/1.85  
% 4.53/1.85  Timing (in seconds)
% 4.53/1.85  ----------------------
% 4.53/1.85  Preprocessing        : 0.31
% 4.53/1.85  Parsing              : 0.15
% 4.53/1.85  CNF conversion       : 0.02
% 4.53/1.85  Main loop            : 0.78
% 4.53/1.85  Inferencing          : 0.38
% 4.53/1.85  Reduction            : 0.16
% 4.53/1.85  Demodulation         : 0.10
% 4.53/1.85  BG Simplification    : 0.04
% 4.53/1.85  Subsumption          : 0.15
% 4.53/1.85  Abstraction          : 0.04
% 4.53/1.85  MUC search           : 0.00
% 4.53/1.85  Cooper               : 0.00
% 4.53/1.85  Total                : 1.11
% 4.53/1.85  Index Insertion      : 0.00
% 4.53/1.85  Index Deletion       : 0.00
% 4.53/1.85  Index Matching       : 0.00
% 4.53/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
