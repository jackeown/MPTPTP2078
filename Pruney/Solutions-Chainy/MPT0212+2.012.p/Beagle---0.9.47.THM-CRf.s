%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:27 EST 2020

% Result     : Theorem 6.56s
% Output     : CNFRefutation 6.56s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 172 expanded)
%              Number of leaves         :   25 (  67 expanded)
%              Depth                    :   15
%              Number of atoms          :  110 ( 377 expanded)
%              Number of equality atoms :   73 ( 279 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_61,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_50,plain,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_54,plain,(
    ! [A_47] : k2_tarski(A_47,A_47) = k1_tarski(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8,plain,(
    ! [D_8,A_3] : r2_hidden(D_8,k2_tarski(A_3,D_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_60,plain,(
    ! [A_47] : r2_hidden(A_47,k1_tarski(A_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_8])).

tff(c_48,plain,(
    ! [A_37,B_38] :
      ( r1_tarski('#skF_3'(A_37,B_38),A_37)
      | r2_hidden('#skF_4'(A_37,B_38),B_38)
      | k1_zfmisc_1(A_37) = B_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_18,plain,(
    ! [A_3,B_4,C_5] :
      ( '#skF_1'(A_3,B_4,C_5) = B_4
      | '#skF_1'(A_3,B_4,C_5) = A_3
      | '#skF_2'(A_3,B_4,C_5) != A_3
      | k2_tarski(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_302,plain,(
    ! [B_4,C_5] :
      ( '#skF_2'(B_4,B_4,C_5) != B_4
      | k2_tarski(B_4,B_4) = C_5
      | '#skF_1'(B_4,B_4,C_5) = B_4 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_18])).

tff(c_685,plain,(
    ! [B_1877,C_1878] :
      ( '#skF_2'(B_1877,B_1877,C_1878) != B_1877
      | k1_tarski(B_1877) = C_1878
      | '#skF_1'(B_1877,B_1877,C_1878) = B_1877 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_302])).

tff(c_93,plain,(
    ! [D_56,B_57,A_58] :
      ( D_56 = B_57
      | D_56 = A_58
      | ~ r2_hidden(D_56,k2_tarski(A_58,B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_96,plain,(
    ! [D_56,A_9] :
      ( D_56 = A_9
      | D_56 = A_9
      | ~ r2_hidden(D_56,k1_tarski(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_93])).

tff(c_1567,plain,(
    ! [D_5690,B_5691,C_5692] :
      ( D_5690 = B_5691
      | D_5690 = B_5691
      | ~ r2_hidden(D_5690,C_5692)
      | '#skF_2'(B_5691,B_5691,C_5692) != B_5691
      | '#skF_1'(B_5691,B_5691,C_5692) = B_5691 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_685,c_96])).

tff(c_3663,plain,(
    ! [B_9277,A_9278,B_9279] :
      ( B_9277 = '#skF_4'(A_9278,B_9279)
      | '#skF_2'(B_9277,B_9277,B_9279) != B_9277
      | '#skF_1'(B_9277,B_9277,B_9279) = B_9277
      | r1_tarski('#skF_3'(A_9278,B_9279),A_9278)
      | k1_zfmisc_1(A_9278) = B_9279 ) ),
    inference(resolution,[status(thm)],[c_48,c_1567])).

tff(c_4,plain,(
    ! [A_2] :
      ( k1_xboole_0 = A_2
      | ~ r1_tarski(A_2,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4625,plain,(
    ! [B_12476,B_12477] :
      ( '#skF_3'(k1_xboole_0,B_12476) = k1_xboole_0
      | B_12477 = '#skF_4'(k1_xboole_0,B_12476)
      | '#skF_2'(B_12477,B_12477,B_12476) != B_12477
      | '#skF_1'(B_12477,B_12477,B_12476) = B_12477
      | k1_zfmisc_1(k1_xboole_0) = B_12476 ) ),
    inference(resolution,[status(thm)],[c_3663,c_4])).

tff(c_5268,plain,(
    ! [B_12476,B_12477] :
      ( k1_tarski(k1_xboole_0) != B_12476
      | '#skF_3'(k1_xboole_0,B_12476) = k1_xboole_0
      | B_12477 = '#skF_4'(k1_xboole_0,B_12476)
      | '#skF_2'(B_12477,B_12477,B_12476) != B_12477
      | '#skF_1'(B_12477,B_12477,B_12476) = B_12477 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4625,c_50])).

tff(c_5383,plain,(
    ! [B_12477] :
      ( '#skF_3'(k1_xboole_0,k1_tarski(k1_xboole_0)) = k1_xboole_0
      | B_12477 = '#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0))
      | '#skF_2'(B_12477,B_12477,k1_tarski(k1_xboole_0)) != B_12477
      | '#skF_1'(B_12477,B_12477,k1_tarski(k1_xboole_0)) = B_12477 ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_5268])).

tff(c_6239,plain,(
    '#skF_3'(k1_xboole_0,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5383])).

tff(c_46,plain,(
    ! [A_37,B_38] :
      ( ~ r2_hidden('#skF_3'(A_37,B_38),B_38)
      | r2_hidden('#skF_4'(A_37,B_38),B_38)
      | k1_zfmisc_1(A_37) = B_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6253,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | r2_hidden('#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0))
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6239,c_46])).

tff(c_6301,plain,
    ( r2_hidden('#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0))
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6253])).

tff(c_6302,plain,(
    r2_hidden('#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_6301])).

tff(c_6423,plain,(
    '#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6302,c_96])).

tff(c_42,plain,(
    ! [A_37,B_38] :
      ( ~ r2_hidden('#skF_3'(A_37,B_38),B_38)
      | ~ r1_tarski('#skF_4'(A_37,B_38),A_37)
      | k1_zfmisc_1(A_37) = B_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6255,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | ~ r1_tarski('#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)),k1_xboole_0)
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6239,c_42])).

tff(c_6304,plain,
    ( ~ r1_tarski('#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)),k1_xboole_0)
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6255])).

tff(c_6305,plain,(
    ~ r1_tarski('#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_6304])).

tff(c_6425,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6423,c_6305])).

tff(c_6429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6425])).

tff(c_6431,plain,(
    '#skF_3'(k1_xboole_0,k1_tarski(k1_xboole_0)) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_5383])).

tff(c_158,plain,(
    ! [A_80,B_81] :
      ( r1_tarski('#skF_3'(A_80,B_81),A_80)
      | r2_hidden('#skF_4'(A_80,B_81),B_81)
      | k1_zfmisc_1(A_80) = B_81 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_197,plain,(
    ! [A_94,A_95] :
      ( '#skF_4'(A_94,k1_tarski(A_95)) = A_95
      | r1_tarski('#skF_3'(A_94,k1_tarski(A_95)),A_94)
      | k1_zfmisc_1(A_94) = k1_tarski(A_95) ) ),
    inference(resolution,[status(thm)],[c_158,c_96])).

tff(c_202,plain,(
    ! [A_95] :
      ( '#skF_3'(k1_xboole_0,k1_tarski(A_95)) = k1_xboole_0
      | '#skF_4'(k1_xboole_0,k1_tarski(A_95)) = A_95
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_95) ) ),
    inference(resolution,[status(thm)],[c_197,c_4])).

tff(c_6444,plain,
    ( '#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_6431])).

tff(c_6447,plain,(
    '#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_6444])).

tff(c_131,plain,(
    ! [A_68,B_69] :
      ( r1_tarski('#skF_3'(A_68,B_69),A_68)
      | ~ r1_tarski('#skF_4'(A_68,B_69),A_68)
      | k1_zfmisc_1(A_68) = B_69 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_136,plain,(
    ! [B_69] :
      ( '#skF_3'(k1_xboole_0,B_69) = k1_xboole_0
      | ~ r1_tarski('#skF_4'(k1_xboole_0,B_69),k1_xboole_0)
      | k1_zfmisc_1(k1_xboole_0) = B_69 ) ),
    inference(resolution,[status(thm)],[c_131,c_4])).

tff(c_6554,plain,
    ( '#skF_3'(k1_xboole_0,k1_tarski(k1_xboole_0)) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6447,c_136])).

tff(c_6618,plain,
    ( '#skF_3'(k1_xboole_0,k1_tarski(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6554])).

tff(c_6620,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_6431,c_6618])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:50:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.56/2.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.56/2.31  
% 6.56/2.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.56/2.31  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 6.56/2.31  
% 6.56/2.31  %Foreground sorts:
% 6.56/2.31  
% 6.56/2.31  
% 6.56/2.31  %Background operators:
% 6.56/2.31  
% 6.56/2.31  
% 6.56/2.31  %Foreground operators:
% 6.56/2.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.56/2.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.56/2.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.56/2.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.56/2.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.56/2.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.56/2.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.56/2.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.56/2.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.56/2.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.56/2.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.56/2.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.56/2.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.56/2.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.56/2.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.56/2.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.56/2.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.56/2.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.56/2.31  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.56/2.31  
% 6.56/2.32  tff(f_63, negated_conjecture, ~(k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 6.56/2.32  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.56/2.32  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.56/2.32  tff(f_40, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 6.56/2.32  tff(f_61, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 6.56/2.32  tff(f_31, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 6.56/2.32  tff(c_50, plain, (k1_zfmisc_1(k1_xboole_0)!=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.56/2.32  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.56/2.32  tff(c_54, plain, (![A_47]: (k2_tarski(A_47, A_47)=k1_tarski(A_47))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.56/2.32  tff(c_8, plain, (![D_8, A_3]: (r2_hidden(D_8, k2_tarski(A_3, D_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.56/2.32  tff(c_60, plain, (![A_47]: (r2_hidden(A_47, k1_tarski(A_47)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_8])).
% 6.56/2.32  tff(c_48, plain, (![A_37, B_38]: (r1_tarski('#skF_3'(A_37, B_38), A_37) | r2_hidden('#skF_4'(A_37, B_38), B_38) | k1_zfmisc_1(A_37)=B_38)), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.56/2.32  tff(c_24, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.56/2.32  tff(c_18, plain, (![A_3, B_4, C_5]: ('#skF_1'(A_3, B_4, C_5)=B_4 | '#skF_1'(A_3, B_4, C_5)=A_3 | '#skF_2'(A_3, B_4, C_5)!=A_3 | k2_tarski(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.56/2.32  tff(c_302, plain, (![B_4, C_5]: ('#skF_2'(B_4, B_4, C_5)!=B_4 | k2_tarski(B_4, B_4)=C_5 | '#skF_1'(B_4, B_4, C_5)=B_4)), inference(factorization, [status(thm), theory('equality')], [c_18])).
% 6.56/2.32  tff(c_685, plain, (![B_1877, C_1878]: ('#skF_2'(B_1877, B_1877, C_1878)!=B_1877 | k1_tarski(B_1877)=C_1878 | '#skF_1'(B_1877, B_1877, C_1878)=B_1877)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_302])).
% 6.56/2.32  tff(c_93, plain, (![D_56, B_57, A_58]: (D_56=B_57 | D_56=A_58 | ~r2_hidden(D_56, k2_tarski(A_58, B_57)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.56/2.32  tff(c_96, plain, (![D_56, A_9]: (D_56=A_9 | D_56=A_9 | ~r2_hidden(D_56, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_93])).
% 6.56/2.32  tff(c_1567, plain, (![D_5690, B_5691, C_5692]: (D_5690=B_5691 | D_5690=B_5691 | ~r2_hidden(D_5690, C_5692) | '#skF_2'(B_5691, B_5691, C_5692)!=B_5691 | '#skF_1'(B_5691, B_5691, C_5692)=B_5691)), inference(superposition, [status(thm), theory('equality')], [c_685, c_96])).
% 6.56/2.32  tff(c_3663, plain, (![B_9277, A_9278, B_9279]: (B_9277='#skF_4'(A_9278, B_9279) | '#skF_2'(B_9277, B_9277, B_9279)!=B_9277 | '#skF_1'(B_9277, B_9277, B_9279)=B_9277 | r1_tarski('#skF_3'(A_9278, B_9279), A_9278) | k1_zfmisc_1(A_9278)=B_9279)), inference(resolution, [status(thm)], [c_48, c_1567])).
% 6.56/2.32  tff(c_4, plain, (![A_2]: (k1_xboole_0=A_2 | ~r1_tarski(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.56/2.32  tff(c_4625, plain, (![B_12476, B_12477]: ('#skF_3'(k1_xboole_0, B_12476)=k1_xboole_0 | B_12477='#skF_4'(k1_xboole_0, B_12476) | '#skF_2'(B_12477, B_12477, B_12476)!=B_12477 | '#skF_1'(B_12477, B_12477, B_12476)=B_12477 | k1_zfmisc_1(k1_xboole_0)=B_12476)), inference(resolution, [status(thm)], [c_3663, c_4])).
% 6.56/2.32  tff(c_5268, plain, (![B_12476, B_12477]: (k1_tarski(k1_xboole_0)!=B_12476 | '#skF_3'(k1_xboole_0, B_12476)=k1_xboole_0 | B_12477='#skF_4'(k1_xboole_0, B_12476) | '#skF_2'(B_12477, B_12477, B_12476)!=B_12477 | '#skF_1'(B_12477, B_12477, B_12476)=B_12477)), inference(superposition, [status(thm), theory('equality')], [c_4625, c_50])).
% 6.56/2.32  tff(c_5383, plain, (![B_12477]: ('#skF_3'(k1_xboole_0, k1_tarski(k1_xboole_0))=k1_xboole_0 | B_12477='#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0)) | '#skF_2'(B_12477, B_12477, k1_tarski(k1_xboole_0))!=B_12477 | '#skF_1'(B_12477, B_12477, k1_tarski(k1_xboole_0))=B_12477)), inference(reflexivity, [status(thm), theory('equality')], [c_5268])).
% 6.56/2.32  tff(c_6239, plain, ('#skF_3'(k1_xboole_0, k1_tarski(k1_xboole_0))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5383])).
% 6.56/2.32  tff(c_46, plain, (![A_37, B_38]: (~r2_hidden('#skF_3'(A_37, B_38), B_38) | r2_hidden('#skF_4'(A_37, B_38), B_38) | k1_zfmisc_1(A_37)=B_38)), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.56/2.32  tff(c_6253, plain, (~r2_hidden(k1_xboole_0, k1_tarski(k1_xboole_0)) | r2_hidden('#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0)), k1_tarski(k1_xboole_0)) | k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6239, c_46])).
% 6.56/2.32  tff(c_6301, plain, (r2_hidden('#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0)), k1_tarski(k1_xboole_0)) | k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_6253])).
% 6.56/2.32  tff(c_6302, plain, (r2_hidden('#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0)), k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_50, c_6301])).
% 6.56/2.32  tff(c_6423, plain, ('#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_6302, c_96])).
% 6.56/2.32  tff(c_42, plain, (![A_37, B_38]: (~r2_hidden('#skF_3'(A_37, B_38), B_38) | ~r1_tarski('#skF_4'(A_37, B_38), A_37) | k1_zfmisc_1(A_37)=B_38)), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.56/2.32  tff(c_6255, plain, (~r2_hidden(k1_xboole_0, k1_tarski(k1_xboole_0)) | ~r1_tarski('#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0)), k1_xboole_0) | k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6239, c_42])).
% 6.56/2.32  tff(c_6304, plain, (~r1_tarski('#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0)), k1_xboole_0) | k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_6255])).
% 6.56/2.32  tff(c_6305, plain, (~r1_tarski('#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0)), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_50, c_6304])).
% 6.56/2.32  tff(c_6425, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6423, c_6305])).
% 6.56/2.32  tff(c_6429, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_6425])).
% 6.56/2.32  tff(c_6431, plain, ('#skF_3'(k1_xboole_0, k1_tarski(k1_xboole_0))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_5383])).
% 6.56/2.32  tff(c_158, plain, (![A_80, B_81]: (r1_tarski('#skF_3'(A_80, B_81), A_80) | r2_hidden('#skF_4'(A_80, B_81), B_81) | k1_zfmisc_1(A_80)=B_81)), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.56/2.32  tff(c_197, plain, (![A_94, A_95]: ('#skF_4'(A_94, k1_tarski(A_95))=A_95 | r1_tarski('#skF_3'(A_94, k1_tarski(A_95)), A_94) | k1_zfmisc_1(A_94)=k1_tarski(A_95))), inference(resolution, [status(thm)], [c_158, c_96])).
% 6.56/2.32  tff(c_202, plain, (![A_95]: ('#skF_3'(k1_xboole_0, k1_tarski(A_95))=k1_xboole_0 | '#skF_4'(k1_xboole_0, k1_tarski(A_95))=A_95 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_95))), inference(resolution, [status(thm)], [c_197, c_4])).
% 6.56/2.32  tff(c_6444, plain, ('#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0))=k1_xboole_0 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_202, c_6431])).
% 6.56/2.32  tff(c_6447, plain, ('#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_50, c_6444])).
% 6.56/2.32  tff(c_131, plain, (![A_68, B_69]: (r1_tarski('#skF_3'(A_68, B_69), A_68) | ~r1_tarski('#skF_4'(A_68, B_69), A_68) | k1_zfmisc_1(A_68)=B_69)), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.56/2.32  tff(c_136, plain, (![B_69]: ('#skF_3'(k1_xboole_0, B_69)=k1_xboole_0 | ~r1_tarski('#skF_4'(k1_xboole_0, B_69), k1_xboole_0) | k1_zfmisc_1(k1_xboole_0)=B_69)), inference(resolution, [status(thm)], [c_131, c_4])).
% 6.56/2.32  tff(c_6554, plain, ('#skF_3'(k1_xboole_0, k1_tarski(k1_xboole_0))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_xboole_0) | k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6447, c_136])).
% 6.56/2.32  tff(c_6618, plain, ('#skF_3'(k1_xboole_0, k1_tarski(k1_xboole_0))=k1_xboole_0 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6554])).
% 6.56/2.32  tff(c_6620, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_6431, c_6618])).
% 6.56/2.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.56/2.32  
% 6.56/2.32  Inference rules
% 6.56/2.32  ----------------------
% 6.56/2.32  #Ref     : 1
% 6.56/2.32  #Sup     : 872
% 6.56/2.32  #Fact    : 18
% 6.56/2.32  #Define  : 0
% 6.56/2.32  #Split   : 1
% 6.56/2.32  #Chain   : 0
% 6.56/2.32  #Close   : 0
% 6.56/2.32  
% 6.56/2.32  Ordering : KBO
% 6.56/2.32  
% 6.56/2.32  Simplification rules
% 6.56/2.32  ----------------------
% 6.56/2.32  #Subsume      : 222
% 6.56/2.32  #Demod        : 145
% 6.56/2.32  #Tautology    : 222
% 6.56/2.32  #SimpNegUnit  : 10
% 6.56/2.32  #BackRed      : 2
% 6.56/2.32  
% 6.56/2.32  #Partial instantiations: 4788
% 6.56/2.32  #Strategies tried      : 1
% 6.56/2.32  
% 6.56/2.32  Timing (in seconds)
% 6.56/2.32  ----------------------
% 6.56/2.33  Preprocessing        : 0.31
% 6.56/2.33  Parsing              : 0.16
% 6.56/2.33  CNF conversion       : 0.02
% 6.56/2.33  Main loop            : 1.22
% 6.56/2.33  Inferencing          : 0.60
% 6.56/2.33  Reduction            : 0.21
% 6.56/2.33  Demodulation         : 0.14
% 6.56/2.33  BG Simplification    : 0.06
% 6.56/2.33  Subsumption          : 0.29
% 6.56/2.33  Abstraction          : 0.07
% 6.56/2.33  MUC search           : 0.00
% 6.56/2.33  Cooper               : 0.00
% 6.56/2.33  Total                : 1.56
% 6.56/2.33  Index Insertion      : 0.00
% 6.56/2.33  Index Deletion       : 0.00
% 6.56/2.33  Index Matching       : 0.00
% 6.56/2.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
