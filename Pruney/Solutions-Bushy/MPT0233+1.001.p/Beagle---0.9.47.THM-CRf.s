%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0233+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:57 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   52 (  89 expanded)
%              Number of leaves         :   20 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   71 ( 183 expanded)
%              Number of equality atoms :   57 ( 148 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > k2_tarski > #nlpp > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_25,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : ~ v1_xboole_0(k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ~ ( k2_tarski(A,B) = k2_tarski(C,D)
        & A != C
        & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( k1_tarski(A) = k2_tarski(B,C)
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_zfmisc_1)).

tff(c_22,plain,(
    '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_25])).

tff(c_4,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_27,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_26,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_43,plain,(
    ! [B_30,C_31,A_32] :
      ( k2_tarski(B_30,C_31) = A_32
      | k1_tarski(C_31) = A_32
      | k1_tarski(B_30) = A_32
      | k1_xboole_0 = A_32
      | ~ r1_tarski(A_32,k2_tarski(B_30,C_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_59,plain,
    ( k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_2')
    | k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_4')
    | k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3')
    | k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_43])).

tff(c_68,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_59])).

tff(c_6,plain,(
    ! [A_1,B_2] : ~ v1_xboole_0(k2_tarski(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_99,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_6])).

tff(c_107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_99])).

tff(c_108,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3')
    | k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_4')
    | k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_110,plain,(
    k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_18,plain,(
    ! [D_9,A_6,C_8,B_7] :
      ( D_9 = A_6
      | C_8 = A_6
      | k2_tarski(C_8,D_9) != k2_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_122,plain,(
    ! [D_9,C_8] :
      ( D_9 = '#skF_3'
      | C_8 = '#skF_3'
      | k2_tarski(C_8,D_9) != k2_tarski('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_18])).

tff(c_160,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_122])).

tff(c_161,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_160])).

tff(c_119,plain,(
    ! [A_6,B_7] :
      ( A_6 = '#skF_4'
      | A_6 = '#skF_3'
      | k2_tarski(A_6,B_7) != k2_tarski('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_18])).

tff(c_183,plain,(
    ! [A_6,B_7] :
      ( A_6 = '#skF_4'
      | A_6 = '#skF_3'
      | k2_tarski(A_6,B_7) != k2_tarski('#skF_1','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_119])).

tff(c_186,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_183])).

tff(c_188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_186])).

tff(c_189,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_4')
    | k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_191,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_20,plain,(
    ! [B_11,A_10,C_12] :
      ( B_11 = A_10
      | k2_tarski(B_11,C_12) != k1_tarski(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_208,plain,(
    ! [A_10] :
      ( A_10 = '#skF_1'
      | k1_tarski(A_10) != k1_tarski('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_20])).

tff(c_234,plain,(
    '#skF_3' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_208])).

tff(c_236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_234])).

tff(c_237,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_255,plain,(
    ! [A_10] :
      ( A_10 = '#skF_1'
      | k1_tarski(A_10) != k1_tarski('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_20])).

tff(c_282,plain,(
    '#skF_1' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_255])).

tff(c_284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_282])).

%------------------------------------------------------------------------------
