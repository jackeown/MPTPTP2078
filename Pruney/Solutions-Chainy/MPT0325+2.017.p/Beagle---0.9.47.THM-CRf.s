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
% DateTime   : Thu Dec  3 09:54:23 EST 2020

% Result     : Theorem 8.38s
% Output     : CNFRefutation 8.38s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 256 expanded)
%              Number of leaves         :   25 (  91 expanded)
%              Depth                    :   11
%              Number of atoms          :  133 ( 472 expanded)
%              Number of equality atoms :   60 ( 153 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | ( A = C
          & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_12,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,
    ( ~ r1_tarski('#skF_4','#skF_6')
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_83,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_282,plain,(
    ! [A_57,B_58] :
      ( r2_hidden('#skF_1'(A_57,B_58),k3_xboole_0(A_57,B_58))
      | r1_xboole_0(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_104,plain,(
    ! [A_41,B_42,C_43] :
      ( ~ r1_xboole_0(A_41,B_42)
      | ~ r2_hidden(C_43,k3_xboole_0(A_41,B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_111,plain,(
    ! [A_1,B_2,C_43] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_43,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_104])).

tff(c_303,plain,(
    ! [B_59,A_60] :
      ( ~ r1_xboole_0(B_59,A_60)
      | r1_xboole_0(A_60,B_59) ) ),
    inference(resolution,[status(thm)],[c_282,c_111])).

tff(c_309,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_303])).

tff(c_22,plain,(
    ! [A_20,B_21,C_22,D_23] :
      ( ~ r1_xboole_0(A_20,B_21)
      | r1_xboole_0(k2_zfmisc_1(A_20,C_22),k2_zfmisc_1(B_21,D_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_91,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(A_39,B_40) = A_39
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_101,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_91])).

tff(c_264,plain,(
    ! [A_54,B_55,C_56] :
      ( ~ r1_xboole_0(A_54,B_55)
      | ~ r2_hidden(C_56,k3_xboole_0(B_55,A_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_104])).

tff(c_267,plain,(
    ! [C_56] :
      ( ~ r1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'),k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(C_56,k2_zfmisc_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_264])).

tff(c_331,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_267])).

tff(c_343,plain,(
    ~ r1_xboole_0('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_331])).

tff(c_352,plain,(
    k3_xboole_0('#skF_3','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_309,c_343])).

tff(c_355,plain,(
    ! [C_65,D_66,A_67,B_68] :
      ( ~ r1_xboole_0(C_65,D_66)
      | r1_xboole_0(k2_zfmisc_1(A_67,C_65),k2_zfmisc_1(B_68,D_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_367,plain,(
    ~ r1_xboole_0('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_355,c_331])).

tff(c_377,plain,(
    k3_xboole_0('#skF_4','#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_309,c_367])).

tff(c_1144,plain,(
    ! [A_89,C_90,B_91,D_92] : k3_xboole_0(k2_zfmisc_1(A_89,C_90),k2_zfmisc_1(B_91,D_92)) = k2_zfmisc_1(k3_xboole_0(A_89,B_91),k3_xboole_0(C_90,D_92)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1177,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_3','#skF_5'),k3_xboole_0('#skF_4','#skF_6')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1144,c_101])).

tff(c_26,plain,(
    ! [C_26,A_24,B_25,D_27] :
      ( C_26 = A_24
      | k1_xboole_0 = B_25
      | k1_xboole_0 = A_24
      | k2_zfmisc_1(C_26,D_27) != k2_zfmisc_1(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1257,plain,(
    ! [C_26,D_27] :
      ( k3_xboole_0('#skF_3','#skF_5') = C_26
      | k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0
      | k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0
      | k2_zfmisc_1(C_26,D_27) != k2_zfmisc_1('#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1177,c_26])).

tff(c_1275,plain,(
    ! [C_26,D_27] :
      ( k3_xboole_0('#skF_3','#skF_5') = C_26
      | k2_zfmisc_1(C_26,D_27) != k2_zfmisc_1('#skF_3','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_352,c_377,c_1257])).

tff(c_6959,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1275])).

tff(c_34,plain,(
    ! [B_30,A_31] : k3_xboole_0(B_30,A_31) = k3_xboole_0(A_31,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_12,B_13] : r1_tarski(k3_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_49,plain,(
    ! [B_30,A_31] : r1_tarski(k3_xboole_0(B_30,A_31),A_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_14])).

tff(c_7194,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6959,c_49])).

tff(c_7230,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_7194])).

tff(c_7233,plain,(
    ! [C_265] : ~ r2_hidden(C_265,k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_267])).

tff(c_7237,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_7233])).

tff(c_7241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_7237])).

tff(c_7242,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_7243,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_7246,plain,(
    ! [A_269,B_270] :
      ( k3_xboole_0(A_269,B_270) = A_269
      | ~ r1_tarski(A_269,B_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_7260,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_7243,c_7246])).

tff(c_7310,plain,(
    ! [A_273,B_274,C_275] :
      ( ~ r1_xboole_0(A_273,B_274)
      | ~ r2_hidden(C_275,k3_xboole_0(A_273,B_274)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_7319,plain,(
    ! [C_275] :
      ( ~ r1_xboole_0('#skF_3','#skF_5')
      | ~ r2_hidden(C_275,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7260,c_7310])).

tff(c_7351,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_7319])).

tff(c_7354,plain,(
    k3_xboole_0('#skF_3','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_7351])).

tff(c_7356,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7260,c_7354])).

tff(c_7398,plain,(
    ! [C_283,D_284,A_285,B_286] :
      ( ~ r1_xboole_0(C_283,D_284)
      | r1_xboole_0(k2_zfmisc_1(A_285,C_283),k2_zfmisc_1(B_286,D_284)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_7259,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_7246])).

tff(c_7316,plain,(
    ! [C_275] :
      ( ~ r1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(C_275,k2_zfmisc_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7259,c_7310])).

tff(c_7357,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_7316])).

tff(c_7408,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_7398,c_7357])).

tff(c_7413,plain,(
    k3_xboole_0('#skF_4','#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_7408])).

tff(c_8579,plain,(
    ! [A_323,C_324,B_325,D_326] : k3_xboole_0(k2_zfmisc_1(A_323,C_324),k2_zfmisc_1(B_325,D_326)) = k2_zfmisc_1(k3_xboole_0(A_323,B_325),k3_xboole_0(C_324,D_326)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8632,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_3','#skF_5'),k3_xboole_0('#skF_4','#skF_6')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8579,c_7259])).

tff(c_8674,plain,(
    k2_zfmisc_1('#skF_3',k3_xboole_0('#skF_4','#skF_6')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7260,c_8632])).

tff(c_24,plain,(
    ! [D_27,B_25,A_24,C_26] :
      ( D_27 = B_25
      | k1_xboole_0 = B_25
      | k1_xboole_0 = A_24
      | k2_zfmisc_1(C_26,D_27) != k2_zfmisc_1(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8696,plain,(
    ! [D_27,C_26] :
      ( k3_xboole_0('#skF_4','#skF_6') = D_27
      | k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0
      | k1_xboole_0 = '#skF_3'
      | k2_zfmisc_1(C_26,D_27) != k2_zfmisc_1('#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8674,c_24])).

tff(c_8714,plain,(
    ! [D_27,C_26] :
      ( k3_xboole_0('#skF_4','#skF_6') = D_27
      | k2_zfmisc_1(C_26,D_27) != k2_zfmisc_1('#skF_3','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_7356,c_7413,c_8696])).

tff(c_13403,plain,(
    k3_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8714])).

tff(c_13607,plain,(
    r1_tarski('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_13403,c_49])).

tff(c_13643,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7242,c_13607])).

tff(c_13646,plain,(
    ! [C_479] : ~ r2_hidden(C_479,k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7316])).

tff(c_13650,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_13646])).

tff(c_13654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_13650])).

tff(c_13662,plain,(
    ! [C_484] : ~ r2_hidden(C_484,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_7319])).

tff(c_13667,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_12,c_13662])).

tff(c_13671,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13667,c_30])).

tff(c_13670,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | A_10 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13667,c_12])).

tff(c_13656,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_7319])).

tff(c_13754,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_7316])).

tff(c_13806,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_13754])).

tff(c_13813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13656,c_13806])).

tff(c_13859,plain,(
    ! [C_499] : ~ r2_hidden(C_499,k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7316])).

tff(c_13863,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_13670,c_13859])).

tff(c_13867,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13671,c_13863])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n008.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 20:00:00 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.38/2.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.38/2.92  
% 8.38/2.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.38/2.92  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 8.38/2.92  
% 8.38/2.92  %Foreground sorts:
% 8.38/2.92  
% 8.38/2.92  
% 8.38/2.92  %Background operators:
% 8.38/2.92  
% 8.38/2.92  
% 8.38/2.92  %Foreground operators:
% 8.38/2.92  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.38/2.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.38/2.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.38/2.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.38/2.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.38/2.92  tff('#skF_5', type, '#skF_5': $i).
% 8.38/2.92  tff('#skF_6', type, '#skF_6': $i).
% 8.38/2.92  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.38/2.92  tff('#skF_3', type, '#skF_3': $i).
% 8.38/2.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.38/2.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.38/2.92  tff('#skF_4', type, '#skF_4': $i).
% 8.38/2.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.38/2.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.38/2.92  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.38/2.92  
% 8.38/2.93  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.38/2.93  tff(f_86, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 8.38/2.93  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.38/2.93  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.38/2.93  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.38/2.93  tff(f_67, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 8.38/2.93  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.38/2.93  tff(f_61, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 8.38/2.93  tff(f_77, axiom, (![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 8.38/2.93  tff(f_55, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 8.38/2.93  tff(c_12, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.38/2.93  tff(c_30, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.38/2.93  tff(c_28, plain, (~r1_tarski('#skF_4', '#skF_6') | ~r1_tarski('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.38/2.93  tff(c_83, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_28])).
% 8.38/2.93  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.38/2.93  tff(c_282, plain, (![A_57, B_58]: (r2_hidden('#skF_1'(A_57, B_58), k3_xboole_0(A_57, B_58)) | r1_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.38/2.93  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.38/2.93  tff(c_104, plain, (![A_41, B_42, C_43]: (~r1_xboole_0(A_41, B_42) | ~r2_hidden(C_43, k3_xboole_0(A_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.38/2.93  tff(c_111, plain, (![A_1, B_2, C_43]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_43, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_104])).
% 8.38/2.93  tff(c_303, plain, (![B_59, A_60]: (~r1_xboole_0(B_59, A_60) | r1_xboole_0(A_60, B_59))), inference(resolution, [status(thm)], [c_282, c_111])).
% 8.38/2.93  tff(c_309, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_303])).
% 8.38/2.93  tff(c_22, plain, (![A_20, B_21, C_22, D_23]: (~r1_xboole_0(A_20, B_21) | r1_xboole_0(k2_zfmisc_1(A_20, C_22), k2_zfmisc_1(B_21, D_23)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.38/2.93  tff(c_32, plain, (r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.38/2.93  tff(c_91, plain, (![A_39, B_40]: (k3_xboole_0(A_39, B_40)=A_39 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.38/2.93  tff(c_101, plain, (k3_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_91])).
% 8.38/2.93  tff(c_264, plain, (![A_54, B_55, C_56]: (~r1_xboole_0(A_54, B_55) | ~r2_hidden(C_56, k3_xboole_0(B_55, A_54)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_104])).
% 8.38/2.93  tff(c_267, plain, (![C_56]: (~r1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(C_56, k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_101, c_264])).
% 8.38/2.93  tff(c_331, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_267])).
% 8.38/2.93  tff(c_343, plain, (~r1_xboole_0('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_331])).
% 8.38/2.93  tff(c_352, plain, (k3_xboole_0('#skF_3', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_309, c_343])).
% 8.38/2.93  tff(c_355, plain, (![C_65, D_66, A_67, B_68]: (~r1_xboole_0(C_65, D_66) | r1_xboole_0(k2_zfmisc_1(A_67, C_65), k2_zfmisc_1(B_68, D_66)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.38/2.93  tff(c_367, plain, (~r1_xboole_0('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_355, c_331])).
% 8.38/2.93  tff(c_377, plain, (k3_xboole_0('#skF_4', '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_309, c_367])).
% 8.38/2.93  tff(c_1144, plain, (![A_89, C_90, B_91, D_92]: (k3_xboole_0(k2_zfmisc_1(A_89, C_90), k2_zfmisc_1(B_91, D_92))=k2_zfmisc_1(k3_xboole_0(A_89, B_91), k3_xboole_0(C_90, D_92)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.38/2.93  tff(c_1177, plain, (k2_zfmisc_1(k3_xboole_0('#skF_3', '#skF_5'), k3_xboole_0('#skF_4', '#skF_6'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1144, c_101])).
% 8.38/2.93  tff(c_26, plain, (![C_26, A_24, B_25, D_27]: (C_26=A_24 | k1_xboole_0=B_25 | k1_xboole_0=A_24 | k2_zfmisc_1(C_26, D_27)!=k2_zfmisc_1(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.38/2.93  tff(c_1257, plain, (![C_26, D_27]: (k3_xboole_0('#skF_3', '#skF_5')=C_26 | k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0 | k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0 | k2_zfmisc_1(C_26, D_27)!=k2_zfmisc_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1177, c_26])).
% 8.38/2.93  tff(c_1275, plain, (![C_26, D_27]: (k3_xboole_0('#skF_3', '#skF_5')=C_26 | k2_zfmisc_1(C_26, D_27)!=k2_zfmisc_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_352, c_377, c_1257])).
% 8.38/2.93  tff(c_6959, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_1275])).
% 8.38/2.93  tff(c_34, plain, (![B_30, A_31]: (k3_xboole_0(B_30, A_31)=k3_xboole_0(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.38/2.93  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(k3_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.38/2.93  tff(c_49, plain, (![B_30, A_31]: (r1_tarski(k3_xboole_0(B_30, A_31), A_31))), inference(superposition, [status(thm), theory('equality')], [c_34, c_14])).
% 8.38/2.93  tff(c_7194, plain, (r1_tarski('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6959, c_49])).
% 8.38/2.93  tff(c_7230, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_7194])).
% 8.38/2.93  tff(c_7233, plain, (![C_265]: (~r2_hidden(C_265, k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_267])).
% 8.38/2.93  tff(c_7237, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_7233])).
% 8.38/2.93  tff(c_7241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_7237])).
% 8.38/2.93  tff(c_7242, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_28])).
% 8.38/2.93  tff(c_7243, plain, (r1_tarski('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_28])).
% 8.38/2.93  tff(c_7246, plain, (![A_269, B_270]: (k3_xboole_0(A_269, B_270)=A_269 | ~r1_tarski(A_269, B_270))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.38/2.93  tff(c_7260, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(resolution, [status(thm)], [c_7243, c_7246])).
% 8.38/2.93  tff(c_7310, plain, (![A_273, B_274, C_275]: (~r1_xboole_0(A_273, B_274) | ~r2_hidden(C_275, k3_xboole_0(A_273, B_274)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.38/2.93  tff(c_7319, plain, (![C_275]: (~r1_xboole_0('#skF_3', '#skF_5') | ~r2_hidden(C_275, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_7260, c_7310])).
% 8.38/2.93  tff(c_7351, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_7319])).
% 8.38/2.93  tff(c_7354, plain, (k3_xboole_0('#skF_3', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_7351])).
% 8.38/2.93  tff(c_7356, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7260, c_7354])).
% 8.38/2.93  tff(c_7398, plain, (![C_283, D_284, A_285, B_286]: (~r1_xboole_0(C_283, D_284) | r1_xboole_0(k2_zfmisc_1(A_285, C_283), k2_zfmisc_1(B_286, D_284)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.38/2.93  tff(c_7259, plain, (k3_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_7246])).
% 8.38/2.93  tff(c_7316, plain, (![C_275]: (~r1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(C_275, k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_7259, c_7310])).
% 8.38/2.93  tff(c_7357, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_7316])).
% 8.38/2.93  tff(c_7408, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_7398, c_7357])).
% 8.38/2.93  tff(c_7413, plain, (k3_xboole_0('#skF_4', '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_7408])).
% 8.38/2.93  tff(c_8579, plain, (![A_323, C_324, B_325, D_326]: (k3_xboole_0(k2_zfmisc_1(A_323, C_324), k2_zfmisc_1(B_325, D_326))=k2_zfmisc_1(k3_xboole_0(A_323, B_325), k3_xboole_0(C_324, D_326)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.38/2.93  tff(c_8632, plain, (k2_zfmisc_1(k3_xboole_0('#skF_3', '#skF_5'), k3_xboole_0('#skF_4', '#skF_6'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8579, c_7259])).
% 8.38/2.93  tff(c_8674, plain, (k2_zfmisc_1('#skF_3', k3_xboole_0('#skF_4', '#skF_6'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7260, c_8632])).
% 8.38/2.93  tff(c_24, plain, (![D_27, B_25, A_24, C_26]: (D_27=B_25 | k1_xboole_0=B_25 | k1_xboole_0=A_24 | k2_zfmisc_1(C_26, D_27)!=k2_zfmisc_1(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.38/2.93  tff(c_8696, plain, (![D_27, C_26]: (k3_xboole_0('#skF_4', '#skF_6')=D_27 | k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0 | k1_xboole_0='#skF_3' | k2_zfmisc_1(C_26, D_27)!=k2_zfmisc_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8674, c_24])).
% 8.38/2.93  tff(c_8714, plain, (![D_27, C_26]: (k3_xboole_0('#skF_4', '#skF_6')=D_27 | k2_zfmisc_1(C_26, D_27)!=k2_zfmisc_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_7356, c_7413, c_8696])).
% 8.38/2.93  tff(c_13403, plain, (k3_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_8714])).
% 8.38/2.93  tff(c_13607, plain, (r1_tarski('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_13403, c_49])).
% 8.38/2.93  tff(c_13643, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7242, c_13607])).
% 8.38/2.93  tff(c_13646, plain, (![C_479]: (~r2_hidden(C_479, k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_7316])).
% 8.38/2.93  tff(c_13650, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_13646])).
% 8.38/2.93  tff(c_13654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_13650])).
% 8.38/2.93  tff(c_13662, plain, (![C_484]: (~r2_hidden(C_484, '#skF_3'))), inference(splitRight, [status(thm)], [c_7319])).
% 8.38/2.93  tff(c_13667, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_12, c_13662])).
% 8.38/2.93  tff(c_13671, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13667, c_30])).
% 8.38/2.93  tff(c_13670, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | A_10='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13667, c_12])).
% 8.38/2.93  tff(c_13656, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_7319])).
% 8.38/2.93  tff(c_13754, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_7316])).
% 8.38/2.93  tff(c_13806, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_22, c_13754])).
% 8.38/2.93  tff(c_13813, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13656, c_13806])).
% 8.38/2.93  tff(c_13859, plain, (![C_499]: (~r2_hidden(C_499, k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_7316])).
% 8.38/2.93  tff(c_13863, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_13670, c_13859])).
% 8.38/2.93  tff(c_13867, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13671, c_13863])).
% 8.38/2.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.38/2.93  
% 8.38/2.93  Inference rules
% 8.38/2.93  ----------------------
% 8.38/2.93  #Ref     : 9
% 8.38/2.93  #Sup     : 4089
% 8.38/2.93  #Fact    : 0
% 8.38/2.93  #Define  : 0
% 8.38/2.93  #Split   : 9
% 8.38/2.93  #Chain   : 0
% 8.38/2.93  #Close   : 0
% 8.38/2.93  
% 8.38/2.93  Ordering : KBO
% 8.38/2.93  
% 8.38/2.93  Simplification rules
% 8.38/2.93  ----------------------
% 8.38/2.93  #Subsume      : 923
% 8.38/2.93  #Demod        : 2025
% 8.38/2.93  #Tautology    : 999
% 8.38/2.93  #SimpNegUnit  : 107
% 8.38/2.93  #BackRed      : 13
% 8.38/2.93  
% 8.38/2.93  #Partial instantiations: 0
% 8.38/2.93  #Strategies tried      : 1
% 8.38/2.93  
% 8.38/2.93  Timing (in seconds)
% 8.38/2.93  ----------------------
% 8.38/2.94  Preprocessing        : 0.30
% 8.38/2.94  Parsing              : 0.16
% 8.38/2.94  CNF conversion       : 0.02
% 8.38/2.94  Main loop            : 1.92
% 8.38/2.94  Inferencing          : 0.47
% 8.38/2.94  Reduction            : 0.86
% 8.38/2.94  Demodulation         : 0.70
% 8.38/2.94  BG Simplification    : 0.06
% 8.38/2.94  Subsumption          : 0.40
% 8.38/2.94  Abstraction          : 0.08
% 8.38/2.94  MUC search           : 0.00
% 8.38/2.94  Cooper               : 0.00
% 8.38/2.94  Total                : 2.25
% 8.38/2.94  Index Insertion      : 0.00
% 8.38/2.94  Index Deletion       : 0.00
% 8.38/2.94  Index Matching       : 0.00
% 8.38/2.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
