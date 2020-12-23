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
% DateTime   : Thu Dec  3 09:56:36 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 149 expanded)
%              Number of leaves         :   42 (  67 expanded)
%              Depth                    :   12
%              Number of atoms          :  126 ( 235 expanded)
%              Number of equality atoms :   27 (  42 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,C)
            <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_95,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_75,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_41,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(A,C)
        & r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_48,plain,(
    ! [A_56] : ~ v1_xboole_0(k1_zfmisc_1(A_56)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1398,plain,(
    ! [B_215,A_216] :
      ( r2_hidden(B_215,A_216)
      | ~ m1_subset_1(B_215,A_216)
      | v1_xboole_0(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_36,plain,(
    ! [A_51] : k3_tarski(k1_zfmisc_1(A_51)) = A_51 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1335,plain,(
    ! [A_195,B_196] :
      ( r1_tarski(A_195,k3_tarski(B_196))
      | ~ r2_hidden(A_195,B_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1341,plain,(
    ! [A_195,A_51] :
      ( r1_tarski(A_195,A_51)
      | ~ r2_hidden(A_195,k1_zfmisc_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1335])).

tff(c_1405,plain,(
    ! [B_215,A_51] :
      ( r1_tarski(B_215,A_51)
      | ~ m1_subset_1(B_215,k1_zfmisc_1(A_51))
      | v1_xboole_0(k1_zfmisc_1(A_51)) ) ),
    inference(resolution,[status(thm)],[c_1398,c_1341])).

tff(c_1410,plain,(
    ! [B_217,A_218] :
      ( r1_tarski(B_217,A_218)
      | ~ m1_subset_1(B_217,k1_zfmisc_1(A_218)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1405])).

tff(c_1422,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_1410])).

tff(c_56,plain,
    ( ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3'))
    | ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_124,plain,(
    ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_398,plain,(
    ! [A_105,B_106] :
      ( k4_xboole_0(A_105,B_106) = k3_subset_1(A_105,B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_410,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_398])).

tff(c_253,plain,(
    ! [B_96,A_97] :
      ( r2_hidden(B_96,A_97)
      | ~ m1_subset_1(B_96,A_97)
      | v1_xboole_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_126,plain,(
    ! [A_75,B_76] :
      ( r1_tarski(A_75,k3_tarski(B_76))
      | ~ r2_hidden(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_132,plain,(
    ! [A_75,A_51] :
      ( r1_tarski(A_75,A_51)
      | ~ r2_hidden(A_75,k1_zfmisc_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_126])).

tff(c_257,plain,(
    ! [B_96,A_51] :
      ( r1_tarski(B_96,A_51)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_51))
      | v1_xboole_0(k1_zfmisc_1(A_51)) ) ),
    inference(resolution,[status(thm)],[c_253,c_132])).

tff(c_266,plain,(
    ! [B_98,A_99] :
      ( r1_tarski(B_98,A_99)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_99)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_257])).

tff(c_278,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_266])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_283,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_278,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_300,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_2])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_367,plain,(
    k5_xboole_0('#skF_1','#skF_2') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_6])).

tff(c_436,plain,(
    k5_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_367])).

tff(c_134,plain,(
    ! [A_77,B_78] : r1_xboole_0(k3_xboole_0(A_77,B_78),k5_xboole_0(A_77,B_78)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_143,plain,(
    ! [A_1,B_2] : r1_xboole_0(k3_xboole_0(A_1,B_2),k5_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_134])).

tff(c_294,plain,(
    r1_xboole_0('#skF_2',k5_xboole_0('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_143])).

tff(c_437,plain,(
    r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_294])).

tff(c_14,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_209,plain,(
    ! [A_93,B_94] : k5_xboole_0(A_93,k3_xboole_0(A_93,B_94)) = k4_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_227,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k5_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_209])).

tff(c_237,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_227])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_62,plain,
    ( r1_xboole_0('#skF_2','#skF_3')
    | r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_191,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_62])).

tff(c_1181,plain,(
    ! [C_188,A_189,B_190] :
      ( r1_tarski(C_188,k3_subset_1(A_189,B_190))
      | ~ r1_tarski(B_190,k3_subset_1(A_189,C_188))
      | ~ m1_subset_1(C_188,k1_zfmisc_1(A_189))
      | ~ m1_subset_1(B_190,k1_zfmisc_1(A_189)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1187,plain,
    ( r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_191,c_1181])).

tff(c_1196,plain,(
    r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1187])).

tff(c_1205,plain,(
    k3_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1196,c_10])).

tff(c_1218,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1205,c_6])).

tff(c_1228,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_1218])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16] :
      ( ~ r1_xboole_0(A_14,k4_xboole_0(B_15,C_16))
      | ~ r1_xboole_0(A_14,C_16)
      | r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1236,plain,(
    ! [A_14] :
      ( ~ r1_xboole_0(A_14,k1_xboole_0)
      | ~ r1_xboole_0(A_14,k3_subset_1('#skF_1','#skF_2'))
      | r1_xboole_0(A_14,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1228,c_16])).

tff(c_1316,plain,(
    ! [A_192] :
      ( ~ r1_xboole_0(A_192,k3_subset_1('#skF_1','#skF_2'))
      | r1_xboole_0(A_192,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1236])).

tff(c_1319,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_437,c_1316])).

tff(c_1323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_1319])).

tff(c_1325,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1573,plain,(
    ! [A_225,B_226] :
      ( k4_xboole_0(A_225,B_226) = k3_subset_1(A_225,B_226)
      | ~ m1_subset_1(B_226,k1_zfmisc_1(A_225)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1586,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_1573])).

tff(c_1630,plain,(
    ! [A_227,B_228,C_229] :
      ( r1_tarski(A_227,k4_xboole_0(B_228,C_229))
      | ~ r1_xboole_0(A_227,C_229)
      | ~ r1_tarski(A_227,B_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1691,plain,(
    ! [A_232] :
      ( r1_tarski(A_232,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_xboole_0(A_232,'#skF_3')
      | ~ r1_tarski(A_232,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1586,c_1630])).

tff(c_1324,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1697,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_3')
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_1691,c_1324])).

tff(c_1702,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1422,c_1325,c_1697])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.51/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.63  
% 3.51/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.63  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.51/1.63  
% 3.51/1.63  %Foreground sorts:
% 3.51/1.63  
% 3.51/1.63  
% 3.51/1.63  %Background operators:
% 3.51/1.63  
% 3.51/1.63  
% 3.51/1.63  %Foreground operators:
% 3.51/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.51/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.51/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.51/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.51/1.63  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.51/1.63  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.51/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.51/1.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.51/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.51/1.63  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.51/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.51/1.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.51/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.51/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.51/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.51/1.63  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.51/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.51/1.63  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.51/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.51/1.63  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.51/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.51/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.51/1.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.51/1.63  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.51/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.51/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.51/1.63  
% 3.89/1.65  tff(f_114, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 3.89/1.65  tff(f_95, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.89/1.65  tff(f_88, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.89/1.65  tff(f_75, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 3.89/1.65  tff(f_71, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.89/1.65  tff(f_92, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.89/1.65  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.89/1.65  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.89/1.65  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.89/1.65  tff(f_29, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 3.89/1.65  tff(f_41, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.89/1.65  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.89/1.65  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.89/1.65  tff(f_104, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 3.89/1.65  tff(f_49, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_xboole_1)).
% 3.89/1.65  tff(f_55, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 3.89/1.65  tff(c_54, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.89/1.65  tff(c_48, plain, (![A_56]: (~v1_xboole_0(k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.89/1.65  tff(c_1398, plain, (![B_215, A_216]: (r2_hidden(B_215, A_216) | ~m1_subset_1(B_215, A_216) | v1_xboole_0(A_216))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.89/1.65  tff(c_36, plain, (![A_51]: (k3_tarski(k1_zfmisc_1(A_51))=A_51)), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.89/1.65  tff(c_1335, plain, (![A_195, B_196]: (r1_tarski(A_195, k3_tarski(B_196)) | ~r2_hidden(A_195, B_196))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.89/1.65  tff(c_1341, plain, (![A_195, A_51]: (r1_tarski(A_195, A_51) | ~r2_hidden(A_195, k1_zfmisc_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1335])).
% 3.89/1.65  tff(c_1405, plain, (![B_215, A_51]: (r1_tarski(B_215, A_51) | ~m1_subset_1(B_215, k1_zfmisc_1(A_51)) | v1_xboole_0(k1_zfmisc_1(A_51)))), inference(resolution, [status(thm)], [c_1398, c_1341])).
% 3.89/1.65  tff(c_1410, plain, (![B_217, A_218]: (r1_tarski(B_217, A_218) | ~m1_subset_1(B_217, k1_zfmisc_1(A_218)))), inference(negUnitSimplification, [status(thm)], [c_48, c_1405])).
% 3.89/1.65  tff(c_1422, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_1410])).
% 3.89/1.65  tff(c_56, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3')) | ~r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.89/1.65  tff(c_124, plain, (~r1_xboole_0('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 3.89/1.65  tff(c_398, plain, (![A_105, B_106]: (k4_xboole_0(A_105, B_106)=k3_subset_1(A_105, B_106) | ~m1_subset_1(B_106, k1_zfmisc_1(A_105)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.89/1.65  tff(c_410, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_398])).
% 3.89/1.65  tff(c_253, plain, (![B_96, A_97]: (r2_hidden(B_96, A_97) | ~m1_subset_1(B_96, A_97) | v1_xboole_0(A_97))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.89/1.65  tff(c_126, plain, (![A_75, B_76]: (r1_tarski(A_75, k3_tarski(B_76)) | ~r2_hidden(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.89/1.65  tff(c_132, plain, (![A_75, A_51]: (r1_tarski(A_75, A_51) | ~r2_hidden(A_75, k1_zfmisc_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_126])).
% 3.89/1.65  tff(c_257, plain, (![B_96, A_51]: (r1_tarski(B_96, A_51) | ~m1_subset_1(B_96, k1_zfmisc_1(A_51)) | v1_xboole_0(k1_zfmisc_1(A_51)))), inference(resolution, [status(thm)], [c_253, c_132])).
% 3.89/1.65  tff(c_266, plain, (![B_98, A_99]: (r1_tarski(B_98, A_99) | ~m1_subset_1(B_98, k1_zfmisc_1(A_99)))), inference(negUnitSimplification, [status(thm)], [c_48, c_257])).
% 3.89/1.65  tff(c_278, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_266])).
% 3.89/1.65  tff(c_10, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.89/1.65  tff(c_283, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_278, c_10])).
% 3.89/1.65  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.89/1.65  tff(c_300, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_283, c_2])).
% 3.89/1.65  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.89/1.65  tff(c_367, plain, (k5_xboole_0('#skF_1', '#skF_2')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_300, c_6])).
% 3.89/1.65  tff(c_436, plain, (k5_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_410, c_367])).
% 3.89/1.65  tff(c_134, plain, (![A_77, B_78]: (r1_xboole_0(k3_xboole_0(A_77, B_78), k5_xboole_0(A_77, B_78)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.89/1.65  tff(c_143, plain, (![A_1, B_2]: (r1_xboole_0(k3_xboole_0(A_1, B_2), k5_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_134])).
% 3.89/1.65  tff(c_294, plain, (r1_xboole_0('#skF_2', k5_xboole_0('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_283, c_143])).
% 3.89/1.65  tff(c_437, plain, (r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_436, c_294])).
% 3.89/1.65  tff(c_14, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.89/1.65  tff(c_12, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.89/1.65  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, k2_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.89/1.65  tff(c_209, plain, (![A_93, B_94]: (k5_xboole_0(A_93, k3_xboole_0(A_93, B_94))=k4_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.89/1.65  tff(c_227, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k5_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_209])).
% 3.89/1.65  tff(c_237, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_227])).
% 3.89/1.65  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.89/1.65  tff(c_62, plain, (r1_xboole_0('#skF_2', '#skF_3') | r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.89/1.65  tff(c_191, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_124, c_62])).
% 3.89/1.65  tff(c_1181, plain, (![C_188, A_189, B_190]: (r1_tarski(C_188, k3_subset_1(A_189, B_190)) | ~r1_tarski(B_190, k3_subset_1(A_189, C_188)) | ~m1_subset_1(C_188, k1_zfmisc_1(A_189)) | ~m1_subset_1(B_190, k1_zfmisc_1(A_189)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.89/1.65  tff(c_1187, plain, (r1_tarski('#skF_3', k3_subset_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_191, c_1181])).
% 3.89/1.65  tff(c_1196, plain, (r1_tarski('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1187])).
% 3.89/1.65  tff(c_1205, plain, (k3_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2'))='#skF_3'), inference(resolution, [status(thm)], [c_1196, c_10])).
% 3.89/1.65  tff(c_1218, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1205, c_6])).
% 3.89/1.65  tff(c_1228, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_237, c_1218])).
% 3.89/1.65  tff(c_16, plain, (![A_14, B_15, C_16]: (~r1_xboole_0(A_14, k4_xboole_0(B_15, C_16)) | ~r1_xboole_0(A_14, C_16) | r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.89/1.65  tff(c_1236, plain, (![A_14]: (~r1_xboole_0(A_14, k1_xboole_0) | ~r1_xboole_0(A_14, k3_subset_1('#skF_1', '#skF_2')) | r1_xboole_0(A_14, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1228, c_16])).
% 3.89/1.65  tff(c_1316, plain, (![A_192]: (~r1_xboole_0(A_192, k3_subset_1('#skF_1', '#skF_2')) | r1_xboole_0(A_192, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1236])).
% 3.89/1.65  tff(c_1319, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_437, c_1316])).
% 3.89/1.65  tff(c_1323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_1319])).
% 3.89/1.65  tff(c_1325, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_56])).
% 3.89/1.65  tff(c_1573, plain, (![A_225, B_226]: (k4_xboole_0(A_225, B_226)=k3_subset_1(A_225, B_226) | ~m1_subset_1(B_226, k1_zfmisc_1(A_225)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.89/1.65  tff(c_1586, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_1573])).
% 3.89/1.65  tff(c_1630, plain, (![A_227, B_228, C_229]: (r1_tarski(A_227, k4_xboole_0(B_228, C_229)) | ~r1_xboole_0(A_227, C_229) | ~r1_tarski(A_227, B_228))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.89/1.65  tff(c_1691, plain, (![A_232]: (r1_tarski(A_232, k3_subset_1('#skF_1', '#skF_3')) | ~r1_xboole_0(A_232, '#skF_3') | ~r1_tarski(A_232, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1586, c_1630])).
% 3.89/1.65  tff(c_1324, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_56])).
% 3.89/1.65  tff(c_1697, plain, (~r1_xboole_0('#skF_2', '#skF_3') | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_1691, c_1324])).
% 3.89/1.65  tff(c_1702, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1422, c_1325, c_1697])).
% 3.89/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/1.65  
% 3.89/1.65  Inference rules
% 3.89/1.65  ----------------------
% 3.89/1.65  #Ref     : 0
% 3.89/1.65  #Sup     : 419
% 3.89/1.65  #Fact    : 0
% 3.89/1.65  #Define  : 0
% 3.89/1.65  #Split   : 4
% 3.89/1.65  #Chain   : 0
% 3.89/1.65  #Close   : 0
% 3.89/1.65  
% 3.89/1.65  Ordering : KBO
% 3.89/1.65  
% 3.89/1.65  Simplification rules
% 3.89/1.65  ----------------------
% 3.89/1.65  #Subsume      : 28
% 3.89/1.65  #Demod        : 192
% 3.89/1.65  #Tautology    : 213
% 3.89/1.65  #SimpNegUnit  : 11
% 3.89/1.65  #BackRed      : 5
% 3.89/1.65  
% 3.89/1.65  #Partial instantiations: 0
% 3.89/1.65  #Strategies tried      : 1
% 3.89/1.65  
% 3.89/1.65  Timing (in seconds)
% 3.89/1.65  ----------------------
% 3.89/1.65  Preprocessing        : 0.35
% 3.89/1.65  Parsing              : 0.19
% 3.89/1.65  CNF conversion       : 0.02
% 3.89/1.65  Main loop            : 0.54
% 3.89/1.65  Inferencing          : 0.20
% 3.89/1.65  Reduction            : 0.19
% 3.89/1.65  Demodulation         : 0.14
% 3.89/1.65  BG Simplification    : 0.03
% 3.89/1.65  Subsumption          : 0.08
% 3.89/1.65  Abstraction          : 0.02
% 3.89/1.65  MUC search           : 0.00
% 3.89/1.65  Cooper               : 0.00
% 3.89/1.65  Total                : 0.92
% 3.89/1.65  Index Insertion      : 0.00
% 3.89/1.65  Index Deletion       : 0.00
% 3.89/1.65  Index Matching       : 0.00
% 3.89/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
