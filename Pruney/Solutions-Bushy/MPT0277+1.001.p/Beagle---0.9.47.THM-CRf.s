%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0277+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:02 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 614 expanded)
%              Number of leaves         :   18 ( 173 expanded)
%              Depth                    :    9
%              Number of atoms          :  246 (1623 expanded)
%              Number of equality atoms :  196 (1513 expanded)
%              Maximal formula depth    :   11 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(A,k2_tarski(B,C)) = k1_xboole_0
      <=> ~ ( A != k1_xboole_0
            & A != k1_tarski(B)
            & A != k1_tarski(C)
            & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(c_30,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_93,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_26,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_102,plain,(
    k1_tarski('#skF_5') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_22,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k1_tarski('#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_101,plain,(
    k1_tarski('#skF_6') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_18,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_103,plain,(
    k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_36,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_131,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | k4_xboole_0(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_105,plain,(
    ! [B_26,C_27,A_28] :
      ( k2_tarski(B_26,C_27) = A_28
      | k1_tarski(C_27) = A_28
      | k1_tarski(B_26) = A_28
      | k1_xboole_0 = A_28
      | ~ r1_tarski(A_28,k2_tarski(B_26,C_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_136,plain,(
    ! [B_29,C_30,A_31] :
      ( k2_tarski(B_29,C_30) = A_31
      | k1_tarski(C_30) = A_31
      | k1_tarski(B_29) = A_31
      | k1_xboole_0 = A_31
      | k4_xboole_0(A_31,k2_tarski(B_29,C_30)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_105])).

tff(c_139,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_136])).

tff(c_156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_102,c_101,c_103,c_139])).

tff(c_157,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_159,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_34,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_104,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_160,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_104])).

tff(c_4,plain,(
    ! [B_2,C_3] : r1_tarski(k2_tarski(B_2,C_3),k2_tarski(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_179,plain,(
    r1_tarski('#skF_1',k2_tarski('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_4])).

tff(c_196,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_179])).

tff(c_14,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = k1_xboole_0
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_202,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_196,c_14])).

tff(c_217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_202])).

tff(c_218,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_220,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_16,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_231,plain,(
    ! [A_6] : k4_xboole_0('#skF_1',A_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_220,c_16])).

tff(c_223,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_104])).

tff(c_245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_223])).

tff(c_246,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_248,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_6,plain,(
    ! [C_3,B_2] : r1_tarski(k1_tarski(C_3),k2_tarski(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_276,plain,(
    ! [B_36] : r1_tarski('#skF_1',k2_tarski(B_36,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_6])).

tff(c_286,plain,(
    ! [B_36] : k4_xboole_0('#skF_1',k2_tarski(B_36,'#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_276,c_14])).

tff(c_296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_104])).

tff(c_297,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_8,plain,(
    ! [B_2,C_3] : r1_tarski(k1_tarski(B_2),k2_tarski(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_49,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_67,plain,(
    ! [B_2,C_3] : k4_xboole_0(k1_tarski(B_2),k2_tarski(B_2,C_3)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_49])).

tff(c_305,plain,(
    ! [C_3] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_3)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_67])).

tff(c_339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_104])).

tff(c_340,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_350,plain,(
    ! [B_40,C_41,A_42] :
      ( k2_tarski(B_40,C_41) = A_42
      | k1_tarski(C_41) = A_42
      | k1_tarski(B_40) = A_42
      | k1_xboole_0 = A_42
      | ~ r1_tarski(A_42,k2_tarski(B_40,C_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_377,plain,(
    ! [B_43,C_44,A_45] :
      ( k2_tarski(B_43,C_44) = A_45
      | k1_tarski(C_44) = A_45
      | k1_tarski(B_43) = A_45
      | k1_xboole_0 = A_45
      | k4_xboole_0(A_45,k2_tarski(B_43,C_44)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_350])).

tff(c_383,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_377])).

tff(c_401,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_102,c_101,c_103,c_383])).

tff(c_403,plain,(
    k2_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_20,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_475,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_20])).

tff(c_476,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_475])).

tff(c_489,plain,(
    ! [A_6] : k4_xboole_0('#skF_1',A_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_476,c_16])).

tff(c_447,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k4_xboole_0('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_34])).

tff(c_448,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_447])).

tff(c_479,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_448])).

tff(c_519,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_479])).

tff(c_520,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_475])).

tff(c_522,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_520])).

tff(c_523,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_448])).

tff(c_66,plain,(
    ! [B_2,C_3] : k4_xboole_0(k2_tarski(B_2,C_3),k2_tarski(B_2,C_3)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_49])).

tff(c_527,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_66])).

tff(c_553,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_527])).

tff(c_612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_523,c_553])).

tff(c_613,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_520])).

tff(c_617,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_613])).

tff(c_634,plain,(
    ! [C_52] : r1_tarski('#skF_1',k2_tarski('#skF_2',C_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_617,c_8])).

tff(c_638,plain,(
    ! [C_52] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_52)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_634,c_14])).

tff(c_646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_638,c_448])).

tff(c_647,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_613])).

tff(c_68,plain,(
    ! [C_3,B_2] : k4_xboole_0(k1_tarski(C_3),k2_tarski(B_2,C_3)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_49])).

tff(c_652,plain,(
    ! [B_2] : k4_xboole_0('#skF_1',k2_tarski(B_2,'#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_68])).

tff(c_677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_448])).

tff(c_679,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_447])).

tff(c_402,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_711,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_402])).

tff(c_713,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_28,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_766,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_713,c_28])).

tff(c_767,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_766])).

tff(c_778,plain,(
    ! [A_6] : k4_xboole_0('#skF_1',A_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_767,c_767,c_16])).

tff(c_712,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_770,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_767,c_712])).

tff(c_793,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_770])).

tff(c_794,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_766])).

tff(c_796,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_794])).

tff(c_797,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_712])).

tff(c_813,plain,(
    r1_tarski('#skF_1',k2_tarski('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_796,c_4])).

tff(c_829,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_813])).

tff(c_834,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_829,c_14])).

tff(c_838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_797,c_834])).

tff(c_839,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_794])).

tff(c_841,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_839])).

tff(c_859,plain,(
    ! [C_63] : r1_tarski('#skF_1',k2_tarski('#skF_2',C_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_841,c_8])).

tff(c_863,plain,(
    ! [C_63] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_63)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_859,c_14])).

tff(c_871,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_863,c_712])).

tff(c_872,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_839])).

tff(c_890,plain,(
    ! [B_65] : r1_tarski('#skF_1',k2_tarski(B_65,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_872,c_6])).

tff(c_894,plain,(
    ! [B_65] : k4_xboole_0('#skF_1',k2_tarski(B_65,'#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_890,c_14])).

tff(c_902,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_894,c_712])).

tff(c_904,plain,(
    k1_tarski('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_24,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_958,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_904,c_24])).

tff(c_959,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_958])).

tff(c_970,plain,(
    ! [A_6] : k4_xboole_0('#skF_1',A_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_959,c_959,c_16])).

tff(c_903,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_962,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_959,c_903])).

tff(c_984,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_962])).

tff(c_985,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_958])).

tff(c_988,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_985])).

tff(c_989,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_988,c_903])).

tff(c_1005,plain,(
    r1_tarski('#skF_1',k2_tarski('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_988,c_4])).

tff(c_1021,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_988,c_1005])).

tff(c_1027,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1021,c_14])).

tff(c_1044,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_989,c_1027])).

tff(c_1045,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_985])).

tff(c_1047,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1045])).

tff(c_1102,plain,(
    ! [C_77] : r1_tarski('#skF_1',k2_tarski('#skF_2',C_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1047,c_8])).

tff(c_1112,plain,(
    ! [C_77] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_77)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1102,c_14])).

tff(c_1126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1112,c_903])).

tff(c_1127,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1045])).

tff(c_1152,plain,(
    ! [B_80] : r1_tarski('#skF_1',k2_tarski(B_80,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1127,c_6])).

tff(c_1156,plain,(
    ! [B_80] : k4_xboole_0('#skF_1',k2_tarski(B_80,'#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1152,c_14])).

tff(c_1216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1156,c_903])).

tff(c_1218,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1224,plain,(
    ! [A_6] : k4_xboole_0('#skF_4',A_6) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1218,c_1218,c_16])).

tff(c_32,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1300,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1218,c_1218,c_32])).

tff(c_1301,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1300])).

tff(c_1217,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1239,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1218,c_1217])).

tff(c_1302,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_2','#skF_3')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1301,c_1239])).

tff(c_1305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1224,c_1302])).

tff(c_1306,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1300])).

tff(c_1308,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1306])).

tff(c_1309,plain,(
    k4_xboole_0('#skF_1','#skF_1') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1308,c_1239])).

tff(c_1330,plain,(
    r1_tarski(k2_tarski('#skF_2','#skF_3'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1308,c_4])).

tff(c_1342,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1308,c_1330])).

tff(c_1221,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = '#skF_4'
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1218,c_14])).

tff(c_1354,plain,(
    k4_xboole_0('#skF_1','#skF_1') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1342,c_1221])).

tff(c_1366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1309,c_1354])).

tff(c_1367,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1306])).

tff(c_1372,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1367])).

tff(c_1389,plain,(
    ! [C_98] : r1_tarski('#skF_1',k2_tarski('#skF_2',C_98)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1372,c_8])).

tff(c_1393,plain,(
    ! [C_98] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_98)) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1389,c_1221])).

tff(c_1403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1393,c_1239])).

tff(c_1404,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1367])).

tff(c_1429,plain,(
    ! [B_101] : r1_tarski('#skF_1',k2_tarski(B_101,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1404,c_6])).

tff(c_1433,plain,(
    ! [B_101] : k4_xboole_0('#skF_1',k2_tarski(B_101,'#skF_3')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1429,c_1221])).

tff(c_1443,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1433,c_1239])).

%------------------------------------------------------------------------------
