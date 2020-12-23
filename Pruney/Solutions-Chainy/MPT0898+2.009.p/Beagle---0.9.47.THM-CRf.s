%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:51 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 487 expanded)
%              Number of leaves         :   15 ( 155 expanded)
%              Depth                    :   12
%              Number of atoms          :  127 (1119 expanded)
%              Number of equality atoms :  120 (1112 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_zfmisc_1(A,A,A,A) = k4_zfmisc_1(B,B,B,B)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_mcart_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

tff(c_20,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [B_11,C_12,D_13] : k4_zfmisc_1(k1_xboole_0,B_11,C_12,D_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_148,plain,(
    ! [A_33,B_34,C_35,D_36] : k2_zfmisc_1(k3_zfmisc_1(A_33,B_34,C_35),D_36) = k4_zfmisc_1(A_33,B_34,C_35,D_36) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_relat_1(k2_zfmisc_1(A_1,B_2)) = B_2
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_244,plain,(
    ! [A_51,B_52,C_53,D_54] :
      ( k2_relat_1(k4_zfmisc_1(A_51,B_52,C_53,D_54)) = D_54
      | k1_xboole_0 = D_54
      | k3_zfmisc_1(A_51,B_52,C_53) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_2])).

tff(c_259,plain,(
    ! [D_13,B_11,C_12] :
      ( k2_relat_1(k1_xboole_0) = D_13
      | k1_xboole_0 = D_13
      | k3_zfmisc_1(k1_xboole_0,B_11,C_12) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_244])).

tff(c_330,plain,(
    ! [B_58,C_59] : k3_zfmisc_1(k1_xboole_0,B_58,C_59) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_259])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8,D_9] : k2_zfmisc_1(k3_zfmisc_1(A_6,B_7,C_8),D_9) = k4_zfmisc_1(A_6,B_7,C_8,D_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_341,plain,(
    ! [B_58,C_59,D_9] : k4_zfmisc_1(k1_xboole_0,B_58,C_59,D_9) = k2_zfmisc_1(k1_xboole_0,D_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_8])).

tff(c_345,plain,(
    ! [D_9] : k2_zfmisc_1(k1_xboole_0,D_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_341])).

tff(c_22,plain,(
    k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_202,plain,(
    ! [A_44,B_45,C_46,D_47] :
      ( k4_zfmisc_1(A_44,B_45,C_46,D_47) != k1_xboole_0
      | k1_xboole_0 = D_47
      | k1_xboole_0 = C_46
      | k1_xboole_0 = B_45
      | k1_xboole_0 = A_44 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_205,plain,
    ( k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_202])).

tff(c_240,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_271,plain,(
    ! [B_55,C_56] : k3_zfmisc_1(k1_xboole_0,B_55,C_56) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_259])).

tff(c_282,plain,(
    ! [B_55,C_56,D_9] : k4_zfmisc_1(k1_xboole_0,B_55,C_56,D_9) = k2_zfmisc_1(k1_xboole_0,D_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_8])).

tff(c_286,plain,(
    ! [D_9] : k2_zfmisc_1(k1_xboole_0,D_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_282])).

tff(c_253,plain,
    ( k2_relat_1(k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1')) = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_244])).

tff(c_270,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_253])).

tff(c_320,plain,(
    ! [D_9] : k4_zfmisc_1('#skF_2','#skF_2','#skF_2',D_9) = k2_zfmisc_1(k1_xboole_0,D_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_8])).

tff(c_323,plain,(
    ! [D_9] : k4_zfmisc_1('#skF_2','#skF_2','#skF_2',D_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_320])).

tff(c_325,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_22])).

tff(c_327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_325])).

tff(c_328,plain,
    ( k1_xboole_0 = '#skF_2'
    | k2_relat_1(k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_407,plain,(
    k2_relat_1(k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1')) = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_328])).

tff(c_157,plain,(
    ! [A_33,B_34,C_35,D_36] :
      ( k2_relat_1(k4_zfmisc_1(A_33,B_34,C_35,D_36)) = D_36
      | k1_xboole_0 = D_36
      | k3_zfmisc_1(A_33,B_34,C_35) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_2])).

tff(c_411,plain,
    ( '#skF_2' = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_157])).

tff(c_417,plain,
    ( k1_xboole_0 = '#skF_1'
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_411])).

tff(c_420,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_417])).

tff(c_433,plain,(
    ! [D_9] : k4_zfmisc_1('#skF_1','#skF_1','#skF_1',D_9) = k2_zfmisc_1(k1_xboole_0,D_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_8])).

tff(c_437,plain,(
    ! [D_9] : k4_zfmisc_1('#skF_1','#skF_1','#skF_1',D_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_433])).

tff(c_443,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_240])).

tff(c_444,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_417])).

tff(c_269,plain,(
    ! [B_11,C_12] : k3_zfmisc_1(k1_xboole_0,B_11,C_12) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_259])).

tff(c_448,plain,(
    ! [B_11,C_12] : k3_zfmisc_1('#skF_1',B_11,C_12) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_444,c_269])).

tff(c_445,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_417])).

tff(c_493,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_445])).

tff(c_496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_493])).

tff(c_497,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_328])).

tff(c_501,plain,(
    ! [B_11,C_12] : k3_zfmisc_1('#skF_2',B_11,C_12) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_497,c_269])).

tff(c_329,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_499,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_329])).

tff(c_533,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_499])).

tff(c_644,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_259])).

tff(c_541,plain,(
    ! [D_72] :
      ( k2_relat_1(k1_xboole_0) = D_72
      | k1_xboole_0 = D_72 ) ),
    inference(splitRight,[status(thm)],[c_259])).

tff(c_645,plain,(
    ! [D_72] :
      ( D_72 = '#skF_2'
      | k1_xboole_0 = D_72
      | k1_xboole_0 = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_644,c_541])).

tff(c_708,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_645])).

tff(c_719,plain,(
    ! [B_11,C_12,D_13] : k4_zfmisc_1('#skF_2',B_11,C_12,D_13) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_708,c_708,c_18])).

tff(c_963,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_22])).

tff(c_712,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_708,c_240])).

tff(c_1118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_963,c_712])).

tff(c_1129,plain,
    ( '#skF_2' = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_645])).

tff(c_1119,plain,(
    ! [D_72] :
      ( D_72 = '#skF_2'
      | k1_xboole_0 = D_72 ) ),
    inference(splitRight,[status(thm)],[c_645])).

tff(c_1130,plain,(
    ! [D_72] :
      ( D_72 = '#skF_2'
      | D_72 = '#skF_1'
      | '#skF_2' = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1129,c_1119])).

tff(c_1361,plain,(
    ! [D_966] :
      ( D_966 = '#skF_2'
      | D_966 = '#skF_1' ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_1130])).

tff(c_1120,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_645])).

tff(c_1493,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1361,c_1120])).

tff(c_1256,plain,
    ( '#skF_2' = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_645])).

tff(c_1257,plain,(
    ! [B_11,C_12,D_13] :
      ( k4_zfmisc_1('#skF_1',B_11,C_12,D_13) = k1_xboole_0
      | '#skF_2' = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1256,c_18])).

tff(c_1313,plain,(
    ! [B_11,C_12,D_13] : k4_zfmisc_1('#skF_1',B_11,C_12,D_13) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_1257])).

tff(c_1628,plain,(
    ! [B_11,C_12,D_13] : k4_zfmisc_1('#skF_1',B_11,C_12,D_13) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1493,c_1313])).

tff(c_1128,plain,(
    ! [D_690] :
      ( D_690 = '#skF_2'
      | k1_xboole_0 = D_690 ) ),
    inference(splitRight,[status(thm)],[c_645])).

tff(c_1298,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1128,c_240])).

tff(c_1730,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1628,c_1298])).

tff(c_1731,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_1730])).

tff(c_1733,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_10,plain,(
    ! [A_10,B_11,C_12,D_13] :
      ( k4_zfmisc_1(A_10,B_11,C_12,D_13) != k1_xboole_0
      | k1_xboole_0 = D_13
      | k1_xboole_0 = C_12
      | k1_xboole_0 = B_11
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1741,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1733,c_10])).

tff(c_1732,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_1766,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1741,c_1741,c_1741,c_1741,c_1732])).

tff(c_1767,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_20,c_20,c_20,c_1766])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:12:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.50  
% 3.07/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.50  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.07/1.50  
% 3.07/1.50  %Foreground sorts:
% 3.07/1.50  
% 3.07/1.50  
% 3.07/1.50  %Background operators:
% 3.07/1.50  
% 3.07/1.50  
% 3.07/1.50  %Foreground operators:
% 3.07/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.07/1.50  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.07/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.07/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.07/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.07/1.50  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.07/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.07/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.07/1.50  
% 3.27/1.52  tff(f_61, negated_conjecture, ~(![A, B]: ((k4_zfmisc_1(A, A, A, A) = k4_zfmisc_1(B, B, B, B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_mcart_1)).
% 3.27/1.52  tff(f_56, axiom, (![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_mcart_1)).
% 3.27/1.52  tff(f_41, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 3.27/1.52  tff(f_37, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 3.27/1.52  tff(c_20, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.27/1.52  tff(c_18, plain, (![B_11, C_12, D_13]: (k4_zfmisc_1(k1_xboole_0, B_11, C_12, D_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.27/1.52  tff(c_148, plain, (![A_33, B_34, C_35, D_36]: (k2_zfmisc_1(k3_zfmisc_1(A_33, B_34, C_35), D_36)=k4_zfmisc_1(A_33, B_34, C_35, D_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.27/1.52  tff(c_2, plain, (![A_1, B_2]: (k2_relat_1(k2_zfmisc_1(A_1, B_2))=B_2 | k1_xboole_0=B_2 | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.27/1.52  tff(c_244, plain, (![A_51, B_52, C_53, D_54]: (k2_relat_1(k4_zfmisc_1(A_51, B_52, C_53, D_54))=D_54 | k1_xboole_0=D_54 | k3_zfmisc_1(A_51, B_52, C_53)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_148, c_2])).
% 3.27/1.52  tff(c_259, plain, (![D_13, B_11, C_12]: (k2_relat_1(k1_xboole_0)=D_13 | k1_xboole_0=D_13 | k3_zfmisc_1(k1_xboole_0, B_11, C_12)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_244])).
% 3.27/1.52  tff(c_330, plain, (![B_58, C_59]: (k3_zfmisc_1(k1_xboole_0, B_58, C_59)=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_259])).
% 3.27/1.52  tff(c_8, plain, (![A_6, B_7, C_8, D_9]: (k2_zfmisc_1(k3_zfmisc_1(A_6, B_7, C_8), D_9)=k4_zfmisc_1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.27/1.52  tff(c_341, plain, (![B_58, C_59, D_9]: (k4_zfmisc_1(k1_xboole_0, B_58, C_59, D_9)=k2_zfmisc_1(k1_xboole_0, D_9))), inference(superposition, [status(thm), theory('equality')], [c_330, c_8])).
% 3.27/1.52  tff(c_345, plain, (![D_9]: (k2_zfmisc_1(k1_xboole_0, D_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_341])).
% 3.27/1.52  tff(c_22, plain, (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.27/1.52  tff(c_202, plain, (![A_44, B_45, C_46, D_47]: (k4_zfmisc_1(A_44, B_45, C_46, D_47)!=k1_xboole_0 | k1_xboole_0=D_47 | k1_xboole_0=C_46 | k1_xboole_0=B_45 | k1_xboole_0=A_44)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.27/1.52  tff(c_205, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_22, c_202])).
% 3.27/1.52  tff(c_240, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_205])).
% 3.27/1.52  tff(c_271, plain, (![B_55, C_56]: (k3_zfmisc_1(k1_xboole_0, B_55, C_56)=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_259])).
% 3.27/1.52  tff(c_282, plain, (![B_55, C_56, D_9]: (k4_zfmisc_1(k1_xboole_0, B_55, C_56, D_9)=k2_zfmisc_1(k1_xboole_0, D_9))), inference(superposition, [status(thm), theory('equality')], [c_271, c_8])).
% 3.27/1.52  tff(c_286, plain, (![D_9]: (k2_zfmisc_1(k1_xboole_0, D_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_282])).
% 3.27/1.52  tff(c_253, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))='#skF_2' | k1_xboole_0='#skF_2' | k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_22, c_244])).
% 3.27/1.52  tff(c_270, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_253])).
% 3.27/1.52  tff(c_320, plain, (![D_9]: (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', D_9)=k2_zfmisc_1(k1_xboole_0, D_9))), inference(superposition, [status(thm), theory('equality')], [c_270, c_8])).
% 3.27/1.52  tff(c_323, plain, (![D_9]: (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', D_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_286, c_320])).
% 3.27/1.52  tff(c_325, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_323, c_22])).
% 3.27/1.52  tff(c_327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_240, c_325])).
% 3.27/1.52  tff(c_328, plain, (k1_xboole_0='#skF_2' | k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))='#skF_2'), inference(splitRight, [status(thm)], [c_253])).
% 3.27/1.52  tff(c_407, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))='#skF_2'), inference(splitLeft, [status(thm)], [c_328])).
% 3.27/1.52  tff(c_157, plain, (![A_33, B_34, C_35, D_36]: (k2_relat_1(k4_zfmisc_1(A_33, B_34, C_35, D_36))=D_36 | k1_xboole_0=D_36 | k3_zfmisc_1(A_33, B_34, C_35)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_148, c_2])).
% 3.27/1.52  tff(c_411, plain, ('#skF_2'='#skF_1' | k1_xboole_0='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_407, c_157])).
% 3.27/1.52  tff(c_417, plain, (k1_xboole_0='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_20, c_411])).
% 3.27/1.52  tff(c_420, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_417])).
% 3.27/1.52  tff(c_433, plain, (![D_9]: (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', D_9)=k2_zfmisc_1(k1_xboole_0, D_9))), inference(superposition, [status(thm), theory('equality')], [c_420, c_8])).
% 3.27/1.52  tff(c_437, plain, (![D_9]: (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', D_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_345, c_433])).
% 3.27/1.52  tff(c_443, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_437, c_240])).
% 3.27/1.52  tff(c_444, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_417])).
% 3.27/1.52  tff(c_269, plain, (![B_11, C_12]: (k3_zfmisc_1(k1_xboole_0, B_11, C_12)=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_259])).
% 3.27/1.52  tff(c_448, plain, (![B_11, C_12]: (k3_zfmisc_1('#skF_1', B_11, C_12)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_444, c_444, c_269])).
% 3.27/1.52  tff(c_445, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_417])).
% 3.27/1.52  tff(c_493, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_444, c_445])).
% 3.27/1.52  tff(c_496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_448, c_493])).
% 3.27/1.52  tff(c_497, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_328])).
% 3.27/1.52  tff(c_501, plain, (![B_11, C_12]: (k3_zfmisc_1('#skF_2', B_11, C_12)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_497, c_497, c_269])).
% 3.27/1.52  tff(c_329, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_253])).
% 3.27/1.52  tff(c_499, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_497, c_329])).
% 3.27/1.52  tff(c_533, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_501, c_499])).
% 3.27/1.52  tff(c_644, plain, (k2_relat_1(k1_xboole_0)='#skF_2' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_259])).
% 3.27/1.52  tff(c_541, plain, (![D_72]: (k2_relat_1(k1_xboole_0)=D_72 | k1_xboole_0=D_72)), inference(splitRight, [status(thm)], [c_259])).
% 3.27/1.52  tff(c_645, plain, (![D_72]: (D_72='#skF_2' | k1_xboole_0=D_72 | k1_xboole_0='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_644, c_541])).
% 3.27/1.52  tff(c_708, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_645])).
% 3.27/1.52  tff(c_719, plain, (![B_11, C_12, D_13]: (k4_zfmisc_1('#skF_2', B_11, C_12, D_13)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_708, c_708, c_18])).
% 3.27/1.52  tff(c_963, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_719, c_22])).
% 3.27/1.52  tff(c_712, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_708, c_240])).
% 3.27/1.52  tff(c_1118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_963, c_712])).
% 3.27/1.52  tff(c_1129, plain, ('#skF_2'='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_645])).
% 3.27/1.52  tff(c_1119, plain, (![D_72]: (D_72='#skF_2' | k1_xboole_0=D_72)), inference(splitRight, [status(thm)], [c_645])).
% 3.27/1.52  tff(c_1130, plain, (![D_72]: (D_72='#skF_2' | D_72='#skF_1' | '#skF_2'='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1129, c_1119])).
% 3.27/1.52  tff(c_1361, plain, (![D_966]: (D_966='#skF_2' | D_966='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_20, c_1130])).
% 3.27/1.52  tff(c_1120, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_645])).
% 3.27/1.52  tff(c_1493, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1361, c_1120])).
% 3.27/1.52  tff(c_1256, plain, ('#skF_2'='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_645])).
% 3.27/1.52  tff(c_1257, plain, (![B_11, C_12, D_13]: (k4_zfmisc_1('#skF_1', B_11, C_12, D_13)=k1_xboole_0 | '#skF_2'='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1256, c_18])).
% 3.27/1.52  tff(c_1313, plain, (![B_11, C_12, D_13]: (k4_zfmisc_1('#skF_1', B_11, C_12, D_13)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_20, c_1257])).
% 3.27/1.52  tff(c_1628, plain, (![B_11, C_12, D_13]: (k4_zfmisc_1('#skF_1', B_11, C_12, D_13)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1493, c_1313])).
% 3.27/1.52  tff(c_1128, plain, (![D_690]: (D_690='#skF_2' | k1_xboole_0=D_690)), inference(splitRight, [status(thm)], [c_645])).
% 3.27/1.52  tff(c_1298, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1128, c_240])).
% 3.27/1.52  tff(c_1730, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1628, c_1298])).
% 3.27/1.52  tff(c_1731, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_1730])).
% 3.27/1.52  tff(c_1733, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_205])).
% 3.27/1.52  tff(c_10, plain, (![A_10, B_11, C_12, D_13]: (k4_zfmisc_1(A_10, B_11, C_12, D_13)!=k1_xboole_0 | k1_xboole_0=D_13 | k1_xboole_0=C_12 | k1_xboole_0=B_11 | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.27/1.52  tff(c_1741, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1733, c_10])).
% 3.27/1.52  tff(c_1732, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_205])).
% 3.27/1.52  tff(c_1766, plain, ('#skF_2'='#skF_1' | '#skF_2'='#skF_1' | '#skF_2'='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1741, c_1741, c_1741, c_1741, c_1732])).
% 3.27/1.52  tff(c_1767, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_20, c_20, c_20, c_1766])).
% 3.27/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.52  
% 3.27/1.52  Inference rules
% 3.27/1.52  ----------------------
% 3.27/1.52  #Ref     : 0
% 3.27/1.52  #Sup     : 410
% 3.27/1.52  #Fact    : 5
% 3.27/1.52  #Define  : 0
% 3.27/1.52  #Split   : 7
% 3.27/1.52  #Chain   : 0
% 3.27/1.52  #Close   : 0
% 3.27/1.52  
% 3.27/1.52  Ordering : KBO
% 3.27/1.52  
% 3.27/1.52  Simplification rules
% 3.27/1.52  ----------------------
% 3.27/1.52  #Subsume      : 67
% 3.27/1.52  #Demod        : 295
% 3.27/1.52  #Tautology    : 230
% 3.27/1.52  #SimpNegUnit  : 54
% 3.27/1.52  #BackRed      : 79
% 3.27/1.52  
% 3.27/1.52  #Partial instantiations: 268
% 3.27/1.52  #Strategies tried      : 1
% 3.27/1.52  
% 3.27/1.52  Timing (in seconds)
% 3.27/1.52  ----------------------
% 3.27/1.52  Preprocessing        : 0.28
% 3.27/1.52  Parsing              : 0.15
% 3.27/1.52  CNF conversion       : 0.02
% 3.27/1.52  Main loop            : 0.47
% 3.27/1.52  Inferencing          : 0.20
% 3.27/1.52  Reduction            : 0.14
% 3.27/1.52  Demodulation         : 0.10
% 3.27/1.52  BG Simplification    : 0.03
% 3.27/1.52  Subsumption          : 0.07
% 3.27/1.52  Abstraction          : 0.03
% 3.27/1.52  MUC search           : 0.00
% 3.27/1.52  Cooper               : 0.00
% 3.27/1.52  Total                : 0.78
% 3.27/1.52  Index Insertion      : 0.00
% 3.27/1.52  Index Deletion       : 0.00
% 3.27/1.52  Index Matching       : 0.00
% 3.27/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
