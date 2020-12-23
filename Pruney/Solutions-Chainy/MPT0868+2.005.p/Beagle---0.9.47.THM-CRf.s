%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:24 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 271 expanded)
%              Number of leaves         :   26 (  99 expanded)
%              Depth                    :    9
%              Number of atoms          :  135 ( 641 expanded)
%              Number of equality atoms :   73 ( 256 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => ( C != k1_mcart_1(C)
                  & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_mcart_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_372,plain,(
    ! [B_82,A_83] :
      ( v1_xboole_0(B_82)
      | ~ m1_subset_1(B_82,A_83)
      | ~ v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_380,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_372])).

tff(c_381,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_380])).

tff(c_28,plain,(
    ! [A_16,B_17] : k2_mcart_1(k4_tarski(A_16,B_17)) = B_17 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_20,plain,(
    ! [B_12,C_13] : k2_mcart_1(k4_tarski(B_12,C_13)) != k4_tarski(B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_38,plain,(
    ! [B_12,C_13] : k4_tarski(B_12,C_13) != C_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_20])).

tff(c_14,plain,(
    ! [A_5,B_6] : v1_relat_1(k2_zfmisc_1(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_95,plain,(
    ! [B_35,A_36] :
      ( v1_xboole_0(B_35)
      | ~ m1_subset_1(B_35,A_36)
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_103,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_95])).

tff(c_104,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_26,plain,(
    ! [A_16,B_17] : k1_mcart_1(k4_tarski(A_16,B_17)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22,plain,(
    ! [B_12,C_13] : k1_mcart_1(k4_tarski(B_12,C_13)) != k4_tarski(B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_37,plain,(
    ! [B_12,C_13] : k4_tarski(B_12,C_13) != B_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22])).

tff(c_30,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_61,plain,(
    k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( r2_hidden(B_3,A_2)
      | ~ m1_subset_1(B_3,A_2)
      | v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_225,plain,(
    ! [A_63,B_64] :
      ( k4_tarski(k1_mcart_1(A_63),k2_mcart_1(A_63)) = A_63
      | ~ r2_hidden(A_63,B_64)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_230,plain,(
    ! [B_67,A_68] :
      ( k4_tarski(k1_mcart_1(B_67),k2_mcart_1(B_67)) = B_67
      | ~ v1_relat_1(A_68)
      | ~ m1_subset_1(B_67,A_68)
      | v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_6,c_225])).

tff(c_234,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_230])).

tff(c_238,plain,
    ( k4_tarski('#skF_3',k2_mcart_1('#skF_3')) = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_61,c_234])).

tff(c_240,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_37,c_238])).

tff(c_241,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_250,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_241,c_2])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_255,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_36])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_254,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_34])).

tff(c_66,plain,(
    ! [A_30] :
      ( v1_xboole_0(k1_relat_1(A_30))
      | ~ v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_70,plain,(
    ! [A_30] :
      ( k1_relat_1(A_30) = k1_xboole_0
      | ~ v1_xboole_0(A_30) ) ),
    inference(resolution,[status(thm)],[c_66,c_2])).

tff(c_249,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_241,c_70])).

tff(c_261,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_249])).

tff(c_242,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_276,plain,(
    ! [A_73] :
      ( A_73 = '#skF_3'
      | ~ v1_xboole_0(A_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_2])).

tff(c_286,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_242,c_276])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( k1_relat_1(k2_zfmisc_1(A_7,B_8)) = A_7
      | k1_xboole_0 = B_8
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_319,plain,(
    ! [A_75,B_76] :
      ( k1_relat_1(k2_zfmisc_1(A_75,B_76)) = A_75
      | B_76 = '#skF_3'
      | A_75 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_250,c_18])).

tff(c_331,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_319])).

tff(c_334,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_331])).

tff(c_336,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_254,c_255,c_334])).

tff(c_337,plain,(
    k2_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_501,plain,(
    ! [A_108,B_109] :
      ( k4_tarski(k1_mcart_1(A_108),k2_mcart_1(A_108)) = A_108
      | ~ r2_hidden(A_108,B_109)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_506,plain,(
    ! [B_112,A_113] :
      ( k4_tarski(k1_mcart_1(B_112),k2_mcart_1(B_112)) = B_112
      | ~ v1_relat_1(A_113)
      | ~ m1_subset_1(B_112,A_113)
      | v1_xboole_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_6,c_501])).

tff(c_510,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_506])).

tff(c_514,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),'#skF_3') = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_337,c_510])).

tff(c_516,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_38,c_514])).

tff(c_517,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_380])).

tff(c_526,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_517,c_2])).

tff(c_539,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_36])).

tff(c_538,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_34])).

tff(c_343,plain,(
    ! [A_77] :
      ( v1_xboole_0(k1_relat_1(A_77))
      | ~ v1_xboole_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_347,plain,(
    ! [A_77] :
      ( k1_relat_1(A_77) = k1_xboole_0
      | ~ v1_xboole_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_343,c_2])).

tff(c_525,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_517,c_347])).

tff(c_544,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_525])).

tff(c_518,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_380])).

tff(c_534,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_518,c_2])).

tff(c_569,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_534])).

tff(c_635,plain,(
    ! [A_121,B_122] :
      ( k1_relat_1(k2_zfmisc_1(A_121,B_122)) = A_121
      | B_122 = '#skF_3'
      | A_121 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_526,c_18])).

tff(c_650,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_635])).

tff(c_653,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_650])).

tff(c_655,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_539,c_538,c_539,c_653])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:28:05 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.36  
% 2.46/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.36  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.46/1.36  
% 2.46/1.36  %Foreground sorts:
% 2.46/1.36  
% 2.46/1.36  
% 2.46/1.36  %Background operators:
% 2.46/1.36  
% 2.46/1.36  
% 2.46/1.36  %Foreground operators:
% 2.46/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.46/1.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.46/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.46/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.46/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.46/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.46/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.36  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.46/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.46/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.46/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.36  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.46/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.46/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.46/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.46/1.36  
% 2.46/1.38  tff(f_97, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_mcart_1)).
% 2.46/1.38  tff(f_42, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.46/1.38  tff(f_79, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.46/1.38  tff(f_69, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.46/1.38  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.46/1.38  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 2.46/1.38  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.46/1.38  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 2.46/1.38  tff(f_60, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 2.46/1.38  tff(c_32, plain, (m1_subset_1('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.46/1.38  tff(c_372, plain, (![B_82, A_83]: (v1_xboole_0(B_82) | ~m1_subset_1(B_82, A_83) | ~v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.46/1.38  tff(c_380, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_372])).
% 2.46/1.38  tff(c_381, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_380])).
% 2.46/1.38  tff(c_28, plain, (![A_16, B_17]: (k2_mcart_1(k4_tarski(A_16, B_17))=B_17)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.46/1.38  tff(c_20, plain, (![B_12, C_13]: (k2_mcart_1(k4_tarski(B_12, C_13))!=k4_tarski(B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.46/1.38  tff(c_38, plain, (![B_12, C_13]: (k4_tarski(B_12, C_13)!=C_13)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_20])).
% 2.46/1.38  tff(c_14, plain, (![A_5, B_6]: (v1_relat_1(k2_zfmisc_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.46/1.38  tff(c_95, plain, (![B_35, A_36]: (v1_xboole_0(B_35) | ~m1_subset_1(B_35, A_36) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.46/1.38  tff(c_103, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_95])).
% 2.46/1.38  tff(c_104, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_103])).
% 2.46/1.38  tff(c_26, plain, (![A_16, B_17]: (k1_mcart_1(k4_tarski(A_16, B_17))=A_16)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.46/1.38  tff(c_22, plain, (![B_12, C_13]: (k1_mcart_1(k4_tarski(B_12, C_13))!=k4_tarski(B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.46/1.38  tff(c_37, plain, (![B_12, C_13]: (k4_tarski(B_12, C_13)!=B_12)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22])).
% 2.46/1.38  tff(c_30, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.46/1.38  tff(c_61, plain, (k1_mcart_1('#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_30])).
% 2.46/1.38  tff(c_6, plain, (![B_3, A_2]: (r2_hidden(B_3, A_2) | ~m1_subset_1(B_3, A_2) | v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.46/1.38  tff(c_225, plain, (![A_63, B_64]: (k4_tarski(k1_mcart_1(A_63), k2_mcart_1(A_63))=A_63 | ~r2_hidden(A_63, B_64) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.46/1.38  tff(c_230, plain, (![B_67, A_68]: (k4_tarski(k1_mcart_1(B_67), k2_mcart_1(B_67))=B_67 | ~v1_relat_1(A_68) | ~m1_subset_1(B_67, A_68) | v1_xboole_0(A_68))), inference(resolution, [status(thm)], [c_6, c_225])).
% 2.46/1.38  tff(c_234, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_230])).
% 2.46/1.38  tff(c_238, plain, (k4_tarski('#skF_3', k2_mcart_1('#skF_3'))='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_61, c_234])).
% 2.46/1.38  tff(c_240, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_37, c_238])).
% 2.46/1.38  tff(c_241, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_103])).
% 2.46/1.38  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.46/1.38  tff(c_250, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_241, c_2])).
% 2.46/1.38  tff(c_36, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.46/1.38  tff(c_255, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_250, c_36])).
% 2.46/1.38  tff(c_34, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.46/1.38  tff(c_254, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_250, c_34])).
% 2.46/1.38  tff(c_66, plain, (![A_30]: (v1_xboole_0(k1_relat_1(A_30)) | ~v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.46/1.38  tff(c_70, plain, (![A_30]: (k1_relat_1(A_30)=k1_xboole_0 | ~v1_xboole_0(A_30))), inference(resolution, [status(thm)], [c_66, c_2])).
% 2.46/1.38  tff(c_249, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_241, c_70])).
% 2.46/1.38  tff(c_261, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_250, c_249])).
% 2.46/1.38  tff(c_242, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_103])).
% 2.46/1.38  tff(c_276, plain, (![A_73]: (A_73='#skF_3' | ~v1_xboole_0(A_73))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_2])).
% 2.46/1.38  tff(c_286, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_242, c_276])).
% 2.46/1.38  tff(c_18, plain, (![A_7, B_8]: (k1_relat_1(k2_zfmisc_1(A_7, B_8))=A_7 | k1_xboole_0=B_8 | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.46/1.38  tff(c_319, plain, (![A_75, B_76]: (k1_relat_1(k2_zfmisc_1(A_75, B_76))=A_75 | B_76='#skF_3' | A_75='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_250, c_250, c_18])).
% 2.46/1.38  tff(c_331, plain, (k1_relat_1('#skF_3')='#skF_1' | '#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_286, c_319])).
% 2.46/1.38  tff(c_334, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_261, c_331])).
% 2.46/1.38  tff(c_336, plain, $false, inference(negUnitSimplification, [status(thm)], [c_255, c_254, c_255, c_334])).
% 2.46/1.38  tff(c_337, plain, (k2_mcart_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 2.46/1.38  tff(c_501, plain, (![A_108, B_109]: (k4_tarski(k1_mcart_1(A_108), k2_mcart_1(A_108))=A_108 | ~r2_hidden(A_108, B_109) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.46/1.38  tff(c_506, plain, (![B_112, A_113]: (k4_tarski(k1_mcart_1(B_112), k2_mcart_1(B_112))=B_112 | ~v1_relat_1(A_113) | ~m1_subset_1(B_112, A_113) | v1_xboole_0(A_113))), inference(resolution, [status(thm)], [c_6, c_501])).
% 2.46/1.38  tff(c_510, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_506])).
% 2.46/1.38  tff(c_514, plain, (k4_tarski(k1_mcart_1('#skF_3'), '#skF_3')='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_337, c_510])).
% 2.46/1.38  tff(c_516, plain, $false, inference(negUnitSimplification, [status(thm)], [c_381, c_38, c_514])).
% 2.46/1.38  tff(c_517, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_380])).
% 2.46/1.38  tff(c_526, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_517, c_2])).
% 2.46/1.38  tff(c_539, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_526, c_36])).
% 2.46/1.38  tff(c_538, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_526, c_34])).
% 2.46/1.38  tff(c_343, plain, (![A_77]: (v1_xboole_0(k1_relat_1(A_77)) | ~v1_xboole_0(A_77))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.46/1.38  tff(c_347, plain, (![A_77]: (k1_relat_1(A_77)=k1_xboole_0 | ~v1_xboole_0(A_77))), inference(resolution, [status(thm)], [c_343, c_2])).
% 2.46/1.38  tff(c_525, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_517, c_347])).
% 2.46/1.38  tff(c_544, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_526, c_525])).
% 2.46/1.38  tff(c_518, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_380])).
% 2.46/1.38  tff(c_534, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_518, c_2])).
% 2.46/1.38  tff(c_569, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_526, c_534])).
% 2.46/1.38  tff(c_635, plain, (![A_121, B_122]: (k1_relat_1(k2_zfmisc_1(A_121, B_122))=A_121 | B_122='#skF_3' | A_121='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_526, c_526, c_18])).
% 2.46/1.38  tff(c_650, plain, (k1_relat_1('#skF_3')='#skF_1' | '#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_569, c_635])).
% 2.46/1.38  tff(c_653, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_544, c_650])).
% 2.46/1.38  tff(c_655, plain, $false, inference(negUnitSimplification, [status(thm)], [c_539, c_538, c_539, c_653])).
% 2.46/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.38  
% 2.46/1.38  Inference rules
% 2.46/1.38  ----------------------
% 2.46/1.38  #Ref     : 0
% 2.46/1.38  #Sup     : 127
% 2.46/1.38  #Fact    : 0
% 2.46/1.38  #Define  : 0
% 2.46/1.38  #Split   : 5
% 2.46/1.38  #Chain   : 0
% 2.46/1.38  #Close   : 0
% 2.46/1.38  
% 2.46/1.38  Ordering : KBO
% 2.46/1.38  
% 2.46/1.38  Simplification rules
% 2.46/1.38  ----------------------
% 2.46/1.38  #Subsume      : 24
% 2.46/1.38  #Demod        : 74
% 2.46/1.38  #Tautology    : 89
% 2.46/1.38  #SimpNegUnit  : 14
% 2.46/1.38  #BackRed      : 16
% 2.46/1.38  
% 2.46/1.38  #Partial instantiations: 0
% 2.46/1.38  #Strategies tried      : 1
% 2.46/1.38  
% 2.46/1.38  Timing (in seconds)
% 2.46/1.38  ----------------------
% 2.46/1.38  Preprocessing        : 0.30
% 2.46/1.38  Parsing              : 0.16
% 2.46/1.38  CNF conversion       : 0.02
% 2.46/1.38  Main loop            : 0.29
% 2.46/1.38  Inferencing          : 0.11
% 2.46/1.38  Reduction            : 0.08
% 2.46/1.38  Demodulation         : 0.05
% 2.46/1.38  BG Simplification    : 0.02
% 2.46/1.38  Subsumption          : 0.05
% 2.46/1.38  Abstraction          : 0.01
% 2.46/1.38  MUC search           : 0.00
% 2.46/1.38  Cooper               : 0.00
% 2.46/1.38  Total                : 0.63
% 2.46/1.38  Index Insertion      : 0.00
% 2.46/1.38  Index Deletion       : 0.00
% 2.46/1.39  Index Matching       : 0.00
% 2.46/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
