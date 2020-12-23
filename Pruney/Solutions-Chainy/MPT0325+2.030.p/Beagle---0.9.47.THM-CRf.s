%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:24 EST 2020

% Result     : Theorem 10.79s
% Output     : CNFRefutation 10.79s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 215 expanded)
%              Number of leaves         :   32 (  87 expanded)
%              Depth                    :    9
%              Number of atoms          :  116 ( 446 expanded)
%              Number of equality atoms :   18 (  56 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_15 > #skF_10 > #skF_14 > #skF_13 > #skF_2 > #skF_11 > #skF_7 > #skF_9 > #skF_3 > #skF_8 > #skF_1 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_63,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_65,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_64,plain,
    ( ~ r1_tarski('#skF_13','#skF_15')
    | ~ r1_tarski('#skF_12','#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_71,plain,(
    ~ r1_tarski('#skF_12','#skF_14') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_5'(A_17),A_17)
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_68,plain,(
    r1_tarski(k2_zfmisc_1('#skF_12','#skF_13'),k2_zfmisc_1('#skF_14','#skF_15')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_691,plain,(
    ! [A_134,B_135,C_136,D_137] :
      ( r2_hidden(k4_tarski(A_134,B_135),k2_zfmisc_1(C_136,D_137))
      | ~ r2_hidden(B_135,D_137)
      | ~ r2_hidden(A_134,C_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10971,plain,(
    ! [B_479,D_481,C_480,A_478,B_477] :
      ( r2_hidden(k4_tarski(A_478,B_477),B_479)
      | ~ r1_tarski(k2_zfmisc_1(C_480,D_481),B_479)
      | ~ r2_hidden(B_477,D_481)
      | ~ r2_hidden(A_478,C_480) ) ),
    inference(resolution,[status(thm)],[c_691,c_2])).

tff(c_11107,plain,(
    ! [A_486,B_487] :
      ( r2_hidden(k4_tarski(A_486,B_487),k2_zfmisc_1('#skF_14','#skF_15'))
      | ~ r2_hidden(B_487,'#skF_13')
      | ~ r2_hidden(A_486,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_68,c_10971])).

tff(c_62,plain,(
    ! [A_54,C_56,B_55,D_57] :
      ( r2_hidden(A_54,C_56)
      | ~ r2_hidden(k4_tarski(A_54,B_55),k2_zfmisc_1(C_56,D_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_11130,plain,(
    ! [A_486,B_487] :
      ( r2_hidden(A_486,'#skF_14')
      | ~ r2_hidden(B_487,'#skF_13')
      | ~ r2_hidden(A_486,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_11107,c_62])).

tff(c_11289,plain,(
    ! [B_494] : ~ r2_hidden(B_494,'#skF_13') ),
    inference(splitLeft,[status(thm)],[c_11130])).

tff(c_11447,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(resolution,[status(thm)],[c_30,c_11289])).

tff(c_807,plain,(
    ! [A_153,B_154,D_155] :
      ( r2_hidden('#skF_11'(A_153,B_154,k2_zfmisc_1(A_153,B_154),D_155),B_154)
      | ~ r2_hidden(D_155,k2_zfmisc_1(A_153,B_154)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_32,plain,(
    ! [A_19] : r1_xboole_0(A_19,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_95,plain,(
    ! [A_68,B_69,C_70] :
      ( ~ r1_xboole_0(A_68,B_69)
      | ~ r2_hidden(C_70,k3_xboole_0(A_68,B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_106,plain,(
    ! [A_71,B_72] :
      ( ~ r1_xboole_0(A_71,B_72)
      | k3_xboole_0(A_71,B_72) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_95])).

tff(c_111,plain,(
    ! [A_73] : k3_xboole_0(A_73,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_106])).

tff(c_28,plain,(
    ! [A_12,B_13,C_16] :
      ( ~ r1_xboole_0(A_12,B_13)
      | ~ r2_hidden(C_16,k3_xboole_0(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_116,plain,(
    ! [A_73,C_16] :
      ( ~ r1_xboole_0(A_73,k1_xboole_0)
      | ~ r2_hidden(C_16,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_28])).

tff(c_127,plain,(
    ! [C_16] : ~ r2_hidden(C_16,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_116])).

tff(c_831,plain,(
    ! [D_156,A_157] : ~ r2_hidden(D_156,k2_zfmisc_1(A_157,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_807,c_127])).

tff(c_886,plain,(
    ! [A_157] : k2_zfmisc_1(A_157,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_831])).

tff(c_11497,plain,(
    ! [A_157] : k2_zfmisc_1(A_157,'#skF_13') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11447,c_11447,c_886])).

tff(c_66,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_11516,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11447,c_66])).

tff(c_12088,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11497,c_11516])).

tff(c_12154,plain,(
    ! [A_512] :
      ( r2_hidden(A_512,'#skF_14')
      | ~ r2_hidden(A_512,'#skF_12') ) ),
    inference(splitRight,[status(thm)],[c_11130])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_13085,plain,(
    ! [A_536] :
      ( r1_tarski(A_536,'#skF_14')
      | ~ r2_hidden('#skF_1'(A_536,'#skF_14'),'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_12154,c_4])).

tff(c_13101,plain,(
    r1_tarski('#skF_12','#skF_14') ),
    inference(resolution,[status(thm)],[c_6,c_13085])).

tff(c_13108,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_71,c_13101])).

tff(c_13109,plain,(
    ~ r1_tarski('#skF_13','#skF_15') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_13673,plain,(
    ! [A_603,B_604,C_605,D_606] :
      ( r2_hidden(k4_tarski(A_603,B_604),k2_zfmisc_1(C_605,D_606))
      | ~ r2_hidden(B_604,D_606)
      | ~ r2_hidden(A_603,C_605) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_23895,plain,(
    ! [A_948,C_946,B_945,D_947,B_949] :
      ( r2_hidden(k4_tarski(A_948,B_945),B_949)
      | ~ r1_tarski(k2_zfmisc_1(C_946,D_947),B_949)
      | ~ r2_hidden(B_945,D_947)
      | ~ r2_hidden(A_948,C_946) ) ),
    inference(resolution,[status(thm)],[c_13673,c_2])).

tff(c_24031,plain,(
    ! [A_954,B_955] :
      ( r2_hidden(k4_tarski(A_954,B_955),k2_zfmisc_1('#skF_14','#skF_15'))
      | ~ r2_hidden(B_955,'#skF_13')
      | ~ r2_hidden(A_954,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_68,c_23895])).

tff(c_60,plain,(
    ! [B_55,D_57,A_54,C_56] :
      ( r2_hidden(B_55,D_57)
      | ~ r2_hidden(k4_tarski(A_54,B_55),k2_zfmisc_1(C_56,D_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_24054,plain,(
    ! [B_955,A_954] :
      ( r2_hidden(B_955,'#skF_15')
      | ~ r2_hidden(B_955,'#skF_13')
      | ~ r2_hidden(A_954,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_24031,c_60])).

tff(c_24220,plain,(
    ! [A_962] : ~ r2_hidden(A_962,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_24054])).

tff(c_24383,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_30,c_24220])).

tff(c_13844,plain,(
    ! [A_621,B_622,D_623] :
      ( r2_hidden('#skF_10'(A_621,B_622,k2_zfmisc_1(A_621,B_622),D_623),A_621)
      | ~ r2_hidden(D_623,k2_zfmisc_1(A_621,B_622)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_13140,plain,(
    ! [A_547,B_548,C_549] :
      ( ~ r1_xboole_0(A_547,B_548)
      | ~ r2_hidden(C_549,k3_xboole_0(A_547,B_548)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_13152,plain,(
    ! [A_551,B_552] :
      ( ~ r1_xboole_0(A_551,B_552)
      | k3_xboole_0(A_551,B_552) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_13140])).

tff(c_13157,plain,(
    ! [A_553] : k3_xboole_0(A_553,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_13152])).

tff(c_13162,plain,(
    ! [A_553,C_16] :
      ( ~ r1_xboole_0(A_553,k1_xboole_0)
      | ~ r2_hidden(C_16,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13157,c_28])).

tff(c_13173,plain,(
    ! [C_16] : ~ r2_hidden(C_16,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_13162])).

tff(c_13872,plain,(
    ! [D_624,B_625] : ~ r2_hidden(D_624,k2_zfmisc_1(k1_xboole_0,B_625)) ),
    inference(resolution,[status(thm)],[c_13844,c_13173])).

tff(c_13930,plain,(
    ! [B_625] : k2_zfmisc_1(k1_xboole_0,B_625) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_13872])).

tff(c_24434,plain,(
    ! [B_625] : k2_zfmisc_1('#skF_12',B_625) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24383,c_24383,c_13930])).

tff(c_24451,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24383,c_66])).

tff(c_25154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24434,c_24451])).

tff(c_25156,plain,(
    ! [B_981] :
      ( r2_hidden(B_981,'#skF_15')
      | ~ r2_hidden(B_981,'#skF_13') ) ),
    inference(splitRight,[status(thm)],[c_24054])).

tff(c_26394,plain,(
    ! [A_1017] :
      ( r1_tarski(A_1017,'#skF_15')
      | ~ r2_hidden('#skF_1'(A_1017,'#skF_15'),'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_25156,c_4])).

tff(c_26410,plain,(
    r1_tarski('#skF_13','#skF_15') ),
    inference(resolution,[status(thm)],[c_6,c_26394])).

tff(c_26417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13109,c_13109,c_26410])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:27:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.79/3.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.79/3.90  
% 10.79/3.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.79/3.90  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_15 > #skF_10 > #skF_14 > #skF_13 > #skF_2 > #skF_11 > #skF_7 > #skF_9 > #skF_3 > #skF_8 > #skF_1 > #skF_12 > #skF_4
% 10.79/3.90  
% 10.79/3.90  %Foreground sorts:
% 10.79/3.90  
% 10.79/3.90  
% 10.79/3.90  %Background operators:
% 10.79/3.90  
% 10.79/3.90  
% 10.79/3.90  %Foreground operators:
% 10.79/3.90  tff('#skF_5', type, '#skF_5': $i > $i).
% 10.79/3.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.79/3.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.79/3.90  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 10.79/3.90  tff('#skF_15', type, '#skF_15': $i).
% 10.79/3.90  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.79/3.90  tff('#skF_10', type, '#skF_10': ($i * $i * $i * $i) > $i).
% 10.79/3.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.79/3.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.79/3.90  tff('#skF_14', type, '#skF_14': $i).
% 10.79/3.90  tff('#skF_13', type, '#skF_13': $i).
% 10.79/3.90  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.79/3.90  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.79/3.90  tff('#skF_11', type, '#skF_11': ($i * $i * $i * $i) > $i).
% 10.79/3.90  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 10.79/3.90  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 10.79/3.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.79/3.90  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.79/3.90  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.79/3.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.79/3.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.79/3.90  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 10.79/3.90  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.79/3.90  tff('#skF_12', type, '#skF_12': $i).
% 10.79/3.90  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.79/3.90  
% 10.79/3.92  tff(f_92, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 10.79/3.92  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 10.79/3.92  tff(f_63, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 10.79/3.92  tff(f_83, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 10.79/3.92  tff(f_77, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 10.79/3.92  tff(f_65, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 10.79/3.92  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 10.79/3.92  tff(c_64, plain, (~r1_tarski('#skF_13', '#skF_15') | ~r1_tarski('#skF_12', '#skF_14')), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.79/3.92  tff(c_71, plain, (~r1_tarski('#skF_12', '#skF_14')), inference(splitLeft, [status(thm)], [c_64])).
% 10.79/3.92  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.79/3.92  tff(c_30, plain, (![A_17]: (r2_hidden('#skF_5'(A_17), A_17) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.79/3.92  tff(c_68, plain, (r1_tarski(k2_zfmisc_1('#skF_12', '#skF_13'), k2_zfmisc_1('#skF_14', '#skF_15'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.79/3.92  tff(c_691, plain, (![A_134, B_135, C_136, D_137]: (r2_hidden(k4_tarski(A_134, B_135), k2_zfmisc_1(C_136, D_137)) | ~r2_hidden(B_135, D_137) | ~r2_hidden(A_134, C_136))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.79/3.92  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.79/3.92  tff(c_10971, plain, (![B_479, D_481, C_480, A_478, B_477]: (r2_hidden(k4_tarski(A_478, B_477), B_479) | ~r1_tarski(k2_zfmisc_1(C_480, D_481), B_479) | ~r2_hidden(B_477, D_481) | ~r2_hidden(A_478, C_480))), inference(resolution, [status(thm)], [c_691, c_2])).
% 10.79/3.92  tff(c_11107, plain, (![A_486, B_487]: (r2_hidden(k4_tarski(A_486, B_487), k2_zfmisc_1('#skF_14', '#skF_15')) | ~r2_hidden(B_487, '#skF_13') | ~r2_hidden(A_486, '#skF_12'))), inference(resolution, [status(thm)], [c_68, c_10971])).
% 10.79/3.92  tff(c_62, plain, (![A_54, C_56, B_55, D_57]: (r2_hidden(A_54, C_56) | ~r2_hidden(k4_tarski(A_54, B_55), k2_zfmisc_1(C_56, D_57)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.79/3.92  tff(c_11130, plain, (![A_486, B_487]: (r2_hidden(A_486, '#skF_14') | ~r2_hidden(B_487, '#skF_13') | ~r2_hidden(A_486, '#skF_12'))), inference(resolution, [status(thm)], [c_11107, c_62])).
% 10.79/3.92  tff(c_11289, plain, (![B_494]: (~r2_hidden(B_494, '#skF_13'))), inference(splitLeft, [status(thm)], [c_11130])).
% 10.79/3.92  tff(c_11447, plain, (k1_xboole_0='#skF_13'), inference(resolution, [status(thm)], [c_30, c_11289])).
% 10.79/3.92  tff(c_807, plain, (![A_153, B_154, D_155]: (r2_hidden('#skF_11'(A_153, B_154, k2_zfmisc_1(A_153, B_154), D_155), B_154) | ~r2_hidden(D_155, k2_zfmisc_1(A_153, B_154)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.79/3.92  tff(c_32, plain, (![A_19]: (r1_xboole_0(A_19, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.79/3.92  tff(c_95, plain, (![A_68, B_69, C_70]: (~r1_xboole_0(A_68, B_69) | ~r2_hidden(C_70, k3_xboole_0(A_68, B_69)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.79/3.92  tff(c_106, plain, (![A_71, B_72]: (~r1_xboole_0(A_71, B_72) | k3_xboole_0(A_71, B_72)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_95])).
% 10.79/3.92  tff(c_111, plain, (![A_73]: (k3_xboole_0(A_73, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_106])).
% 10.79/3.92  tff(c_28, plain, (![A_12, B_13, C_16]: (~r1_xboole_0(A_12, B_13) | ~r2_hidden(C_16, k3_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.79/3.92  tff(c_116, plain, (![A_73, C_16]: (~r1_xboole_0(A_73, k1_xboole_0) | ~r2_hidden(C_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_111, c_28])).
% 10.79/3.92  tff(c_127, plain, (![C_16]: (~r2_hidden(C_16, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_116])).
% 10.79/3.92  tff(c_831, plain, (![D_156, A_157]: (~r2_hidden(D_156, k2_zfmisc_1(A_157, k1_xboole_0)))), inference(resolution, [status(thm)], [c_807, c_127])).
% 10.79/3.92  tff(c_886, plain, (![A_157]: (k2_zfmisc_1(A_157, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_831])).
% 10.79/3.92  tff(c_11497, plain, (![A_157]: (k2_zfmisc_1(A_157, '#skF_13')='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_11447, c_11447, c_886])).
% 10.79/3.92  tff(c_66, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.79/3.92  tff(c_11516, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_11447, c_66])).
% 10.79/3.92  tff(c_12088, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11497, c_11516])).
% 10.79/3.92  tff(c_12154, plain, (![A_512]: (r2_hidden(A_512, '#skF_14') | ~r2_hidden(A_512, '#skF_12'))), inference(splitRight, [status(thm)], [c_11130])).
% 10.79/3.92  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.79/3.92  tff(c_13085, plain, (![A_536]: (r1_tarski(A_536, '#skF_14') | ~r2_hidden('#skF_1'(A_536, '#skF_14'), '#skF_12'))), inference(resolution, [status(thm)], [c_12154, c_4])).
% 10.79/3.92  tff(c_13101, plain, (r1_tarski('#skF_12', '#skF_14')), inference(resolution, [status(thm)], [c_6, c_13085])).
% 10.79/3.92  tff(c_13108, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_71, c_13101])).
% 10.79/3.92  tff(c_13109, plain, (~r1_tarski('#skF_13', '#skF_15')), inference(splitRight, [status(thm)], [c_64])).
% 10.79/3.92  tff(c_13673, plain, (![A_603, B_604, C_605, D_606]: (r2_hidden(k4_tarski(A_603, B_604), k2_zfmisc_1(C_605, D_606)) | ~r2_hidden(B_604, D_606) | ~r2_hidden(A_603, C_605))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.79/3.92  tff(c_23895, plain, (![A_948, C_946, B_945, D_947, B_949]: (r2_hidden(k4_tarski(A_948, B_945), B_949) | ~r1_tarski(k2_zfmisc_1(C_946, D_947), B_949) | ~r2_hidden(B_945, D_947) | ~r2_hidden(A_948, C_946))), inference(resolution, [status(thm)], [c_13673, c_2])).
% 10.79/3.92  tff(c_24031, plain, (![A_954, B_955]: (r2_hidden(k4_tarski(A_954, B_955), k2_zfmisc_1('#skF_14', '#skF_15')) | ~r2_hidden(B_955, '#skF_13') | ~r2_hidden(A_954, '#skF_12'))), inference(resolution, [status(thm)], [c_68, c_23895])).
% 10.79/3.92  tff(c_60, plain, (![B_55, D_57, A_54, C_56]: (r2_hidden(B_55, D_57) | ~r2_hidden(k4_tarski(A_54, B_55), k2_zfmisc_1(C_56, D_57)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.79/3.92  tff(c_24054, plain, (![B_955, A_954]: (r2_hidden(B_955, '#skF_15') | ~r2_hidden(B_955, '#skF_13') | ~r2_hidden(A_954, '#skF_12'))), inference(resolution, [status(thm)], [c_24031, c_60])).
% 10.79/3.92  tff(c_24220, plain, (![A_962]: (~r2_hidden(A_962, '#skF_12'))), inference(splitLeft, [status(thm)], [c_24054])).
% 10.79/3.92  tff(c_24383, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_30, c_24220])).
% 10.79/3.92  tff(c_13844, plain, (![A_621, B_622, D_623]: (r2_hidden('#skF_10'(A_621, B_622, k2_zfmisc_1(A_621, B_622), D_623), A_621) | ~r2_hidden(D_623, k2_zfmisc_1(A_621, B_622)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.79/3.92  tff(c_13140, plain, (![A_547, B_548, C_549]: (~r1_xboole_0(A_547, B_548) | ~r2_hidden(C_549, k3_xboole_0(A_547, B_548)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.79/3.92  tff(c_13152, plain, (![A_551, B_552]: (~r1_xboole_0(A_551, B_552) | k3_xboole_0(A_551, B_552)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_13140])).
% 10.79/3.92  tff(c_13157, plain, (![A_553]: (k3_xboole_0(A_553, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_13152])).
% 10.79/3.92  tff(c_13162, plain, (![A_553, C_16]: (~r1_xboole_0(A_553, k1_xboole_0) | ~r2_hidden(C_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_13157, c_28])).
% 10.79/3.92  tff(c_13173, plain, (![C_16]: (~r2_hidden(C_16, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_13162])).
% 10.79/3.92  tff(c_13872, plain, (![D_624, B_625]: (~r2_hidden(D_624, k2_zfmisc_1(k1_xboole_0, B_625)))), inference(resolution, [status(thm)], [c_13844, c_13173])).
% 10.79/3.92  tff(c_13930, plain, (![B_625]: (k2_zfmisc_1(k1_xboole_0, B_625)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_13872])).
% 10.79/3.92  tff(c_24434, plain, (![B_625]: (k2_zfmisc_1('#skF_12', B_625)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_24383, c_24383, c_13930])).
% 10.79/3.92  tff(c_24451, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_24383, c_66])).
% 10.79/3.92  tff(c_25154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24434, c_24451])).
% 10.79/3.92  tff(c_25156, plain, (![B_981]: (r2_hidden(B_981, '#skF_15') | ~r2_hidden(B_981, '#skF_13'))), inference(splitRight, [status(thm)], [c_24054])).
% 10.79/3.92  tff(c_26394, plain, (![A_1017]: (r1_tarski(A_1017, '#skF_15') | ~r2_hidden('#skF_1'(A_1017, '#skF_15'), '#skF_13'))), inference(resolution, [status(thm)], [c_25156, c_4])).
% 10.79/3.92  tff(c_26410, plain, (r1_tarski('#skF_13', '#skF_15')), inference(resolution, [status(thm)], [c_6, c_26394])).
% 10.79/3.92  tff(c_26417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13109, c_13109, c_26410])).
% 10.79/3.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.79/3.92  
% 10.79/3.92  Inference rules
% 10.79/3.92  ----------------------
% 10.79/3.92  #Ref     : 0
% 10.79/3.92  #Sup     : 6411
% 10.79/3.92  #Fact    : 0
% 10.79/3.92  #Define  : 0
% 10.79/3.92  #Split   : 11
% 10.79/3.92  #Chain   : 0
% 10.79/3.92  #Close   : 0
% 10.79/3.92  
% 10.79/3.92  Ordering : KBO
% 10.79/3.92  
% 10.79/3.92  Simplification rules
% 10.79/3.92  ----------------------
% 10.79/3.92  #Subsume      : 2032
% 10.79/3.92  #Demod        : 3934
% 10.79/3.92  #Tautology    : 2649
% 10.79/3.92  #SimpNegUnit  : 127
% 10.79/3.92  #BackRed      : 291
% 10.79/3.92  
% 10.79/3.92  #Partial instantiations: 0
% 10.79/3.92  #Strategies tried      : 1
% 10.79/3.92  
% 10.79/3.92  Timing (in seconds)
% 10.79/3.92  ----------------------
% 10.79/3.92  Preprocessing        : 0.33
% 10.79/3.92  Parsing              : 0.17
% 10.79/3.92  CNF conversion       : 0.03
% 10.79/3.92  Main loop            : 2.77
% 10.79/3.92  Inferencing          : 0.78
% 10.79/3.92  Reduction            : 0.74
% 10.79/3.92  Demodulation         : 0.51
% 10.79/3.92  BG Simplification    : 0.10
% 10.79/3.92  Subsumption          : 0.96
% 10.79/3.92  Abstraction          : 0.11
% 10.79/3.92  MUC search           : 0.00
% 10.79/3.92  Cooper               : 0.00
% 10.79/3.92  Total                : 3.14
% 10.79/3.92  Index Insertion      : 0.00
% 10.79/3.92  Index Deletion       : 0.00
% 10.79/3.92  Index Matching       : 0.00
% 10.79/3.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
