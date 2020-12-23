%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:14 EST 2020

% Result     : Theorem 10.46s
% Output     : CNFRefutation 10.46s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 175 expanded)
%              Number of leaves         :   38 (  73 expanded)
%              Depth                    :   11
%              Number of atoms          :  131 ( 299 expanded)
%              Number of equality atoms :   20 (  58 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_13 > #skF_10 > #skF_2 > #skF_8 > #skF_11 > #skF_5 > #skF_3 > #skF_7 > #skF_9 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_40,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_77,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_4,B_5] : k4_xboole_0(A_4,k2_xboole_0(A_4,B_5)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_80,plain,(
    ! [A_99,B_100] :
      ( v1_relat_1(k4_xboole_0(A_99,B_100))
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_83,plain,(
    ! [A_4] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_80])).

tff(c_84,plain,(
    ! [A_4] : ~ v1_relat_1(A_4) ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_54,plain,(
    v1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_87,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_54])).

tff(c_88,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_50,plain,(
    ! [A_89,B_90,C_91] :
      ( r2_hidden(k4_tarski(A_89,B_90),C_91)
      | ~ r2_hidden(B_90,k11_relat_1(C_91,A_89))
      | ~ v1_relat_1(C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_11116,plain,(
    ! [C_495,D_496,B_497,A_498] :
      ( r2_hidden(k4_tarski(C_495,D_496),B_497)
      | ~ r2_hidden(k4_tarski(C_495,D_496),A_498)
      | ~ r1_tarski(A_498,B_497)
      | ~ v1_relat_1(A_498) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_11388,plain,(
    ! [A_517,B_518,B_519,C_520] :
      ( r2_hidden(k4_tarski(A_517,B_518),B_519)
      | ~ r1_tarski(C_520,B_519)
      | ~ r2_hidden(B_518,k11_relat_1(C_520,A_517))
      | ~ v1_relat_1(C_520) ) ),
    inference(resolution,[status(thm)],[c_50,c_11116])).

tff(c_11392,plain,(
    ! [A_517,B_518,A_3] :
      ( r2_hidden(k4_tarski(A_517,B_518),A_3)
      | ~ r2_hidden(B_518,k11_relat_1(k1_xboole_0,A_517))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_11388])).

tff(c_11397,plain,(
    ! [A_521,B_522,A_523] :
      ( r2_hidden(k4_tarski(A_521,B_522),A_523)
      | ~ r2_hidden(B_522,k11_relat_1(k1_xboole_0,A_521)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_11392])).

tff(c_8,plain,(
    ! [A_6,B_7] : ~ r2_hidden(A_6,k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_11497,plain,(
    ! [B_527,A_528] : ~ r2_hidden(B_527,k11_relat_1(k1_xboole_0,A_528)) ),
    inference(resolution,[status(thm)],[c_11397,c_8])).

tff(c_11540,plain,(
    ! [A_528] : k11_relat_1(k1_xboole_0,A_528) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_11497])).

tff(c_48,plain,(
    ! [A_88] : k9_relat_1(k1_xboole_0,A_88) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_62,plain,
    ( r2_hidden('#skF_12',k1_relat_1('#skF_13'))
    | k11_relat_1('#skF_13','#skF_12') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_89,plain,(
    k11_relat_1('#skF_13','#skF_12') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_93,plain,(
    ! [A_107,B_108,C_109] :
      ( r2_hidden(k4_tarski(A_107,B_108),C_109)
      | ~ r2_hidden(B_108,k11_relat_1(C_109,A_107))
      | ~ v1_relat_1(C_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_36,plain,(
    ! [C_82,A_67,D_85] :
      ( r2_hidden(C_82,k1_relat_1(A_67))
      | ~ r2_hidden(k4_tarski(C_82,D_85),A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_107,plain,(
    ! [A_110,C_111,B_112] :
      ( r2_hidden(A_110,k1_relat_1(C_111))
      | ~ r2_hidden(B_112,k11_relat_1(C_111,A_110))
      | ~ v1_relat_1(C_111) ) ),
    inference(resolution,[status(thm)],[c_93,c_36])).

tff(c_116,plain,(
    ! [A_113,C_114] :
      ( r2_hidden(A_113,k1_relat_1(C_114))
      | ~ v1_relat_1(C_114)
      | k11_relat_1(C_114,A_113) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_107])).

tff(c_56,plain,
    ( k11_relat_1('#skF_13','#skF_12') = k1_xboole_0
    | ~ r2_hidden('#skF_12',k1_relat_1('#skF_13')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_90,plain,(
    ~ r2_hidden('#skF_12',k1_relat_1('#skF_13')) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_56])).

tff(c_127,plain,
    ( ~ v1_relat_1('#skF_13')
    | k11_relat_1('#skF_13','#skF_12') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_116,c_90])).

tff(c_132,plain,(
    k11_relat_1('#skF_13','#skF_12') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_127])).

tff(c_134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_132])).

tff(c_135,plain,(
    r2_hidden('#skF_12',k1_relat_1('#skF_13')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_496,plain,(
    ! [D_158,A_159,B_160,E_161] :
      ( r2_hidden(D_158,k9_relat_1(A_159,B_160))
      | ~ r2_hidden(E_161,B_160)
      | ~ r2_hidden(k4_tarski(E_161,D_158),A_159)
      | ~ v1_relat_1(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_533,plain,(
    ! [D_162,A_163] :
      ( r2_hidden(D_162,k9_relat_1(A_163,k1_relat_1('#skF_13')))
      | ~ r2_hidden(k4_tarski('#skF_12',D_162),A_163)
      | ~ v1_relat_1(A_163) ) ),
    inference(resolution,[status(thm)],[c_135,c_496])).

tff(c_551,plain,(
    ! [D_162] :
      ( r2_hidden(D_162,k1_xboole_0)
      | ~ r2_hidden(k4_tarski('#skF_12',D_162),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_533])).

tff(c_558,plain,(
    ! [D_164] :
      ( r2_hidden(D_164,k1_xboole_0)
      | ~ r2_hidden(k4_tarski('#skF_12',D_164),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_551])).

tff(c_566,plain,(
    ! [B_90] :
      ( r2_hidden(B_90,k1_xboole_0)
      | ~ r2_hidden(B_90,k11_relat_1(k1_xboole_0,'#skF_12'))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_50,c_558])).

tff(c_571,plain,(
    ! [B_165] :
      ( r2_hidden(B_165,k1_xboole_0)
      | ~ r2_hidden(B_165,k11_relat_1(k1_xboole_0,'#skF_12')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_566])).

tff(c_596,plain,
    ( r2_hidden('#skF_1'(k11_relat_1(k1_xboole_0,'#skF_12')),k1_xboole_0)
    | k11_relat_1(k1_xboole_0,'#skF_12') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_571])).

tff(c_622,plain,(
    k11_relat_1(k1_xboole_0,'#skF_12') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_596])).

tff(c_10822,plain,(
    ! [C_474,D_475,B_476,A_477] :
      ( r2_hidden(k4_tarski(C_474,D_475),B_476)
      | ~ r2_hidden(k4_tarski(C_474,D_475),A_477)
      | ~ r1_tarski(A_477,B_476)
      | ~ v1_relat_1(A_477) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10892,plain,(
    ! [A_480,B_481,B_482,C_483] :
      ( r2_hidden(k4_tarski(A_480,B_481),B_482)
      | ~ r1_tarski(C_483,B_482)
      | ~ r2_hidden(B_481,k11_relat_1(C_483,A_480))
      | ~ v1_relat_1(C_483) ) ),
    inference(resolution,[status(thm)],[c_50,c_10822])).

tff(c_10896,plain,(
    ! [A_480,B_481,A_3] :
      ( r2_hidden(k4_tarski(A_480,B_481),A_3)
      | ~ r2_hidden(B_481,k11_relat_1(k1_xboole_0,A_480))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_10892])).

tff(c_10901,plain,(
    ! [A_484,B_485,A_486] :
      ( r2_hidden(k4_tarski(A_484,B_485),A_486)
      | ~ r2_hidden(B_485,k11_relat_1(k1_xboole_0,A_484)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_10896])).

tff(c_10995,plain,(
    ! [B_490,A_491] : ~ r2_hidden(B_490,k11_relat_1(k1_xboole_0,A_491)) ),
    inference(resolution,[status(thm)],[c_10901,c_8])).

tff(c_11005,plain,(
    ! [B_490] : ~ r2_hidden(B_490,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_622,c_10995])).

tff(c_136,plain,(
    k11_relat_1('#skF_13','#skF_12') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_192,plain,(
    ! [C_129,A_130] :
      ( r2_hidden(k4_tarski(C_129,'#skF_11'(A_130,k1_relat_1(A_130),C_129)),A_130)
      | ~ r2_hidden(C_129,k1_relat_1(A_130)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_52,plain,(
    ! [B_90,C_91,A_89] :
      ( r2_hidden(B_90,k11_relat_1(C_91,A_89))
      | ~ r2_hidden(k4_tarski(A_89,B_90),C_91)
      | ~ v1_relat_1(C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10860,plain,(
    ! [A_478,C_479] :
      ( r2_hidden('#skF_11'(A_478,k1_relat_1(A_478),C_479),k11_relat_1(A_478,C_479))
      | ~ v1_relat_1(A_478)
      | ~ r2_hidden(C_479,k1_relat_1(A_478)) ) ),
    inference(resolution,[status(thm)],[c_192,c_52])).

tff(c_10882,plain,
    ( r2_hidden('#skF_11'('#skF_13',k1_relat_1('#skF_13'),'#skF_12'),k1_xboole_0)
    | ~ v1_relat_1('#skF_13')
    | ~ r2_hidden('#skF_12',k1_relat_1('#skF_13')) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_10860])).

tff(c_10888,plain,(
    r2_hidden('#skF_11'('#skF_13',k1_relat_1('#skF_13'),'#skF_12'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_54,c_10882])).

tff(c_11051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11005,c_10888])).

tff(c_11053,plain,(
    k11_relat_1(k1_xboole_0,'#skF_12') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_596])).

tff(c_11545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11540,c_11053])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:17:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.46/3.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.46/3.33  
% 10.46/3.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.46/3.33  %$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_13 > #skF_10 > #skF_2 > #skF_8 > #skF_11 > #skF_5 > #skF_3 > #skF_7 > #skF_9 > #skF_12
% 10.46/3.33  
% 10.46/3.33  %Foreground sorts:
% 10.46/3.33  
% 10.46/3.33  
% 10.46/3.33  %Background operators:
% 10.46/3.33  
% 10.46/3.33  
% 10.46/3.33  %Foreground operators:
% 10.46/3.33  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 10.46/3.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.46/3.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.46/3.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.46/3.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.46/3.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.46/3.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.46/3.33  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 10.46/3.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.46/3.33  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 10.46/3.33  tff('#skF_13', type, '#skF_13': $i).
% 10.46/3.33  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 10.46/3.33  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 10.46/3.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.46/3.33  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 10.46/3.33  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 10.46/3.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.46/3.33  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 10.46/3.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.46/3.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.46/3.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.46/3.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.46/3.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.46/3.33  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 10.46/3.33  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 10.46/3.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.46/3.33  tff('#skF_12', type, '#skF_12': $i).
% 10.46/3.33  
% 10.46/3.35  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 10.46/3.35  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 10.46/3.35  tff(f_75, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 10.46/3.35  tff(f_91, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 10.46/3.35  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.46/3.35  tff(f_83, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 10.46/3.35  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 10.46/3.35  tff(f_40, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 10.46/3.35  tff(f_77, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 10.46/3.35  tff(f_71, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 10.46/3.35  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 10.46/3.35  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.46/3.35  tff(c_6, plain, (![A_4, B_5]: (k4_xboole_0(A_4, k2_xboole_0(A_4, B_5))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.46/3.35  tff(c_80, plain, (![A_99, B_100]: (v1_relat_1(k4_xboole_0(A_99, B_100)) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.46/3.35  tff(c_83, plain, (![A_4]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_4))), inference(superposition, [status(thm), theory('equality')], [c_6, c_80])).
% 10.46/3.35  tff(c_84, plain, (![A_4]: (~v1_relat_1(A_4))), inference(splitLeft, [status(thm)], [c_83])).
% 10.46/3.35  tff(c_54, plain, (v1_relat_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.46/3.35  tff(c_87, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_54])).
% 10.46/3.35  tff(c_88, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_83])).
% 10.46/3.35  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.46/3.35  tff(c_50, plain, (![A_89, B_90, C_91]: (r2_hidden(k4_tarski(A_89, B_90), C_91) | ~r2_hidden(B_90, k11_relat_1(C_91, A_89)) | ~v1_relat_1(C_91))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.46/3.35  tff(c_11116, plain, (![C_495, D_496, B_497, A_498]: (r2_hidden(k4_tarski(C_495, D_496), B_497) | ~r2_hidden(k4_tarski(C_495, D_496), A_498) | ~r1_tarski(A_498, B_497) | ~v1_relat_1(A_498))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.46/3.35  tff(c_11388, plain, (![A_517, B_518, B_519, C_520]: (r2_hidden(k4_tarski(A_517, B_518), B_519) | ~r1_tarski(C_520, B_519) | ~r2_hidden(B_518, k11_relat_1(C_520, A_517)) | ~v1_relat_1(C_520))), inference(resolution, [status(thm)], [c_50, c_11116])).
% 10.46/3.35  tff(c_11392, plain, (![A_517, B_518, A_3]: (r2_hidden(k4_tarski(A_517, B_518), A_3) | ~r2_hidden(B_518, k11_relat_1(k1_xboole_0, A_517)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_11388])).
% 10.46/3.35  tff(c_11397, plain, (![A_521, B_522, A_523]: (r2_hidden(k4_tarski(A_521, B_522), A_523) | ~r2_hidden(B_522, k11_relat_1(k1_xboole_0, A_521)))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_11392])).
% 10.46/3.35  tff(c_8, plain, (![A_6, B_7]: (~r2_hidden(A_6, k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 10.46/3.35  tff(c_11497, plain, (![B_527, A_528]: (~r2_hidden(B_527, k11_relat_1(k1_xboole_0, A_528)))), inference(resolution, [status(thm)], [c_11397, c_8])).
% 10.46/3.35  tff(c_11540, plain, (![A_528]: (k11_relat_1(k1_xboole_0, A_528)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_11497])).
% 10.46/3.35  tff(c_48, plain, (![A_88]: (k9_relat_1(k1_xboole_0, A_88)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.46/3.35  tff(c_62, plain, (r2_hidden('#skF_12', k1_relat_1('#skF_13')) | k11_relat_1('#skF_13', '#skF_12')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.46/3.35  tff(c_89, plain, (k11_relat_1('#skF_13', '#skF_12')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_62])).
% 10.46/3.35  tff(c_93, plain, (![A_107, B_108, C_109]: (r2_hidden(k4_tarski(A_107, B_108), C_109) | ~r2_hidden(B_108, k11_relat_1(C_109, A_107)) | ~v1_relat_1(C_109))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.46/3.35  tff(c_36, plain, (![C_82, A_67, D_85]: (r2_hidden(C_82, k1_relat_1(A_67)) | ~r2_hidden(k4_tarski(C_82, D_85), A_67))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.46/3.35  tff(c_107, plain, (![A_110, C_111, B_112]: (r2_hidden(A_110, k1_relat_1(C_111)) | ~r2_hidden(B_112, k11_relat_1(C_111, A_110)) | ~v1_relat_1(C_111))), inference(resolution, [status(thm)], [c_93, c_36])).
% 10.46/3.35  tff(c_116, plain, (![A_113, C_114]: (r2_hidden(A_113, k1_relat_1(C_114)) | ~v1_relat_1(C_114) | k11_relat_1(C_114, A_113)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_107])).
% 10.46/3.35  tff(c_56, plain, (k11_relat_1('#skF_13', '#skF_12')=k1_xboole_0 | ~r2_hidden('#skF_12', k1_relat_1('#skF_13'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.46/3.35  tff(c_90, plain, (~r2_hidden('#skF_12', k1_relat_1('#skF_13'))), inference(negUnitSimplification, [status(thm)], [c_89, c_56])).
% 10.46/3.35  tff(c_127, plain, (~v1_relat_1('#skF_13') | k11_relat_1('#skF_13', '#skF_12')=k1_xboole_0), inference(resolution, [status(thm)], [c_116, c_90])).
% 10.46/3.35  tff(c_132, plain, (k11_relat_1('#skF_13', '#skF_12')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_127])).
% 10.46/3.35  tff(c_134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_132])).
% 10.46/3.35  tff(c_135, plain, (r2_hidden('#skF_12', k1_relat_1('#skF_13'))), inference(splitRight, [status(thm)], [c_62])).
% 10.46/3.35  tff(c_496, plain, (![D_158, A_159, B_160, E_161]: (r2_hidden(D_158, k9_relat_1(A_159, B_160)) | ~r2_hidden(E_161, B_160) | ~r2_hidden(k4_tarski(E_161, D_158), A_159) | ~v1_relat_1(A_159))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.46/3.35  tff(c_533, plain, (![D_162, A_163]: (r2_hidden(D_162, k9_relat_1(A_163, k1_relat_1('#skF_13'))) | ~r2_hidden(k4_tarski('#skF_12', D_162), A_163) | ~v1_relat_1(A_163))), inference(resolution, [status(thm)], [c_135, c_496])).
% 10.46/3.35  tff(c_551, plain, (![D_162]: (r2_hidden(D_162, k1_xboole_0) | ~r2_hidden(k4_tarski('#skF_12', D_162), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48, c_533])).
% 10.46/3.35  tff(c_558, plain, (![D_164]: (r2_hidden(D_164, k1_xboole_0) | ~r2_hidden(k4_tarski('#skF_12', D_164), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_551])).
% 10.46/3.35  tff(c_566, plain, (![B_90]: (r2_hidden(B_90, k1_xboole_0) | ~r2_hidden(B_90, k11_relat_1(k1_xboole_0, '#skF_12')) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_50, c_558])).
% 10.46/3.35  tff(c_571, plain, (![B_165]: (r2_hidden(B_165, k1_xboole_0) | ~r2_hidden(B_165, k11_relat_1(k1_xboole_0, '#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_566])).
% 10.46/3.35  tff(c_596, plain, (r2_hidden('#skF_1'(k11_relat_1(k1_xboole_0, '#skF_12')), k1_xboole_0) | k11_relat_1(k1_xboole_0, '#skF_12')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_571])).
% 10.46/3.35  tff(c_622, plain, (k11_relat_1(k1_xboole_0, '#skF_12')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_596])).
% 10.46/3.35  tff(c_10822, plain, (![C_474, D_475, B_476, A_477]: (r2_hidden(k4_tarski(C_474, D_475), B_476) | ~r2_hidden(k4_tarski(C_474, D_475), A_477) | ~r1_tarski(A_477, B_476) | ~v1_relat_1(A_477))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.46/3.35  tff(c_10892, plain, (![A_480, B_481, B_482, C_483]: (r2_hidden(k4_tarski(A_480, B_481), B_482) | ~r1_tarski(C_483, B_482) | ~r2_hidden(B_481, k11_relat_1(C_483, A_480)) | ~v1_relat_1(C_483))), inference(resolution, [status(thm)], [c_50, c_10822])).
% 10.46/3.35  tff(c_10896, plain, (![A_480, B_481, A_3]: (r2_hidden(k4_tarski(A_480, B_481), A_3) | ~r2_hidden(B_481, k11_relat_1(k1_xboole_0, A_480)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_10892])).
% 10.46/3.35  tff(c_10901, plain, (![A_484, B_485, A_486]: (r2_hidden(k4_tarski(A_484, B_485), A_486) | ~r2_hidden(B_485, k11_relat_1(k1_xboole_0, A_484)))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_10896])).
% 10.46/3.35  tff(c_10995, plain, (![B_490, A_491]: (~r2_hidden(B_490, k11_relat_1(k1_xboole_0, A_491)))), inference(resolution, [status(thm)], [c_10901, c_8])).
% 10.46/3.35  tff(c_11005, plain, (![B_490]: (~r2_hidden(B_490, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_622, c_10995])).
% 10.46/3.35  tff(c_136, plain, (k11_relat_1('#skF_13', '#skF_12')=k1_xboole_0), inference(splitRight, [status(thm)], [c_62])).
% 10.46/3.35  tff(c_192, plain, (![C_129, A_130]: (r2_hidden(k4_tarski(C_129, '#skF_11'(A_130, k1_relat_1(A_130), C_129)), A_130) | ~r2_hidden(C_129, k1_relat_1(A_130)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.46/3.35  tff(c_52, plain, (![B_90, C_91, A_89]: (r2_hidden(B_90, k11_relat_1(C_91, A_89)) | ~r2_hidden(k4_tarski(A_89, B_90), C_91) | ~v1_relat_1(C_91))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.46/3.35  tff(c_10860, plain, (![A_478, C_479]: (r2_hidden('#skF_11'(A_478, k1_relat_1(A_478), C_479), k11_relat_1(A_478, C_479)) | ~v1_relat_1(A_478) | ~r2_hidden(C_479, k1_relat_1(A_478)))), inference(resolution, [status(thm)], [c_192, c_52])).
% 10.46/3.35  tff(c_10882, plain, (r2_hidden('#skF_11'('#skF_13', k1_relat_1('#skF_13'), '#skF_12'), k1_xboole_0) | ~v1_relat_1('#skF_13') | ~r2_hidden('#skF_12', k1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_10860])).
% 10.46/3.35  tff(c_10888, plain, (r2_hidden('#skF_11'('#skF_13', k1_relat_1('#skF_13'), '#skF_12'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_135, c_54, c_10882])).
% 10.46/3.35  tff(c_11051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11005, c_10888])).
% 10.46/3.35  tff(c_11053, plain, (k11_relat_1(k1_xboole_0, '#skF_12')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_596])).
% 10.46/3.35  tff(c_11545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11540, c_11053])).
% 10.46/3.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.46/3.35  
% 10.46/3.35  Inference rules
% 10.46/3.35  ----------------------
% 10.46/3.35  #Ref     : 0
% 10.46/3.35  #Sup     : 2664
% 10.46/3.35  #Fact    : 0
% 10.46/3.35  #Define  : 0
% 10.46/3.35  #Split   : 8
% 10.46/3.35  #Chain   : 0
% 10.46/3.35  #Close   : 0
% 10.46/3.35  
% 10.46/3.35  Ordering : KBO
% 10.46/3.35  
% 10.46/3.35  Simplification rules
% 10.46/3.35  ----------------------
% 10.46/3.35  #Subsume      : 899
% 10.46/3.35  #Demod        : 1312
% 10.46/3.35  #Tautology    : 379
% 10.46/3.35  #SimpNegUnit  : 224
% 10.46/3.35  #BackRed      : 11
% 10.46/3.35  
% 10.46/3.35  #Partial instantiations: 0
% 10.46/3.35  #Strategies tried      : 1
% 10.46/3.35  
% 10.46/3.35  Timing (in seconds)
% 10.46/3.35  ----------------------
% 10.46/3.35  Preprocessing        : 0.31
% 10.46/3.35  Parsing              : 0.16
% 10.46/3.35  CNF conversion       : 0.03
% 10.46/3.35  Main loop            : 2.29
% 10.46/3.35  Inferencing          : 0.57
% 10.46/3.35  Reduction            : 0.51
% 10.46/3.35  Demodulation         : 0.35
% 10.46/3.35  BG Simplification    : 0.07
% 10.46/3.35  Subsumption          : 0.97
% 10.46/3.35  Abstraction          : 0.09
% 10.46/3.35  MUC search           : 0.00
% 10.46/3.35  Cooper               : 0.00
% 10.46/3.35  Total                : 2.63
% 10.46/3.35  Index Insertion      : 0.00
% 10.46/3.35  Index Deletion       : 0.00
% 10.46/3.35  Index Matching       : 0.00
% 10.46/3.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
