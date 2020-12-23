%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:58 EST 2020

% Result     : Theorem 16.44s
% Output     : CNFRefutation 16.53s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 225 expanded)
%              Number of leaves         :   31 (  88 expanded)
%              Depth                    :   10
%              Number of atoms          :  137 ( 447 expanded)
%              Number of equality atoms :    4 (  50 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k7_relat_1(C,A),k7_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_relat_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    ! [A_28,B_29] :
      ( v1_relat_1(k7_relat_1(A_28,B_29))
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_146,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_1'(A_64,B_65),A_64)
      | r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_151,plain,(
    ! [A_64] : r1_tarski(A_64,A_64) ),
    inference(resolution,[status(thm)],[c_146,c_6])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_30,plain,(
    ! [C_32,A_30,B_31] :
      ( r1_tarski(k7_relat_1(C_32,A_30),k7_relat_1(C_32,B_31))
      | ~ r1_tarski(A_30,B_31)
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_11759,plain,(
    ! [C_655,A_656,B_657] :
      ( r1_tarski(k7_relat_1(C_655,A_656),k7_relat_1(C_655,B_657))
      | ~ r1_tarski(A_656,B_657)
      | ~ v1_relat_1(C_655) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_14,plain,(
    ! [A_13,C_15,B_14] :
      ( r1_tarski(A_13,C_15)
      | ~ r1_tarski(B_14,C_15)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12793,plain,(
    ! [A_720,C_721,B_722,A_723] :
      ( r1_tarski(A_720,k7_relat_1(C_721,B_722))
      | ~ r1_tarski(A_720,k7_relat_1(C_721,A_723))
      | ~ r1_tarski(A_723,B_722)
      | ~ v1_relat_1(C_721) ) ),
    inference(resolution,[status(thm)],[c_11759,c_14])).

tff(c_17372,plain,(
    ! [C_972,A_973,B_974,B_975] :
      ( r1_tarski(k7_relat_1(C_972,A_973),k7_relat_1(C_972,B_974))
      | ~ r1_tarski(B_975,B_974)
      | ~ r1_tarski(A_973,B_975)
      | ~ v1_relat_1(C_972) ) ),
    inference(resolution,[status(thm)],[c_30,c_12793])).

tff(c_27435,plain,(
    ! [C_1325,A_1326,A_1327,B_1328] :
      ( r1_tarski(k7_relat_1(C_1325,A_1326),k7_relat_1(C_1325,A_1327))
      | ~ r1_tarski(A_1326,k3_xboole_0(A_1327,B_1328))
      | ~ v1_relat_1(C_1325) ) ),
    inference(resolution,[status(thm)],[c_10,c_17372])).

tff(c_27608,plain,(
    ! [C_1329,A_1330,B_1331] :
      ( r1_tarski(k7_relat_1(C_1329,k3_xboole_0(A_1330,B_1331)),k7_relat_1(C_1329,A_1330))
      | ~ v1_relat_1(C_1329) ) ),
    inference(resolution,[status(thm)],[c_151,c_27435])).

tff(c_27650,plain,(
    ! [C_1329,B_2,A_1] :
      ( r1_tarski(k7_relat_1(C_1329,k3_xboole_0(B_2,A_1)),k7_relat_1(C_1329,A_1))
      | ~ v1_relat_1(C_1329) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_27608])).

tff(c_32,plain,(
    ! [B_34,A_33] :
      ( k2_relat_1(k7_relat_1(B_34,A_33)) = k9_relat_1(B_34,A_33)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_11617,plain,(
    ! [A_636,B_637] :
      ( r1_tarski(k2_relat_1(A_636),k2_relat_1(B_637))
      | ~ r1_tarski(A_636,B_637)
      | ~ v1_relat_1(B_637)
      | ~ v1_relat_1(A_636) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_13010,plain,(
    ! [A_734,B_735,A_736] :
      ( r1_tarski(k2_relat_1(A_734),k9_relat_1(B_735,A_736))
      | ~ r1_tarski(A_734,k7_relat_1(B_735,A_736))
      | ~ v1_relat_1(k7_relat_1(B_735,A_736))
      | ~ v1_relat_1(A_734)
      | ~ v1_relat_1(B_735) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_11617])).

tff(c_23769,plain,(
    ! [B_1141,A_1142,B_1143,A_1144] :
      ( r1_tarski(k9_relat_1(B_1141,A_1142),k9_relat_1(B_1143,A_1144))
      | ~ r1_tarski(k7_relat_1(B_1141,A_1142),k7_relat_1(B_1143,A_1144))
      | ~ v1_relat_1(k7_relat_1(B_1143,A_1144))
      | ~ v1_relat_1(k7_relat_1(B_1141,A_1142))
      | ~ v1_relat_1(B_1143)
      | ~ v1_relat_1(B_1141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_13010])).

tff(c_355,plain,(
    ! [A_96,B_97] :
      ( r1_tarski(k2_relat_1(A_96),k2_relat_1(B_97))
      | ~ r1_tarski(A_96,B_97)
      | ~ v1_relat_1(B_97)
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1609,plain,(
    ! [B_199,A_200,B_201] :
      ( r1_tarski(k9_relat_1(B_199,A_200),k2_relat_1(B_201))
      | ~ r1_tarski(k7_relat_1(B_199,A_200),B_201)
      | ~ v1_relat_1(B_201)
      | ~ v1_relat_1(k7_relat_1(B_199,A_200))
      | ~ v1_relat_1(B_199) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_355])).

tff(c_11127,plain,(
    ! [B_616,A_617,B_618,A_619] :
      ( r1_tarski(k9_relat_1(B_616,A_617),k9_relat_1(B_618,A_619))
      | ~ r1_tarski(k7_relat_1(B_616,A_617),k7_relat_1(B_618,A_619))
      | ~ v1_relat_1(k7_relat_1(B_618,A_619))
      | ~ v1_relat_1(k7_relat_1(B_616,A_617))
      | ~ v1_relat_1(B_616)
      | ~ v1_relat_1(B_618) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1609])).

tff(c_212,plain,(
    ! [A_81,B_82,C_83] :
      ( r1_tarski(A_81,k3_xboole_0(B_82,C_83))
      | ~ r1_tarski(A_81,C_83)
      | ~ r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_38,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k9_relat_1('#skF_4','#skF_2'),k9_relat_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_41,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(k9_relat_1('#skF_4','#skF_3'),k9_relat_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_38])).

tff(c_233,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4',k3_xboole_0('#skF_3','#skF_2')),k9_relat_1('#skF_4','#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_4',k3_xboole_0('#skF_3','#skF_2')),k9_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_212,c_41])).

tff(c_291,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4',k3_xboole_0('#skF_3','#skF_2')),k9_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_233])).

tff(c_11156,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_4',k3_xboole_0('#skF_3','#skF_2')),k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_4',k3_xboole_0('#skF_3','#skF_2')))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_11127,c_291])).

tff(c_11177,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_4',k3_xboole_0('#skF_3','#skF_2')),k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_4',k3_xboole_0('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_11156])).

tff(c_11180,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4',k3_xboole_0('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_11177])).

tff(c_11183,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_11180])).

tff(c_11187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_11183])).

tff(c_11188,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ r1_tarski(k7_relat_1('#skF_4',k3_xboole_0('#skF_3','#skF_2')),k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_11177])).

tff(c_11537,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4',k3_xboole_0('#skF_3','#skF_2')),k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_11188])).

tff(c_11540,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_11537])).

tff(c_11544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_10,c_11540])).

tff(c_11545,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_11188])).

tff(c_11549,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_11545])).

tff(c_11553,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_11549])).

tff(c_11554,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4',k3_xboole_0('#skF_3','#skF_2')),k9_relat_1('#skF_4','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_233])).

tff(c_23805,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_4',k3_xboole_0('#skF_3','#skF_2')),k7_relat_1('#skF_4','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_4',k3_xboole_0('#skF_3','#skF_2')))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_23769,c_11554])).

tff(c_23832,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_4',k3_xboole_0('#skF_3','#skF_2')),k7_relat_1('#skF_4','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_4',k3_xboole_0('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_23805])).

tff(c_34525,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4',k3_xboole_0('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_23832])).

tff(c_34528,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_34525])).

tff(c_34532,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34528])).

tff(c_34533,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2'))
    | ~ r1_tarski(k7_relat_1('#skF_4',k3_xboole_0('#skF_3','#skF_2')),k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_23832])).

tff(c_34941,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4',k3_xboole_0('#skF_3','#skF_2')),k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_34533])).

tff(c_34944,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_27650,c_34941])).

tff(c_34951,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34944])).

tff(c_34952,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_34533])).

tff(c_34956,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_34952])).

tff(c_34960,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34956])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:16:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.44/7.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.44/7.80  
% 16.44/7.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.44/7.80  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 16.44/7.80  
% 16.44/7.80  %Foreground sorts:
% 16.44/7.80  
% 16.44/7.80  
% 16.44/7.80  %Background operators:
% 16.44/7.80  
% 16.44/7.80  
% 16.44/7.80  %Foreground operators:
% 16.44/7.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.44/7.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.44/7.80  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 16.44/7.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.44/7.80  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 16.44/7.80  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 16.44/7.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.44/7.80  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 16.44/7.80  tff('#skF_2', type, '#skF_2': $i).
% 16.44/7.80  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 16.44/7.80  tff('#skF_3', type, '#skF_3': $i).
% 16.44/7.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.44/7.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.44/7.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.44/7.80  tff('#skF_4', type, '#skF_4': $i).
% 16.44/7.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.44/7.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.44/7.80  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.44/7.80  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 16.44/7.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.44/7.80  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 16.44/7.80  
% 16.53/7.81  tff(f_95, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_relat_1)).
% 16.53/7.81  tff(f_69, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 16.53/7.81  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 16.53/7.81  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 16.53/7.81  tff(f_36, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 16.53/7.81  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_relat_1)).
% 16.53/7.81  tff(f_48, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 16.53/7.81  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 16.53/7.81  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 16.53/7.81  tff(f_42, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 16.53/7.81  tff(c_40, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 16.53/7.81  tff(c_28, plain, (![A_28, B_29]: (v1_relat_1(k7_relat_1(A_28, B_29)) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_69])).
% 16.53/7.81  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.53/7.81  tff(c_146, plain, (![A_64, B_65]: (r2_hidden('#skF_1'(A_64, B_65), A_64) | r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.53/7.81  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.53/7.81  tff(c_151, plain, (![A_64]: (r1_tarski(A_64, A_64))), inference(resolution, [status(thm)], [c_146, c_6])).
% 16.53/7.81  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 16.53/7.81  tff(c_30, plain, (![C_32, A_30, B_31]: (r1_tarski(k7_relat_1(C_32, A_30), k7_relat_1(C_32, B_31)) | ~r1_tarski(A_30, B_31) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.53/7.81  tff(c_11759, plain, (![C_655, A_656, B_657]: (r1_tarski(k7_relat_1(C_655, A_656), k7_relat_1(C_655, B_657)) | ~r1_tarski(A_656, B_657) | ~v1_relat_1(C_655))), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.53/7.81  tff(c_14, plain, (![A_13, C_15, B_14]: (r1_tarski(A_13, C_15) | ~r1_tarski(B_14, C_15) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 16.53/7.81  tff(c_12793, plain, (![A_720, C_721, B_722, A_723]: (r1_tarski(A_720, k7_relat_1(C_721, B_722)) | ~r1_tarski(A_720, k7_relat_1(C_721, A_723)) | ~r1_tarski(A_723, B_722) | ~v1_relat_1(C_721))), inference(resolution, [status(thm)], [c_11759, c_14])).
% 16.53/7.81  tff(c_17372, plain, (![C_972, A_973, B_974, B_975]: (r1_tarski(k7_relat_1(C_972, A_973), k7_relat_1(C_972, B_974)) | ~r1_tarski(B_975, B_974) | ~r1_tarski(A_973, B_975) | ~v1_relat_1(C_972))), inference(resolution, [status(thm)], [c_30, c_12793])).
% 16.53/7.81  tff(c_27435, plain, (![C_1325, A_1326, A_1327, B_1328]: (r1_tarski(k7_relat_1(C_1325, A_1326), k7_relat_1(C_1325, A_1327)) | ~r1_tarski(A_1326, k3_xboole_0(A_1327, B_1328)) | ~v1_relat_1(C_1325))), inference(resolution, [status(thm)], [c_10, c_17372])).
% 16.53/7.81  tff(c_27608, plain, (![C_1329, A_1330, B_1331]: (r1_tarski(k7_relat_1(C_1329, k3_xboole_0(A_1330, B_1331)), k7_relat_1(C_1329, A_1330)) | ~v1_relat_1(C_1329))), inference(resolution, [status(thm)], [c_151, c_27435])).
% 16.53/7.81  tff(c_27650, plain, (![C_1329, B_2, A_1]: (r1_tarski(k7_relat_1(C_1329, k3_xboole_0(B_2, A_1)), k7_relat_1(C_1329, A_1)) | ~v1_relat_1(C_1329))), inference(superposition, [status(thm), theory('equality')], [c_2, c_27608])).
% 16.53/7.81  tff(c_32, plain, (![B_34, A_33]: (k2_relat_1(k7_relat_1(B_34, A_33))=k9_relat_1(B_34, A_33) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_79])).
% 16.53/7.81  tff(c_11617, plain, (![A_636, B_637]: (r1_tarski(k2_relat_1(A_636), k2_relat_1(B_637)) | ~r1_tarski(A_636, B_637) | ~v1_relat_1(B_637) | ~v1_relat_1(A_636))), inference(cnfTransformation, [status(thm)], [f_90])).
% 16.53/7.81  tff(c_13010, plain, (![A_734, B_735, A_736]: (r1_tarski(k2_relat_1(A_734), k9_relat_1(B_735, A_736)) | ~r1_tarski(A_734, k7_relat_1(B_735, A_736)) | ~v1_relat_1(k7_relat_1(B_735, A_736)) | ~v1_relat_1(A_734) | ~v1_relat_1(B_735))), inference(superposition, [status(thm), theory('equality')], [c_32, c_11617])).
% 16.53/7.81  tff(c_23769, plain, (![B_1141, A_1142, B_1143, A_1144]: (r1_tarski(k9_relat_1(B_1141, A_1142), k9_relat_1(B_1143, A_1144)) | ~r1_tarski(k7_relat_1(B_1141, A_1142), k7_relat_1(B_1143, A_1144)) | ~v1_relat_1(k7_relat_1(B_1143, A_1144)) | ~v1_relat_1(k7_relat_1(B_1141, A_1142)) | ~v1_relat_1(B_1143) | ~v1_relat_1(B_1141))), inference(superposition, [status(thm), theory('equality')], [c_32, c_13010])).
% 16.53/7.81  tff(c_355, plain, (![A_96, B_97]: (r1_tarski(k2_relat_1(A_96), k2_relat_1(B_97)) | ~r1_tarski(A_96, B_97) | ~v1_relat_1(B_97) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_90])).
% 16.53/7.81  tff(c_1609, plain, (![B_199, A_200, B_201]: (r1_tarski(k9_relat_1(B_199, A_200), k2_relat_1(B_201)) | ~r1_tarski(k7_relat_1(B_199, A_200), B_201) | ~v1_relat_1(B_201) | ~v1_relat_1(k7_relat_1(B_199, A_200)) | ~v1_relat_1(B_199))), inference(superposition, [status(thm), theory('equality')], [c_32, c_355])).
% 16.53/7.81  tff(c_11127, plain, (![B_616, A_617, B_618, A_619]: (r1_tarski(k9_relat_1(B_616, A_617), k9_relat_1(B_618, A_619)) | ~r1_tarski(k7_relat_1(B_616, A_617), k7_relat_1(B_618, A_619)) | ~v1_relat_1(k7_relat_1(B_618, A_619)) | ~v1_relat_1(k7_relat_1(B_616, A_617)) | ~v1_relat_1(B_616) | ~v1_relat_1(B_618))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1609])).
% 16.53/7.81  tff(c_212, plain, (![A_81, B_82, C_83]: (r1_tarski(A_81, k3_xboole_0(B_82, C_83)) | ~r1_tarski(A_81, C_83) | ~r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_42])).
% 16.53/7.81  tff(c_38, plain, (~r1_tarski(k9_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k9_relat_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 16.53/7.81  tff(c_41, plain, (~r1_tarski(k9_relat_1('#skF_4', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(k9_relat_1('#skF_4', '#skF_3'), k9_relat_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_38])).
% 16.53/7.81  tff(c_233, plain, (~r1_tarski(k9_relat_1('#skF_4', k3_xboole_0('#skF_3', '#skF_2')), k9_relat_1('#skF_4', '#skF_2')) | ~r1_tarski(k9_relat_1('#skF_4', k3_xboole_0('#skF_3', '#skF_2')), k9_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_212, c_41])).
% 16.53/7.81  tff(c_291, plain, (~r1_tarski(k9_relat_1('#skF_4', k3_xboole_0('#skF_3', '#skF_2')), k9_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_233])).
% 16.53/7.81  tff(c_11156, plain, (~r1_tarski(k7_relat_1('#skF_4', k3_xboole_0('#skF_3', '#skF_2')), k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_4', k3_xboole_0('#skF_3', '#skF_2'))) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_11127, c_291])).
% 16.53/7.81  tff(c_11177, plain, (~r1_tarski(k7_relat_1('#skF_4', k3_xboole_0('#skF_3', '#skF_2')), k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_4', k3_xboole_0('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_11156])).
% 16.53/7.81  tff(c_11180, plain, (~v1_relat_1(k7_relat_1('#skF_4', k3_xboole_0('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_11177])).
% 16.53/7.81  tff(c_11183, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_11180])).
% 16.53/7.81  tff(c_11187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_11183])).
% 16.53/7.81  tff(c_11188, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | ~r1_tarski(k7_relat_1('#skF_4', k3_xboole_0('#skF_3', '#skF_2')), k7_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_11177])).
% 16.53/7.81  tff(c_11537, plain, (~r1_tarski(k7_relat_1('#skF_4', k3_xboole_0('#skF_3', '#skF_2')), k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_11188])).
% 16.53/7.81  tff(c_11540, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_11537])).
% 16.53/7.81  tff(c_11544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_10, c_11540])).
% 16.53/7.81  tff(c_11545, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_11188])).
% 16.53/7.81  tff(c_11549, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_11545])).
% 16.53/7.81  tff(c_11553, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_11549])).
% 16.53/7.81  tff(c_11554, plain, (~r1_tarski(k9_relat_1('#skF_4', k3_xboole_0('#skF_3', '#skF_2')), k9_relat_1('#skF_4', '#skF_2'))), inference(splitRight, [status(thm)], [c_233])).
% 16.53/7.81  tff(c_23805, plain, (~r1_tarski(k7_relat_1('#skF_4', k3_xboole_0('#skF_3', '#skF_2')), k7_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_4', k3_xboole_0('#skF_3', '#skF_2'))) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_23769, c_11554])).
% 16.53/7.81  tff(c_23832, plain, (~r1_tarski(k7_relat_1('#skF_4', k3_xboole_0('#skF_3', '#skF_2')), k7_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_4', k3_xboole_0('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_23805])).
% 16.53/7.81  tff(c_34525, plain, (~v1_relat_1(k7_relat_1('#skF_4', k3_xboole_0('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_23832])).
% 16.53/7.81  tff(c_34528, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_34525])).
% 16.53/7.81  tff(c_34532, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_34528])).
% 16.53/7.81  tff(c_34533, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_2')) | ~r1_tarski(k7_relat_1('#skF_4', k3_xboole_0('#skF_3', '#skF_2')), k7_relat_1('#skF_4', '#skF_2'))), inference(splitRight, [status(thm)], [c_23832])).
% 16.53/7.81  tff(c_34941, plain, (~r1_tarski(k7_relat_1('#skF_4', k3_xboole_0('#skF_3', '#skF_2')), k7_relat_1('#skF_4', '#skF_2'))), inference(splitLeft, [status(thm)], [c_34533])).
% 16.53/7.81  tff(c_34944, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_27650, c_34941])).
% 16.53/7.81  tff(c_34951, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_34944])).
% 16.53/7.81  tff(c_34952, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(splitRight, [status(thm)], [c_34533])).
% 16.53/7.81  tff(c_34956, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_34952])).
% 16.53/7.81  tff(c_34960, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_34956])).
% 16.53/7.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.53/7.81  
% 16.53/7.81  Inference rules
% 16.53/7.81  ----------------------
% 16.53/7.81  #Ref     : 0
% 16.53/7.81  #Sup     : 8946
% 16.53/7.81  #Fact    : 0
% 16.53/7.81  #Define  : 0
% 16.53/7.81  #Split   : 11
% 16.53/7.81  #Chain   : 0
% 16.53/7.81  #Close   : 0
% 16.53/7.81  
% 16.53/7.81  Ordering : KBO
% 16.53/7.81  
% 16.53/7.81  Simplification rules
% 16.53/7.81  ----------------------
% 16.53/7.81  #Subsume      : 1575
% 16.53/7.81  #Demod        : 821
% 16.53/7.81  #Tautology    : 744
% 16.53/7.81  #SimpNegUnit  : 0
% 16.53/7.81  #BackRed      : 0
% 16.53/7.81  
% 16.53/7.81  #Partial instantiations: 0
% 16.53/7.81  #Strategies tried      : 1
% 16.53/7.81  
% 16.53/7.81  Timing (in seconds)
% 16.53/7.81  ----------------------
% 16.53/7.82  Preprocessing        : 0.31
% 16.53/7.82  Parsing              : 0.17
% 16.53/7.82  CNF conversion       : 0.02
% 16.53/7.82  Main loop            : 6.74
% 16.53/7.82  Inferencing          : 0.91
% 16.53/7.82  Reduction            : 2.65
% 16.53/7.82  Demodulation         : 2.33
% 16.53/7.82  BG Simplification    : 0.13
% 16.53/7.82  Subsumption          : 2.63
% 16.53/7.82  Abstraction          : 0.15
% 16.53/7.82  MUC search           : 0.00
% 16.53/7.82  Cooper               : 0.00
% 16.53/7.82  Total                : 7.08
% 16.53/7.82  Index Insertion      : 0.00
% 16.53/7.82  Index Deletion       : 0.00
% 16.53/7.82  Index Matching       : 0.00
% 16.53/7.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
