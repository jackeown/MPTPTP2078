%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:58 EST 2020

% Result     : Theorem 18.73s
% Output     : CNFRefutation 18.85s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 475 expanded)
%              Number of leaves         :   29 ( 164 expanded)
%              Depth                    :   15
%              Number of atoms          :  194 (1084 expanded)
%              Number of equality atoms :    5 (  52 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k7_relat_1(C,A),k7_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_41,plain,(
    ! [B_40,A_41] : k3_xboole_0(B_40,A_41) = k3_xboole_0(A_41,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    ! [B_40,A_41] : r1_tarski(k3_xboole_0(B_40,A_41),A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_4])).

tff(c_24,plain,(
    ! [C_27,A_25,B_26] :
      ( r1_tarski(k7_relat_1(C_27,A_25),k7_relat_1(C_27,B_26))
      | ~ r1_tarski(A_25,B_26)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    ! [A_23,B_24] :
      ( v1_relat_1(k7_relat_1(A_23,B_24))
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_30,plain,(
    ! [B_32,A_31] :
      ( k2_relat_1(k7_relat_1(B_32,A_31)) = k9_relat_1(B_32,A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_18846,plain,(
    ! [A_867,B_868] :
      ( r1_tarski(k2_relat_1(A_867),k2_relat_1(B_868))
      | ~ r1_tarski(A_867,B_868)
      | ~ v1_relat_1(B_868)
      | ~ v1_relat_1(A_867) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_18857,plain,(
    ! [A_867,B_32,A_31] :
      ( r1_tarski(k2_relat_1(A_867),k9_relat_1(B_32,A_31))
      | ~ r1_tarski(A_867,k7_relat_1(B_32,A_31))
      | ~ v1_relat_1(k7_relat_1(B_32,A_31))
      | ~ v1_relat_1(A_867)
      | ~ v1_relat_1(B_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_18846])).

tff(c_26,plain,(
    ! [B_29,A_28] :
      ( r1_tarski(k9_relat_1(B_29,A_28),k2_relat_1(B_29))
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_325,plain,(
    ! [A_86,B_87,C_88] :
      ( r1_tarski(A_86,k3_xboole_0(B_87,C_88))
      | ~ r1_tarski(A_86,C_88)
      | ~ r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,C_10)
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_19340,plain,(
    ! [A_904,B_905,C_906,A_907] :
      ( r1_tarski(A_904,k3_xboole_0(B_905,C_906))
      | ~ r1_tarski(A_904,A_907)
      | ~ r1_tarski(A_907,C_906)
      | ~ r1_tarski(A_907,B_905) ) ),
    inference(resolution,[status(thm)],[c_325,c_8])).

tff(c_24126,plain,(
    ! [B_1176,A_1177,B_1178,C_1179] :
      ( r1_tarski(k9_relat_1(B_1176,A_1177),k3_xboole_0(B_1178,C_1179))
      | ~ r1_tarski(k2_relat_1(B_1176),C_1179)
      | ~ r1_tarski(k2_relat_1(B_1176),B_1178)
      | ~ v1_relat_1(B_1176) ) ),
    inference(resolution,[status(thm)],[c_26,c_19340])).

tff(c_36,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_24164,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k9_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k2_relat_1('#skF_3'),k9_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24126,c_36])).

tff(c_24188,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k9_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k2_relat_1('#skF_3'),k9_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_24164])).

tff(c_24192,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_24188])).

tff(c_24195,plain,
    ( ~ r1_tarski('#skF_3',k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18857,c_24192])).

tff(c_24198,plain,
    ( ~ r1_tarski('#skF_3',k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_24195])).

tff(c_24199,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_24198])).

tff(c_24202,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_24199])).

tff(c_24206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_24202])).

tff(c_24208,plain,(
    v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_24198])).

tff(c_20466,plain,(
    ! [A_976,B_977,A_978] :
      ( r1_tarski(k2_relat_1(A_976),k9_relat_1(B_977,A_978))
      | ~ r1_tarski(A_976,k7_relat_1(B_977,A_978))
      | ~ v1_relat_1(k7_relat_1(B_977,A_978))
      | ~ v1_relat_1(A_976)
      | ~ v1_relat_1(B_977) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_18846])).

tff(c_32176,plain,(
    ! [B_1488,A_1489,B_1490,A_1491] :
      ( r1_tarski(k9_relat_1(B_1488,A_1489),k9_relat_1(B_1490,A_1491))
      | ~ r1_tarski(k7_relat_1(B_1488,A_1489),k7_relat_1(B_1490,A_1491))
      | ~ v1_relat_1(k7_relat_1(B_1490,A_1491))
      | ~ v1_relat_1(k7_relat_1(B_1488,A_1489))
      | ~ v1_relat_1(B_1490)
      | ~ v1_relat_1(B_1488) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_20466])).

tff(c_489,plain,(
    ! [A_112,B_113] :
      ( r1_tarski(k2_relat_1(A_112),k2_relat_1(B_113))
      | ~ r1_tarski(A_112,B_113)
      | ~ v1_relat_1(B_113)
      | ~ v1_relat_1(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_500,plain,(
    ! [A_112,B_32,A_31] :
      ( r1_tarski(k2_relat_1(A_112),k9_relat_1(B_32,A_31))
      | ~ r1_tarski(A_112,k7_relat_1(B_32,A_31))
      | ~ v1_relat_1(k7_relat_1(B_32,A_31))
      | ~ v1_relat_1(A_112)
      | ~ v1_relat_1(B_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_489])).

tff(c_931,plain,(
    ! [A_149,B_150,C_151,A_152] :
      ( r1_tarski(A_149,k3_xboole_0(B_150,C_151))
      | ~ r1_tarski(A_149,A_152)
      | ~ r1_tarski(A_152,C_151)
      | ~ r1_tarski(A_152,B_150) ) ),
    inference(resolution,[status(thm)],[c_325,c_8])).

tff(c_7575,plain,(
    ! [B_485,A_486,B_487,C_488] :
      ( r1_tarski(k9_relat_1(B_485,A_486),k3_xboole_0(B_487,C_488))
      | ~ r1_tarski(k2_relat_1(B_485),C_488)
      | ~ r1_tarski(k2_relat_1(B_485),B_487)
      | ~ v1_relat_1(B_485) ) ),
    inference(resolution,[status(thm)],[c_26,c_931])).

tff(c_7653,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k9_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k2_relat_1('#skF_3'),k9_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7575,c_36])).

tff(c_7689,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k9_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k2_relat_1('#skF_3'),k9_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_7653])).

tff(c_7690,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_7689])).

tff(c_7693,plain,
    ( ~ r1_tarski('#skF_3',k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_500,c_7690])).

tff(c_7696,plain,
    ( ~ r1_tarski('#skF_3',k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_7693])).

tff(c_7697,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_7696])).

tff(c_7700,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_7697])).

tff(c_7704,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_7700])).

tff(c_7706,plain,(
    v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_7696])).

tff(c_1826,plain,(
    ! [A_220,B_221,A_222] :
      ( r1_tarski(k2_relat_1(A_220),k9_relat_1(B_221,A_222))
      | ~ r1_tarski(A_220,k7_relat_1(B_221,A_222))
      | ~ v1_relat_1(k7_relat_1(B_221,A_222))
      | ~ v1_relat_1(A_220)
      | ~ v1_relat_1(B_221) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_489])).

tff(c_18424,plain,(
    ! [B_847,A_848,B_849,A_850] :
      ( r1_tarski(k9_relat_1(B_847,A_848),k9_relat_1(B_849,A_850))
      | ~ r1_tarski(k7_relat_1(B_847,A_848),k7_relat_1(B_849,A_850))
      | ~ v1_relat_1(k7_relat_1(B_849,A_850))
      | ~ v1_relat_1(k7_relat_1(B_847,A_848))
      | ~ v1_relat_1(B_849)
      | ~ v1_relat_1(B_847) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1826])).

tff(c_346,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_325,c_36])).

tff(c_417,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_346])).

tff(c_18454,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18424,c_417])).

tff(c_18480,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_7706,c_18454])).

tff(c_18774,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_18480])).

tff(c_18777,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_18774])).

tff(c_18781,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_18777])).

tff(c_18782,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_18480])).

tff(c_18786,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_18782])).

tff(c_18790,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4,c_18786])).

tff(c_18792,plain,(
    r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_346])).

tff(c_19407,plain,(
    ! [B_908,C_909] :
      ( r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(B_908,C_909))
      | ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),C_909)
      | ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),B_908) ) ),
    inference(resolution,[status(thm)],[c_18792,c_19340])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_145,plain,(
    ! [A_59,C_60,B_61] :
      ( r1_tarski(A_59,C_60)
      | ~ r1_tarski(B_61,C_60)
      | ~ r1_tarski(A_59,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_181,plain,(
    ! [A_68,A_69,B_70] :
      ( r1_tarski(A_68,A_69)
      | ~ r1_tarski(A_68,k3_xboole_0(A_69,B_70)) ) ),
    inference(resolution,[status(thm)],[c_4,c_145])).

tff(c_188,plain,(
    ! [A_68,A_1,B_2] :
      ( r1_tarski(A_68,A_1)
      | ~ r1_tarski(A_68,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_181])).

tff(c_19431,plain,(
    ! [C_909,B_908] :
      ( r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),C_909)
      | ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),C_909)
      | ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),B_908) ) ),
    inference(resolution,[status(thm)],[c_19407,c_188])).

tff(c_24436,plain,(
    ! [B_1183] : ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),B_1183) ),
    inference(splitLeft,[status(thm)],[c_19431])).

tff(c_24456,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_24436])).

tff(c_24470,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_24456])).

tff(c_24571,plain,(
    ! [C_1192] :
      ( r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),C_1192)
      | ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),C_1192) ) ),
    inference(splitRight,[status(thm)],[c_19431])).

tff(c_18791,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_346])).

tff(c_24655,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24571,c_18791])).

tff(c_32195,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32176,c_24655])).

tff(c_32247,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_24208,c_32195])).

tff(c_32275,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_32247])).

tff(c_32359,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_32275])).

tff(c_32363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32359])).

tff(c_32365,plain,(
    v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_32247])).

tff(c_32224,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32176,c_18791])).

tff(c_32266,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32224])).

tff(c_43119,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32365,c_32266])).

tff(c_43120,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_43119])).

tff(c_43123,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_43120])).

tff(c_43127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_43123])).

tff(c_43128,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_43119])).

tff(c_43132,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_43128])).

tff(c_43136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_56,c_43132])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:12:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.73/9.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.73/9.47  
% 18.73/9.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.73/9.47  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 18.73/9.47  
% 18.73/9.47  %Foreground sorts:
% 18.73/9.47  
% 18.73/9.47  
% 18.73/9.47  %Background operators:
% 18.73/9.47  
% 18.73/9.47  
% 18.73/9.47  %Foreground operators:
% 18.73/9.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.73/9.47  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 18.73/9.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.73/9.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 18.73/9.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 18.73/9.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.73/9.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 18.73/9.47  tff('#skF_2', type, '#skF_2': $i).
% 18.73/9.47  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 18.73/9.47  tff('#skF_3', type, '#skF_3': $i).
% 18.73/9.47  tff('#skF_1', type, '#skF_1': $i).
% 18.73/9.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 18.73/9.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.73/9.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 18.73/9.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.73/9.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.73/9.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 18.73/9.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 18.73/9.47  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 18.73/9.47  
% 18.85/9.49  tff(f_96, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_relat_1)).
% 18.85/9.49  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 18.85/9.49  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 18.85/9.49  tff(f_68, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_relat_1)).
% 18.85/9.49  tff(f_62, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 18.85/9.49  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 18.85/9.49  tff(f_91, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 18.85/9.49  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 18.85/9.49  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 18.85/9.49  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 18.85/9.49  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 18.85/9.49  tff(c_41, plain, (![B_40, A_41]: (k3_xboole_0(B_40, A_41)=k3_xboole_0(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.85/9.49  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 18.85/9.49  tff(c_56, plain, (![B_40, A_41]: (r1_tarski(k3_xboole_0(B_40, A_41), A_41))), inference(superposition, [status(thm), theory('equality')], [c_41, c_4])).
% 18.85/9.49  tff(c_24, plain, (![C_27, A_25, B_26]: (r1_tarski(k7_relat_1(C_27, A_25), k7_relat_1(C_27, B_26)) | ~r1_tarski(A_25, B_26) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_68])).
% 18.85/9.49  tff(c_22, plain, (![A_23, B_24]: (v1_relat_1(k7_relat_1(A_23, B_24)) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_62])).
% 18.85/9.49  tff(c_30, plain, (![B_32, A_31]: (k2_relat_1(k7_relat_1(B_32, A_31))=k9_relat_1(B_32, A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_80])).
% 18.85/9.49  tff(c_18846, plain, (![A_867, B_868]: (r1_tarski(k2_relat_1(A_867), k2_relat_1(B_868)) | ~r1_tarski(A_867, B_868) | ~v1_relat_1(B_868) | ~v1_relat_1(A_867))), inference(cnfTransformation, [status(thm)], [f_91])).
% 18.85/9.49  tff(c_18857, plain, (![A_867, B_32, A_31]: (r1_tarski(k2_relat_1(A_867), k9_relat_1(B_32, A_31)) | ~r1_tarski(A_867, k7_relat_1(B_32, A_31)) | ~v1_relat_1(k7_relat_1(B_32, A_31)) | ~v1_relat_1(A_867) | ~v1_relat_1(B_32))), inference(superposition, [status(thm), theory('equality')], [c_30, c_18846])).
% 18.85/9.49  tff(c_26, plain, (![B_29, A_28]: (r1_tarski(k9_relat_1(B_29, A_28), k2_relat_1(B_29)) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_72])).
% 18.85/9.49  tff(c_325, plain, (![A_86, B_87, C_88]: (r1_tarski(A_86, k3_xboole_0(B_87, C_88)) | ~r1_tarski(A_86, C_88) | ~r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_35])).
% 18.85/9.49  tff(c_8, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, C_10) | ~r1_tarski(B_9, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 18.85/9.49  tff(c_19340, plain, (![A_904, B_905, C_906, A_907]: (r1_tarski(A_904, k3_xboole_0(B_905, C_906)) | ~r1_tarski(A_904, A_907) | ~r1_tarski(A_907, C_906) | ~r1_tarski(A_907, B_905))), inference(resolution, [status(thm)], [c_325, c_8])).
% 18.85/9.49  tff(c_24126, plain, (![B_1176, A_1177, B_1178, C_1179]: (r1_tarski(k9_relat_1(B_1176, A_1177), k3_xboole_0(B_1178, C_1179)) | ~r1_tarski(k2_relat_1(B_1176), C_1179) | ~r1_tarski(k2_relat_1(B_1176), B_1178) | ~v1_relat_1(B_1176))), inference(resolution, [status(thm)], [c_26, c_19340])).
% 18.85/9.49  tff(c_36, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 18.85/9.49  tff(c_24164, plain, (~r1_tarski(k2_relat_1('#skF_3'), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k2_relat_1('#skF_3'), k9_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24126, c_36])).
% 18.85/9.49  tff(c_24188, plain, (~r1_tarski(k2_relat_1('#skF_3'), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k2_relat_1('#skF_3'), k9_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_24164])).
% 18.85/9.49  tff(c_24192, plain, (~r1_tarski(k2_relat_1('#skF_3'), k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_24188])).
% 18.85/9.49  tff(c_24195, plain, (~r1_tarski('#skF_3', k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18857, c_24192])).
% 18.85/9.49  tff(c_24198, plain, (~r1_tarski('#skF_3', k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_24195])).
% 18.85/9.49  tff(c_24199, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_24198])).
% 18.85/9.49  tff(c_24202, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_24199])).
% 18.85/9.49  tff(c_24206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_24202])).
% 18.85/9.49  tff(c_24208, plain, (v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_24198])).
% 18.85/9.49  tff(c_20466, plain, (![A_976, B_977, A_978]: (r1_tarski(k2_relat_1(A_976), k9_relat_1(B_977, A_978)) | ~r1_tarski(A_976, k7_relat_1(B_977, A_978)) | ~v1_relat_1(k7_relat_1(B_977, A_978)) | ~v1_relat_1(A_976) | ~v1_relat_1(B_977))), inference(superposition, [status(thm), theory('equality')], [c_30, c_18846])).
% 18.85/9.49  tff(c_32176, plain, (![B_1488, A_1489, B_1490, A_1491]: (r1_tarski(k9_relat_1(B_1488, A_1489), k9_relat_1(B_1490, A_1491)) | ~r1_tarski(k7_relat_1(B_1488, A_1489), k7_relat_1(B_1490, A_1491)) | ~v1_relat_1(k7_relat_1(B_1490, A_1491)) | ~v1_relat_1(k7_relat_1(B_1488, A_1489)) | ~v1_relat_1(B_1490) | ~v1_relat_1(B_1488))), inference(superposition, [status(thm), theory('equality')], [c_30, c_20466])).
% 18.85/9.49  tff(c_489, plain, (![A_112, B_113]: (r1_tarski(k2_relat_1(A_112), k2_relat_1(B_113)) | ~r1_tarski(A_112, B_113) | ~v1_relat_1(B_113) | ~v1_relat_1(A_112))), inference(cnfTransformation, [status(thm)], [f_91])).
% 18.85/9.49  tff(c_500, plain, (![A_112, B_32, A_31]: (r1_tarski(k2_relat_1(A_112), k9_relat_1(B_32, A_31)) | ~r1_tarski(A_112, k7_relat_1(B_32, A_31)) | ~v1_relat_1(k7_relat_1(B_32, A_31)) | ~v1_relat_1(A_112) | ~v1_relat_1(B_32))), inference(superposition, [status(thm), theory('equality')], [c_30, c_489])).
% 18.85/9.49  tff(c_931, plain, (![A_149, B_150, C_151, A_152]: (r1_tarski(A_149, k3_xboole_0(B_150, C_151)) | ~r1_tarski(A_149, A_152) | ~r1_tarski(A_152, C_151) | ~r1_tarski(A_152, B_150))), inference(resolution, [status(thm)], [c_325, c_8])).
% 18.85/9.49  tff(c_7575, plain, (![B_485, A_486, B_487, C_488]: (r1_tarski(k9_relat_1(B_485, A_486), k3_xboole_0(B_487, C_488)) | ~r1_tarski(k2_relat_1(B_485), C_488) | ~r1_tarski(k2_relat_1(B_485), B_487) | ~v1_relat_1(B_485))), inference(resolution, [status(thm)], [c_26, c_931])).
% 18.85/9.49  tff(c_7653, plain, (~r1_tarski(k2_relat_1('#skF_3'), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k2_relat_1('#skF_3'), k9_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_7575, c_36])).
% 18.85/9.49  tff(c_7689, plain, (~r1_tarski(k2_relat_1('#skF_3'), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k2_relat_1('#skF_3'), k9_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_7653])).
% 18.85/9.49  tff(c_7690, plain, (~r1_tarski(k2_relat_1('#skF_3'), k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_7689])).
% 18.85/9.49  tff(c_7693, plain, (~r1_tarski('#skF_3', k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_500, c_7690])).
% 18.85/9.49  tff(c_7696, plain, (~r1_tarski('#skF_3', k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_7693])).
% 18.85/9.49  tff(c_7697, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_7696])).
% 18.85/9.49  tff(c_7700, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_7697])).
% 18.85/9.49  tff(c_7704, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_7700])).
% 18.85/9.49  tff(c_7706, plain, (v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_7696])).
% 18.85/9.49  tff(c_1826, plain, (![A_220, B_221, A_222]: (r1_tarski(k2_relat_1(A_220), k9_relat_1(B_221, A_222)) | ~r1_tarski(A_220, k7_relat_1(B_221, A_222)) | ~v1_relat_1(k7_relat_1(B_221, A_222)) | ~v1_relat_1(A_220) | ~v1_relat_1(B_221))), inference(superposition, [status(thm), theory('equality')], [c_30, c_489])).
% 18.85/9.49  tff(c_18424, plain, (![B_847, A_848, B_849, A_850]: (r1_tarski(k9_relat_1(B_847, A_848), k9_relat_1(B_849, A_850)) | ~r1_tarski(k7_relat_1(B_847, A_848), k7_relat_1(B_849, A_850)) | ~v1_relat_1(k7_relat_1(B_849, A_850)) | ~v1_relat_1(k7_relat_1(B_847, A_848)) | ~v1_relat_1(B_849) | ~v1_relat_1(B_847))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1826])).
% 18.85/9.49  tff(c_346, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_325, c_36])).
% 18.85/9.49  tff(c_417, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_346])).
% 18.85/9.49  tff(c_18454, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18424, c_417])).
% 18.85/9.49  tff(c_18480, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_7706, c_18454])).
% 18.85/9.49  tff(c_18774, plain, (~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_18480])).
% 18.85/9.49  tff(c_18777, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_18774])).
% 18.85/9.49  tff(c_18781, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_18777])).
% 18.85/9.49  tff(c_18782, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_18480])).
% 18.85/9.49  tff(c_18786, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_18782])).
% 18.85/9.49  tff(c_18790, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_4, c_18786])).
% 18.85/9.49  tff(c_18792, plain, (r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_346])).
% 18.85/9.49  tff(c_19407, plain, (![B_908, C_909]: (r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(B_908, C_909)) | ~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), C_909) | ~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), B_908))), inference(resolution, [status(thm)], [c_18792, c_19340])).
% 18.85/9.49  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.85/9.49  tff(c_145, plain, (![A_59, C_60, B_61]: (r1_tarski(A_59, C_60) | ~r1_tarski(B_61, C_60) | ~r1_tarski(A_59, B_61))), inference(cnfTransformation, [status(thm)], [f_41])).
% 18.85/9.49  tff(c_181, plain, (![A_68, A_69, B_70]: (r1_tarski(A_68, A_69) | ~r1_tarski(A_68, k3_xboole_0(A_69, B_70)))), inference(resolution, [status(thm)], [c_4, c_145])).
% 18.85/9.49  tff(c_188, plain, (![A_68, A_1, B_2]: (r1_tarski(A_68, A_1) | ~r1_tarski(A_68, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_181])).
% 18.85/9.49  tff(c_19431, plain, (![C_909, B_908]: (r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), C_909) | ~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), C_909) | ~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), B_908))), inference(resolution, [status(thm)], [c_19407, c_188])).
% 18.85/9.49  tff(c_24436, plain, (![B_1183]: (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), B_1183))), inference(splitLeft, [status(thm)], [c_19431])).
% 18.85/9.49  tff(c_24456, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_24436])).
% 18.85/9.49  tff(c_24470, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_24456])).
% 18.85/9.49  tff(c_24571, plain, (![C_1192]: (r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), C_1192) | ~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), C_1192))), inference(splitRight, [status(thm)], [c_19431])).
% 18.85/9.49  tff(c_18791, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_346])).
% 18.85/9.49  tff(c_24655, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_24571, c_18791])).
% 18.85/9.49  tff(c_32195, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32176, c_24655])).
% 18.85/9.49  tff(c_32247, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_24208, c_32195])).
% 18.85/9.49  tff(c_32275, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_32247])).
% 18.85/9.49  tff(c_32359, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_32275])).
% 18.85/9.49  tff(c_32363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_32359])).
% 18.85/9.49  tff(c_32365, plain, (v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_32247])).
% 18.85/9.49  tff(c_32224, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32176, c_18791])).
% 18.85/9.49  tff(c_32266, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32224])).
% 18.85/9.49  tff(c_43119, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32365, c_32266])).
% 18.85/9.49  tff(c_43120, plain, (~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_43119])).
% 18.85/9.49  tff(c_43123, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_43120])).
% 18.85/9.49  tff(c_43127, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_43123])).
% 18.85/9.49  tff(c_43128, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_43119])).
% 18.85/9.49  tff(c_43132, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_43128])).
% 18.85/9.49  tff(c_43136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_56, c_43132])).
% 18.85/9.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.85/9.49  
% 18.85/9.49  Inference rules
% 18.85/9.49  ----------------------
% 18.85/9.49  #Ref     : 0
% 18.85/9.49  #Sup     : 10803
% 18.85/9.49  #Fact    : 0
% 18.85/9.49  #Define  : 0
% 18.85/9.49  #Split   : 16
% 18.85/9.49  #Chain   : 0
% 18.85/9.49  #Close   : 0
% 18.85/9.49  
% 18.85/9.49  Ordering : KBO
% 18.85/9.49  
% 18.85/9.49  Simplification rules
% 18.85/9.49  ----------------------
% 18.85/9.49  #Subsume      : 1604
% 18.85/9.49  #Demod        : 1119
% 18.85/9.49  #Tautology    : 944
% 18.85/9.49  #SimpNegUnit  : 0
% 18.85/9.49  #BackRed      : 0
% 18.85/9.49  
% 18.85/9.49  #Partial instantiations: 0
% 18.85/9.49  #Strategies tried      : 1
% 18.85/9.49  
% 18.85/9.49  Timing (in seconds)
% 18.85/9.49  ----------------------
% 18.85/9.49  Preprocessing        : 0.31
% 18.85/9.49  Parsing              : 0.17
% 18.85/9.49  CNF conversion       : 0.02
% 18.85/9.49  Main loop            : 8.39
% 18.85/9.49  Inferencing          : 1.12
% 18.85/9.49  Reduction            : 3.40
% 18.85/9.49  Demodulation         : 3.01
% 18.85/9.49  BG Simplification    : 0.15
% 18.85/9.49  Subsumption          : 3.25
% 18.85/9.49  Abstraction          : 0.18
% 18.85/9.49  MUC search           : 0.00
% 18.85/9.49  Cooper               : 0.00
% 18.85/9.49  Total                : 8.74
% 18.85/9.49  Index Insertion      : 0.00
% 18.85/9.49  Index Deletion       : 0.00
% 18.85/9.49  Index Matching       : 0.00
% 18.85/9.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
