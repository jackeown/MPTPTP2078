%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0296+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:04 EST 2020

% Result     : Theorem 10.37s
% Output     : CNFRefutation 10.37s
% Verified   : 
% Statistics : Number of formulae       :   80 (1893 expanded)
%              Number of leaves         :   24 ( 644 expanded)
%              Depth                    :   24
%              Number of atoms          :  126 (4861 expanded)
%              Number of equality atoms :   40 (1590 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > #skF_1 > #skF_11 > #skF_4 > #skF_10 > #skF_13 > #skF_2 > #skF_6 > #skF_9 > #skF_7 > #skF_5 > #skF_3 > #skF_8 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ~ ( r2_hidden(A,k3_xboole_0(k2_zfmisc_1(B,C),k2_zfmisc_1(D,E)))
          & ! [F,G] :
              ~ ( A = k4_tarski(F,G)
                & r2_hidden(F,k3_xboole_0(B,D))
                & r2_hidden(G,k3_xboole_0(C,E)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( k4_tarski(A,B) = k4_tarski(C,D)
     => ( A = C
        & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_zfmisc_1)).

tff(c_50,plain,(
    r2_hidden('#skF_9',k3_xboole_0(k2_zfmisc_1('#skF_10','#skF_11'),k2_zfmisc_1('#skF_12','#skF_13'))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_28,plain,(
    ! [D_40,B_36,A_35] :
      ( r2_hidden(D_40,B_36)
      | ~ r2_hidden(D_40,k3_xboole_0(A_35,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_69,plain,(
    r2_hidden('#skF_9',k2_zfmisc_1('#skF_12','#skF_13')) ),
    inference(resolution,[status(thm)],[c_50,c_28])).

tff(c_8,plain,(
    ! [A_1,B_2,D_28] :
      ( r2_hidden('#skF_5'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),A_1)
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_30,plain,(
    ! [D_40,A_35,B_36] :
      ( r2_hidden(D_40,A_35)
      | ~ r2_hidden(D_40,k3_xboole_0(A_35,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_70,plain,(
    r2_hidden('#skF_9',k2_zfmisc_1('#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_50,c_30])).

tff(c_4,plain,(
    ! [A_1,B_2,D_28] :
      ( k4_tarski('#skF_5'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),'#skF_6'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28)) = D_28
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_377,plain,(
    ! [A_113,B_114,D_115] :
      ( k4_tarski('#skF_5'(A_113,B_114,k2_zfmisc_1(A_113,B_114),D_115),'#skF_6'(A_113,B_114,k2_zfmisc_1(A_113,B_114),D_115)) = D_115
      | ~ r2_hidden(D_115,k2_zfmisc_1(A_113,B_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_44,plain,(
    ! [D_44,B_42,C_43,A_41] :
      ( D_44 = B_42
      | k4_tarski(C_43,D_44) != k4_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_411,plain,(
    ! [A_117,D_119,B_120,A_118,B_116] :
      ( B_120 = '#skF_6'(A_118,B_116,k2_zfmisc_1(A_118,B_116),D_119)
      | k4_tarski(A_117,B_120) != D_119
      | ~ r2_hidden(D_119,k2_zfmisc_1(A_118,B_116)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_44])).

tff(c_2281,plain,(
    ! [B_357,A_358,D_354,B_356,A_355] :
      ( '#skF_6'(A_358,B_356,k2_zfmisc_1(A_358,B_356),D_354) = '#skF_6'(A_355,B_357,k2_zfmisc_1(A_355,B_357),D_354)
      | ~ r2_hidden(D_354,k2_zfmisc_1(A_355,B_357))
      | ~ r2_hidden(D_354,k2_zfmisc_1(A_358,B_356)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_411])).

tff(c_2571,plain,(
    ! [A_359,B_360] :
      ( '#skF_6'(A_359,B_360,k2_zfmisc_1(A_359,B_360),'#skF_9') = '#skF_6'('#skF_10','#skF_11',k2_zfmisc_1('#skF_10','#skF_11'),'#skF_9')
      | ~ r2_hidden('#skF_9',k2_zfmisc_1(A_359,B_360)) ) ),
    inference(resolution,[status(thm)],[c_70,c_2281])).

tff(c_2578,plain,(
    '#skF_6'('#skF_10','#skF_11',k2_zfmisc_1('#skF_10','#skF_11'),'#skF_9') = '#skF_6'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_69,c_2571])).

tff(c_6,plain,(
    ! [A_1,B_2,D_28] :
      ( r2_hidden('#skF_6'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),B_2)
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2586,plain,
    ( r2_hidden('#skF_6'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_9'),'#skF_11')
    | ~ r2_hidden('#skF_9',k2_zfmisc_1('#skF_10','#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2578,c_6])).

tff(c_2592,plain,(
    r2_hidden('#skF_6'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_9'),'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2586])).

tff(c_2,plain,(
    ! [E_33,F_34,A_1,B_2] :
      ( r2_hidden(k4_tarski(E_33,F_34),k2_zfmisc_1(A_1,B_2))
      | ~ r2_hidden(F_34,B_2)
      | ~ r2_hidden(E_33,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2644,plain,(
    ! [D_365,A_364,B_363,B_361,A_362] :
      ( r2_hidden(D_365,k2_zfmisc_1(A_364,B_363))
      | ~ r2_hidden('#skF_6'(A_362,B_361,k2_zfmisc_1(A_362,B_361),D_365),B_363)
      | ~ r2_hidden('#skF_5'(A_362,B_361,k2_zfmisc_1(A_362,B_361),D_365),A_364)
      | ~ r2_hidden(D_365,k2_zfmisc_1(A_362,B_361)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_2])).

tff(c_2646,plain,(
    ! [A_364] :
      ( r2_hidden('#skF_9',k2_zfmisc_1(A_364,'#skF_11'))
      | ~ r2_hidden('#skF_5'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_9'),A_364)
      | ~ r2_hidden('#skF_9',k2_zfmisc_1('#skF_12','#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_2592,c_2644])).

tff(c_2688,plain,(
    ! [A_373] :
      ( r2_hidden('#skF_9',k2_zfmisc_1(A_373,'#skF_11'))
      | ~ r2_hidden('#skF_5'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_9'),A_373) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_2646])).

tff(c_2692,plain,
    ( r2_hidden('#skF_9',k2_zfmisc_1('#skF_12','#skF_11'))
    | ~ r2_hidden('#skF_9',k2_zfmisc_1('#skF_12','#skF_13')) ),
    inference(resolution,[status(thm)],[c_8,c_2688])).

tff(c_2699,plain,(
    r2_hidden('#skF_9',k2_zfmisc_1('#skF_12','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_2692])).

tff(c_4251,plain,(
    ! [A_419,B_420] :
      ( '#skF_6'(A_419,B_420,k2_zfmisc_1(A_419,B_420),'#skF_9') = '#skF_6'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_9')
      | ~ r2_hidden('#skF_9',k2_zfmisc_1(A_419,B_420)) ) ),
    inference(resolution,[status(thm)],[c_69,c_2281])).

tff(c_4258,plain,(
    '#skF_6'('#skF_12','#skF_11',k2_zfmisc_1('#skF_12','#skF_11'),'#skF_9') = '#skF_6'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_2699,c_4251])).

tff(c_4268,plain,
    ( k4_tarski('#skF_5'('#skF_12','#skF_11',k2_zfmisc_1('#skF_12','#skF_11'),'#skF_9'),'#skF_6'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_9')) = '#skF_9'
    | ~ r2_hidden('#skF_9',k2_zfmisc_1('#skF_12','#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4258,c_4])).

tff(c_4277,plain,(
    k4_tarski('#skF_5'('#skF_12','#skF_11',k2_zfmisc_1('#skF_12','#skF_11'),'#skF_9'),'#skF_6'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_9')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2699,c_4268])).

tff(c_2583,plain,
    ( k4_tarski('#skF_5'('#skF_10','#skF_11',k2_zfmisc_1('#skF_10','#skF_11'),'#skF_9'),'#skF_6'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_9')) = '#skF_9'
    | ~ r2_hidden('#skF_9',k2_zfmisc_1('#skF_10','#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2578,c_4])).

tff(c_2590,plain,(
    k4_tarski('#skF_5'('#skF_10','#skF_11',k2_zfmisc_1('#skF_10','#skF_11'),'#skF_9'),'#skF_6'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_9')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2583])).

tff(c_46,plain,(
    ! [C_43,A_41,D_44,B_42] :
      ( C_43 = A_41
      | k4_tarski(C_43,D_44) != k4_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2635,plain,(
    ! [C_43,D_44] :
      ( C_43 = '#skF_5'('#skF_10','#skF_11',k2_zfmisc_1('#skF_10','#skF_11'),'#skF_9')
      | k4_tarski(C_43,D_44) != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2590,c_46])).

tff(c_4335,plain,(
    '#skF_5'('#skF_10','#skF_11',k2_zfmisc_1('#skF_10','#skF_11'),'#skF_9') = '#skF_5'('#skF_12','#skF_11',k2_zfmisc_1('#skF_12','#skF_11'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_4277,c_2635])).

tff(c_398,plain,(
    ! [A_113,D_115,B_114,A_41,B_42] :
      ( A_41 = '#skF_5'(A_113,B_114,k2_zfmisc_1(A_113,B_114),D_115)
      | k4_tarski(A_41,B_42) != D_115
      | ~ r2_hidden(D_115,k2_zfmisc_1(A_113,B_114)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_46])).

tff(c_418,plain,(
    ! [A_113,B_114,A_41,B_42] :
      ( '#skF_5'(A_113,B_114,k2_zfmisc_1(A_113,B_114),k4_tarski(A_41,B_42)) = A_41
      | ~ r2_hidden(k4_tarski(A_41,B_42),k2_zfmisc_1(A_113,B_114)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_398])).

tff(c_2614,plain,(
    ! [A_113,B_114] :
      ( '#skF_5'(A_113,B_114,k2_zfmisc_1(A_113,B_114),k4_tarski('#skF_5'('#skF_10','#skF_11',k2_zfmisc_1('#skF_10','#skF_11'),'#skF_9'),'#skF_6'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_9'))) = '#skF_5'('#skF_10','#skF_11',k2_zfmisc_1('#skF_10','#skF_11'),'#skF_9')
      | ~ r2_hidden('#skF_9',k2_zfmisc_1(A_113,B_114)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2590,c_418])).

tff(c_2639,plain,(
    ! [A_113,B_114] :
      ( '#skF_5'(A_113,B_114,k2_zfmisc_1(A_113,B_114),'#skF_9') = '#skF_5'('#skF_10','#skF_11',k2_zfmisc_1('#skF_10','#skF_11'),'#skF_9')
      | ~ r2_hidden('#skF_9',k2_zfmisc_1(A_113,B_114)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2590,c_2614])).

tff(c_4449,plain,(
    ! [A_434,B_435] :
      ( '#skF_5'(A_434,B_435,k2_zfmisc_1(A_434,B_435),'#skF_9') = '#skF_5'('#skF_12','#skF_11',k2_zfmisc_1('#skF_12','#skF_11'),'#skF_9')
      | ~ r2_hidden('#skF_9',k2_zfmisc_1(A_434,B_435)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4335,c_2639])).

tff(c_4460,plain,(
    '#skF_5'('#skF_12','#skF_11',k2_zfmisc_1('#skF_12','#skF_11'),'#skF_9') = '#skF_5'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_69,c_4449])).

tff(c_4368,plain,
    ( r2_hidden('#skF_5'('#skF_12','#skF_11',k2_zfmisc_1('#skF_12','#skF_11'),'#skF_9'),'#skF_10')
    | ~ r2_hidden('#skF_9',k2_zfmisc_1('#skF_10','#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4335,c_8])).

tff(c_4376,plain,(
    r2_hidden('#skF_5'('#skF_12','#skF_11',k2_zfmisc_1('#skF_12','#skF_11'),'#skF_9'),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4368])).

tff(c_4463,plain,(
    r2_hidden('#skF_5'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_9'),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4460,c_4376])).

tff(c_4476,plain,
    ( r2_hidden('#skF_5'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_9'),'#skF_12')
    | ~ r2_hidden('#skF_9',k2_zfmisc_1('#skF_12','#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4460,c_8])).

tff(c_4484,plain,(
    r2_hidden('#skF_5'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_9'),'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2699,c_4476])).

tff(c_2667,plain,(
    ! [D_28,A_364,B_2,A_1] :
      ( r2_hidden(D_28,k2_zfmisc_1(A_364,B_2))
      | ~ r2_hidden('#skF_5'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),A_364)
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(resolution,[status(thm)],[c_6,c_2644])).

tff(c_4488,plain,
    ( r2_hidden('#skF_9',k2_zfmisc_1('#skF_10','#skF_13'))
    | ~ r2_hidden('#skF_9',k2_zfmisc_1('#skF_12','#skF_13')) ),
    inference(resolution,[status(thm)],[c_4463,c_2667])).

tff(c_4494,plain,(
    r2_hidden('#skF_9',k2_zfmisc_1('#skF_10','#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_4488])).

tff(c_2570,plain,(
    ! [A_358,B_356] :
      ( '#skF_6'(A_358,B_356,k2_zfmisc_1(A_358,B_356),'#skF_9') = '#skF_6'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_9')
      | ~ r2_hidden('#skF_9',k2_zfmisc_1(A_358,B_356)) ) ),
    inference(resolution,[status(thm)],[c_69,c_2281])).

tff(c_4501,plain,(
    '#skF_6'('#skF_10','#skF_13',k2_zfmisc_1('#skF_10','#skF_13'),'#skF_9') = '#skF_6'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_4494,c_2570])).

tff(c_4583,plain,
    ( r2_hidden('#skF_6'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_9'),'#skF_13')
    | ~ r2_hidden('#skF_9',k2_zfmisc_1('#skF_10','#skF_13')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4501,c_6])).

tff(c_4591,plain,(
    r2_hidden('#skF_6'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_9'),'#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4494,c_4583])).

tff(c_4466,plain,(
    k4_tarski('#skF_5'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_9'),'#skF_6'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_9')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4460,c_4277])).

tff(c_26,plain,(
    ! [D_40,A_35,B_36] :
      ( r2_hidden(D_40,k3_xboole_0(A_35,B_36))
      | ~ r2_hidden(D_40,B_36)
      | ~ r2_hidden(D_40,A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_81,plain,(
    ! [G_70,F_71] :
      ( ~ r2_hidden(G_70,k3_xboole_0('#skF_11','#skF_13'))
      | ~ r2_hidden(F_71,k3_xboole_0('#skF_10','#skF_12'))
      | k4_tarski(F_71,G_70) != '#skF_9' ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_116,plain,(
    ! [F_78,D_79] :
      ( ~ r2_hidden(F_78,k3_xboole_0('#skF_10','#skF_12'))
      | k4_tarski(F_78,D_79) != '#skF_9'
      | ~ r2_hidden(D_79,'#skF_13')
      | ~ r2_hidden(D_79,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_26,c_81])).

tff(c_128,plain,(
    ! [D_40,D_79] :
      ( k4_tarski(D_40,D_79) != '#skF_9'
      | ~ r2_hidden(D_79,'#skF_13')
      | ~ r2_hidden(D_79,'#skF_11')
      | ~ r2_hidden(D_40,'#skF_12')
      | ~ r2_hidden(D_40,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_26,c_116])).

tff(c_4654,plain,
    ( ~ r2_hidden('#skF_6'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_9'),'#skF_13')
    | ~ r2_hidden('#skF_6'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_9'),'#skF_11')
    | ~ r2_hidden('#skF_5'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_9'),'#skF_12')
    | ~ r2_hidden('#skF_5'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_9'),'#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_4466,c_128])).

tff(c_4687,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4463,c_4484,c_2592,c_4591,c_4654])).

%------------------------------------------------------------------------------
