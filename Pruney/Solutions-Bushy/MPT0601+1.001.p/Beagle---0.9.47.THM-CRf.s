%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0601+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:33 EST 2020

% Result     : Theorem 4.57s
% Output     : CNFRefutation 4.57s
% Verified   : 
% Statistics : Number of formulae       :   59 (  94 expanded)
%              Number of leaves         :   24 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 145 expanded)
%              Number of equality atoms :   13 (  31 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_39,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_18,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_35,plain,(
    ! [A_28] :
      ( k1_xboole_0 = A_28
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_39,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_35])).

tff(c_40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_18])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1408,plain,(
    ! [C_110,A_111] :
      ( r2_hidden(k4_tarski(C_110,'#skF_5'(A_111,k1_relat_1(A_111),C_110)),A_111)
      | ~ r2_hidden(C_110,k1_relat_1(A_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1421,plain,(
    ! [A_112,C_113] :
      ( ~ v1_xboole_0(A_112)
      | ~ r2_hidden(C_113,k1_relat_1(A_112)) ) ),
    inference(resolution,[status(thm)],[c_1408,c_2])).

tff(c_1441,plain,(
    ! [A_114] :
      ( ~ v1_xboole_0(A_114)
      | v1_xboole_0(k1_relat_1(A_114)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1421])).

tff(c_24,plain,(
    ! [A_27] :
      ( k1_xboole_0 = A_27
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1450,plain,(
    ! [A_115] :
      ( k1_relat_1(A_115) = k1_xboole_0
      | ~ v1_xboole_0(A_115) ) ),
    inference(resolution,[status(thm)],[c_1441,c_24])).

tff(c_1458,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_1450])).

tff(c_1420,plain,(
    ! [A_111,C_110] :
      ( ~ v1_xboole_0(A_111)
      | ~ r2_hidden(C_110,k1_relat_1(A_111)) ) ),
    inference(resolution,[status(thm)],[c_1408,c_2])).

tff(c_1465,plain,(
    ! [C_110] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_110,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1458,c_1420])).

tff(c_1474,plain,(
    ! [C_110] : ~ r2_hidden(C_110,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1465])).

tff(c_28,plain,
    ( k11_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_56,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_34,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_7'))
    | k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_57,plain,(
    k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_34])).

tff(c_26,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_60,plain,(
    ! [A_38,B_39,C_40] :
      ( r2_hidden(k4_tarski(A_38,B_39),C_40)
      | ~ r2_hidden(B_39,k11_relat_1(C_40,A_38))
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [C_20,A_5,D_23] :
      ( r2_hidden(C_20,k1_relat_1(A_5))
      | ~ r2_hidden(k4_tarski(C_20,D_23),A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_961,plain,(
    ! [A_90,C_91,B_92] :
      ( r2_hidden(A_90,k1_relat_1(C_91))
      | ~ r2_hidden(B_92,k11_relat_1(C_91,A_90))
      | ~ v1_relat_1(C_91) ) ),
    inference(resolution,[status(thm)],[c_60,c_8])).

tff(c_1273,plain,(
    ! [A_99,C_100] :
      ( r2_hidden(A_99,k1_relat_1(C_100))
      | ~ v1_relat_1(C_100)
      | v1_xboole_0(k11_relat_1(C_100,A_99)) ) ),
    inference(resolution,[status(thm)],[c_4,c_961])).

tff(c_1313,plain,
    ( ~ v1_relat_1('#skF_7')
    | v1_xboole_0(k11_relat_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_1273,c_56])).

tff(c_1347,plain,(
    v1_xboole_0(k11_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1313])).

tff(c_1370,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1347,c_24])).

tff(c_1380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_1370])).

tff(c_1382,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1381,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_22,plain,(
    ! [B_25,C_26,A_24] :
      ( r2_hidden(B_25,k11_relat_1(C_26,A_24))
      | ~ r2_hidden(k4_tarski(A_24,B_25),C_26)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3898,plain,(
    ! [A_193,C_194] :
      ( r2_hidden('#skF_5'(A_193,k1_relat_1(A_193),C_194),k11_relat_1(A_193,C_194))
      | ~ v1_relat_1(A_193)
      | ~ r2_hidden(C_194,k1_relat_1(A_193)) ) ),
    inference(resolution,[status(thm)],[c_1408,c_22])).

tff(c_3936,plain,
    ( r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0)
    | ~ v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1381,c_3898])).

tff(c_3942,plain,(
    r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1382,c_26,c_3936])).

tff(c_3944,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1474,c_3942])).

%------------------------------------------------------------------------------
