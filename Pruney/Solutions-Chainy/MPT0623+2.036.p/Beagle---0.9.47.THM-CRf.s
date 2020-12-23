%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:11 EST 2020

% Result     : Theorem 5.49s
% Output     : CNFRefutation 5.62s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 591 expanded)
%              Number of leaves         :   34 ( 200 expanded)
%              Depth                    :   16
%              Number of atoms          :  250 (1522 expanded)
%              Number of equality atoms :  134 ( 822 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_10 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_124,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_106,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_70,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_73,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_63,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_93,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_61,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(c_74,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_95,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k3_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3663,plain,(
    ! [A_5644,B_5645,C_5646] :
      ( ~ r2_hidden('#skF_2'(A_5644,B_5645,C_5646),C_5646)
      | r2_hidden('#skF_3'(A_5644,B_5645,C_5646),C_5646)
      | k3_xboole_0(A_5644,B_5645) = C_5646 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3676,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_3'(A_6,B_7,B_7),B_7)
      | k3_xboole_0(A_6,B_7) = B_7 ) ),
    inference(resolution,[status(thm)],[c_22,c_3663])).

tff(c_66,plain,(
    ! [A_31,B_35] :
      ( k1_relat_1('#skF_8'(A_31,B_35)) = A_31
      | k1_xboole_0 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_68,plain,(
    ! [A_31,B_35] :
      ( v1_funct_1('#skF_8'(A_31,B_35))
      | k1_xboole_0 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_70,plain,(
    ! [A_31,B_35] :
      ( v1_relat_1('#skF_8'(A_31,B_35))
      | k1_xboole_0 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_259,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_1'(A_67,B_68),A_67)
      | r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36,plain,(
    ! [C_23,A_19] :
      ( C_23 = A_19
      | ~ r2_hidden(C_23,k1_tarski(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3517,plain,(
    ! [A_5632,B_5633] :
      ( '#skF_1'(k1_tarski(A_5632),B_5633) = A_5632
      | r1_tarski(k1_tarski(A_5632),B_5633) ) ),
    inference(resolution,[status(thm)],[c_259,c_36])).

tff(c_317,plain,(
    ! [A_77,B_78] :
      ( k2_relat_1('#skF_8'(A_77,B_78)) = k1_tarski(B_78)
      | k1_xboole_0 = A_77 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_72,plain,(
    ! [C_38] :
      ( ~ r1_tarski(k2_relat_1(C_38),'#skF_9')
      | k1_relat_1(C_38) != '#skF_10'
      | ~ v1_funct_1(C_38)
      | ~ v1_relat_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_323,plain,(
    ! [B_78,A_77] :
      ( ~ r1_tarski(k1_tarski(B_78),'#skF_9')
      | k1_relat_1('#skF_8'(A_77,B_78)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_77,B_78))
      | ~ v1_relat_1('#skF_8'(A_77,B_78))
      | k1_xboole_0 = A_77 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_72])).

tff(c_3542,plain,(
    ! [A_5636,A_5637] :
      ( k1_relat_1('#skF_8'(A_5636,A_5637)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_5636,A_5637))
      | ~ v1_relat_1('#skF_8'(A_5636,A_5637))
      | k1_xboole_0 = A_5636
      | '#skF_1'(k1_tarski(A_5637),'#skF_9') = A_5637 ) ),
    inference(resolution,[status(thm)],[c_3517,c_323])).

tff(c_5902,plain,(
    ! [A_9531,B_9532] :
      ( k1_relat_1('#skF_8'(A_9531,B_9532)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_9531,B_9532))
      | '#skF_1'(k1_tarski(B_9532),'#skF_9') = B_9532
      | k1_xboole_0 = A_9531 ) ),
    inference(resolution,[status(thm)],[c_70,c_3542])).

tff(c_6133,plain,(
    ! [A_9547,B_9548] :
      ( k1_relat_1('#skF_8'(A_9547,B_9548)) != '#skF_10'
      | '#skF_1'(k1_tarski(B_9548),'#skF_9') = B_9548
      | k1_xboole_0 = A_9547 ) ),
    inference(resolution,[status(thm)],[c_68,c_5902])).

tff(c_6136,plain,(
    ! [A_31,B_35] :
      ( A_31 != '#skF_10'
      | '#skF_1'(k1_tarski(B_35),'#skF_9') = B_35
      | k1_xboole_0 = A_31
      | k1_xboole_0 = A_31 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_6133])).

tff(c_6190,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_6136])).

tff(c_50,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_34,plain,(
    ! [A_18] : r1_tarski(k1_xboole_0,A_18) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_48,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_103,plain,(
    ! [C_44] :
      ( ~ r1_tarski(k2_relat_1(C_44),'#skF_9')
      | k1_relat_1(C_44) != '#skF_10'
      | ~ v1_funct_1(C_44)
      | ~ v1_relat_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_106,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_9')
    | k1_relat_1(k1_xboole_0) != '#skF_10'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_103])).

tff(c_108,plain,
    ( k1_xboole_0 != '#skF_10'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_34,c_106])).

tff(c_118,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_58,plain,(
    ! [A_25] : k1_relat_1('#skF_7'(A_25)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_62,plain,(
    ! [A_25] : v1_relat_1('#skF_7'(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_119,plain,(
    ! [A_52] :
      ( k1_relat_1(A_52) != k1_xboole_0
      | k1_xboole_0 = A_52
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_125,plain,(
    ! [A_25] :
      ( k1_relat_1('#skF_7'(A_25)) != k1_xboole_0
      | '#skF_7'(A_25) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_62,c_119])).

tff(c_130,plain,(
    ! [A_53] :
      ( k1_xboole_0 != A_53
      | '#skF_7'(A_53) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_125])).

tff(c_140,plain,(
    ! [A_53] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_53 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_62])).

tff(c_146,plain,(
    ! [A_53] : k1_xboole_0 != A_53 ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_140])).

tff(c_32,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_32])).

tff(c_156,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_158,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_6220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6190,c_158])).

tff(c_6223,plain,(
    ! [B_9551] : '#skF_1'(k1_tarski(B_9551),'#skF_9') = B_9551 ),
    inference(splitRight,[status(thm)],[c_6136])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6251,plain,(
    ! [B_9552] :
      ( ~ r2_hidden(B_9552,'#skF_9')
      | r1_tarski(k1_tarski(B_9552),'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6223,c_4])).

tff(c_6265,plain,(
    ! [A_9555,B_9556] :
      ( k1_relat_1('#skF_8'(A_9555,B_9556)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_9555,B_9556))
      | ~ v1_relat_1('#skF_8'(A_9555,B_9556))
      | k1_xboole_0 = A_9555
      | ~ r2_hidden(B_9556,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_6251,c_323])).

tff(c_6323,plain,(
    ! [A_9560,B_9561] :
      ( k1_relat_1('#skF_8'(A_9560,B_9561)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_9560,B_9561))
      | ~ r2_hidden(B_9561,'#skF_9')
      | k1_xboole_0 = A_9560 ) ),
    inference(resolution,[status(thm)],[c_70,c_6265])).

tff(c_6381,plain,(
    ! [A_9565,B_9566] :
      ( k1_relat_1('#skF_8'(A_9565,B_9566)) != '#skF_10'
      | ~ r2_hidden(B_9566,'#skF_9')
      | k1_xboole_0 = A_9565 ) ),
    inference(resolution,[status(thm)],[c_68,c_6323])).

tff(c_6384,plain,(
    ! [A_31,B_35] :
      ( A_31 != '#skF_10'
      | ~ r2_hidden(B_35,'#skF_9')
      | k1_xboole_0 = A_31
      | k1_xboole_0 = A_31 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_6381])).

tff(c_6386,plain,(
    ! [B_9567] : ~ r2_hidden(B_9567,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_6384])).

tff(c_6562,plain,(
    ! [A_9574] : k3_xboole_0(A_9574,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_3676,c_6386])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5455,plain,(
    ! [A_9315,B_9316,B_9317] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_9315,B_9316),B_9317),A_9315)
      | r1_tarski(k3_xboole_0(A_9315,B_9316),B_9317) ) ),
    inference(resolution,[status(thm)],[c_259,c_12])).

tff(c_5504,plain,(
    ! [A_9315,B_9316] : r1_tarski(k3_xboole_0(A_9315,B_9316),A_9315) ),
    inference(resolution,[status(thm)],[c_5455,c_4])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k3_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3748,plain,(
    ! [A_5656,B_5657] :
      ( r2_hidden('#skF_3'(A_5656,B_5657,A_5656),A_5656)
      | k3_xboole_0(A_5656,B_5657) = A_5656 ) ),
    inference(resolution,[status(thm)],[c_24,c_3663])).

tff(c_239,plain,(
    ! [D_61,A_62,B_63] :
      ( r2_hidden(D_61,A_62)
      | ~ r2_hidden(D_61,k3_xboole_0(A_62,B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_246,plain,(
    ! [D_61,A_17] :
      ( r2_hidden(D_61,A_17)
      | ~ r2_hidden(D_61,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_239])).

tff(c_3887,plain,(
    ! [B_5663,A_5664] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_5663,k1_xboole_0),A_5664)
      | k3_xboole_0(k1_xboole_0,B_5663) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3748,c_246])).

tff(c_3925,plain,(
    ! [A_19,B_5663] :
      ( A_19 = '#skF_3'(k1_xboole_0,B_5663,k1_xboole_0)
      | k3_xboole_0(k1_xboole_0,B_5663) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3887,c_36])).

tff(c_60,plain,(
    ! [A_25] : v1_funct_1('#skF_7'(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3935,plain,(
    ! [A_5665,B_5666] :
      ( A_5665 = '#skF_3'(k1_xboole_0,B_5666,k1_xboole_0)
      | k3_xboole_0(k1_xboole_0,B_5666) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3887,c_36])).

tff(c_4370,plain,(
    ! [B_5666,C_38] :
      ( ~ r1_tarski('#skF_3'(k1_xboole_0,B_5666,k1_xboole_0),'#skF_9')
      | k1_relat_1(C_38) != '#skF_10'
      | ~ v1_funct_1(C_38)
      | ~ v1_relat_1(C_38)
      | k3_xboole_0(k1_xboole_0,B_5666) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3935,c_72])).

tff(c_4697,plain,(
    ! [C_7256] :
      ( k1_relat_1(C_7256) != '#skF_10'
      | ~ v1_funct_1(C_7256)
      | ~ v1_relat_1(C_7256) ) ),
    inference(splitLeft,[status(thm)],[c_4370])).

tff(c_4709,plain,(
    ! [A_25] :
      ( k1_relat_1('#skF_7'(A_25)) != '#skF_10'
      | ~ v1_funct_1('#skF_7'(A_25)) ) ),
    inference(resolution,[status(thm)],[c_62,c_4697])).

tff(c_4717,plain,(
    ! [A_25] : A_25 != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_4709])).

tff(c_4721,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4717])).

tff(c_5310,plain,(
    ! [B_9065] :
      ( ~ r1_tarski('#skF_3'(k1_xboole_0,B_9065,k1_xboole_0),'#skF_9')
      | k3_xboole_0(k1_xboole_0,B_9065) = k1_xboole_0 ) ),
    inference(splitRight,[status(thm)],[c_4370])).

tff(c_5315,plain,(
    ! [A_19,B_5663] :
      ( ~ r1_tarski(A_19,'#skF_9')
      | k3_xboole_0(k1_xboole_0,B_5663) = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,B_5663) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3925,c_5310])).

tff(c_5529,plain,(
    ! [A_9416] : ~ r1_tarski(A_9416,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_5315])).

tff(c_5544,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_5504,c_5529])).

tff(c_5545,plain,(
    ! [B_5663] :
      ( k3_xboole_0(k1_xboole_0,B_5663) = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,B_5663) = k1_xboole_0 ) ),
    inference(splitRight,[status(thm)],[c_5315])).

tff(c_5554,plain,(
    ! [B_5663] : k3_xboole_0(k1_xboole_0,B_5663) = k1_xboole_0 ),
    inference(factorization,[status(thm),theory(equality)],[c_5545])).

tff(c_6594,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_6562,c_5554])).

tff(c_6638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_6594])).

tff(c_6640,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_6384])).

tff(c_6670,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6640,c_158])).

tff(c_6672,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_6671,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_6673,plain,(
    ~ v1_funct_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6672,c_6671])).

tff(c_54,plain,(
    ! [A_24] :
      ( k1_relat_1(A_24) != k1_xboole_0
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6692,plain,(
    ! [A_9576] :
      ( k1_relat_1(A_9576) != '#skF_10'
      | A_9576 = '#skF_10'
      | ~ v1_relat_1(A_9576) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6672,c_6672,c_54])).

tff(c_6698,plain,(
    ! [A_25] :
      ( k1_relat_1('#skF_7'(A_25)) != '#skF_10'
      | '#skF_7'(A_25) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_62,c_6692])).

tff(c_6722,plain,(
    ! [A_9578] :
      ( A_9578 != '#skF_10'
      | '#skF_7'(A_9578) = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_6698])).

tff(c_6730,plain,(
    ! [A_9578] :
      ( v1_funct_1('#skF_10')
      | A_9578 != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6722,c_60])).

tff(c_6738,plain,(
    ! [A_9578] : A_9578 != '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_6673,c_6730])).

tff(c_6677,plain,(
    ! [A_17] : k3_xboole_0(A_17,'#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6672,c_6672,c_32])).

tff(c_6747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6738,c_6677])).

tff(c_6749,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_6748,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_6757,plain,(
    '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6749,c_6748])).

tff(c_6751,plain,(
    k1_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6748,c_6748,c_50])).

tff(c_6771,plain,(
    k1_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6757,c_6757,c_6751])).

tff(c_6752,plain,(
    ! [A_18] : r1_tarski('#skF_10',A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6748,c_34])).

tff(c_6776,plain,(
    ! [A_18] : r1_tarski('#skF_9',A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6757,c_6752])).

tff(c_6750,plain,(
    k2_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6748,c_6748,c_48])).

tff(c_6766,plain,(
    k2_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6757,c_6757,c_6750])).

tff(c_6794,plain,(
    ! [C_9584] :
      ( ~ r1_tarski(k2_relat_1(C_9584),'#skF_9')
      | k1_relat_1(C_9584) != '#skF_9'
      | ~ v1_funct_1(C_9584)
      | ~ v1_relat_1(C_9584) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6757,c_72])).

tff(c_6797,plain,
    ( ~ r1_tarski('#skF_9','#skF_9')
    | k1_relat_1('#skF_9') != '#skF_9'
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_6766,c_6794])).

tff(c_6799,plain,
    ( ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6771,c_6776,c_6797])).

tff(c_6800,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_6799])).

tff(c_6816,plain,(
    ! [A_9590] :
      ( k1_relat_1(A_9590) != '#skF_9'
      | A_9590 = '#skF_9'
      | ~ v1_relat_1(A_9590) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6749,c_6749,c_54])).

tff(c_6822,plain,(
    ! [A_25] :
      ( k1_relat_1('#skF_7'(A_25)) != '#skF_9'
      | '#skF_7'(A_25) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_62,c_6816])).

tff(c_6827,plain,(
    ! [A_9591] :
      ( A_9591 != '#skF_9'
      | '#skF_7'(A_9591) = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_6822])).

tff(c_6837,plain,(
    ! [A_9591] :
      ( v1_relat_1('#skF_9')
      | A_9591 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6827,c_62])).

tff(c_6843,plain,(
    ! [A_9591] : A_9591 != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_6800,c_6837])).

tff(c_6779,plain,(
    ! [A_17] : k3_xboole_0(A_17,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6749,c_6749,c_32])).

tff(c_6855,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6843,c_6779])).

tff(c_6856,plain,(
    ~ v1_funct_1('#skF_9') ),
    inference(splitRight,[status(thm)],[c_6799])).

tff(c_6874,plain,(
    ! [A_9598] :
      ( k1_relat_1(A_9598) != '#skF_9'
      | A_9598 = '#skF_9'
      | ~ v1_relat_1(A_9598) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6749,c_6749,c_54])).

tff(c_6883,plain,(
    ! [A_25] :
      ( k1_relat_1('#skF_7'(A_25)) != '#skF_9'
      | '#skF_7'(A_25) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_62,c_6874])).

tff(c_6892,plain,(
    ! [A_9599] :
      ( A_9599 != '#skF_9'
      | '#skF_7'(A_9599) = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_6883])).

tff(c_6900,plain,(
    ! [A_9599] :
      ( v1_funct_1('#skF_9')
      | A_9599 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6892,c_60])).

tff(c_6908,plain,(
    ! [A_9599] : A_9599 != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_6856,c_6900])).

tff(c_6939,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6908,c_6779])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:58:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.49/2.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.49/2.06  
% 5.49/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.49/2.06  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_10 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 5.49/2.06  
% 5.49/2.06  %Foreground sorts:
% 5.49/2.06  
% 5.49/2.06  
% 5.49/2.06  %Background operators:
% 5.49/2.06  
% 5.49/2.06  
% 5.49/2.06  %Foreground operators:
% 5.49/2.06  tff('#skF_7', type, '#skF_7': $i > $i).
% 5.49/2.06  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.49/2.06  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.49/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.49/2.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.49/2.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.49/2.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.49/2.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.49/2.06  tff('#skF_10', type, '#skF_10': $i).
% 5.49/2.06  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.49/2.06  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.49/2.06  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.49/2.06  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 5.49/2.06  tff('#skF_9', type, '#skF_9': $i).
% 5.49/2.06  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.49/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.49/2.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.49/2.06  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.49/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.49/2.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.49/2.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.49/2.06  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.49/2.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.49/2.06  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.49/2.06  
% 5.62/2.08  tff(f_124, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 5.62/2.08  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 5.62/2.08  tff(f_106, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 5.62/2.08  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.62/2.08  tff(f_70, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 5.62/2.08  tff(f_73, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.62/2.08  tff(f_63, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.62/2.08  tff(f_93, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 5.62/2.08  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 5.62/2.08  tff(f_61, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.62/2.08  tff(c_74, plain, (k1_xboole_0='#skF_10' | k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.62/2.08  tff(c_95, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_74])).
% 5.62/2.08  tff(c_22, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k3_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.62/2.08  tff(c_3663, plain, (![A_5644, B_5645, C_5646]: (~r2_hidden('#skF_2'(A_5644, B_5645, C_5646), C_5646) | r2_hidden('#skF_3'(A_5644, B_5645, C_5646), C_5646) | k3_xboole_0(A_5644, B_5645)=C_5646)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.62/2.08  tff(c_3676, plain, (![A_6, B_7]: (r2_hidden('#skF_3'(A_6, B_7, B_7), B_7) | k3_xboole_0(A_6, B_7)=B_7)), inference(resolution, [status(thm)], [c_22, c_3663])).
% 5.62/2.08  tff(c_66, plain, (![A_31, B_35]: (k1_relat_1('#skF_8'(A_31, B_35))=A_31 | k1_xboole_0=A_31)), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.62/2.08  tff(c_68, plain, (![A_31, B_35]: (v1_funct_1('#skF_8'(A_31, B_35)) | k1_xboole_0=A_31)), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.62/2.08  tff(c_70, plain, (![A_31, B_35]: (v1_relat_1('#skF_8'(A_31, B_35)) | k1_xboole_0=A_31)), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.62/2.08  tff(c_259, plain, (![A_67, B_68]: (r2_hidden('#skF_1'(A_67, B_68), A_67) | r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.62/2.08  tff(c_36, plain, (![C_23, A_19]: (C_23=A_19 | ~r2_hidden(C_23, k1_tarski(A_19)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.62/2.08  tff(c_3517, plain, (![A_5632, B_5633]: ('#skF_1'(k1_tarski(A_5632), B_5633)=A_5632 | r1_tarski(k1_tarski(A_5632), B_5633))), inference(resolution, [status(thm)], [c_259, c_36])).
% 5.62/2.08  tff(c_317, plain, (![A_77, B_78]: (k2_relat_1('#skF_8'(A_77, B_78))=k1_tarski(B_78) | k1_xboole_0=A_77)), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.62/2.08  tff(c_72, plain, (![C_38]: (~r1_tarski(k2_relat_1(C_38), '#skF_9') | k1_relat_1(C_38)!='#skF_10' | ~v1_funct_1(C_38) | ~v1_relat_1(C_38))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.62/2.08  tff(c_323, plain, (![B_78, A_77]: (~r1_tarski(k1_tarski(B_78), '#skF_9') | k1_relat_1('#skF_8'(A_77, B_78))!='#skF_10' | ~v1_funct_1('#skF_8'(A_77, B_78)) | ~v1_relat_1('#skF_8'(A_77, B_78)) | k1_xboole_0=A_77)), inference(superposition, [status(thm), theory('equality')], [c_317, c_72])).
% 5.62/2.08  tff(c_3542, plain, (![A_5636, A_5637]: (k1_relat_1('#skF_8'(A_5636, A_5637))!='#skF_10' | ~v1_funct_1('#skF_8'(A_5636, A_5637)) | ~v1_relat_1('#skF_8'(A_5636, A_5637)) | k1_xboole_0=A_5636 | '#skF_1'(k1_tarski(A_5637), '#skF_9')=A_5637)), inference(resolution, [status(thm)], [c_3517, c_323])).
% 5.62/2.08  tff(c_5902, plain, (![A_9531, B_9532]: (k1_relat_1('#skF_8'(A_9531, B_9532))!='#skF_10' | ~v1_funct_1('#skF_8'(A_9531, B_9532)) | '#skF_1'(k1_tarski(B_9532), '#skF_9')=B_9532 | k1_xboole_0=A_9531)), inference(resolution, [status(thm)], [c_70, c_3542])).
% 5.62/2.08  tff(c_6133, plain, (![A_9547, B_9548]: (k1_relat_1('#skF_8'(A_9547, B_9548))!='#skF_10' | '#skF_1'(k1_tarski(B_9548), '#skF_9')=B_9548 | k1_xboole_0=A_9547)), inference(resolution, [status(thm)], [c_68, c_5902])).
% 5.62/2.08  tff(c_6136, plain, (![A_31, B_35]: (A_31!='#skF_10' | '#skF_1'(k1_tarski(B_35), '#skF_9')=B_35 | k1_xboole_0=A_31 | k1_xboole_0=A_31)), inference(superposition, [status(thm), theory('equality')], [c_66, c_6133])).
% 5.62/2.08  tff(c_6190, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_6136])).
% 5.62/2.08  tff(c_50, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.62/2.08  tff(c_34, plain, (![A_18]: (r1_tarski(k1_xboole_0, A_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.62/2.08  tff(c_48, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.62/2.08  tff(c_103, plain, (![C_44]: (~r1_tarski(k2_relat_1(C_44), '#skF_9') | k1_relat_1(C_44)!='#skF_10' | ~v1_funct_1(C_44) | ~v1_relat_1(C_44))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.62/2.08  tff(c_106, plain, (~r1_tarski(k1_xboole_0, '#skF_9') | k1_relat_1(k1_xboole_0)!='#skF_10' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_103])).
% 5.62/2.08  tff(c_108, plain, (k1_xboole_0!='#skF_10' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_34, c_106])).
% 5.62/2.08  tff(c_118, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_108])).
% 5.62/2.08  tff(c_58, plain, (![A_25]: (k1_relat_1('#skF_7'(A_25))=A_25)), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.62/2.08  tff(c_62, plain, (![A_25]: (v1_relat_1('#skF_7'(A_25)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.62/2.08  tff(c_119, plain, (![A_52]: (k1_relat_1(A_52)!=k1_xboole_0 | k1_xboole_0=A_52 | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.62/2.08  tff(c_125, plain, (![A_25]: (k1_relat_1('#skF_7'(A_25))!=k1_xboole_0 | '#skF_7'(A_25)=k1_xboole_0)), inference(resolution, [status(thm)], [c_62, c_119])).
% 5.62/2.08  tff(c_130, plain, (![A_53]: (k1_xboole_0!=A_53 | '#skF_7'(A_53)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_125])).
% 5.62/2.08  tff(c_140, plain, (![A_53]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_53)), inference(superposition, [status(thm), theory('equality')], [c_130, c_62])).
% 5.62/2.08  tff(c_146, plain, (![A_53]: (k1_xboole_0!=A_53)), inference(negUnitSimplification, [status(thm)], [c_118, c_140])).
% 5.62/2.08  tff(c_32, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.62/2.08  tff(c_155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_32])).
% 5.62/2.08  tff(c_156, plain, (~v1_funct_1(k1_xboole_0) | k1_xboole_0!='#skF_10'), inference(splitRight, [status(thm)], [c_108])).
% 5.62/2.08  tff(c_158, plain, (k1_xboole_0!='#skF_10'), inference(splitLeft, [status(thm)], [c_156])).
% 5.62/2.08  tff(c_6220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6190, c_158])).
% 5.62/2.08  tff(c_6223, plain, (![B_9551]: ('#skF_1'(k1_tarski(B_9551), '#skF_9')=B_9551)), inference(splitRight, [status(thm)], [c_6136])).
% 5.62/2.08  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.62/2.08  tff(c_6251, plain, (![B_9552]: (~r2_hidden(B_9552, '#skF_9') | r1_tarski(k1_tarski(B_9552), '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_6223, c_4])).
% 5.62/2.08  tff(c_6265, plain, (![A_9555, B_9556]: (k1_relat_1('#skF_8'(A_9555, B_9556))!='#skF_10' | ~v1_funct_1('#skF_8'(A_9555, B_9556)) | ~v1_relat_1('#skF_8'(A_9555, B_9556)) | k1_xboole_0=A_9555 | ~r2_hidden(B_9556, '#skF_9'))), inference(resolution, [status(thm)], [c_6251, c_323])).
% 5.62/2.08  tff(c_6323, plain, (![A_9560, B_9561]: (k1_relat_1('#skF_8'(A_9560, B_9561))!='#skF_10' | ~v1_funct_1('#skF_8'(A_9560, B_9561)) | ~r2_hidden(B_9561, '#skF_9') | k1_xboole_0=A_9560)), inference(resolution, [status(thm)], [c_70, c_6265])).
% 5.62/2.08  tff(c_6381, plain, (![A_9565, B_9566]: (k1_relat_1('#skF_8'(A_9565, B_9566))!='#skF_10' | ~r2_hidden(B_9566, '#skF_9') | k1_xboole_0=A_9565)), inference(resolution, [status(thm)], [c_68, c_6323])).
% 5.62/2.08  tff(c_6384, plain, (![A_31, B_35]: (A_31!='#skF_10' | ~r2_hidden(B_35, '#skF_9') | k1_xboole_0=A_31 | k1_xboole_0=A_31)), inference(superposition, [status(thm), theory('equality')], [c_66, c_6381])).
% 5.62/2.08  tff(c_6386, plain, (![B_9567]: (~r2_hidden(B_9567, '#skF_9'))), inference(splitLeft, [status(thm)], [c_6384])).
% 5.62/2.08  tff(c_6562, plain, (![A_9574]: (k3_xboole_0(A_9574, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_3676, c_6386])).
% 5.62/2.08  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.62/2.08  tff(c_5455, plain, (![A_9315, B_9316, B_9317]: (r2_hidden('#skF_1'(k3_xboole_0(A_9315, B_9316), B_9317), A_9315) | r1_tarski(k3_xboole_0(A_9315, B_9316), B_9317))), inference(resolution, [status(thm)], [c_259, c_12])).
% 5.62/2.08  tff(c_5504, plain, (![A_9315, B_9316]: (r1_tarski(k3_xboole_0(A_9315, B_9316), A_9315))), inference(resolution, [status(thm)], [c_5455, c_4])).
% 5.62/2.08  tff(c_24, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k3_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.62/2.08  tff(c_3748, plain, (![A_5656, B_5657]: (r2_hidden('#skF_3'(A_5656, B_5657, A_5656), A_5656) | k3_xboole_0(A_5656, B_5657)=A_5656)), inference(resolution, [status(thm)], [c_24, c_3663])).
% 5.62/2.08  tff(c_239, plain, (![D_61, A_62, B_63]: (r2_hidden(D_61, A_62) | ~r2_hidden(D_61, k3_xboole_0(A_62, B_63)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.62/2.08  tff(c_246, plain, (![D_61, A_17]: (r2_hidden(D_61, A_17) | ~r2_hidden(D_61, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_239])).
% 5.62/2.08  tff(c_3887, plain, (![B_5663, A_5664]: (r2_hidden('#skF_3'(k1_xboole_0, B_5663, k1_xboole_0), A_5664) | k3_xboole_0(k1_xboole_0, B_5663)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3748, c_246])).
% 5.62/2.08  tff(c_3925, plain, (![A_19, B_5663]: (A_19='#skF_3'(k1_xboole_0, B_5663, k1_xboole_0) | k3_xboole_0(k1_xboole_0, B_5663)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3887, c_36])).
% 5.62/2.08  tff(c_60, plain, (![A_25]: (v1_funct_1('#skF_7'(A_25)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.62/2.08  tff(c_3935, plain, (![A_5665, B_5666]: (A_5665='#skF_3'(k1_xboole_0, B_5666, k1_xboole_0) | k3_xboole_0(k1_xboole_0, B_5666)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3887, c_36])).
% 5.62/2.08  tff(c_4370, plain, (![B_5666, C_38]: (~r1_tarski('#skF_3'(k1_xboole_0, B_5666, k1_xboole_0), '#skF_9') | k1_relat_1(C_38)!='#skF_10' | ~v1_funct_1(C_38) | ~v1_relat_1(C_38) | k3_xboole_0(k1_xboole_0, B_5666)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3935, c_72])).
% 5.62/2.08  tff(c_4697, plain, (![C_7256]: (k1_relat_1(C_7256)!='#skF_10' | ~v1_funct_1(C_7256) | ~v1_relat_1(C_7256))), inference(splitLeft, [status(thm)], [c_4370])).
% 5.62/2.08  tff(c_4709, plain, (![A_25]: (k1_relat_1('#skF_7'(A_25))!='#skF_10' | ~v1_funct_1('#skF_7'(A_25)))), inference(resolution, [status(thm)], [c_62, c_4697])).
% 5.62/2.08  tff(c_4717, plain, (![A_25]: (A_25!='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_4709])).
% 5.62/2.08  tff(c_4721, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_4717])).
% 5.62/2.08  tff(c_5310, plain, (![B_9065]: (~r1_tarski('#skF_3'(k1_xboole_0, B_9065, k1_xboole_0), '#skF_9') | k3_xboole_0(k1_xboole_0, B_9065)=k1_xboole_0)), inference(splitRight, [status(thm)], [c_4370])).
% 5.62/2.08  tff(c_5315, plain, (![A_19, B_5663]: (~r1_tarski(A_19, '#skF_9') | k3_xboole_0(k1_xboole_0, B_5663)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, B_5663)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3925, c_5310])).
% 5.62/2.08  tff(c_5529, plain, (![A_9416]: (~r1_tarski(A_9416, '#skF_9'))), inference(splitLeft, [status(thm)], [c_5315])).
% 5.62/2.08  tff(c_5544, plain, $false, inference(resolution, [status(thm)], [c_5504, c_5529])).
% 5.62/2.08  tff(c_5545, plain, (![B_5663]: (k3_xboole_0(k1_xboole_0, B_5663)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, B_5663)=k1_xboole_0)), inference(splitRight, [status(thm)], [c_5315])).
% 5.62/2.08  tff(c_5554, plain, (![B_5663]: (k3_xboole_0(k1_xboole_0, B_5663)=k1_xboole_0)), inference(factorization, [status(thm), theory('equality')], [c_5545])).
% 5.62/2.08  tff(c_6594, plain, (k1_xboole_0='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_6562, c_5554])).
% 5.62/2.08  tff(c_6638, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_6594])).
% 5.62/2.08  tff(c_6640, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_6384])).
% 5.62/2.08  tff(c_6670, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6640, c_158])).
% 5.62/2.08  tff(c_6672, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_156])).
% 5.62/2.08  tff(c_6671, plain, (~v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_156])).
% 5.62/2.08  tff(c_6673, plain, (~v1_funct_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_6672, c_6671])).
% 5.62/2.08  tff(c_54, plain, (![A_24]: (k1_relat_1(A_24)!=k1_xboole_0 | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.62/2.08  tff(c_6692, plain, (![A_9576]: (k1_relat_1(A_9576)!='#skF_10' | A_9576='#skF_10' | ~v1_relat_1(A_9576))), inference(demodulation, [status(thm), theory('equality')], [c_6672, c_6672, c_54])).
% 5.62/2.08  tff(c_6698, plain, (![A_25]: (k1_relat_1('#skF_7'(A_25))!='#skF_10' | '#skF_7'(A_25)='#skF_10')), inference(resolution, [status(thm)], [c_62, c_6692])).
% 5.62/2.08  tff(c_6722, plain, (![A_9578]: (A_9578!='#skF_10' | '#skF_7'(A_9578)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_6698])).
% 5.62/2.08  tff(c_6730, plain, (![A_9578]: (v1_funct_1('#skF_10') | A_9578!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_6722, c_60])).
% 5.62/2.08  tff(c_6738, plain, (![A_9578]: (A_9578!='#skF_10')), inference(negUnitSimplification, [status(thm)], [c_6673, c_6730])).
% 5.62/2.08  tff(c_6677, plain, (![A_17]: (k3_xboole_0(A_17, '#skF_10')='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_6672, c_6672, c_32])).
% 5.62/2.08  tff(c_6747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6738, c_6677])).
% 5.62/2.08  tff(c_6749, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_74])).
% 5.62/2.08  tff(c_6748, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_74])).
% 5.62/2.08  tff(c_6757, plain, ('#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_6749, c_6748])).
% 5.62/2.08  tff(c_6751, plain, (k1_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_6748, c_6748, c_50])).
% 5.62/2.08  tff(c_6771, plain, (k1_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_6757, c_6757, c_6751])).
% 5.62/2.08  tff(c_6752, plain, (![A_18]: (r1_tarski('#skF_10', A_18))), inference(demodulation, [status(thm), theory('equality')], [c_6748, c_34])).
% 5.62/2.08  tff(c_6776, plain, (![A_18]: (r1_tarski('#skF_9', A_18))), inference(demodulation, [status(thm), theory('equality')], [c_6757, c_6752])).
% 5.62/2.08  tff(c_6750, plain, (k2_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_6748, c_6748, c_48])).
% 5.62/2.08  tff(c_6766, plain, (k2_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_6757, c_6757, c_6750])).
% 5.62/2.08  tff(c_6794, plain, (![C_9584]: (~r1_tarski(k2_relat_1(C_9584), '#skF_9') | k1_relat_1(C_9584)!='#skF_9' | ~v1_funct_1(C_9584) | ~v1_relat_1(C_9584))), inference(demodulation, [status(thm), theory('equality')], [c_6757, c_72])).
% 5.62/2.08  tff(c_6797, plain, (~r1_tarski('#skF_9', '#skF_9') | k1_relat_1('#skF_9')!='#skF_9' | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_6766, c_6794])).
% 5.62/2.08  tff(c_6799, plain, (~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_6771, c_6776, c_6797])).
% 5.62/2.08  tff(c_6800, plain, (~v1_relat_1('#skF_9')), inference(splitLeft, [status(thm)], [c_6799])).
% 5.62/2.08  tff(c_6816, plain, (![A_9590]: (k1_relat_1(A_9590)!='#skF_9' | A_9590='#skF_9' | ~v1_relat_1(A_9590))), inference(demodulation, [status(thm), theory('equality')], [c_6749, c_6749, c_54])).
% 5.62/2.08  tff(c_6822, plain, (![A_25]: (k1_relat_1('#skF_7'(A_25))!='#skF_9' | '#skF_7'(A_25)='#skF_9')), inference(resolution, [status(thm)], [c_62, c_6816])).
% 5.62/2.08  tff(c_6827, plain, (![A_9591]: (A_9591!='#skF_9' | '#skF_7'(A_9591)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_6822])).
% 5.62/2.08  tff(c_6837, plain, (![A_9591]: (v1_relat_1('#skF_9') | A_9591!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_6827, c_62])).
% 5.62/2.08  tff(c_6843, plain, (![A_9591]: (A_9591!='#skF_9')), inference(negUnitSimplification, [status(thm)], [c_6800, c_6837])).
% 5.62/2.08  tff(c_6779, plain, (![A_17]: (k3_xboole_0(A_17, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_6749, c_6749, c_32])).
% 5.62/2.08  tff(c_6855, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6843, c_6779])).
% 5.62/2.08  tff(c_6856, plain, (~v1_funct_1('#skF_9')), inference(splitRight, [status(thm)], [c_6799])).
% 5.62/2.08  tff(c_6874, plain, (![A_9598]: (k1_relat_1(A_9598)!='#skF_9' | A_9598='#skF_9' | ~v1_relat_1(A_9598))), inference(demodulation, [status(thm), theory('equality')], [c_6749, c_6749, c_54])).
% 5.62/2.08  tff(c_6883, plain, (![A_25]: (k1_relat_1('#skF_7'(A_25))!='#skF_9' | '#skF_7'(A_25)='#skF_9')), inference(resolution, [status(thm)], [c_62, c_6874])).
% 5.62/2.08  tff(c_6892, plain, (![A_9599]: (A_9599!='#skF_9' | '#skF_7'(A_9599)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_6883])).
% 5.62/2.08  tff(c_6900, plain, (![A_9599]: (v1_funct_1('#skF_9') | A_9599!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_6892, c_60])).
% 5.62/2.08  tff(c_6908, plain, (![A_9599]: (A_9599!='#skF_9')), inference(negUnitSimplification, [status(thm)], [c_6856, c_6900])).
% 5.62/2.08  tff(c_6939, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6908, c_6779])).
% 5.62/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.62/2.08  
% 5.62/2.08  Inference rules
% 5.62/2.08  ----------------------
% 5.62/2.08  #Ref     : 5
% 5.62/2.08  #Sup     : 1386
% 5.62/2.08  #Fact    : 7
% 5.62/2.08  #Define  : 0
% 5.62/2.08  #Split   : 15
% 5.62/2.08  #Chain   : 0
% 5.62/2.08  #Close   : 0
% 5.62/2.08  
% 5.62/2.08  Ordering : KBO
% 5.62/2.08  
% 5.62/2.08  Simplification rules
% 5.62/2.08  ----------------------
% 5.62/2.08  #Subsume      : 262
% 5.62/2.08  #Demod        : 783
% 5.62/2.08  #Tautology    : 431
% 5.62/2.08  #SimpNegUnit  : 52
% 5.62/2.08  #BackRed      : 99
% 5.62/2.08  
% 5.62/2.08  #Partial instantiations: 6176
% 5.62/2.09  #Strategies tried      : 1
% 5.62/2.09  
% 5.62/2.09  Timing (in seconds)
% 5.62/2.09  ----------------------
% 5.62/2.09  Preprocessing        : 0.32
% 5.62/2.09  Parsing              : 0.17
% 5.62/2.09  CNF conversion       : 0.03
% 5.62/2.09  Main loop            : 0.96
% 5.62/2.09  Inferencing          : 0.39
% 5.62/2.09  Reduction            : 0.26
% 5.62/2.09  Demodulation         : 0.18
% 5.62/2.09  BG Simplification    : 0.05
% 5.62/2.09  Subsumption          : 0.17
% 5.62/2.09  Abstraction          : 0.04
% 5.62/2.09  MUC search           : 0.00
% 5.62/2.09  Cooper               : 0.00
% 5.62/2.09  Total                : 1.33
% 5.62/2.09  Index Insertion      : 0.00
% 5.62/2.09  Index Deletion       : 0.00
% 5.62/2.09  Index Matching       : 0.00
% 5.62/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
