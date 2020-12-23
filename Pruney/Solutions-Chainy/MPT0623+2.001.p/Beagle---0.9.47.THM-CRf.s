%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:06 EST 2020

% Result     : Theorem 31.24s
% Output     : CNFRefutation 31.55s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 899 expanded)
%              Number of leaves         :   35 ( 323 expanded)
%              Depth                    :   29
%              Number of atoms          :  315 (1974 expanded)
%              Number of equality atoms :  119 ( 858 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_10 > #skF_8 > #skF_9 > #skF_7 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_57,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_82,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_71,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_243,plain,(
    ! [C_97,A_98] :
      ( r2_hidden(k4_tarski(C_97,'#skF_7'(A_98,k1_relat_1(A_98),C_97)),A_98)
      | ~ r2_hidden(C_97,k1_relat_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_259,plain,(
    ! [C_97,A_98,B_2] :
      ( r2_hidden(k4_tarski(C_97,'#skF_7'(A_98,k1_relat_1(A_98),C_97)),B_2)
      | ~ r1_tarski(A_98,B_2)
      | ~ r2_hidden(C_97,k1_relat_1(A_98)) ) ),
    inference(resolution,[status(thm)],[c_243,c_2])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_72,plain,(
    ! [A_45] :
      ( v1_relat_1(A_45)
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_76,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_72])).

tff(c_66,plain,(
    ! [A_44] :
      ( v1_funct_1(A_44)
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_70,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_66])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1016,plain,(
    ! [B_1236,A_1237] :
      ( k1_tarski(k1_funct_1(B_1236,A_1237)) = k2_relat_1(B_1236)
      | k1_tarski(A_1237) != k1_relat_1(B_1236)
      | ~ v1_funct_1(B_1236)
      | ~ v1_relat_1(B_1236) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_14,plain,(
    ! [C_11] : r2_hidden(C_11,k1_tarski(C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_38600,plain,(
    ! [B_13385,A_13386] :
      ( r2_hidden(k1_funct_1(B_13385,A_13386),k2_relat_1(B_13385))
      | k1_tarski(A_13386) != k1_relat_1(B_13385)
      | ~ v1_funct_1(B_13385)
      | ~ v1_relat_1(B_13385) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1016,c_14])).

tff(c_38612,plain,(
    ! [A_13386] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,A_13386),k1_xboole_0)
      | k1_tarski(A_13386) != k1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_38600])).

tff(c_38616,plain,(
    ! [A_13411] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,A_13411),k1_xboole_0)
      | k1_tarski(A_13411) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_70,c_40,c_38612])).

tff(c_38622,plain,(
    ! [A_13411,B_2] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,A_13411),B_2)
      | ~ r1_tarski(k1_xboole_0,B_2)
      | k1_tarski(A_13411) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38616,c_2])).

tff(c_38630,plain,(
    ! [A_13436,B_13437] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,A_13436),B_13437)
      | k1_tarski(A_13436) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_38622])).

tff(c_12,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_38994,plain,(
    ! [A_13462] :
      ( k1_funct_1(k1_xboole_0,A_13462) = '#skF_9'
      | k1_tarski(A_13462) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38630,c_12])).

tff(c_44,plain,(
    ! [B_34,A_33] :
      ( k1_tarski(k1_funct_1(B_34,A_33)) = k2_relat_1(B_34)
      | k1_tarski(A_33) != k1_relat_1(B_34)
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_38997,plain,(
    ! [A_13462] :
      ( k2_relat_1(k1_xboole_0) = k1_tarski('#skF_9')
      | k1_tarski(A_13462) != k1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | k1_tarski(A_13462) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38994,c_44])).

tff(c_39260,plain,(
    ! [A_13462] :
      ( k1_tarski('#skF_9') = k1_xboole_0
      | k1_tarski(A_13462) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_70,c_40,c_38,c_38997])).

tff(c_39278,plain,(
    ! [A_13462] : k1_tarski(A_13462) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_39260])).

tff(c_1176,plain,(
    ! [A_1473,B_1474] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1473,B_1474),'#skF_5'(A_1473,B_1474)),A_1473)
      | r2_hidden('#skF_6'(A_1473,B_1474),B_1474)
      | k1_relat_1(A_1473) = B_1474 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    ! [C_28,A_13,D_31] :
      ( r2_hidden(C_28,k1_relat_1(A_13))
      | ~ r2_hidden(k4_tarski(C_28,D_31),A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_38536,plain,(
    ! [A_13333,B_13334] :
      ( r2_hidden('#skF_4'(A_13333,B_13334),k1_relat_1(A_13333))
      | r2_hidden('#skF_6'(A_13333,B_13334),B_13334)
      | k1_relat_1(A_13333) = B_13334 ) ),
    inference(resolution,[status(thm)],[c_1176,c_28])).

tff(c_38559,plain,(
    ! [B_13334] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_13334),k1_xboole_0)
      | r2_hidden('#skF_6'(k1_xboole_0,B_13334),B_13334)
      | k1_relat_1(k1_xboole_0) = B_13334 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_38536])).

tff(c_39809,plain,(
    ! [B_15420] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_15420),k1_xboole_0)
      | r2_hidden('#skF_6'(k1_xboole_0,B_15420),B_15420)
      | k1_xboole_0 = B_15420 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38559])).

tff(c_39824,plain,(
    ! [A_7] :
      ( '#skF_6'(k1_xboole_0,k1_tarski(A_7)) = A_7
      | r2_hidden('#skF_4'(k1_xboole_0,k1_tarski(A_7)),k1_xboole_0)
      | k1_tarski(A_7) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_39809,c_12])).

tff(c_39836,plain,(
    ! [A_15445] :
      ( '#skF_6'(k1_xboole_0,k1_tarski(A_15445)) = A_15445
      | r2_hidden('#skF_4'(k1_xboole_0,k1_tarski(A_15445)),k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_39278,c_39824])).

tff(c_39842,plain,(
    ! [A_15445,B_2] :
      ( r2_hidden('#skF_4'(k1_xboole_0,k1_tarski(A_15445)),B_2)
      | ~ r1_tarski(k1_xboole_0,B_2)
      | '#skF_6'(k1_xboole_0,k1_tarski(A_15445)) = A_15445 ) ),
    inference(resolution,[status(thm)],[c_39836,c_2])).

tff(c_40170,plain,(
    ! [A_15656,B_15657] :
      ( r2_hidden('#skF_4'(k1_xboole_0,k1_tarski(A_15656)),B_15657)
      | '#skF_6'(k1_xboole_0,k1_tarski(A_15656)) = A_15656 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_39842])).

tff(c_989,plain,(
    ! [A_1185,B_1186] :
      ( ~ r2_hidden('#skF_4'(A_1185,B_1186),B_1186)
      | r2_hidden('#skF_6'(A_1185,B_1186),B_1186)
      | k1_relat_1(A_1185) = B_1186 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1007,plain,(
    ! [A_1185,A_7] :
      ( '#skF_6'(A_1185,k1_tarski(A_7)) = A_7
      | ~ r2_hidden('#skF_4'(A_1185,k1_tarski(A_7)),k1_tarski(A_7))
      | k1_tarski(A_7) = k1_relat_1(A_1185) ) ),
    inference(resolution,[status(thm)],[c_989,c_12])).

tff(c_40182,plain,(
    ! [A_15656] :
      ( k1_tarski(A_15656) = k1_relat_1(k1_xboole_0)
      | '#skF_6'(k1_xboole_0,k1_tarski(A_15656)) = A_15656 ) ),
    inference(resolution,[status(thm)],[c_40170,c_1007])).

tff(c_40211,plain,(
    ! [A_15656] :
      ( k1_tarski(A_15656) = k1_xboole_0
      | '#skF_6'(k1_xboole_0,k1_tarski(A_15656)) = A_15656 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40182])).

tff(c_40212,plain,(
    ! [A_15656] : '#skF_6'(k1_xboole_0,k1_tarski(A_15656)) = A_15656 ),
    inference(negUnitSimplification,[status(thm)],[c_39278,c_40211])).

tff(c_26,plain,(
    ! [C_28,A_13] :
      ( r2_hidden(k4_tarski(C_28,'#skF_7'(A_13,k1_relat_1(A_13),C_28)),A_13)
      | ~ r2_hidden(C_28,k1_relat_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1284,plain,(
    ! [A_1578,B_1579,D_1580] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1578,B_1579),'#skF_5'(A_1578,B_1579)),A_1578)
      | ~ r2_hidden(k4_tarski('#skF_6'(A_1578,B_1579),D_1580),A_1578)
      | k1_relat_1(A_1578) = B_1579 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_39556,plain,(
    ! [A_15262,B_15263] :
      ( r2_hidden(k4_tarski('#skF_4'(A_15262,B_15263),'#skF_5'(A_15262,B_15263)),A_15262)
      | k1_relat_1(A_15262) = B_15263
      | ~ r2_hidden('#skF_6'(A_15262,B_15263),k1_relat_1(A_15262)) ) ),
    inference(resolution,[status(thm)],[c_26,c_1284])).

tff(c_40257,plain,(
    ! [A_15707,B_15708] :
      ( r2_hidden('#skF_4'(A_15707,B_15708),k1_relat_1(A_15707))
      | k1_relat_1(A_15707) = B_15708
      | ~ r2_hidden('#skF_6'(A_15707,B_15708),k1_relat_1(A_15707)) ) ),
    inference(resolution,[status(thm)],[c_39556,c_28])).

tff(c_40260,plain,(
    ! [A_15656] :
      ( r2_hidden('#skF_4'(k1_xboole_0,k1_tarski(A_15656)),k1_relat_1(k1_xboole_0))
      | k1_tarski(A_15656) = k1_relat_1(k1_xboole_0)
      | ~ r2_hidden(A_15656,k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40212,c_40257])).

tff(c_40287,plain,(
    ! [A_15656] :
      ( r2_hidden('#skF_4'(k1_xboole_0,k1_tarski(A_15656)),k1_xboole_0)
      | k1_tarski(A_15656) = k1_xboole_0
      | ~ r2_hidden(A_15656,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_40,c_40260])).

tff(c_40297,plain,(
    ! [A_15733] :
      ( r2_hidden('#skF_4'(k1_xboole_0,k1_tarski(A_15733)),k1_xboole_0)
      | ~ r2_hidden(A_15733,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_39278,c_40287])).

tff(c_258,plain,(
    ! [C_97] :
      ( r2_hidden(k4_tarski(C_97,'#skF_7'(k1_xboole_0,k1_xboole_0,C_97)),k1_xboole_0)
      | ~ r2_hidden(C_97,k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_243])).

tff(c_263,plain,(
    ! [C_99] :
      ( r2_hidden(k4_tarski(C_99,'#skF_7'(k1_xboole_0,k1_xboole_0,C_99)),k1_xboole_0)
      | ~ r2_hidden(C_99,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_258])).

tff(c_265,plain,(
    ! [C_99,B_2] :
      ( r2_hidden(k4_tarski(C_99,'#skF_7'(k1_xboole_0,k1_xboole_0,C_99)),B_2)
      | ~ r1_tarski(k1_xboole_0,B_2)
      | ~ r2_hidden(C_99,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_263,c_2])).

tff(c_274,plain,(
    ! [C_100,B_101] :
      ( r2_hidden(k4_tarski(C_100,'#skF_7'(k1_xboole_0,k1_xboole_0,C_100)),B_101)
      | ~ r2_hidden(C_100,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_265])).

tff(c_287,plain,(
    ! [C_102,B_103] :
      ( r2_hidden(C_102,k1_relat_1(B_103))
      | ~ r2_hidden(C_102,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_274,c_28])).

tff(c_1233,plain,(
    ! [C_1525,B_1526,B_1527] :
      ( r2_hidden(C_1525,B_1526)
      | ~ r1_tarski(k1_relat_1(B_1527),B_1526)
      | ~ r2_hidden(C_1525,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_287,c_2])).

tff(c_1243,plain,(
    ! [C_1525,B_1526] :
      ( r2_hidden(C_1525,B_1526)
      | ~ r1_tarski(k1_xboole_0,B_1526)
      | ~ r2_hidden(C_1525,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1233])).

tff(c_1247,plain,(
    ! [C_1525,B_1526] :
      ( r2_hidden(C_1525,B_1526)
      | ~ r2_hidden(C_1525,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1243])).

tff(c_40320,plain,(
    ! [A_15758,B_15759] :
      ( r2_hidden('#skF_4'(k1_xboole_0,k1_tarski(A_15758)),B_15759)
      | ~ r2_hidden(A_15758,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_40297,c_1247])).

tff(c_30,plain,(
    ! [A_13,B_14,D_27] :
      ( ~ r2_hidden('#skF_4'(A_13,B_14),B_14)
      | ~ r2_hidden(k4_tarski('#skF_6'(A_13,B_14),D_27),A_13)
      | k1_relat_1(A_13) = B_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_40338,plain,(
    ! [A_15758,D_27] :
      ( ~ r2_hidden(k4_tarski('#skF_6'(k1_xboole_0,k1_tarski(A_15758)),D_27),k1_xboole_0)
      | k1_tarski(A_15758) = k1_relat_1(k1_xboole_0)
      | ~ r2_hidden(A_15758,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_40320,c_30])).

tff(c_40365,plain,(
    ! [A_15758,D_27] :
      ( ~ r2_hidden(k4_tarski(A_15758,D_27),k1_xboole_0)
      | k1_tarski(A_15758) = k1_xboole_0
      | ~ r2_hidden(A_15758,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40212,c_40338])).

tff(c_40370,plain,(
    ! [A_15784,D_15785] :
      ( ~ r2_hidden(k4_tarski(A_15784,D_15785),k1_xboole_0)
      | ~ r2_hidden(A_15784,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_39278,c_40365])).

tff(c_46102,plain,(
    ! [C_26197,A_26198] :
      ( ~ r2_hidden(C_26197,k1_xboole_0)
      | ~ r1_tarski(A_26198,k1_xboole_0)
      | ~ r2_hidden(C_26197,k1_relat_1(A_26198)) ) ),
    inference(resolution,[status(thm)],[c_259,c_40370])).

tff(c_46214,plain,(
    ! [C_26197] :
      ( ~ r2_hidden(C_26197,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden(C_26197,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_46102])).

tff(c_46242,plain,(
    ! [C_26197] : ~ r2_hidden(C_26197,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_46214])).

tff(c_38563,plain,(
    ! [B_13334] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_13334),k1_xboole_0)
      | r2_hidden('#skF_6'(k1_xboole_0,B_13334),B_13334)
      | k1_xboole_0 = B_13334 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38559])).

tff(c_46243,plain,(
    ! [B_13334] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_13334),B_13334)
      | k1_xboole_0 = B_13334 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46242,c_38563])).

tff(c_48,plain,(
    ! [A_35,B_39] :
      ( k1_relat_1('#skF_8'(A_35,B_39)) = A_35
      | k1_xboole_0 = A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_50,plain,(
    ! [A_35,B_39] :
      ( v1_funct_1('#skF_8'(A_35,B_39))
      | k1_xboole_0 = A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_52,plain,(
    ! [A_35,B_39] :
      ( v1_relat_1('#skF_8'(A_35,B_39))
      | k1_xboole_0 = A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_104,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_1'(A_56,B_57),A_56)
      | r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_109,plain,(
    ! [A_7,B_57] :
      ( '#skF_1'(k1_tarski(A_7),B_57) = A_7
      | r1_tarski(k1_tarski(A_7),B_57) ) ),
    inference(resolution,[status(thm)],[c_104,c_12])).

tff(c_117,plain,(
    ! [A_60,B_61] :
      ( k2_relat_1('#skF_8'(A_60,B_61)) = k1_tarski(B_61)
      | k1_xboole_0 = A_60 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_54,plain,(
    ! [C_42] :
      ( ~ r1_tarski(k2_relat_1(C_42),'#skF_9')
      | k1_relat_1(C_42) != '#skF_10'
      | ~ v1_funct_1(C_42)
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_188,plain,(
    ! [B_82,A_83] :
      ( ~ r1_tarski(k1_tarski(B_82),'#skF_9')
      | k1_relat_1('#skF_8'(A_83,B_82)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_83,B_82))
      | ~ v1_relat_1('#skF_8'(A_83,B_82))
      | k1_xboole_0 = A_83 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_54])).

tff(c_310,plain,(
    ! [A_104,A_105] :
      ( k1_relat_1('#skF_8'(A_104,A_105)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_104,A_105))
      | ~ v1_relat_1('#skF_8'(A_104,A_105))
      | k1_xboole_0 = A_104
      | '#skF_1'(k1_tarski(A_105),'#skF_9') = A_105 ) ),
    inference(resolution,[status(thm)],[c_109,c_188])).

tff(c_1226,plain,(
    ! [A_1499,B_1500] :
      ( k1_relat_1('#skF_8'(A_1499,B_1500)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_1499,B_1500))
      | '#skF_1'(k1_tarski(B_1500),'#skF_9') = B_1500
      | k1_xboole_0 = A_1499 ) ),
    inference(resolution,[status(thm)],[c_52,c_310])).

tff(c_50744,plain,(
    ! [A_26460,B_26461] :
      ( k1_relat_1('#skF_8'(A_26460,B_26461)) != '#skF_10'
      | '#skF_1'(k1_tarski(B_26461),'#skF_9') = B_26461
      | k1_xboole_0 = A_26460 ) ),
    inference(resolution,[status(thm)],[c_50,c_1226])).

tff(c_50747,plain,(
    ! [A_35,B_39] :
      ( A_35 != '#skF_10'
      | '#skF_1'(k1_tarski(B_39),'#skF_9') = B_39
      | k1_xboole_0 = A_35
      | k1_xboole_0 = A_35 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_50744])).

tff(c_50749,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_50747])).

tff(c_77,plain,(
    ! [C_46] :
      ( ~ r1_tarski(k2_relat_1(C_46),'#skF_9')
      | k1_relat_1(C_46) != '#skF_10'
      | ~ v1_funct_1(C_46)
      | ~ v1_relat_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_80,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_9')
    | k1_relat_1(k1_xboole_0) != '#skF_10'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_77])).

tff(c_82,plain,
    ( k1_xboole_0 != '#skF_10'
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_40,c_10,c_80])).

tff(c_85,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_82])).

tff(c_50821,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50749,c_85])).

tff(c_50840,plain,(
    ! [B_26465] : '#skF_1'(k1_tarski(B_26465),'#skF_9') = B_26465 ),
    inference(splitRight,[status(thm)],[c_50747])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50881,plain,(
    ! [B_26466] :
      ( ~ r2_hidden(B_26466,'#skF_9')
      | r1_tarski(k1_tarski(B_26466),'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50840,c_4])).

tff(c_123,plain,(
    ! [B_61,A_60] :
      ( ~ r1_tarski(k1_tarski(B_61),'#skF_9')
      | k1_relat_1('#skF_8'(A_60,B_61)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_60,B_61))
      | ~ v1_relat_1('#skF_8'(A_60,B_61))
      | k1_xboole_0 = A_60 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_54])).

tff(c_51009,plain,(
    ! [A_26470,B_26471] :
      ( k1_relat_1('#skF_8'(A_26470,B_26471)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_26470,B_26471))
      | ~ v1_relat_1('#skF_8'(A_26470,B_26471))
      | k1_xboole_0 = A_26470
      | ~ r2_hidden(B_26471,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_50881,c_123])).

tff(c_220928,plain,(
    ! [A_96604,B_96605] :
      ( k1_relat_1('#skF_8'(A_96604,B_96605)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_96604,B_96605))
      | ~ r2_hidden(B_96605,'#skF_9')
      | k1_xboole_0 = A_96604 ) ),
    inference(resolution,[status(thm)],[c_52,c_51009])).

tff(c_221013,plain,(
    ! [A_96798,B_96799] :
      ( k1_relat_1('#skF_8'(A_96798,B_96799)) != '#skF_10'
      | ~ r2_hidden(B_96799,'#skF_9')
      | k1_xboole_0 = A_96798 ) ),
    inference(resolution,[status(thm)],[c_50,c_220928])).

tff(c_221112,plain,(
    ! [A_35,B_39] :
      ( A_35 != '#skF_10'
      | ~ r2_hidden(B_39,'#skF_9')
      | k1_xboole_0 = A_35
      | k1_xboole_0 = A_35 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_221013])).

tff(c_223025,plain,(
    ! [B_97187] : ~ r2_hidden(B_97187,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_221112])).

tff(c_223095,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_46243,c_223025])).

tff(c_223171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_223095])).

tff(c_223173,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_221112])).

tff(c_223314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_223173,c_85])).

tff(c_223315,plain,(
    k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_39260])).

tff(c_142,plain,(
    ! [C_68,B_69,A_70] :
      ( r2_hidden(C_68,B_69)
      | ~ r2_hidden(C_68,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_151,plain,(
    ! [C_11,B_69] :
      ( r2_hidden(C_11,B_69)
      | ~ r1_tarski(k1_tarski(C_11),B_69) ) ),
    inference(resolution,[status(thm)],[c_14,c_142])).

tff(c_223343,plain,(
    ! [B_69] :
      ( r2_hidden('#skF_9',B_69)
      | ~ r1_tarski(k1_xboole_0,B_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_223315,c_151])).

tff(c_223361,plain,(
    ! [B_69] : r2_hidden('#skF_9',B_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_223343])).

tff(c_223363,plain,(
    ! [B_97428] : r2_hidden('#skF_9',B_97428) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_223343])).

tff(c_363,plain,(
    ! [C_108] :
      ( k4_tarski(C_108,'#skF_7'(k1_xboole_0,k1_xboole_0,C_108)) = '#skF_9'
      | ~ r2_hidden(C_108,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_274,c_12])).

tff(c_286,plain,(
    ! [C_100,A_7] :
      ( k4_tarski(C_100,'#skF_7'(k1_xboole_0,k1_xboole_0,C_100)) = A_7
      | ~ r2_hidden(C_100,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_274,c_12])).

tff(c_366,plain,(
    ! [A_7,C_108] :
      ( A_7 = '#skF_9'
      | ~ r2_hidden(C_108,k1_xboole_0)
      | ~ r2_hidden(C_108,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_286])).

tff(c_945,plain,(
    ! [C_108] :
      ( ~ r2_hidden(C_108,k1_xboole_0)
      | ~ r2_hidden(C_108,k1_xboole_0) ) ),
    inference(splitLeft,[status(thm)],[c_366])).

tff(c_223369,plain,(
    ~ r2_hidden('#skF_9',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_223363,c_945])).

tff(c_223381,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_223361,c_223369])).

tff(c_223398,plain,(
    ! [A_97503] : A_97503 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_366])).

tff(c_223522,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_223398,c_71])).

tff(c_223524,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_223523,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_223533,plain,(
    '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_223524,c_223523])).

tff(c_223528,plain,(
    v1_xboole_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223523,c_8])).

tff(c_223544,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223533,c_223528])).

tff(c_223563,plain,(
    ! [A_98562] :
      ( v1_relat_1(A_98562)
      | ~ v1_xboole_0(A_98562) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_223567,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_223544,c_223563])).

tff(c_223549,plain,(
    v1_funct_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223524,c_70])).

tff(c_223526,plain,(
    k1_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_223523,c_223523,c_40])).

tff(c_223551,plain,(
    k1_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_223533,c_223533,c_223526])).

tff(c_223525,plain,(
    ! [A_6] : r1_tarski('#skF_10',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223523,c_10])).

tff(c_223561,plain,(
    ! [A_6] : r1_tarski('#skF_9',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223533,c_223525])).

tff(c_223527,plain,(
    k2_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_223523,c_223523,c_38])).

tff(c_223556,plain,(
    k2_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_223533,c_223533,c_223527])).

tff(c_223568,plain,(
    ! [C_98563] :
      ( ~ r1_tarski(k2_relat_1(C_98563),'#skF_9')
      | k1_relat_1(C_98563) != '#skF_9'
      | ~ v1_funct_1(C_98563)
      | ~ v1_relat_1(C_98563) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223533,c_54])).

tff(c_223571,plain,
    ( ~ r1_tarski('#skF_9','#skF_9')
    | k1_relat_1('#skF_9') != '#skF_9'
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_223556,c_223568])).

tff(c_223574,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_223567,c_223549,c_223551,c_223561,c_223571])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:28:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 31.24/18.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.24/18.80  
% 31.24/18.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.24/18.80  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_10 > #skF_8 > #skF_9 > #skF_7 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 31.24/18.80  
% 31.24/18.80  %Foreground sorts:
% 31.24/18.80  
% 31.24/18.80  
% 31.24/18.80  %Background operators:
% 31.24/18.80  
% 31.24/18.80  
% 31.24/18.80  %Foreground operators:
% 31.24/18.80  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 31.24/18.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 31.24/18.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 31.24/18.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 31.24/18.80  tff(k1_tarski, type, k1_tarski: $i > $i).
% 31.24/18.80  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 31.24/18.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 31.24/18.80  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 31.24/18.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 31.24/18.80  tff('#skF_10', type, '#skF_10': $i).
% 31.24/18.80  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 31.24/18.80  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 31.24/18.80  tff('#skF_9', type, '#skF_9': $i).
% 31.24/18.80  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 31.24/18.80  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 31.24/18.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 31.24/18.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 31.24/18.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 31.24/18.80  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 31.24/18.80  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 31.24/18.80  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 31.24/18.80  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 31.24/18.80  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 31.24/18.80  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 31.24/18.80  
% 31.24/18.83  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 31.24/18.83  tff(f_100, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 31.24/18.83  tff(f_57, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 31.24/18.83  tff(f_54, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 31.24/18.83  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 31.24/18.83  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 31.24/18.83  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 31.24/18.83  tff(f_61, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 31.24/18.83  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 31.24/18.83  tff(f_42, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 31.24/18.83  tff(f_82, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 31.24/18.83  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 31.24/18.83  tff(c_56, plain, (k1_xboole_0='#skF_10' | k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_100])).
% 31.24/18.83  tff(c_71, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_56])).
% 31.24/18.83  tff(c_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 31.24/18.83  tff(c_243, plain, (![C_97, A_98]: (r2_hidden(k4_tarski(C_97, '#skF_7'(A_98, k1_relat_1(A_98), C_97)), A_98) | ~r2_hidden(C_97, k1_relat_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 31.24/18.83  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 31.24/18.83  tff(c_259, plain, (![C_97, A_98, B_2]: (r2_hidden(k4_tarski(C_97, '#skF_7'(A_98, k1_relat_1(A_98), C_97)), B_2) | ~r1_tarski(A_98, B_2) | ~r2_hidden(C_97, k1_relat_1(A_98)))), inference(resolution, [status(thm)], [c_243, c_2])).
% 31.24/18.83  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 31.24/18.83  tff(c_72, plain, (![A_45]: (v1_relat_1(A_45) | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_46])).
% 31.24/18.83  tff(c_76, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_72])).
% 31.24/18.83  tff(c_66, plain, (![A_44]: (v1_funct_1(A_44) | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_61])).
% 31.24/18.83  tff(c_70, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_66])).
% 31.24/18.83  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 31.24/18.83  tff(c_1016, plain, (![B_1236, A_1237]: (k1_tarski(k1_funct_1(B_1236, A_1237))=k2_relat_1(B_1236) | k1_tarski(A_1237)!=k1_relat_1(B_1236) | ~v1_funct_1(B_1236) | ~v1_relat_1(B_1236))), inference(cnfTransformation, [status(thm)], [f_69])).
% 31.24/18.83  tff(c_14, plain, (![C_11]: (r2_hidden(C_11, k1_tarski(C_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 31.24/18.83  tff(c_38600, plain, (![B_13385, A_13386]: (r2_hidden(k1_funct_1(B_13385, A_13386), k2_relat_1(B_13385)) | k1_tarski(A_13386)!=k1_relat_1(B_13385) | ~v1_funct_1(B_13385) | ~v1_relat_1(B_13385))), inference(superposition, [status(thm), theory('equality')], [c_1016, c_14])).
% 31.24/18.83  tff(c_38612, plain, (![A_13386]: (r2_hidden(k1_funct_1(k1_xboole_0, A_13386), k1_xboole_0) | k1_tarski(A_13386)!=k1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_38600])).
% 31.24/18.83  tff(c_38616, plain, (![A_13411]: (r2_hidden(k1_funct_1(k1_xboole_0, A_13411), k1_xboole_0) | k1_tarski(A_13411)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_70, c_40, c_38612])).
% 31.24/18.83  tff(c_38622, plain, (![A_13411, B_2]: (r2_hidden(k1_funct_1(k1_xboole_0, A_13411), B_2) | ~r1_tarski(k1_xboole_0, B_2) | k1_tarski(A_13411)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_38616, c_2])).
% 31.24/18.83  tff(c_38630, plain, (![A_13436, B_13437]: (r2_hidden(k1_funct_1(k1_xboole_0, A_13436), B_13437) | k1_tarski(A_13436)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_38622])).
% 31.24/18.83  tff(c_12, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 31.24/18.83  tff(c_38994, plain, (![A_13462]: (k1_funct_1(k1_xboole_0, A_13462)='#skF_9' | k1_tarski(A_13462)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_38630, c_12])).
% 31.24/18.83  tff(c_44, plain, (![B_34, A_33]: (k1_tarski(k1_funct_1(B_34, A_33))=k2_relat_1(B_34) | k1_tarski(A_33)!=k1_relat_1(B_34) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_69])).
% 31.24/18.83  tff(c_38997, plain, (![A_13462]: (k2_relat_1(k1_xboole_0)=k1_tarski('#skF_9') | k1_tarski(A_13462)!=k1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | k1_tarski(A_13462)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38994, c_44])).
% 31.24/18.83  tff(c_39260, plain, (![A_13462]: (k1_tarski('#skF_9')=k1_xboole_0 | k1_tarski(A_13462)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_70, c_40, c_38, c_38997])).
% 31.24/18.83  tff(c_39278, plain, (![A_13462]: (k1_tarski(A_13462)!=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_39260])).
% 31.24/18.83  tff(c_1176, plain, (![A_1473, B_1474]: (r2_hidden(k4_tarski('#skF_4'(A_1473, B_1474), '#skF_5'(A_1473, B_1474)), A_1473) | r2_hidden('#skF_6'(A_1473, B_1474), B_1474) | k1_relat_1(A_1473)=B_1474)), inference(cnfTransformation, [status(thm)], [f_54])).
% 31.24/18.83  tff(c_28, plain, (![C_28, A_13, D_31]: (r2_hidden(C_28, k1_relat_1(A_13)) | ~r2_hidden(k4_tarski(C_28, D_31), A_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 31.24/18.83  tff(c_38536, plain, (![A_13333, B_13334]: (r2_hidden('#skF_4'(A_13333, B_13334), k1_relat_1(A_13333)) | r2_hidden('#skF_6'(A_13333, B_13334), B_13334) | k1_relat_1(A_13333)=B_13334)), inference(resolution, [status(thm)], [c_1176, c_28])).
% 31.24/18.83  tff(c_38559, plain, (![B_13334]: (r2_hidden('#skF_4'(k1_xboole_0, B_13334), k1_xboole_0) | r2_hidden('#skF_6'(k1_xboole_0, B_13334), B_13334) | k1_relat_1(k1_xboole_0)=B_13334)), inference(superposition, [status(thm), theory('equality')], [c_40, c_38536])).
% 31.24/18.83  tff(c_39809, plain, (![B_15420]: (r2_hidden('#skF_4'(k1_xboole_0, B_15420), k1_xboole_0) | r2_hidden('#skF_6'(k1_xboole_0, B_15420), B_15420) | k1_xboole_0=B_15420)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38559])).
% 31.24/18.83  tff(c_39824, plain, (![A_7]: ('#skF_6'(k1_xboole_0, k1_tarski(A_7))=A_7 | r2_hidden('#skF_4'(k1_xboole_0, k1_tarski(A_7)), k1_xboole_0) | k1_tarski(A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_39809, c_12])).
% 31.24/18.83  tff(c_39836, plain, (![A_15445]: ('#skF_6'(k1_xboole_0, k1_tarski(A_15445))=A_15445 | r2_hidden('#skF_4'(k1_xboole_0, k1_tarski(A_15445)), k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_39278, c_39824])).
% 31.24/18.83  tff(c_39842, plain, (![A_15445, B_2]: (r2_hidden('#skF_4'(k1_xboole_0, k1_tarski(A_15445)), B_2) | ~r1_tarski(k1_xboole_0, B_2) | '#skF_6'(k1_xboole_0, k1_tarski(A_15445))=A_15445)), inference(resolution, [status(thm)], [c_39836, c_2])).
% 31.24/18.83  tff(c_40170, plain, (![A_15656, B_15657]: (r2_hidden('#skF_4'(k1_xboole_0, k1_tarski(A_15656)), B_15657) | '#skF_6'(k1_xboole_0, k1_tarski(A_15656))=A_15656)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_39842])).
% 31.24/18.83  tff(c_989, plain, (![A_1185, B_1186]: (~r2_hidden('#skF_4'(A_1185, B_1186), B_1186) | r2_hidden('#skF_6'(A_1185, B_1186), B_1186) | k1_relat_1(A_1185)=B_1186)), inference(cnfTransformation, [status(thm)], [f_54])).
% 31.24/18.83  tff(c_1007, plain, (![A_1185, A_7]: ('#skF_6'(A_1185, k1_tarski(A_7))=A_7 | ~r2_hidden('#skF_4'(A_1185, k1_tarski(A_7)), k1_tarski(A_7)) | k1_tarski(A_7)=k1_relat_1(A_1185))), inference(resolution, [status(thm)], [c_989, c_12])).
% 31.24/18.83  tff(c_40182, plain, (![A_15656]: (k1_tarski(A_15656)=k1_relat_1(k1_xboole_0) | '#skF_6'(k1_xboole_0, k1_tarski(A_15656))=A_15656)), inference(resolution, [status(thm)], [c_40170, c_1007])).
% 31.24/18.83  tff(c_40211, plain, (![A_15656]: (k1_tarski(A_15656)=k1_xboole_0 | '#skF_6'(k1_xboole_0, k1_tarski(A_15656))=A_15656)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40182])).
% 31.24/18.83  tff(c_40212, plain, (![A_15656]: ('#skF_6'(k1_xboole_0, k1_tarski(A_15656))=A_15656)), inference(negUnitSimplification, [status(thm)], [c_39278, c_40211])).
% 31.24/18.83  tff(c_26, plain, (![C_28, A_13]: (r2_hidden(k4_tarski(C_28, '#skF_7'(A_13, k1_relat_1(A_13), C_28)), A_13) | ~r2_hidden(C_28, k1_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 31.24/18.83  tff(c_1284, plain, (![A_1578, B_1579, D_1580]: (r2_hidden(k4_tarski('#skF_4'(A_1578, B_1579), '#skF_5'(A_1578, B_1579)), A_1578) | ~r2_hidden(k4_tarski('#skF_6'(A_1578, B_1579), D_1580), A_1578) | k1_relat_1(A_1578)=B_1579)), inference(cnfTransformation, [status(thm)], [f_54])).
% 31.24/18.83  tff(c_39556, plain, (![A_15262, B_15263]: (r2_hidden(k4_tarski('#skF_4'(A_15262, B_15263), '#skF_5'(A_15262, B_15263)), A_15262) | k1_relat_1(A_15262)=B_15263 | ~r2_hidden('#skF_6'(A_15262, B_15263), k1_relat_1(A_15262)))), inference(resolution, [status(thm)], [c_26, c_1284])).
% 31.24/18.83  tff(c_40257, plain, (![A_15707, B_15708]: (r2_hidden('#skF_4'(A_15707, B_15708), k1_relat_1(A_15707)) | k1_relat_1(A_15707)=B_15708 | ~r2_hidden('#skF_6'(A_15707, B_15708), k1_relat_1(A_15707)))), inference(resolution, [status(thm)], [c_39556, c_28])).
% 31.24/18.83  tff(c_40260, plain, (![A_15656]: (r2_hidden('#skF_4'(k1_xboole_0, k1_tarski(A_15656)), k1_relat_1(k1_xboole_0)) | k1_tarski(A_15656)=k1_relat_1(k1_xboole_0) | ~r2_hidden(A_15656, k1_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_40212, c_40257])).
% 31.24/18.83  tff(c_40287, plain, (![A_15656]: (r2_hidden('#skF_4'(k1_xboole_0, k1_tarski(A_15656)), k1_xboole_0) | k1_tarski(A_15656)=k1_xboole_0 | ~r2_hidden(A_15656, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_40, c_40260])).
% 31.24/18.83  tff(c_40297, plain, (![A_15733]: (r2_hidden('#skF_4'(k1_xboole_0, k1_tarski(A_15733)), k1_xboole_0) | ~r2_hidden(A_15733, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_39278, c_40287])).
% 31.24/18.83  tff(c_258, plain, (![C_97]: (r2_hidden(k4_tarski(C_97, '#skF_7'(k1_xboole_0, k1_xboole_0, C_97)), k1_xboole_0) | ~r2_hidden(C_97, k1_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_243])).
% 31.24/18.83  tff(c_263, plain, (![C_99]: (r2_hidden(k4_tarski(C_99, '#skF_7'(k1_xboole_0, k1_xboole_0, C_99)), k1_xboole_0) | ~r2_hidden(C_99, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_258])).
% 31.24/18.83  tff(c_265, plain, (![C_99, B_2]: (r2_hidden(k4_tarski(C_99, '#skF_7'(k1_xboole_0, k1_xboole_0, C_99)), B_2) | ~r1_tarski(k1_xboole_0, B_2) | ~r2_hidden(C_99, k1_xboole_0))), inference(resolution, [status(thm)], [c_263, c_2])).
% 31.24/18.83  tff(c_274, plain, (![C_100, B_101]: (r2_hidden(k4_tarski(C_100, '#skF_7'(k1_xboole_0, k1_xboole_0, C_100)), B_101) | ~r2_hidden(C_100, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_265])).
% 31.24/18.83  tff(c_287, plain, (![C_102, B_103]: (r2_hidden(C_102, k1_relat_1(B_103)) | ~r2_hidden(C_102, k1_xboole_0))), inference(resolution, [status(thm)], [c_274, c_28])).
% 31.24/18.83  tff(c_1233, plain, (![C_1525, B_1526, B_1527]: (r2_hidden(C_1525, B_1526) | ~r1_tarski(k1_relat_1(B_1527), B_1526) | ~r2_hidden(C_1525, k1_xboole_0))), inference(resolution, [status(thm)], [c_287, c_2])).
% 31.24/18.83  tff(c_1243, plain, (![C_1525, B_1526]: (r2_hidden(C_1525, B_1526) | ~r1_tarski(k1_xboole_0, B_1526) | ~r2_hidden(C_1525, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1233])).
% 31.24/18.83  tff(c_1247, plain, (![C_1525, B_1526]: (r2_hidden(C_1525, B_1526) | ~r2_hidden(C_1525, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1243])).
% 31.24/18.83  tff(c_40320, plain, (![A_15758, B_15759]: (r2_hidden('#skF_4'(k1_xboole_0, k1_tarski(A_15758)), B_15759) | ~r2_hidden(A_15758, k1_xboole_0))), inference(resolution, [status(thm)], [c_40297, c_1247])).
% 31.24/18.83  tff(c_30, plain, (![A_13, B_14, D_27]: (~r2_hidden('#skF_4'(A_13, B_14), B_14) | ~r2_hidden(k4_tarski('#skF_6'(A_13, B_14), D_27), A_13) | k1_relat_1(A_13)=B_14)), inference(cnfTransformation, [status(thm)], [f_54])).
% 31.24/18.83  tff(c_40338, plain, (![A_15758, D_27]: (~r2_hidden(k4_tarski('#skF_6'(k1_xboole_0, k1_tarski(A_15758)), D_27), k1_xboole_0) | k1_tarski(A_15758)=k1_relat_1(k1_xboole_0) | ~r2_hidden(A_15758, k1_xboole_0))), inference(resolution, [status(thm)], [c_40320, c_30])).
% 31.24/18.83  tff(c_40365, plain, (![A_15758, D_27]: (~r2_hidden(k4_tarski(A_15758, D_27), k1_xboole_0) | k1_tarski(A_15758)=k1_xboole_0 | ~r2_hidden(A_15758, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40212, c_40338])).
% 31.24/18.83  tff(c_40370, plain, (![A_15784, D_15785]: (~r2_hidden(k4_tarski(A_15784, D_15785), k1_xboole_0) | ~r2_hidden(A_15784, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_39278, c_40365])).
% 31.24/18.83  tff(c_46102, plain, (![C_26197, A_26198]: (~r2_hidden(C_26197, k1_xboole_0) | ~r1_tarski(A_26198, k1_xboole_0) | ~r2_hidden(C_26197, k1_relat_1(A_26198)))), inference(resolution, [status(thm)], [c_259, c_40370])).
% 31.24/18.83  tff(c_46214, plain, (![C_26197]: (~r2_hidden(C_26197, k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~r2_hidden(C_26197, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_46102])).
% 31.24/18.83  tff(c_46242, plain, (![C_26197]: (~r2_hidden(C_26197, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_46214])).
% 31.24/18.83  tff(c_38563, plain, (![B_13334]: (r2_hidden('#skF_4'(k1_xboole_0, B_13334), k1_xboole_0) | r2_hidden('#skF_6'(k1_xboole_0, B_13334), B_13334) | k1_xboole_0=B_13334)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38559])).
% 31.24/18.83  tff(c_46243, plain, (![B_13334]: (r2_hidden('#skF_6'(k1_xboole_0, B_13334), B_13334) | k1_xboole_0=B_13334)), inference(negUnitSimplification, [status(thm)], [c_46242, c_38563])).
% 31.24/18.83  tff(c_48, plain, (![A_35, B_39]: (k1_relat_1('#skF_8'(A_35, B_39))=A_35 | k1_xboole_0=A_35)), inference(cnfTransformation, [status(thm)], [f_82])).
% 31.24/18.83  tff(c_50, plain, (![A_35, B_39]: (v1_funct_1('#skF_8'(A_35, B_39)) | k1_xboole_0=A_35)), inference(cnfTransformation, [status(thm)], [f_82])).
% 31.24/18.83  tff(c_52, plain, (![A_35, B_39]: (v1_relat_1('#skF_8'(A_35, B_39)) | k1_xboole_0=A_35)), inference(cnfTransformation, [status(thm)], [f_82])).
% 31.24/18.83  tff(c_104, plain, (![A_56, B_57]: (r2_hidden('#skF_1'(A_56, B_57), A_56) | r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_32])).
% 31.24/18.83  tff(c_109, plain, (![A_7, B_57]: ('#skF_1'(k1_tarski(A_7), B_57)=A_7 | r1_tarski(k1_tarski(A_7), B_57))), inference(resolution, [status(thm)], [c_104, c_12])).
% 31.24/18.83  tff(c_117, plain, (![A_60, B_61]: (k2_relat_1('#skF_8'(A_60, B_61))=k1_tarski(B_61) | k1_xboole_0=A_60)), inference(cnfTransformation, [status(thm)], [f_82])).
% 31.24/18.83  tff(c_54, plain, (![C_42]: (~r1_tarski(k2_relat_1(C_42), '#skF_9') | k1_relat_1(C_42)!='#skF_10' | ~v1_funct_1(C_42) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_100])).
% 31.24/18.83  tff(c_188, plain, (![B_82, A_83]: (~r1_tarski(k1_tarski(B_82), '#skF_9') | k1_relat_1('#skF_8'(A_83, B_82))!='#skF_10' | ~v1_funct_1('#skF_8'(A_83, B_82)) | ~v1_relat_1('#skF_8'(A_83, B_82)) | k1_xboole_0=A_83)), inference(superposition, [status(thm), theory('equality')], [c_117, c_54])).
% 31.24/18.83  tff(c_310, plain, (![A_104, A_105]: (k1_relat_1('#skF_8'(A_104, A_105))!='#skF_10' | ~v1_funct_1('#skF_8'(A_104, A_105)) | ~v1_relat_1('#skF_8'(A_104, A_105)) | k1_xboole_0=A_104 | '#skF_1'(k1_tarski(A_105), '#skF_9')=A_105)), inference(resolution, [status(thm)], [c_109, c_188])).
% 31.24/18.83  tff(c_1226, plain, (![A_1499, B_1500]: (k1_relat_1('#skF_8'(A_1499, B_1500))!='#skF_10' | ~v1_funct_1('#skF_8'(A_1499, B_1500)) | '#skF_1'(k1_tarski(B_1500), '#skF_9')=B_1500 | k1_xboole_0=A_1499)), inference(resolution, [status(thm)], [c_52, c_310])).
% 31.24/18.83  tff(c_50744, plain, (![A_26460, B_26461]: (k1_relat_1('#skF_8'(A_26460, B_26461))!='#skF_10' | '#skF_1'(k1_tarski(B_26461), '#skF_9')=B_26461 | k1_xboole_0=A_26460)), inference(resolution, [status(thm)], [c_50, c_1226])).
% 31.24/18.83  tff(c_50747, plain, (![A_35, B_39]: (A_35!='#skF_10' | '#skF_1'(k1_tarski(B_39), '#skF_9')=B_39 | k1_xboole_0=A_35 | k1_xboole_0=A_35)), inference(superposition, [status(thm), theory('equality')], [c_48, c_50744])).
% 31.24/18.83  tff(c_50749, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_50747])).
% 31.24/18.83  tff(c_77, plain, (![C_46]: (~r1_tarski(k2_relat_1(C_46), '#skF_9') | k1_relat_1(C_46)!='#skF_10' | ~v1_funct_1(C_46) | ~v1_relat_1(C_46))), inference(cnfTransformation, [status(thm)], [f_100])).
% 31.24/18.83  tff(c_80, plain, (~r1_tarski(k1_xboole_0, '#skF_9') | k1_relat_1(k1_xboole_0)!='#skF_10' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_77])).
% 31.24/18.83  tff(c_82, plain, (k1_xboole_0!='#skF_10' | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_40, c_10, c_80])).
% 31.24/18.83  tff(c_85, plain, (k1_xboole_0!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_82])).
% 31.24/18.83  tff(c_50821, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50749, c_85])).
% 31.24/18.83  tff(c_50840, plain, (![B_26465]: ('#skF_1'(k1_tarski(B_26465), '#skF_9')=B_26465)), inference(splitRight, [status(thm)], [c_50747])).
% 31.24/18.83  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 31.24/18.83  tff(c_50881, plain, (![B_26466]: (~r2_hidden(B_26466, '#skF_9') | r1_tarski(k1_tarski(B_26466), '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_50840, c_4])).
% 31.24/18.83  tff(c_123, plain, (![B_61, A_60]: (~r1_tarski(k1_tarski(B_61), '#skF_9') | k1_relat_1('#skF_8'(A_60, B_61))!='#skF_10' | ~v1_funct_1('#skF_8'(A_60, B_61)) | ~v1_relat_1('#skF_8'(A_60, B_61)) | k1_xboole_0=A_60)), inference(superposition, [status(thm), theory('equality')], [c_117, c_54])).
% 31.24/18.83  tff(c_51009, plain, (![A_26470, B_26471]: (k1_relat_1('#skF_8'(A_26470, B_26471))!='#skF_10' | ~v1_funct_1('#skF_8'(A_26470, B_26471)) | ~v1_relat_1('#skF_8'(A_26470, B_26471)) | k1_xboole_0=A_26470 | ~r2_hidden(B_26471, '#skF_9'))), inference(resolution, [status(thm)], [c_50881, c_123])).
% 31.24/18.83  tff(c_220928, plain, (![A_96604, B_96605]: (k1_relat_1('#skF_8'(A_96604, B_96605))!='#skF_10' | ~v1_funct_1('#skF_8'(A_96604, B_96605)) | ~r2_hidden(B_96605, '#skF_9') | k1_xboole_0=A_96604)), inference(resolution, [status(thm)], [c_52, c_51009])).
% 31.24/18.83  tff(c_221013, plain, (![A_96798, B_96799]: (k1_relat_1('#skF_8'(A_96798, B_96799))!='#skF_10' | ~r2_hidden(B_96799, '#skF_9') | k1_xboole_0=A_96798)), inference(resolution, [status(thm)], [c_50, c_220928])).
% 31.24/18.83  tff(c_221112, plain, (![A_35, B_39]: (A_35!='#skF_10' | ~r2_hidden(B_39, '#skF_9') | k1_xboole_0=A_35 | k1_xboole_0=A_35)), inference(superposition, [status(thm), theory('equality')], [c_48, c_221013])).
% 31.24/18.83  tff(c_223025, plain, (![B_97187]: (~r2_hidden(B_97187, '#skF_9'))), inference(splitLeft, [status(thm)], [c_221112])).
% 31.24/18.83  tff(c_223095, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_46243, c_223025])).
% 31.24/18.83  tff(c_223171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_223095])).
% 31.24/18.83  tff(c_223173, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_221112])).
% 31.24/18.83  tff(c_223314, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_223173, c_85])).
% 31.24/18.83  tff(c_223315, plain, (k1_tarski('#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_39260])).
% 31.24/18.83  tff(c_142, plain, (![C_68, B_69, A_70]: (r2_hidden(C_68, B_69) | ~r2_hidden(C_68, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_32])).
% 31.24/18.83  tff(c_151, plain, (![C_11, B_69]: (r2_hidden(C_11, B_69) | ~r1_tarski(k1_tarski(C_11), B_69))), inference(resolution, [status(thm)], [c_14, c_142])).
% 31.24/18.83  tff(c_223343, plain, (![B_69]: (r2_hidden('#skF_9', B_69) | ~r1_tarski(k1_xboole_0, B_69))), inference(superposition, [status(thm), theory('equality')], [c_223315, c_151])).
% 31.24/18.83  tff(c_223361, plain, (![B_69]: (r2_hidden('#skF_9', B_69))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_223343])).
% 31.24/18.83  tff(c_223363, plain, (![B_97428]: (r2_hidden('#skF_9', B_97428))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_223343])).
% 31.24/18.83  tff(c_363, plain, (![C_108]: (k4_tarski(C_108, '#skF_7'(k1_xboole_0, k1_xboole_0, C_108))='#skF_9' | ~r2_hidden(C_108, k1_xboole_0))), inference(resolution, [status(thm)], [c_274, c_12])).
% 31.24/18.83  tff(c_286, plain, (![C_100, A_7]: (k4_tarski(C_100, '#skF_7'(k1_xboole_0, k1_xboole_0, C_100))=A_7 | ~r2_hidden(C_100, k1_xboole_0))), inference(resolution, [status(thm)], [c_274, c_12])).
% 31.24/18.83  tff(c_366, plain, (![A_7, C_108]: (A_7='#skF_9' | ~r2_hidden(C_108, k1_xboole_0) | ~r2_hidden(C_108, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_363, c_286])).
% 31.24/18.83  tff(c_945, plain, (![C_108]: (~r2_hidden(C_108, k1_xboole_0) | ~r2_hidden(C_108, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_366])).
% 31.24/18.83  tff(c_223369, plain, (~r2_hidden('#skF_9', k1_xboole_0)), inference(resolution, [status(thm)], [c_223363, c_945])).
% 31.24/18.83  tff(c_223381, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_223361, c_223369])).
% 31.24/18.83  tff(c_223398, plain, (![A_97503]: (A_97503='#skF_9')), inference(splitRight, [status(thm)], [c_366])).
% 31.24/18.83  tff(c_223522, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_223398, c_71])).
% 31.24/18.83  tff(c_223524, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_56])).
% 31.24/18.83  tff(c_223523, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_56])).
% 31.24/18.83  tff(c_223533, plain, ('#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_223524, c_223523])).
% 31.24/18.83  tff(c_223528, plain, (v1_xboole_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_223523, c_8])).
% 31.24/18.83  tff(c_223544, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_223533, c_223528])).
% 31.24/18.83  tff(c_223563, plain, (![A_98562]: (v1_relat_1(A_98562) | ~v1_xboole_0(A_98562))), inference(cnfTransformation, [status(thm)], [f_46])).
% 31.24/18.83  tff(c_223567, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_223544, c_223563])).
% 31.24/18.83  tff(c_223549, plain, (v1_funct_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_223524, c_70])).
% 31.24/18.83  tff(c_223526, plain, (k1_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_223523, c_223523, c_40])).
% 31.24/18.83  tff(c_223551, plain, (k1_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_223533, c_223533, c_223526])).
% 31.55/18.83  tff(c_223525, plain, (![A_6]: (r1_tarski('#skF_10', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_223523, c_10])).
% 31.55/18.83  tff(c_223561, plain, (![A_6]: (r1_tarski('#skF_9', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_223533, c_223525])).
% 31.55/18.83  tff(c_223527, plain, (k2_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_223523, c_223523, c_38])).
% 31.55/18.83  tff(c_223556, plain, (k2_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_223533, c_223533, c_223527])).
% 31.55/18.83  tff(c_223568, plain, (![C_98563]: (~r1_tarski(k2_relat_1(C_98563), '#skF_9') | k1_relat_1(C_98563)!='#skF_9' | ~v1_funct_1(C_98563) | ~v1_relat_1(C_98563))), inference(demodulation, [status(thm), theory('equality')], [c_223533, c_54])).
% 31.55/18.83  tff(c_223571, plain, (~r1_tarski('#skF_9', '#skF_9') | k1_relat_1('#skF_9')!='#skF_9' | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_223556, c_223568])).
% 31.55/18.83  tff(c_223574, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_223567, c_223549, c_223551, c_223561, c_223571])).
% 31.55/18.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.55/18.83  
% 31.55/18.83  Inference rules
% 31.55/18.83  ----------------------
% 31.55/18.83  #Ref     : 0
% 31.55/18.83  #Sup     : 25020
% 31.55/18.83  #Fact    : 38
% 31.55/18.83  #Define  : 0
% 31.55/18.83  #Split   : 11
% 31.55/18.83  #Chain   : 0
% 31.55/18.83  #Close   : 0
% 31.55/18.83  
% 31.55/18.83  Ordering : KBO
% 31.55/18.83  
% 31.55/18.83  Simplification rules
% 31.55/18.83  ----------------------
% 31.55/18.83  #Subsume      : 7353
% 31.55/18.83  #Demod        : 4974
% 31.55/18.83  #Tautology    : 2333
% 31.55/18.83  #SimpNegUnit  : 841
% 31.55/18.83  #BackRed      : 218
% 31.55/18.83  
% 31.55/18.83  #Partial instantiations: 64384
% 31.55/18.83  #Strategies tried      : 1
% 31.55/18.83  
% 31.55/18.83  Timing (in seconds)
% 31.55/18.83  ----------------------
% 31.55/18.83  Preprocessing        : 0.31
% 31.55/18.83  Parsing              : 0.16
% 31.55/18.83  CNF conversion       : 0.03
% 31.55/18.83  Main loop            : 17.74
% 31.55/18.83  Inferencing          : 4.31
% 31.55/18.83  Reduction            : 2.80
% 31.55/18.83  Demodulation         : 1.89
% 31.55/18.83  BG Simplification    : 0.46
% 31.55/18.83  Subsumption          : 8.94
% 31.55/18.83  Abstraction          : 0.66
% 31.55/18.83  MUC search           : 0.00
% 31.55/18.83  Cooper               : 0.00
% 31.55/18.83  Total                : 18.10
% 31.55/18.83  Index Insertion      : 0.00
% 31.55/18.83  Index Deletion       : 0.00
% 31.55/18.83  Index Matching       : 0.00
% 31.55/18.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
