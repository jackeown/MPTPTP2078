%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0003+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:33 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 156 expanded)
%              Number of leaves         :   23 (  61 expanded)
%              Depth                    :    9
%              Number of atoms          :  130 ( 321 expanded)
%              Number of equality atoms :   17 (  38 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k3_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ ( ~ r1_xboole_0(A,B)
            & ! [C] :
                ~ ( r2_hidden(C,A)
                  & r2_hidden(C,B) ) )
        & ~ ( ? [C] :
                ( r2_hidden(C,A)
                & r2_hidden(C,B) )
            & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_44,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(c_640,plain,(
    ! [A_66,B_67] :
      ( r1_xboole_0(A_66,B_67)
      | k3_xboole_0(A_66,B_67) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_40,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | ~ r1_xboole_0('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_59,plain,(
    ~ r1_xboole_0('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_644,plain,(
    k3_xboole_0('#skF_7','#skF_8') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_640,c_59])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_650,plain,(
    ! [D_70,B_71,A_72] :
      ( r2_hidden(D_70,B_71)
      | ~ r2_hidden(D_70,k3_xboole_0(A_72,B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_891,plain,(
    ! [A_105,B_106] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_105,B_106)),B_106)
      | v1_xboole_0(k3_xboole_0(A_105,B_106)) ) ),
    inference(resolution,[status(thm)],[c_4,c_650])).

tff(c_656,plain,(
    ! [D_73,A_74,B_75] :
      ( r2_hidden(D_73,A_74)
      | ~ r2_hidden(D_73,k3_xboole_0(A_74,B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_670,plain,(
    ! [A_77,B_78] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_77,B_78)),A_77)
      | v1_xboole_0(k3_xboole_0(A_77,B_78)) ) ),
    inference(resolution,[status(thm)],[c_4,c_656])).

tff(c_36,plain,(
    ! [C_16] :
      ( r2_hidden('#skF_6','#skF_4')
      | ~ r2_hidden(C_16,'#skF_8')
      | ~ r2_hidden(C_16,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_662,plain,(
    ! [C_16] :
      ( ~ r2_hidden(C_16,'#skF_8')
      | ~ r2_hidden(C_16,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_686,plain,(
    ! [B_78] :
      ( ~ r2_hidden('#skF_1'(k3_xboole_0('#skF_7',B_78)),'#skF_8')
      | v1_xboole_0(k3_xboole_0('#skF_7',B_78)) ) ),
    inference(resolution,[status(thm)],[c_670,c_662])).

tff(c_933,plain,(
    v1_xboole_0(k3_xboole_0('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_891,c_686])).

tff(c_30,plain,(
    ! [A_13] :
      ( k1_xboole_0 = A_13
      | ~ v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_960,plain,(
    k3_xboole_0('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_933,c_30])).

tff(c_966,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_644,c_960])).

tff(c_967,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_74,plain,(
    ! [A_24,B_25] :
      ( r1_xboole_0(A_24,B_25)
      | k3_xboole_0(A_24,B_25) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_82,plain,(
    k3_xboole_0('#skF_7','#skF_8') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_74,c_59])).

tff(c_83,plain,(
    ! [D_26,B_27,A_28] :
      ( r2_hidden(D_26,B_27)
      | ~ r2_hidden(D_26,k3_xboole_0(A_28,B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_88,plain,(
    ! [A_28,B_27] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_28,B_27)),B_27)
      | v1_xboole_0(k3_xboole_0(A_28,B_27)) ) ),
    inference(resolution,[status(thm)],[c_4,c_83])).

tff(c_89,plain,(
    ! [D_29,A_30,B_31] :
      ( r2_hidden(D_29,A_30)
      | ~ r2_hidden(D_29,k3_xboole_0(A_30,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_214,plain,(
    ! [A_47,B_48] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_47,B_48)),A_47)
      | v1_xboole_0(k3_xboole_0(A_47,B_48)) ) ),
    inference(resolution,[status(thm)],[c_4,c_89])).

tff(c_34,plain,(
    ! [C_16] :
      ( r2_hidden('#skF_6','#skF_5')
      | ~ r2_hidden(C_16,'#skF_8')
      | ~ r2_hidden(C_16,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_60,plain,(
    ! [C_16] :
      ( ~ r2_hidden(C_16,'#skF_8')
      | ~ r2_hidden(C_16,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_598,plain,(
    ! [B_64] :
      ( ~ r2_hidden('#skF_1'(k3_xboole_0('#skF_7',B_64)),'#skF_8')
      | v1_xboole_0(k3_xboole_0('#skF_7',B_64)) ) ),
    inference(resolution,[status(thm)],[c_214,c_60])).

tff(c_616,plain,(
    v1_xboole_0(k3_xboole_0('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_88,c_598])).

tff(c_623,plain,(
    k3_xboole_0('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_616,c_30])).

tff(c_629,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_623])).

tff(c_630,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_28,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_43,plain,(
    ! [A_17] :
      ( k1_xboole_0 = A_17
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_47,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_43])).

tff(c_48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_28])).

tff(c_1258,plain,(
    ! [A_140,B_141] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_140,B_141)),B_141)
      | v1_xboole_0(k3_xboole_0(A_140,B_141)) ) ),
    inference(resolution,[status(thm)],[c_4,c_650])).

tff(c_1030,plain,(
    ! [A_118,B_119] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_118,B_119)),A_118)
      | v1_xboole_0(k3_xboole_0(A_118,B_119)) ) ),
    inference(resolution,[status(thm)],[c_4,c_656])).

tff(c_32,plain,(
    ! [C_16] :
      ( r1_xboole_0('#skF_4','#skF_5')
      | ~ r2_hidden(C_16,'#skF_8')
      | ~ r2_hidden(C_16,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_972,plain,(
    ! [C_16] :
      ( ~ r2_hidden(C_16,'#skF_8')
      | ~ r2_hidden(C_16,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_1046,plain,(
    ! [B_119] :
      ( ~ r2_hidden('#skF_1'(k3_xboole_0('#skF_7',B_119)),'#skF_8')
      | v1_xboole_0(k3_xboole_0('#skF_7',B_119)) ) ),
    inference(resolution,[status(thm)],[c_1030,c_972])).

tff(c_1298,plain,(
    v1_xboole_0(k3_xboole_0('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_1258,c_1046])).

tff(c_1312,plain,(
    k3_xboole_0('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1298,c_30])).

tff(c_1318,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_644,c_1312])).

tff(c_1319,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = k1_xboole_0
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1323,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1319,c_24])).

tff(c_1348,plain,(
    ! [D_144,A_145,B_146] :
      ( r2_hidden(D_144,k3_xboole_0(A_145,B_146))
      | ~ r2_hidden(D_144,B_146)
      | ~ r2_hidden(D_144,A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1364,plain,(
    ! [D_147] :
      ( r2_hidden(D_147,k1_xboole_0)
      | ~ r2_hidden(D_147,'#skF_5')
      | ~ r2_hidden(D_147,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1323,c_1348])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1373,plain,(
    ! [D_147] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(D_147,'#skF_5')
      | ~ r2_hidden(D_147,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1364,c_2])).

tff(c_1379,plain,(
    ! [D_148] :
      ( ~ r2_hidden(D_148,'#skF_5')
      | ~ r2_hidden(D_148,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1373])).

tff(c_1386,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_630,c_1379])).

tff(c_1393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_967,c_1386])).

tff(c_1395,plain,(
    r1_xboole_0('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_42,plain,
    ( r2_hidden('#skF_6','#skF_4')
    | ~ r1_xboole_0('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1401,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1395,c_42])).

tff(c_1394,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,
    ( r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1407,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1395,c_38])).

tff(c_1415,plain,(
    ! [A_152,B_153] :
      ( k3_xboole_0(A_152,B_153) = k1_xboole_0
      | ~ r1_xboole_0(A_152,B_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1426,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1407,c_1415])).

tff(c_1553,plain,(
    ! [D_170,A_171,B_172] :
      ( r2_hidden(D_170,k3_xboole_0(A_171,B_172))
      | ~ r2_hidden(D_170,B_172)
      | ~ r2_hidden(D_170,A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1676,plain,(
    ! [D_181] :
      ( r2_hidden(D_181,k1_xboole_0)
      | ~ r2_hidden(D_181,'#skF_5')
      | ~ r2_hidden(D_181,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1426,c_1553])).

tff(c_1681,plain,(
    ! [D_181] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(D_181,'#skF_5')
      | ~ r2_hidden(D_181,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1676,c_2])).

tff(c_1686,plain,(
    ! [D_182] :
      ( ~ r2_hidden(D_182,'#skF_5')
      | ~ r2_hidden(D_182,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1681])).

tff(c_1697,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_1394,c_1686])).

tff(c_1705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1401,c_1697])).

%------------------------------------------------------------------------------
