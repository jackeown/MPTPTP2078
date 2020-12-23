%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:13 EST 2020

% Result     : Theorem 10.21s
% Output     : CNFRefutation 10.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 171 expanded)
%              Number of leaves         :   29 (  68 expanded)
%              Depth                    :   12
%              Number of atoms          :  158 ( 378 expanded)
%              Number of equality atoms :    2 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_80,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_66,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_76,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_85,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_40,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_42,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_4776,plain,(
    ! [A_440,B_441] :
      ( r1_tarski(A_440,B_441)
      | ~ r1_ordinal1(A_440,B_441)
      | ~ v3_ordinal1(B_441)
      | ~ v3_ordinal1(A_440) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_44,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_78,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_36,plain,(
    ! [A_35] :
      ( v3_ordinal1(k1_ordinal1(A_35))
      | ~ v3_ordinal1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_50,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_88,plain,(
    r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_50])).

tff(c_28,plain,(
    ! [A_31] : k2_xboole_0(A_31,k1_tarski(A_31)) = k1_ordinal1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_289,plain,(
    ! [A_90,B_91] :
      ( r1_tarski(A_90,B_91)
      | ~ r1_ordinal1(A_90,B_91)
      | ~ v3_ordinal1(B_91)
      | ~ v3_ordinal1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(k2_xboole_0(A_6,B_7),C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2040,plain,(
    ! [A_233,B_234,B_235] :
      ( r1_tarski(A_233,B_234)
      | ~ r1_ordinal1(k2_xboole_0(A_233,B_235),B_234)
      | ~ v3_ordinal1(B_234)
      | ~ v3_ordinal1(k2_xboole_0(A_233,B_235)) ) ),
    inference(resolution,[status(thm)],[c_289,c_8])).

tff(c_2059,plain,(
    ! [A_31,B_234] :
      ( r1_tarski(A_31,B_234)
      | ~ r1_ordinal1(k1_ordinal1(A_31),B_234)
      | ~ v3_ordinal1(B_234)
      | ~ v3_ordinal1(k2_xboole_0(A_31,k1_tarski(A_31))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2040])).

tff(c_3521,plain,(
    ! [A_344,B_345] :
      ( r1_tarski(A_344,B_345)
      | ~ r1_ordinal1(k1_ordinal1(A_344),B_345)
      | ~ v3_ordinal1(B_345)
      | ~ v3_ordinal1(k1_ordinal1(A_344)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2059])).

tff(c_3548,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_88,c_3521])).

tff(c_3559,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3548])).

tff(c_3560,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3559])).

tff(c_3563,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_3560])).

tff(c_3567,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3563])).

tff(c_3569,plain,(
    v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_3559])).

tff(c_34,plain,(
    ! [A_34] : r2_hidden(A_34,k1_ordinal1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_207,plain,(
    ! [C_76,B_77,A_78] :
      ( r2_hidden(C_76,B_77)
      | ~ r2_hidden(C_76,A_78)
      | ~ r1_tarski(A_78,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_222,plain,(
    ! [A_34,B_77] :
      ( r2_hidden(A_34,B_77)
      | ~ r1_tarski(k1_ordinal1(A_34),B_77) ) ),
    inference(resolution,[status(thm)],[c_34,c_207])).

tff(c_4356,plain,(
    ! [A_382,B_383] :
      ( r2_hidden(A_382,B_383)
      | ~ r1_ordinal1(k1_ordinal1(A_382),B_383)
      | ~ v3_ordinal1(B_383)
      | ~ v3_ordinal1(k1_ordinal1(A_382)) ) ),
    inference(resolution,[status(thm)],[c_289,c_222])).

tff(c_4383,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_88,c_4356])).

tff(c_4394,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3569,c_40,c_4383])).

tff(c_4396,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4394])).

tff(c_4398,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_38,plain,(
    ! [B_37,A_36] :
      ( ~ r1_tarski(B_37,A_36)
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4402,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_4398,c_38])).

tff(c_4826,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4776,c_4402])).

tff(c_4854,plain,(
    ~ r1_ordinal1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_4826])).

tff(c_26,plain,(
    ! [B_30,A_29] :
      ( r1_ordinal1(B_30,A_29)
      | r1_ordinal1(A_29,B_30)
      | ~ v3_ordinal1(B_30)
      | ~ v3_ordinal1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | ~ r1_ordinal1(A_32,B_33)
      | ~ v3_ordinal1(B_33)
      | ~ v3_ordinal1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4999,plain,(
    ! [B_456,A_457] :
      ( r1_ordinal1(B_456,A_457)
      | r1_ordinal1(A_457,B_456)
      | ~ v3_ordinal1(B_456)
      | ~ v3_ordinal1(A_457) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4397,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_5003,plain,
    ( r1_ordinal1('#skF_3',k1_ordinal1('#skF_2'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_2'))
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4999,c_4397])).

tff(c_5010,plain,
    ( r1_ordinal1('#skF_3',k1_ordinal1('#skF_2'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5003])).

tff(c_5014,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_5010])).

tff(c_5017,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_5014])).

tff(c_5021,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_5017])).

tff(c_5023,plain,(
    v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_5010])).

tff(c_24,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(k1_tarski(A_27),B_28)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_5225,plain,(
    ! [A_483,C_484,B_485] :
      ( r1_tarski(k2_xboole_0(A_483,C_484),B_485)
      | ~ r1_tarski(C_484,B_485)
      | ~ r1_tarski(A_483,B_485) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_30,plain,(
    ! [A_32,B_33] :
      ( r1_ordinal1(A_32,B_33)
      | ~ r1_tarski(A_32,B_33)
      | ~ v3_ordinal1(B_33)
      | ~ v3_ordinal1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6729,plain,(
    ! [A_598,C_599,B_600] :
      ( r1_ordinal1(k2_xboole_0(A_598,C_599),B_600)
      | ~ v3_ordinal1(B_600)
      | ~ v3_ordinal1(k2_xboole_0(A_598,C_599))
      | ~ r1_tarski(C_599,B_600)
      | ~ r1_tarski(A_598,B_600) ) ),
    inference(resolution,[status(thm)],[c_5225,c_30])).

tff(c_6742,plain,(
    ! [A_31,B_600] :
      ( r1_ordinal1(k1_ordinal1(A_31),B_600)
      | ~ v3_ordinal1(B_600)
      | ~ v3_ordinal1(k2_xboole_0(A_31,k1_tarski(A_31)))
      | ~ r1_tarski(k1_tarski(A_31),B_600)
      | ~ r1_tarski(A_31,B_600) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_6729])).

tff(c_10386,plain,(
    ! [A_805,B_806] :
      ( r1_ordinal1(k1_ordinal1(A_805),B_806)
      | ~ v3_ordinal1(B_806)
      | ~ v3_ordinal1(k1_ordinal1(A_805))
      | ~ r1_tarski(k1_tarski(A_805),B_806)
      | ~ r1_tarski(A_805,B_806) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6742])).

tff(c_17885,plain,(
    ! [A_1117,B_1118] :
      ( r1_ordinal1(k1_ordinal1(A_1117),B_1118)
      | ~ v3_ordinal1(B_1118)
      | ~ v3_ordinal1(k1_ordinal1(A_1117))
      | ~ r1_tarski(A_1117,B_1118)
      | ~ r2_hidden(A_1117,B_1118) ) ),
    inference(resolution,[status(thm)],[c_24,c_10386])).

tff(c_17919,plain,
    ( ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_3')
    | ~ r2_hidden('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_17885,c_4397])).

tff(c_17943,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4398,c_5023,c_40,c_17919])).

tff(c_17946,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_17943])).

tff(c_17949,plain,(
    ~ r1_ordinal1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_17946])).

tff(c_17955,plain,
    ( r1_ordinal1('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_17949])).

tff(c_17964,plain,(
    r1_ordinal1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_17955])).

tff(c_17966,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4854,c_17964])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:19:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.21/3.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.21/3.98  
% 10.21/3.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.21/3.98  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_3 > #skF_1
% 10.21/3.98  
% 10.21/3.98  %Foreground sorts:
% 10.21/3.98  
% 10.21/3.98  
% 10.21/3.98  %Background operators:
% 10.21/3.98  
% 10.21/3.98  
% 10.21/3.98  %Foreground operators:
% 10.21/3.98  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 10.21/3.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.21/3.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.21/3.98  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.21/3.98  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.21/3.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.21/3.98  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.21/3.98  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 10.21/3.98  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.21/3.98  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.21/3.98  tff('#skF_2', type, '#skF_2': $i).
% 10.21/3.98  tff('#skF_3', type, '#skF_3': $i).
% 10.21/3.98  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 10.21/3.98  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.21/3.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.21/3.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.21/3.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.21/3.98  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.21/3.98  
% 10.21/4.00  tff(f_95, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 10.21/4.00  tff(f_74, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 10.21/4.00  tff(f_80, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 10.21/4.00  tff(f_66, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 10.21/4.00  tff(f_36, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 10.21/4.00  tff(f_76, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 10.21/4.00  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 10.21/4.00  tff(f_85, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 10.21/4.00  tff(f_64, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 10.21/4.00  tff(f_56, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 10.21/4.00  tff(f_42, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 10.21/4.00  tff(c_40, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.21/4.00  tff(c_42, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.21/4.00  tff(c_4776, plain, (![A_440, B_441]: (r1_tarski(A_440, B_441) | ~r1_ordinal1(A_440, B_441) | ~v3_ordinal1(B_441) | ~v3_ordinal1(A_440))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.21/4.00  tff(c_44, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3') | ~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.21/4.00  tff(c_78, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 10.21/4.00  tff(c_36, plain, (![A_35]: (v3_ordinal1(k1_ordinal1(A_35)) | ~v3_ordinal1(A_35))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.21/4.00  tff(c_50, plain, (r2_hidden('#skF_2', '#skF_3') | r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.21/4.00  tff(c_88, plain, (r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_78, c_50])).
% 10.21/4.00  tff(c_28, plain, (![A_31]: (k2_xboole_0(A_31, k1_tarski(A_31))=k1_ordinal1(A_31))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.21/4.00  tff(c_289, plain, (![A_90, B_91]: (r1_tarski(A_90, B_91) | ~r1_ordinal1(A_90, B_91) | ~v3_ordinal1(B_91) | ~v3_ordinal1(A_90))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.21/4.00  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(k2_xboole_0(A_6, B_7), C_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.21/4.00  tff(c_2040, plain, (![A_233, B_234, B_235]: (r1_tarski(A_233, B_234) | ~r1_ordinal1(k2_xboole_0(A_233, B_235), B_234) | ~v3_ordinal1(B_234) | ~v3_ordinal1(k2_xboole_0(A_233, B_235)))), inference(resolution, [status(thm)], [c_289, c_8])).
% 10.21/4.00  tff(c_2059, plain, (![A_31, B_234]: (r1_tarski(A_31, B_234) | ~r1_ordinal1(k1_ordinal1(A_31), B_234) | ~v3_ordinal1(B_234) | ~v3_ordinal1(k2_xboole_0(A_31, k1_tarski(A_31))))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2040])).
% 10.21/4.00  tff(c_3521, plain, (![A_344, B_345]: (r1_tarski(A_344, B_345) | ~r1_ordinal1(k1_ordinal1(A_344), B_345) | ~v3_ordinal1(B_345) | ~v3_ordinal1(k1_ordinal1(A_344)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2059])).
% 10.21/4.00  tff(c_3548, plain, (r1_tarski('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_88, c_3521])).
% 10.21/4.00  tff(c_3559, plain, (r1_tarski('#skF_2', '#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_3548])).
% 10.21/4.00  tff(c_3560, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_3559])).
% 10.21/4.00  tff(c_3563, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_3560])).
% 10.21/4.00  tff(c_3567, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_3563])).
% 10.21/4.00  tff(c_3569, plain, (v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitRight, [status(thm)], [c_3559])).
% 10.21/4.00  tff(c_34, plain, (![A_34]: (r2_hidden(A_34, k1_ordinal1(A_34)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.21/4.00  tff(c_207, plain, (![C_76, B_77, A_78]: (r2_hidden(C_76, B_77) | ~r2_hidden(C_76, A_78) | ~r1_tarski(A_78, B_77))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.21/4.00  tff(c_222, plain, (![A_34, B_77]: (r2_hidden(A_34, B_77) | ~r1_tarski(k1_ordinal1(A_34), B_77))), inference(resolution, [status(thm)], [c_34, c_207])).
% 10.21/4.00  tff(c_4356, plain, (![A_382, B_383]: (r2_hidden(A_382, B_383) | ~r1_ordinal1(k1_ordinal1(A_382), B_383) | ~v3_ordinal1(B_383) | ~v3_ordinal1(k1_ordinal1(A_382)))), inference(resolution, [status(thm)], [c_289, c_222])).
% 10.21/4.00  tff(c_4383, plain, (r2_hidden('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_88, c_4356])).
% 10.21/4.00  tff(c_4394, plain, (r2_hidden('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3569, c_40, c_4383])).
% 10.21/4.00  tff(c_4396, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_4394])).
% 10.21/4.00  tff(c_4398, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 10.21/4.00  tff(c_38, plain, (![B_37, A_36]: (~r1_tarski(B_37, A_36) | ~r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.21/4.00  tff(c_4402, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_4398, c_38])).
% 10.21/4.00  tff(c_4826, plain, (~r1_ordinal1('#skF_3', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_4776, c_4402])).
% 10.21/4.00  tff(c_4854, plain, (~r1_ordinal1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_4826])).
% 10.21/4.00  tff(c_26, plain, (![B_30, A_29]: (r1_ordinal1(B_30, A_29) | r1_ordinal1(A_29, B_30) | ~v3_ordinal1(B_30) | ~v3_ordinal1(A_29))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.21/4.00  tff(c_32, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | ~r1_ordinal1(A_32, B_33) | ~v3_ordinal1(B_33) | ~v3_ordinal1(A_32))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.21/4.00  tff(c_4999, plain, (![B_456, A_457]: (r1_ordinal1(B_456, A_457) | r1_ordinal1(A_457, B_456) | ~v3_ordinal1(B_456) | ~v3_ordinal1(A_457))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.21/4.00  tff(c_4397, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 10.21/4.00  tff(c_5003, plain, (r1_ordinal1('#skF_3', k1_ordinal1('#skF_2')) | ~v3_ordinal1(k1_ordinal1('#skF_2')) | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_4999, c_4397])).
% 10.21/4.00  tff(c_5010, plain, (r1_ordinal1('#skF_3', k1_ordinal1('#skF_2')) | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_5003])).
% 10.21/4.00  tff(c_5014, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_5010])).
% 10.21/4.00  tff(c_5017, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_5014])).
% 10.21/4.00  tff(c_5021, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_5017])).
% 10.21/4.00  tff(c_5023, plain, (v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitRight, [status(thm)], [c_5010])).
% 10.21/4.00  tff(c_24, plain, (![A_27, B_28]: (r1_tarski(k1_tarski(A_27), B_28) | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.21/4.00  tff(c_5225, plain, (![A_483, C_484, B_485]: (r1_tarski(k2_xboole_0(A_483, C_484), B_485) | ~r1_tarski(C_484, B_485) | ~r1_tarski(A_483, B_485))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.21/4.00  tff(c_30, plain, (![A_32, B_33]: (r1_ordinal1(A_32, B_33) | ~r1_tarski(A_32, B_33) | ~v3_ordinal1(B_33) | ~v3_ordinal1(A_32))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.21/4.00  tff(c_6729, plain, (![A_598, C_599, B_600]: (r1_ordinal1(k2_xboole_0(A_598, C_599), B_600) | ~v3_ordinal1(B_600) | ~v3_ordinal1(k2_xboole_0(A_598, C_599)) | ~r1_tarski(C_599, B_600) | ~r1_tarski(A_598, B_600))), inference(resolution, [status(thm)], [c_5225, c_30])).
% 10.21/4.00  tff(c_6742, plain, (![A_31, B_600]: (r1_ordinal1(k1_ordinal1(A_31), B_600) | ~v3_ordinal1(B_600) | ~v3_ordinal1(k2_xboole_0(A_31, k1_tarski(A_31))) | ~r1_tarski(k1_tarski(A_31), B_600) | ~r1_tarski(A_31, B_600))), inference(superposition, [status(thm), theory('equality')], [c_28, c_6729])).
% 10.21/4.00  tff(c_10386, plain, (![A_805, B_806]: (r1_ordinal1(k1_ordinal1(A_805), B_806) | ~v3_ordinal1(B_806) | ~v3_ordinal1(k1_ordinal1(A_805)) | ~r1_tarski(k1_tarski(A_805), B_806) | ~r1_tarski(A_805, B_806))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_6742])).
% 10.21/4.00  tff(c_17885, plain, (![A_1117, B_1118]: (r1_ordinal1(k1_ordinal1(A_1117), B_1118) | ~v3_ordinal1(B_1118) | ~v3_ordinal1(k1_ordinal1(A_1117)) | ~r1_tarski(A_1117, B_1118) | ~r2_hidden(A_1117, B_1118))), inference(resolution, [status(thm)], [c_24, c_10386])).
% 10.21/4.00  tff(c_17919, plain, (~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2')) | ~r1_tarski('#skF_2', '#skF_3') | ~r2_hidden('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_17885, c_4397])).
% 10.21/4.00  tff(c_17943, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4398, c_5023, c_40, c_17919])).
% 10.21/4.00  tff(c_17946, plain, (~r1_ordinal1('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_17943])).
% 10.21/4.00  tff(c_17949, plain, (~r1_ordinal1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_17946])).
% 10.21/4.00  tff(c_17955, plain, (r1_ordinal1('#skF_3', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_17949])).
% 10.21/4.00  tff(c_17964, plain, (r1_ordinal1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_17955])).
% 10.21/4.00  tff(c_17966, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4854, c_17964])).
% 10.21/4.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.21/4.00  
% 10.21/4.00  Inference rules
% 10.21/4.00  ----------------------
% 10.21/4.00  #Ref     : 0
% 10.21/4.00  #Sup     : 3685
% 10.21/4.00  #Fact    : 6
% 10.21/4.00  #Define  : 0
% 10.21/4.00  #Split   : 18
% 10.21/4.00  #Chain   : 0
% 10.21/4.00  #Close   : 0
% 10.21/4.00  
% 10.21/4.00  Ordering : KBO
% 10.21/4.00  
% 10.21/4.00  Simplification rules
% 10.21/4.00  ----------------------
% 10.21/4.00  #Subsume      : 596
% 10.21/4.00  #Demod        : 596
% 10.21/4.00  #Tautology    : 497
% 10.21/4.00  #SimpNegUnit  : 4
% 10.21/4.00  #BackRed      : 0
% 10.21/4.00  
% 10.21/4.00  #Partial instantiations: 0
% 10.21/4.00  #Strategies tried      : 1
% 10.21/4.00  
% 10.21/4.00  Timing (in seconds)
% 10.21/4.00  ----------------------
% 10.21/4.00  Preprocessing        : 0.31
% 10.21/4.00  Parsing              : 0.16
% 10.21/4.00  CNF conversion       : 0.02
% 10.21/4.00  Main loop            : 2.93
% 10.21/4.00  Inferencing          : 0.76
% 10.21/4.00  Reduction            : 1.08
% 10.21/4.00  Demodulation         : 0.77
% 10.21/4.00  BG Simplification    : 0.07
% 10.21/4.00  Subsumption          : 0.83
% 10.21/4.00  Abstraction          : 0.08
% 10.21/4.00  MUC search           : 0.00
% 10.21/4.00  Cooper               : 0.00
% 10.21/4.00  Total                : 3.27
% 10.21/4.00  Index Insertion      : 0.00
% 10.21/4.01  Index Deletion       : 0.00
% 10.21/4.01  Index Matching       : 0.00
% 10.21/4.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
