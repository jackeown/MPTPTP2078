%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:12 EST 2020

% Result     : Theorem 16.26s
% Output     : CNFRefutation 16.26s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 239 expanded)
%              Number of leaves         :   31 (  92 expanded)
%              Depth                    :   13
%              Number of atoms          :  174 ( 564 expanded)
%              Number of equality atoms :   17 (  35 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_108,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_95,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_113,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_104,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_64,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_66,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_27846,plain,(
    ! [A_1393,B_1394] :
      ( r1_tarski(A_1393,B_1394)
      | ~ r1_ordinal1(A_1393,B_1394)
      | ~ v3_ordinal1(B_1394)
      | ~ v3_ordinal1(A_1393) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_60,plain,(
    ! [A_52] :
      ( v3_ordinal1(k1_ordinal1(A_52))
      | ~ v3_ordinal1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_68,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4')
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_103,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_74,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_133,plain,(
    r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_74])).

tff(c_48,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ r1_ordinal1(A_42,B_43)
      | ~ v3_ordinal1(B_43)
      | ~ v3_ordinal1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_594,plain,(
    ! [A_124,B_125] :
      ( r1_tarski(A_124,B_125)
      | ~ r1_ordinal1(A_124,B_125)
      | ~ v3_ordinal1(B_125)
      | ~ v3_ordinal1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3952,plain,(
    ! [B_293,A_294] :
      ( B_293 = A_294
      | ~ r1_tarski(B_293,A_294)
      | ~ r1_ordinal1(A_294,B_293)
      | ~ v3_ordinal1(B_293)
      | ~ v3_ordinal1(A_294) ) ),
    inference(resolution,[status(thm)],[c_594,c_20])).

tff(c_23566,plain,(
    ! [B_1170,A_1171] :
      ( B_1170 = A_1171
      | ~ r1_ordinal1(B_1170,A_1171)
      | ~ r1_ordinal1(A_1171,B_1170)
      | ~ v3_ordinal1(B_1170)
      | ~ v3_ordinal1(A_1171) ) ),
    inference(resolution,[status(thm)],[c_48,c_3952])).

tff(c_23592,plain,
    ( k1_ordinal1('#skF_3') = '#skF_4'
    | ~ r1_ordinal1('#skF_4',k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_133,c_23566])).

tff(c_23610,plain,
    ( k1_ordinal1('#skF_3') = '#skF_4'
    | ~ r1_ordinal1('#skF_4',k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_23592])).

tff(c_23611,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_23610])).

tff(c_23614,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_23611])).

tff(c_23618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_23614])).

tff(c_23620,plain,(
    v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_23610])).

tff(c_1073,plain,(
    ! [B_161,A_162] :
      ( r2_hidden(B_161,A_162)
      | B_161 = A_162
      | r2_hidden(A_162,B_161)
      | ~ v3_ordinal1(B_161)
      | ~ v3_ordinal1(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1209,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1073,c_103])).

tff(c_1389,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_1209])).

tff(c_1430,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1389])).

tff(c_134,plain,(
    ! [A_67,B_68] :
      ( ~ r2_hidden(A_67,B_68)
      | r2_hidden(A_67,k1_ordinal1(B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_62,plain,(
    ! [B_54,A_53] :
      ( ~ r1_tarski(B_54,A_53)
      | ~ r2_hidden(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_138,plain,(
    ! [B_68,A_67] :
      ( ~ r1_tarski(k1_ordinal1(B_68),A_67)
      | ~ r2_hidden(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_134,c_62])).

tff(c_23732,plain,(
    ! [B_1180,B_1181] :
      ( ~ r2_hidden(B_1180,B_1181)
      | ~ r1_ordinal1(k1_ordinal1(B_1181),B_1180)
      | ~ v3_ordinal1(B_1180)
      | ~ v3_ordinal1(k1_ordinal1(B_1181)) ) ),
    inference(resolution,[status(thm)],[c_594,c_138])).

tff(c_23770,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_133,c_23732])).

tff(c_23783,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23620,c_64,c_1430,c_23770])).

tff(c_23784,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1389])).

tff(c_23787,plain,(
    r1_ordinal1(k1_ordinal1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23784,c_133])).

tff(c_52,plain,(
    ! [B_45] : r2_hidden(B_45,k1_ordinal1(B_45)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_97,plain,(
    ! [B_61,A_62] :
      ( ~ r1_tarski(B_61,A_62)
      | ~ r2_hidden(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_101,plain,(
    ! [B_45] : ~ r1_tarski(k1_ordinal1(B_45),B_45) ),
    inference(resolution,[status(thm)],[c_52,c_97])).

tff(c_27446,plain,(
    ! [B_1344] :
      ( ~ r1_ordinal1(k1_ordinal1(B_1344),B_1344)
      | ~ v3_ordinal1(B_1344)
      | ~ v3_ordinal1(k1_ordinal1(B_1344)) ) ),
    inference(resolution,[status(thm)],[c_594,c_101])).

tff(c_27453,plain,
    ( ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_23787,c_27446])).

tff(c_27466,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_27453])).

tff(c_27471,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_27466])).

tff(c_27475,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_27471])).

tff(c_27477,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_27481,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_27477,c_62])).

tff(c_27859,plain,
    ( ~ r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_27846,c_27481])).

tff(c_27869,plain,(
    ~ r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_27859])).

tff(c_42,plain,(
    ! [B_40,A_39] :
      ( r1_ordinal1(B_40,A_39)
      | r1_ordinal1(A_39,B_40)
      | ~ v3_ordinal1(B_40)
      | ~ v3_ordinal1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28006,plain,(
    ! [B_1407,A_1408] :
      ( r1_ordinal1(B_1407,A_1408)
      | r1_ordinal1(A_1408,B_1407)
      | ~ v3_ordinal1(B_1407)
      | ~ v3_ordinal1(A_1408) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_27476,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_28010,plain,
    ( r1_ordinal1('#skF_4',k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28006,c_27476])).

tff(c_28017,plain,
    ( r1_ordinal1('#skF_4',k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_28010])).

tff(c_28021,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_28017])).

tff(c_28024,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_28021])).

tff(c_28028,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_28024])).

tff(c_28030,plain,(
    v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_28017])).

tff(c_28113,plain,(
    ! [B_1416,A_1417] :
      ( r2_hidden(B_1416,A_1417)
      | r1_ordinal1(A_1417,B_1416)
      | ~ v3_ordinal1(B_1416)
      | ~ v3_ordinal1(A_1417) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_50,plain,(
    ! [B_45,A_44] :
      ( B_45 = A_44
      | r2_hidden(A_44,B_45)
      | ~ r2_hidden(A_44,k1_ordinal1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_32099,plain,(
    ! [B_1594,B_1593] :
      ( B_1594 = B_1593
      | r2_hidden(B_1594,B_1593)
      | r1_ordinal1(k1_ordinal1(B_1593),B_1594)
      | ~ v3_ordinal1(B_1594)
      | ~ v3_ordinal1(k1_ordinal1(B_1593)) ) ),
    inference(resolution,[status(thm)],[c_28113,c_50])).

tff(c_32102,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_32099,c_27476])).

tff(c_32105,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28030,c_64,c_32102])).

tff(c_32106,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_32105])).

tff(c_32110,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_32106,c_62])).

tff(c_32113,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_32110])).

tff(c_32116,plain,(
    ~ r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_32113])).

tff(c_32119,plain,
    ( r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_32116])).

tff(c_32125,plain,(
    r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_32119])).

tff(c_32127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27869,c_32125])).

tff(c_32128,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_32105])).

tff(c_32134,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32128,c_27481])).

tff(c_32139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_32134])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:26:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.26/6.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.26/6.78  
% 16.26/6.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.26/6.78  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 16.26/6.78  
% 16.26/6.78  %Foreground sorts:
% 16.26/6.78  
% 16.26/6.78  
% 16.26/6.78  %Background operators:
% 16.26/6.78  
% 16.26/6.78  
% 16.26/6.78  %Foreground operators:
% 16.26/6.78  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 16.26/6.78  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 16.26/6.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.26/6.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.26/6.78  tff(k1_tarski, type, k1_tarski: $i > $i).
% 16.26/6.78  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 16.26/6.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.26/6.78  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 16.26/6.78  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 16.26/6.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.26/6.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 16.26/6.78  tff('#skF_3', type, '#skF_3': $i).
% 16.26/6.78  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 16.26/6.78  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 16.26/6.78  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 16.26/6.78  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 16.26/6.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.26/6.78  tff(k3_tarski, type, k3_tarski: $i > $i).
% 16.26/6.78  tff('#skF_4', type, '#skF_4': $i).
% 16.26/6.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.26/6.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.26/6.78  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 16.26/6.78  
% 16.26/6.80  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.26/6.80  tff(f_123, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 16.26/6.80  tff(f_74, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 16.26/6.80  tff(f_108, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 16.26/6.80  tff(f_95, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 16.26/6.80  tff(f_80, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 16.26/6.80  tff(f_113, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 16.26/6.80  tff(f_64, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 16.26/6.80  tff(f_104, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 16.26/6.80  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 16.26/6.80  tff(c_64, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 16.26/6.80  tff(c_66, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 16.26/6.80  tff(c_27846, plain, (![A_1393, B_1394]: (r1_tarski(A_1393, B_1394) | ~r1_ordinal1(A_1393, B_1394) | ~v3_ordinal1(B_1394) | ~v3_ordinal1(A_1393))), inference(cnfTransformation, [status(thm)], [f_74])).
% 16.26/6.80  tff(c_60, plain, (![A_52]: (v3_ordinal1(k1_ordinal1(A_52)) | ~v3_ordinal1(A_52))), inference(cnfTransformation, [status(thm)], [f_108])).
% 16.26/6.80  tff(c_68, plain, (~r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4') | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 16.26/6.80  tff(c_103, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_68])).
% 16.26/6.80  tff(c_74, plain, (r2_hidden('#skF_3', '#skF_4') | r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 16.26/6.80  tff(c_133, plain, (r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_103, c_74])).
% 16.26/6.80  tff(c_48, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~r1_ordinal1(A_42, B_43) | ~v3_ordinal1(B_43) | ~v3_ordinal1(A_42))), inference(cnfTransformation, [status(thm)], [f_74])).
% 16.26/6.80  tff(c_594, plain, (![A_124, B_125]: (r1_tarski(A_124, B_125) | ~r1_ordinal1(A_124, B_125) | ~v3_ordinal1(B_125) | ~v3_ordinal1(A_124))), inference(cnfTransformation, [status(thm)], [f_74])).
% 16.26/6.80  tff(c_20, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 16.26/6.80  tff(c_3952, plain, (![B_293, A_294]: (B_293=A_294 | ~r1_tarski(B_293, A_294) | ~r1_ordinal1(A_294, B_293) | ~v3_ordinal1(B_293) | ~v3_ordinal1(A_294))), inference(resolution, [status(thm)], [c_594, c_20])).
% 16.26/6.80  tff(c_23566, plain, (![B_1170, A_1171]: (B_1170=A_1171 | ~r1_ordinal1(B_1170, A_1171) | ~r1_ordinal1(A_1171, B_1170) | ~v3_ordinal1(B_1170) | ~v3_ordinal1(A_1171))), inference(resolution, [status(thm)], [c_48, c_3952])).
% 16.26/6.80  tff(c_23592, plain, (k1_ordinal1('#skF_3')='#skF_4' | ~r1_ordinal1('#skF_4', k1_ordinal1('#skF_3')) | ~v3_ordinal1(k1_ordinal1('#skF_3')) | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_133, c_23566])).
% 16.26/6.80  tff(c_23610, plain, (k1_ordinal1('#skF_3')='#skF_4' | ~r1_ordinal1('#skF_4', k1_ordinal1('#skF_3')) | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_23592])).
% 16.26/6.80  tff(c_23611, plain, (~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(splitLeft, [status(thm)], [c_23610])).
% 16.26/6.80  tff(c_23614, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_23611])).
% 16.26/6.80  tff(c_23618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_23614])).
% 16.26/6.80  tff(c_23620, plain, (v3_ordinal1(k1_ordinal1('#skF_3'))), inference(splitRight, [status(thm)], [c_23610])).
% 16.26/6.80  tff(c_1073, plain, (![B_161, A_162]: (r2_hidden(B_161, A_162) | B_161=A_162 | r2_hidden(A_162, B_161) | ~v3_ordinal1(B_161) | ~v3_ordinal1(A_162))), inference(cnfTransformation, [status(thm)], [f_95])).
% 16.26/6.80  tff(c_1209, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_1073, c_103])).
% 16.26/6.80  tff(c_1389, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_66, c_1209])).
% 16.26/6.80  tff(c_1430, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_1389])).
% 16.26/6.80  tff(c_134, plain, (![A_67, B_68]: (~r2_hidden(A_67, B_68) | r2_hidden(A_67, k1_ordinal1(B_68)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 16.26/6.80  tff(c_62, plain, (![B_54, A_53]: (~r1_tarski(B_54, A_53) | ~r2_hidden(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_113])).
% 16.26/6.80  tff(c_138, plain, (![B_68, A_67]: (~r1_tarski(k1_ordinal1(B_68), A_67) | ~r2_hidden(A_67, B_68))), inference(resolution, [status(thm)], [c_134, c_62])).
% 16.26/6.80  tff(c_23732, plain, (![B_1180, B_1181]: (~r2_hidden(B_1180, B_1181) | ~r1_ordinal1(k1_ordinal1(B_1181), B_1180) | ~v3_ordinal1(B_1180) | ~v3_ordinal1(k1_ordinal1(B_1181)))), inference(resolution, [status(thm)], [c_594, c_138])).
% 16.26/6.80  tff(c_23770, plain, (~r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(resolution, [status(thm)], [c_133, c_23732])).
% 16.26/6.80  tff(c_23783, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23620, c_64, c_1430, c_23770])).
% 16.26/6.80  tff(c_23784, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_1389])).
% 16.26/6.80  tff(c_23787, plain, (r1_ordinal1(k1_ordinal1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_23784, c_133])).
% 16.26/6.80  tff(c_52, plain, (![B_45]: (r2_hidden(B_45, k1_ordinal1(B_45)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 16.26/6.80  tff(c_97, plain, (![B_61, A_62]: (~r1_tarski(B_61, A_62) | ~r2_hidden(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_113])).
% 16.26/6.80  tff(c_101, plain, (![B_45]: (~r1_tarski(k1_ordinal1(B_45), B_45))), inference(resolution, [status(thm)], [c_52, c_97])).
% 16.26/6.80  tff(c_27446, plain, (![B_1344]: (~r1_ordinal1(k1_ordinal1(B_1344), B_1344) | ~v3_ordinal1(B_1344) | ~v3_ordinal1(k1_ordinal1(B_1344)))), inference(resolution, [status(thm)], [c_594, c_101])).
% 16.26/6.80  tff(c_27453, plain, (~v3_ordinal1('#skF_4') | ~v3_ordinal1(k1_ordinal1('#skF_4'))), inference(resolution, [status(thm)], [c_23787, c_27446])).
% 16.26/6.80  tff(c_27466, plain, (~v3_ordinal1(k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_27453])).
% 16.26/6.80  tff(c_27471, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_27466])).
% 16.26/6.80  tff(c_27475, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_27471])).
% 16.26/6.80  tff(c_27477, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_68])).
% 16.26/6.80  tff(c_27481, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_27477, c_62])).
% 16.26/6.80  tff(c_27859, plain, (~r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_27846, c_27481])).
% 16.26/6.80  tff(c_27869, plain, (~r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_66, c_27859])).
% 16.26/6.80  tff(c_42, plain, (![B_40, A_39]: (r1_ordinal1(B_40, A_39) | r1_ordinal1(A_39, B_40) | ~v3_ordinal1(B_40) | ~v3_ordinal1(A_39))), inference(cnfTransformation, [status(thm)], [f_64])).
% 16.26/6.80  tff(c_28006, plain, (![B_1407, A_1408]: (r1_ordinal1(B_1407, A_1408) | r1_ordinal1(A_1408, B_1407) | ~v3_ordinal1(B_1407) | ~v3_ordinal1(A_1408))), inference(cnfTransformation, [status(thm)], [f_64])).
% 16.26/6.80  tff(c_27476, plain, (~r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_68])).
% 16.26/6.80  tff(c_28010, plain, (r1_ordinal1('#skF_4', k1_ordinal1('#skF_3')) | ~v3_ordinal1(k1_ordinal1('#skF_3')) | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_28006, c_27476])).
% 16.26/6.80  tff(c_28017, plain, (r1_ordinal1('#skF_4', k1_ordinal1('#skF_3')) | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_28010])).
% 16.26/6.80  tff(c_28021, plain, (~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(splitLeft, [status(thm)], [c_28017])).
% 16.26/6.80  tff(c_28024, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_28021])).
% 16.26/6.80  tff(c_28028, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_28024])).
% 16.26/6.80  tff(c_28030, plain, (v3_ordinal1(k1_ordinal1('#skF_3'))), inference(splitRight, [status(thm)], [c_28017])).
% 16.26/6.80  tff(c_28113, plain, (![B_1416, A_1417]: (r2_hidden(B_1416, A_1417) | r1_ordinal1(A_1417, B_1416) | ~v3_ordinal1(B_1416) | ~v3_ordinal1(A_1417))), inference(cnfTransformation, [status(thm)], [f_104])).
% 16.26/6.80  tff(c_50, plain, (![B_45, A_44]: (B_45=A_44 | r2_hidden(A_44, B_45) | ~r2_hidden(A_44, k1_ordinal1(B_45)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 16.26/6.80  tff(c_32099, plain, (![B_1594, B_1593]: (B_1594=B_1593 | r2_hidden(B_1594, B_1593) | r1_ordinal1(k1_ordinal1(B_1593), B_1594) | ~v3_ordinal1(B_1594) | ~v3_ordinal1(k1_ordinal1(B_1593)))), inference(resolution, [status(thm)], [c_28113, c_50])).
% 16.26/6.80  tff(c_32102, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(resolution, [status(thm)], [c_32099, c_27476])).
% 16.26/6.80  tff(c_32105, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28030, c_64, c_32102])).
% 16.26/6.80  tff(c_32106, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_32105])).
% 16.26/6.80  tff(c_32110, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_32106, c_62])).
% 16.26/6.80  tff(c_32113, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_32110])).
% 16.26/6.80  tff(c_32116, plain, (~r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_32113])).
% 16.26/6.80  tff(c_32119, plain, (r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_32116])).
% 16.26/6.80  tff(c_32125, plain, (r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_66, c_32119])).
% 16.26/6.80  tff(c_32127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27869, c_32125])).
% 16.26/6.80  tff(c_32128, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_32105])).
% 16.26/6.80  tff(c_32134, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32128, c_27481])).
% 16.26/6.80  tff(c_32139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_32134])).
% 16.26/6.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.26/6.80  
% 16.26/6.80  Inference rules
% 16.26/6.80  ----------------------
% 16.26/6.80  #Ref     : 0
% 16.26/6.80  #Sup     : 6648
% 16.26/6.80  #Fact    : 64
% 16.26/6.80  #Define  : 0
% 16.26/6.80  #Split   : 6
% 16.26/6.80  #Chain   : 0
% 16.26/6.80  #Close   : 0
% 16.26/6.80  
% 16.26/6.80  Ordering : KBO
% 16.26/6.80  
% 16.26/6.80  Simplification rules
% 16.26/6.80  ----------------------
% 16.26/6.80  #Subsume      : 1752
% 16.26/6.80  #Demod        : 700
% 16.26/6.80  #Tautology    : 162
% 16.26/6.80  #SimpNegUnit  : 89
% 16.26/6.80  #BackRed      : 110
% 16.26/6.80  
% 16.26/6.80  #Partial instantiations: 0
% 16.26/6.80  #Strategies tried      : 1
% 16.26/6.80  
% 16.26/6.80  Timing (in seconds)
% 16.26/6.80  ----------------------
% 16.44/6.80  Preprocessing        : 0.34
% 16.44/6.80  Parsing              : 0.18
% 16.44/6.80  CNF conversion       : 0.02
% 16.44/6.80  Main loop            : 5.69
% 16.44/6.80  Inferencing          : 1.04
% 16.44/6.80  Reduction            : 1.87
% 16.44/6.80  Demodulation         : 0.78
% 16.44/6.80  BG Simplification    : 0.16
% 16.44/6.80  Subsumption          : 2.16
% 16.44/6.80  Abstraction          : 0.21
% 16.44/6.80  MUC search           : 0.00
% 16.44/6.80  Cooper               : 0.00
% 16.44/6.80  Total                : 6.07
% 16.44/6.80  Index Insertion      : 0.00
% 16.44/6.80  Index Deletion       : 0.00
% 16.44/6.80  Index Matching       : 0.00
% 16.44/6.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
