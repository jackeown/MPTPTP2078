%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:09 EST 2020

% Result     : Theorem 18.83s
% Output     : CNFRefutation 18.83s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 259 expanded)
%              Number of leaves         :   31 (  97 expanded)
%              Depth                    :   11
%              Number of atoms          :  168 ( 645 expanded)
%              Number of equality atoms :   20 (  61 expanded)
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

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_105,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_92,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_101,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_110,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_66,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_60,plain,(
    ! [A_52] :
      ( v3_ordinal1(k1_ordinal1(A_52))
      | ~ v3_ordinal1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_64,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1006,plain,(
    ! [B_154,A_155] :
      ( r2_hidden(B_154,A_155)
      | B_154 = A_155
      | r2_hidden(A_155,B_154)
      | ~ v3_ordinal1(B_154)
      | ~ v3_ordinal1(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_74,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_103,plain,(
    r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_68,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4')
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_129,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_68])).

tff(c_1125,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1006,c_129])).

tff(c_1303,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_1125])).

tff(c_1347,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1303])).

tff(c_48,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ r1_ordinal1(A_42,B_43)
      | ~ v3_ordinal1(B_43)
      | ~ v3_ordinal1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_543,plain,(
    ! [A_119,B_120] :
      ( r1_tarski(A_119,B_120)
      | ~ r1_ordinal1(A_119,B_120)
      | ~ v3_ordinal1(B_120)
      | ~ v3_ordinal1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(B_10,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3984,plain,(
    ! [B_294,A_295] :
      ( B_294 = A_295
      | ~ r1_tarski(B_294,A_295)
      | ~ r1_ordinal1(A_295,B_294)
      | ~ v3_ordinal1(B_294)
      | ~ v3_ordinal1(A_295) ) ),
    inference(resolution,[status(thm)],[c_543,c_22])).

tff(c_26504,plain,(
    ! [B_1332,A_1333] :
      ( B_1332 = A_1333
      | ~ r1_ordinal1(B_1332,A_1333)
      | ~ r1_ordinal1(A_1333,B_1332)
      | ~ v3_ordinal1(B_1332)
      | ~ v3_ordinal1(A_1333) ) ),
    inference(resolution,[status(thm)],[c_48,c_3984])).

tff(c_26532,plain,
    ( k1_ordinal1('#skF_3') = '#skF_4'
    | ~ r1_ordinal1('#skF_4',k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_103,c_26504])).

tff(c_26551,plain,
    ( k1_ordinal1('#skF_3') = '#skF_4'
    | ~ r1_ordinal1('#skF_4',k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_26532])).

tff(c_26552,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_26551])).

tff(c_26555,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_26552])).

tff(c_26559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_26555])).

tff(c_26561,plain,(
    v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_26551])).

tff(c_54,plain,(
    ! [A_44,B_45] :
      ( ~ r2_hidden(A_44,B_45)
      | r2_hidden(A_44,k1_ordinal1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_723,plain,(
    ! [B_137,A_138] :
      ( r2_hidden(B_137,A_138)
      | r1_ordinal1(A_138,B_137)
      | ~ v3_ordinal1(B_137)
      | ~ v3_ordinal1(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2942,plain,(
    ! [A_256,B_257] :
      ( ~ r2_hidden(A_256,B_257)
      | r1_ordinal1(A_256,B_257)
      | ~ v3_ordinal1(B_257)
      | ~ v3_ordinal1(A_256) ) ),
    inference(resolution,[status(thm)],[c_723,c_2])).

tff(c_3007,plain,(
    ! [A_44,B_45] :
      ( r1_ordinal1(A_44,k1_ordinal1(B_45))
      | ~ v3_ordinal1(k1_ordinal1(B_45))
      | ~ v3_ordinal1(A_44)
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_54,c_2942])).

tff(c_26560,plain,
    ( ~ r1_ordinal1('#skF_4',k1_ordinal1('#skF_3'))
    | k1_ordinal1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_26551])).

tff(c_26562,plain,(
    ~ r1_ordinal1('#skF_4',k1_ordinal1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_26560])).

tff(c_26565,plain,
    ( ~ v3_ordinal1(k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1('#skF_4')
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_3007,c_26562])).

tff(c_26571,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1347,c_64,c_26561,c_26565])).

tff(c_26572,plain,(
    k1_ordinal1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_26560])).

tff(c_820,plain,
    ( r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_723,c_129])).

tff(c_860,plain,(
    r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_820])).

tff(c_52,plain,(
    ! [B_45] : r2_hidden(B_45,k1_ordinal1(B_45)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_97,plain,(
    ! [B_61,A_62] :
      ( ~ r1_tarski(B_61,A_62)
      | ~ r2_hidden(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_101,plain,(
    ! [B_45] : ~ r1_tarski(k1_ordinal1(B_45),B_45) ),
    inference(resolution,[status(thm)],[c_52,c_97])).

tff(c_561,plain,(
    ! [B_120] :
      ( ~ r1_ordinal1(k1_ordinal1(B_120),B_120)
      | ~ v3_ordinal1(B_120)
      | ~ v3_ordinal1(k1_ordinal1(B_120)) ) ),
    inference(resolution,[status(thm)],[c_543,c_101])).

tff(c_26993,plain,
    ( ~ r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26572,c_561])).

tff(c_27150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_26572,c_66,c_860,c_26993])).

tff(c_27151,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1303])).

tff(c_27155,plain,(
    r1_ordinal1(k1_ordinal1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27151,c_103])).

tff(c_31516,plain,(
    ! [B_1530] :
      ( ~ r1_ordinal1(k1_ordinal1(B_1530),B_1530)
      | ~ v3_ordinal1(B_1530)
      | ~ v3_ordinal1(k1_ordinal1(B_1530)) ) ),
    inference(resolution,[status(thm)],[c_543,c_101])).

tff(c_31523,plain,
    ( ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_27155,c_31516])).

tff(c_31528,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_31523])).

tff(c_31531,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_31528])).

tff(c_31535,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_31531])).

tff(c_31536,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_31542,plain,(
    ! [B_1531,A_1532] :
      ( ~ r2_hidden(B_1531,A_1532)
      | ~ r2_hidden(A_1532,B_1531) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_31547,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_31536,c_31542])).

tff(c_32075,plain,(
    ! [B_1592,A_1593] :
      ( r2_hidden(B_1592,A_1593)
      | r1_ordinal1(A_1593,B_1592)
      | ~ v3_ordinal1(B_1592)
      | ~ v3_ordinal1(A_1593) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_50,plain,(
    ! [B_45,A_44] :
      ( B_45 = A_44
      | r2_hidden(A_44,B_45)
      | ~ r2_hidden(A_44,k1_ordinal1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_36692,plain,(
    ! [B_1798,B_1797] :
      ( B_1798 = B_1797
      | r2_hidden(B_1798,B_1797)
      | r1_ordinal1(k1_ordinal1(B_1797),B_1798)
      | ~ v3_ordinal1(B_1798)
      | ~ v3_ordinal1(k1_ordinal1(B_1797)) ) ),
    inference(resolution,[status(thm)],[c_32075,c_50])).

tff(c_31537,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_36695,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36692,c_31537])).

tff(c_36698,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_36695])).

tff(c_36699,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_31547,c_36698])).

tff(c_36700,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_36699])).

tff(c_36703,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_36700])).

tff(c_36707,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_36703])).

tff(c_36708,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_36699])).

tff(c_62,plain,(
    ! [B_54,A_53] :
      ( ~ r1_tarski(B_54,A_53)
      | ~ r2_hidden(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_31541,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_31536,c_62])).

tff(c_36714,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36708,c_31541])).

tff(c_36719,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_36714])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:37:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.83/7.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.83/7.95  
% 18.83/7.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.83/7.95  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 18.83/7.95  
% 18.83/7.95  %Foreground sorts:
% 18.83/7.95  
% 18.83/7.95  
% 18.83/7.95  %Background operators:
% 18.83/7.95  
% 18.83/7.95  
% 18.83/7.95  %Foreground operators:
% 18.83/7.95  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 18.83/7.95  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 18.83/7.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.83/7.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.83/7.95  tff(k1_tarski, type, k1_tarski: $i > $i).
% 18.83/7.95  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 18.83/7.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.83/7.95  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 18.83/7.95  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 18.83/7.95  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.83/7.95  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 18.83/7.95  tff('#skF_3', type, '#skF_3': $i).
% 18.83/7.95  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 18.83/7.95  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 18.83/7.95  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 18.83/7.95  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 18.83/7.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.83/7.95  tff(k3_tarski, type, k3_tarski: $i > $i).
% 18.83/7.95  tff('#skF_4', type, '#skF_4': $i).
% 18.83/7.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.83/7.95  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 18.83/7.95  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 18.83/7.95  
% 18.83/7.97  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 18.83/7.97  tff(f_120, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 18.83/7.97  tff(f_105, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 18.83/7.97  tff(f_92, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 18.83/7.97  tff(f_71, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 18.83/7.97  tff(f_77, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 18.83/7.97  tff(f_101, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 18.83/7.97  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 18.83/7.97  tff(f_110, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 18.83/7.97  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 18.83/7.97  tff(c_66, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 18.83/7.97  tff(c_60, plain, (![A_52]: (v3_ordinal1(k1_ordinal1(A_52)) | ~v3_ordinal1(A_52))), inference(cnfTransformation, [status(thm)], [f_105])).
% 18.83/7.97  tff(c_64, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 18.83/7.97  tff(c_1006, plain, (![B_154, A_155]: (r2_hidden(B_154, A_155) | B_154=A_155 | r2_hidden(A_155, B_154) | ~v3_ordinal1(B_154) | ~v3_ordinal1(A_155))), inference(cnfTransformation, [status(thm)], [f_92])).
% 18.83/7.97  tff(c_74, plain, (r2_hidden('#skF_3', '#skF_4') | r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 18.83/7.97  tff(c_103, plain, (r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_74])).
% 18.83/7.97  tff(c_68, plain, (~r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4') | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 18.83/7.97  tff(c_129, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_68])).
% 18.83/7.97  tff(c_1125, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_1006, c_129])).
% 18.83/7.97  tff(c_1303, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_66, c_1125])).
% 18.83/7.97  tff(c_1347, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_1303])).
% 18.83/7.97  tff(c_48, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~r1_ordinal1(A_42, B_43) | ~v3_ordinal1(B_43) | ~v3_ordinal1(A_42))), inference(cnfTransformation, [status(thm)], [f_71])).
% 18.83/7.97  tff(c_543, plain, (![A_119, B_120]: (r1_tarski(A_119, B_120) | ~r1_ordinal1(A_119, B_120) | ~v3_ordinal1(B_120) | ~v3_ordinal1(A_119))), inference(cnfTransformation, [status(thm)], [f_71])).
% 18.83/7.97  tff(c_22, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(B_10, A_9) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 18.83/7.97  tff(c_3984, plain, (![B_294, A_295]: (B_294=A_295 | ~r1_tarski(B_294, A_295) | ~r1_ordinal1(A_295, B_294) | ~v3_ordinal1(B_294) | ~v3_ordinal1(A_295))), inference(resolution, [status(thm)], [c_543, c_22])).
% 18.83/7.97  tff(c_26504, plain, (![B_1332, A_1333]: (B_1332=A_1333 | ~r1_ordinal1(B_1332, A_1333) | ~r1_ordinal1(A_1333, B_1332) | ~v3_ordinal1(B_1332) | ~v3_ordinal1(A_1333))), inference(resolution, [status(thm)], [c_48, c_3984])).
% 18.83/7.97  tff(c_26532, plain, (k1_ordinal1('#skF_3')='#skF_4' | ~r1_ordinal1('#skF_4', k1_ordinal1('#skF_3')) | ~v3_ordinal1(k1_ordinal1('#skF_3')) | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_103, c_26504])).
% 18.83/7.97  tff(c_26551, plain, (k1_ordinal1('#skF_3')='#skF_4' | ~r1_ordinal1('#skF_4', k1_ordinal1('#skF_3')) | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_26532])).
% 18.83/7.97  tff(c_26552, plain, (~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(splitLeft, [status(thm)], [c_26551])).
% 18.83/7.97  tff(c_26555, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_26552])).
% 18.83/7.97  tff(c_26559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_26555])).
% 18.83/7.97  tff(c_26561, plain, (v3_ordinal1(k1_ordinal1('#skF_3'))), inference(splitRight, [status(thm)], [c_26551])).
% 18.83/7.97  tff(c_54, plain, (![A_44, B_45]: (~r2_hidden(A_44, B_45) | r2_hidden(A_44, k1_ordinal1(B_45)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 18.83/7.97  tff(c_723, plain, (![B_137, A_138]: (r2_hidden(B_137, A_138) | r1_ordinal1(A_138, B_137) | ~v3_ordinal1(B_137) | ~v3_ordinal1(A_138))), inference(cnfTransformation, [status(thm)], [f_101])).
% 18.83/7.97  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 18.83/7.97  tff(c_2942, plain, (![A_256, B_257]: (~r2_hidden(A_256, B_257) | r1_ordinal1(A_256, B_257) | ~v3_ordinal1(B_257) | ~v3_ordinal1(A_256))), inference(resolution, [status(thm)], [c_723, c_2])).
% 18.83/7.97  tff(c_3007, plain, (![A_44, B_45]: (r1_ordinal1(A_44, k1_ordinal1(B_45)) | ~v3_ordinal1(k1_ordinal1(B_45)) | ~v3_ordinal1(A_44) | ~r2_hidden(A_44, B_45))), inference(resolution, [status(thm)], [c_54, c_2942])).
% 18.83/7.97  tff(c_26560, plain, (~r1_ordinal1('#skF_4', k1_ordinal1('#skF_3')) | k1_ordinal1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_26551])).
% 18.83/7.97  tff(c_26562, plain, (~r1_ordinal1('#skF_4', k1_ordinal1('#skF_3'))), inference(splitLeft, [status(thm)], [c_26560])).
% 18.83/7.97  tff(c_26565, plain, (~v3_ordinal1(k1_ordinal1('#skF_3')) | ~v3_ordinal1('#skF_4') | ~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_3007, c_26562])).
% 18.83/7.97  tff(c_26571, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1347, c_64, c_26561, c_26565])).
% 18.83/7.97  tff(c_26572, plain, (k1_ordinal1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_26560])).
% 18.83/7.97  tff(c_820, plain, (r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_723, c_129])).
% 18.83/7.97  tff(c_860, plain, (r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_66, c_820])).
% 18.83/7.97  tff(c_52, plain, (![B_45]: (r2_hidden(B_45, k1_ordinal1(B_45)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 18.83/7.97  tff(c_97, plain, (![B_61, A_62]: (~r1_tarski(B_61, A_62) | ~r2_hidden(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_110])).
% 18.83/7.97  tff(c_101, plain, (![B_45]: (~r1_tarski(k1_ordinal1(B_45), B_45))), inference(resolution, [status(thm)], [c_52, c_97])).
% 18.83/7.97  tff(c_561, plain, (![B_120]: (~r1_ordinal1(k1_ordinal1(B_120), B_120) | ~v3_ordinal1(B_120) | ~v3_ordinal1(k1_ordinal1(B_120)))), inference(resolution, [status(thm)], [c_543, c_101])).
% 18.83/7.97  tff(c_26993, plain, (~r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_26572, c_561])).
% 18.83/7.97  tff(c_27150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_26572, c_66, c_860, c_26993])).
% 18.83/7.97  tff(c_27151, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_1303])).
% 18.83/7.97  tff(c_27155, plain, (r1_ordinal1(k1_ordinal1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_27151, c_103])).
% 18.83/7.97  tff(c_31516, plain, (![B_1530]: (~r1_ordinal1(k1_ordinal1(B_1530), B_1530) | ~v3_ordinal1(B_1530) | ~v3_ordinal1(k1_ordinal1(B_1530)))), inference(resolution, [status(thm)], [c_543, c_101])).
% 18.83/7.97  tff(c_31523, plain, (~v3_ordinal1('#skF_4') | ~v3_ordinal1(k1_ordinal1('#skF_4'))), inference(resolution, [status(thm)], [c_27155, c_31516])).
% 18.83/7.97  tff(c_31528, plain, (~v3_ordinal1(k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_31523])).
% 18.83/7.97  tff(c_31531, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_31528])).
% 18.83/7.97  tff(c_31535, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_31531])).
% 18.83/7.97  tff(c_31536, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_74])).
% 18.83/7.97  tff(c_31542, plain, (![B_1531, A_1532]: (~r2_hidden(B_1531, A_1532) | ~r2_hidden(A_1532, B_1531))), inference(cnfTransformation, [status(thm)], [f_30])).
% 18.83/7.97  tff(c_31547, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_31536, c_31542])).
% 18.83/7.97  tff(c_32075, plain, (![B_1592, A_1593]: (r2_hidden(B_1592, A_1593) | r1_ordinal1(A_1593, B_1592) | ~v3_ordinal1(B_1592) | ~v3_ordinal1(A_1593))), inference(cnfTransformation, [status(thm)], [f_101])).
% 18.83/7.97  tff(c_50, plain, (![B_45, A_44]: (B_45=A_44 | r2_hidden(A_44, B_45) | ~r2_hidden(A_44, k1_ordinal1(B_45)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 18.83/7.97  tff(c_36692, plain, (![B_1798, B_1797]: (B_1798=B_1797 | r2_hidden(B_1798, B_1797) | r1_ordinal1(k1_ordinal1(B_1797), B_1798) | ~v3_ordinal1(B_1798) | ~v3_ordinal1(k1_ordinal1(B_1797)))), inference(resolution, [status(thm)], [c_32075, c_50])).
% 18.83/7.97  tff(c_31537, plain, (~r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_74])).
% 18.83/7.97  tff(c_36695, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(resolution, [status(thm)], [c_36692, c_31537])).
% 18.83/7.97  tff(c_36698, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_36695])).
% 18.83/7.97  tff(c_36699, plain, ('#skF_3'='#skF_4' | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_31547, c_36698])).
% 18.83/7.97  tff(c_36700, plain, (~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(splitLeft, [status(thm)], [c_36699])).
% 18.83/7.97  tff(c_36703, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_36700])).
% 18.83/7.97  tff(c_36707, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_36703])).
% 18.83/7.97  tff(c_36708, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_36699])).
% 18.83/7.97  tff(c_62, plain, (![B_54, A_53]: (~r1_tarski(B_54, A_53) | ~r2_hidden(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_110])).
% 18.83/7.97  tff(c_31541, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_31536, c_62])).
% 18.83/7.97  tff(c_36714, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36708, c_31541])).
% 18.83/7.97  tff(c_36719, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_36714])).
% 18.83/7.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.83/7.97  
% 18.83/7.97  Inference rules
% 18.83/7.97  ----------------------
% 18.83/7.97  #Ref     : 0
% 18.83/7.97  #Sup     : 7792
% 18.83/7.97  #Fact    : 62
% 18.83/7.97  #Define  : 0
% 18.83/7.97  #Split   : 5
% 18.83/7.97  #Chain   : 0
% 18.83/7.97  #Close   : 0
% 18.83/7.97  
% 18.83/7.97  Ordering : KBO
% 18.83/7.97  
% 18.83/7.97  Simplification rules
% 18.83/7.97  ----------------------
% 18.83/7.97  #Subsume      : 1964
% 18.83/7.97  #Demod        : 803
% 18.83/7.97  #Tautology    : 171
% 18.83/7.97  #SimpNegUnit  : 86
% 18.83/7.97  #BackRed      : 114
% 18.83/7.97  
% 18.83/7.97  #Partial instantiations: 0
% 18.83/7.97  #Strategies tried      : 1
% 18.83/7.97  
% 18.83/7.97  Timing (in seconds)
% 18.83/7.97  ----------------------
% 18.83/7.97  Preprocessing        : 0.34
% 18.83/7.97  Parsing              : 0.18
% 18.83/7.97  CNF conversion       : 0.02
% 18.83/7.97  Main loop            : 6.87
% 18.83/7.97  Inferencing          : 1.15
% 18.83/7.97  Reduction            : 2.10
% 18.83/7.97  Demodulation         : 0.85
% 18.83/7.97  BG Simplification    : 0.17
% 18.83/7.97  Subsumption          : 2.92
% 18.83/7.97  Abstraction          : 0.23
% 18.83/7.97  MUC search           : 0.00
% 18.83/7.97  Cooper               : 0.00
% 18.83/7.97  Total                : 7.25
% 18.83/7.97  Index Insertion      : 0.00
% 18.83/7.97  Index Deletion       : 0.00
% 18.83/7.97  Index Matching       : 0.00
% 18.83/7.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
