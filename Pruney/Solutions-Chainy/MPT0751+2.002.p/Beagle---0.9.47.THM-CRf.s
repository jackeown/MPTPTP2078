%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:25 EST 2020

% Result     : Theorem 25.29s
% Output     : CNFRefutation 25.29s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 287 expanded)
%              Number of leaves         :   20 ( 102 expanded)
%              Depth                    :   14
%              Number of atoms          :  192 ( 957 expanded)
%              Number of equality atoms :   31 ( 178 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v4_ordinal1 > v3_ordinal1 > v1_xboole_0 > #nlpp > k1_ordinal1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v4_ordinal1,type,(
    v4_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ( ~ ( ~ v4_ordinal1(A)
              & ! [B] :
                  ( v3_ordinal1(B)
                 => A != k1_ordinal1(B) ) )
          & ~ ( ? [B] :
                  ( v3_ordinal1(B)
                  & A = k1_ordinal1(B) )
              & v4_ordinal1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_ordinal1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_78,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v4_ordinal1(A)
      <=> ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(B,A)
             => r2_hidden(k1_ordinal1(B),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_44,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( ~ v1_xboole_0(k1_ordinal1(A))
        & v3_ordinal1(k1_ordinal1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_ordinal1)).

tff(f_67,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_34,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_46,plain,
    ( ~ v4_ordinal1('#skF_3')
    | v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_48,plain,(
    ~ v4_ordinal1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_136,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_1'(A_48,B_49),A_48)
      | r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_146,plain,(
    ! [A_48] : r1_tarski(A_48,A_48) ),
    inference(resolution,[status(thm)],[c_136,c_6])).

tff(c_30,plain,(
    ! [A_15] :
      ( v3_ordinal1('#skF_2'(A_15))
      | v4_ordinal1(A_15)
      | ~ v3_ordinal1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( ~ r2_hidden(A_10,B_11)
      | r2_hidden(A_10,k1_ordinal1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_122,plain,(
    ! [A_45,B_46] :
      ( ~ r2_hidden('#skF_1'(A_45,B_46),B_46)
      | r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_408,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(A_77,k1_ordinal1(B_78))
      | ~ r2_hidden('#skF_1'(A_77,k1_ordinal1(B_78)),B_78) ) ),
    inference(resolution,[status(thm)],[c_20,c_122])).

tff(c_427,plain,(
    ! [A_3] : r1_tarski(A_3,k1_ordinal1(A_3)) ),
    inference(resolution,[status(thm)],[c_8,c_408])).

tff(c_10,plain,(
    ! [A_8] :
      ( v3_ordinal1(k1_ordinal1(A_8))
      | ~ v3_ordinal1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_248,plain,(
    ! [B_71,A_72] :
      ( r2_hidden(B_71,A_72)
      | B_71 = A_72
      | r2_hidden(A_72,B_71)
      | ~ v3_ordinal1(B_71)
      | ~ v3_ordinal1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | r2_hidden(A_10,B_11)
      | ~ r2_hidden(A_10,k1_ordinal1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4265,plain,(
    ! [B_234,A_235] :
      ( B_234 = A_235
      | r2_hidden(A_235,B_234)
      | r2_hidden(k1_ordinal1(B_234),A_235)
      | k1_ordinal1(B_234) = A_235
      | ~ v3_ordinal1(k1_ordinal1(B_234))
      | ~ v3_ordinal1(A_235) ) ),
    inference(resolution,[status(thm)],[c_248,c_16])).

tff(c_26,plain,(
    ! [A_15] :
      ( ~ r2_hidden(k1_ordinal1('#skF_2'(A_15)),A_15)
      | v4_ordinal1(A_15)
      | ~ v3_ordinal1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_20601,plain,(
    ! [A_526] :
      ( v4_ordinal1(A_526)
      | '#skF_2'(A_526) = A_526
      | r2_hidden(A_526,'#skF_2'(A_526))
      | k1_ordinal1('#skF_2'(A_526)) = A_526
      | ~ v3_ordinal1(k1_ordinal1('#skF_2'(A_526)))
      | ~ v3_ordinal1(A_526) ) ),
    inference(resolution,[status(thm)],[c_4265,c_26])).

tff(c_56143,plain,(
    ! [A_967] :
      ( v4_ordinal1(A_967)
      | '#skF_2'(A_967) = A_967
      | r2_hidden(A_967,'#skF_2'(A_967))
      | k1_ordinal1('#skF_2'(A_967)) = A_967
      | ~ v3_ordinal1(A_967)
      | ~ v3_ordinal1('#skF_2'(A_967)) ) ),
    inference(resolution,[status(thm)],[c_10,c_20601])).

tff(c_28,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_2'(A_15),A_15)
      | v4_ordinal1(A_15)
      | ~ v3_ordinal1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_201,plain,(
    ! [C_64,B_65,A_66] :
      ( r2_hidden(C_64,B_65)
      | ~ r2_hidden(C_64,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_975,plain,(
    ! [A_109,B_110] :
      ( r2_hidden('#skF_2'(A_109),B_110)
      | ~ r1_tarski(A_109,B_110)
      | v4_ordinal1(A_109)
      | ~ v3_ordinal1(A_109) ) ),
    inference(resolution,[status(thm)],[c_28,c_201])).

tff(c_12453,plain,(
    ! [B_397,A_398] :
      ( B_397 = '#skF_2'(A_398)
      | r2_hidden('#skF_2'(A_398),B_397)
      | ~ r1_tarski(A_398,k1_ordinal1(B_397))
      | v4_ordinal1(A_398)
      | ~ v3_ordinal1(A_398) ) ),
    inference(resolution,[status(thm)],[c_975,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_12509,plain,(
    ! [B_397,A_398] :
      ( ~ r2_hidden(B_397,'#skF_2'(A_398))
      | B_397 = '#skF_2'(A_398)
      | ~ r1_tarski(A_398,k1_ordinal1(B_397))
      | v4_ordinal1(A_398)
      | ~ v3_ordinal1(A_398) ) ),
    inference(resolution,[status(thm)],[c_12453,c_2])).

tff(c_56211,plain,(
    ! [A_967] :
      ( ~ r1_tarski(A_967,k1_ordinal1(A_967))
      | v4_ordinal1(A_967)
      | '#skF_2'(A_967) = A_967
      | k1_ordinal1('#skF_2'(A_967)) = A_967
      | ~ v3_ordinal1(A_967)
      | ~ v3_ordinal1('#skF_2'(A_967)) ) ),
    inference(resolution,[status(thm)],[c_56143,c_12509])).

tff(c_56513,plain,(
    ! [A_968] :
      ( v4_ordinal1(A_968)
      | '#skF_2'(A_968) = A_968
      | k1_ordinal1('#skF_2'(A_968)) = A_968
      | ~ v3_ordinal1(A_968)
      | ~ v3_ordinal1('#skF_2'(A_968)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_56211])).

tff(c_56521,plain,(
    ! [A_969] :
      ( '#skF_2'(A_969) = A_969
      | k1_ordinal1('#skF_2'(A_969)) = A_969
      | v4_ordinal1(A_969)
      | ~ v3_ordinal1(A_969) ) ),
    inference(resolution,[status(thm)],[c_30,c_56513])).

tff(c_74,plain,(
    ! [A_35] :
      ( v3_ordinal1('#skF_2'(A_35))
      | v4_ordinal1(A_35)
      | ~ v3_ordinal1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    ! [B_23] :
      ( k1_ordinal1(B_23) != '#skF_3'
      | ~ v3_ordinal1(B_23)
      | v4_ordinal1('#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_58,plain,(
    ! [B_23] :
      ( k1_ordinal1(B_23) != '#skF_3'
      | ~ v3_ordinal1(B_23) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_36])).

tff(c_78,plain,(
    ! [A_35] :
      ( k1_ordinal1('#skF_2'(A_35)) != '#skF_3'
      | v4_ordinal1(A_35)
      | ~ v3_ordinal1(A_35) ) ),
    inference(resolution,[status(thm)],[c_74,c_58])).

tff(c_57719,plain,(
    ! [A_969] :
      ( A_969 != '#skF_3'
      | v4_ordinal1(A_969)
      | ~ v3_ordinal1(A_969)
      | '#skF_2'(A_969) = A_969
      | v4_ordinal1(A_969)
      | ~ v3_ordinal1(A_969) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56521,c_78])).

tff(c_57904,plain,(
    ! [A_972] :
      ( A_972 != '#skF_3'
      | '#skF_2'(A_972) = A_972
      | ~ v3_ordinal1(A_972)
      | v4_ordinal1(A_972) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_57719])).

tff(c_57910,plain,
    ( '#skF_2'('#skF_3') = '#skF_3'
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_57904,c_48])).

tff(c_57914,plain,(
    '#skF_2'('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_57910])).

tff(c_128,plain,(
    ! [A_47] :
      ( r2_hidden('#skF_2'(A_47),A_47)
      | v4_ordinal1(A_47)
      | ~ v3_ordinal1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_134,plain,(
    ! [A_47] :
      ( ~ r2_hidden(A_47,'#skF_2'(A_47))
      | v4_ordinal1(A_47)
      | ~ v3_ordinal1(A_47) ) ),
    inference(resolution,[status(thm)],[c_128,c_2])).

tff(c_1003,plain,(
    ! [A_109] :
      ( v4_ordinal1('#skF_2'(A_109))
      | ~ v3_ordinal1('#skF_2'(A_109))
      | ~ r1_tarski(A_109,'#skF_2'('#skF_2'(A_109)))
      | v4_ordinal1(A_109)
      | ~ v3_ordinal1(A_109) ) ),
    inference(resolution,[status(thm)],[c_975,c_134])).

tff(c_58007,plain,
    ( v4_ordinal1('#skF_2'('#skF_3'))
    | ~ v3_ordinal1('#skF_2'('#skF_3'))
    | ~ r1_tarski('#skF_3','#skF_2'('#skF_3'))
    | v4_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_57914,c_1003])).

tff(c_58149,plain,(
    v4_ordinal1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_146,c_57914,c_34,c_57914,c_57914,c_58007])).

tff(c_58151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_58149])).

tff(c_58153,plain,(
    v4_ordinal1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_42,plain,
    ( ~ v4_ordinal1('#skF_3')
    | k1_ordinal1('#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_58157,plain,(
    k1_ordinal1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58153,c_42])).

tff(c_58152,plain,(
    v3_ordinal1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_18,plain,(
    ! [B_11] : r2_hidden(B_11,k1_ordinal1(B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_24,plain,(
    ! [B_18,A_15] :
      ( r2_hidden(k1_ordinal1(B_18),A_15)
      | ~ r2_hidden(B_18,A_15)
      | ~ v3_ordinal1(B_18)
      | ~ v4_ordinal1(A_15)
      | ~ v3_ordinal1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_59076,plain,(
    ! [B_1040,A_1041] :
      ( r2_hidden(k1_ordinal1(B_1040),A_1041)
      | ~ r2_hidden(B_1040,A_1041)
      | ~ v3_ordinal1(B_1040)
      | ~ v4_ordinal1(A_1041)
      | ~ v3_ordinal1(A_1041) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_58177,plain,(
    ! [B_976,A_977] :
      ( ~ r2_hidden(B_976,A_977)
      | ~ r2_hidden(A_977,B_976) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_58183,plain,(
    ! [B_11] : ~ r2_hidden(k1_ordinal1(B_11),B_11) ),
    inference(resolution,[status(thm)],[c_18,c_58177])).

tff(c_59233,plain,(
    ! [A_1043] :
      ( ~ r2_hidden(A_1043,A_1043)
      | ~ v4_ordinal1(A_1043)
      | ~ v3_ordinal1(A_1043) ) ),
    inference(resolution,[status(thm)],[c_59076,c_58183])).

tff(c_59237,plain,(
    ! [B_18] :
      ( ~ r2_hidden(B_18,k1_ordinal1(B_18))
      | ~ v3_ordinal1(B_18)
      | ~ v4_ordinal1(k1_ordinal1(B_18))
      | ~ v3_ordinal1(k1_ordinal1(B_18)) ) ),
    inference(resolution,[status(thm)],[c_24,c_59233])).

tff(c_59337,plain,(
    ! [B_1048] :
      ( ~ v3_ordinal1(B_1048)
      | ~ v4_ordinal1(k1_ordinal1(B_1048))
      | ~ v3_ordinal1(k1_ordinal1(B_1048)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_59237])).

tff(c_59340,plain,
    ( ~ v3_ordinal1('#skF_4')
    | ~ v4_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58157,c_59337])).

tff(c_59343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_58157,c_58153,c_58152,c_59340])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 25.29/13.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.29/13.93  
% 25.29/13.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.29/13.93  %$ r2_hidden > r1_tarski > v4_ordinal1 > v3_ordinal1 > v1_xboole_0 > #nlpp > k1_ordinal1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 25.29/13.93  
% 25.29/13.93  %Foreground sorts:
% 25.29/13.93  
% 25.29/13.93  
% 25.29/13.93  %Background operators:
% 25.29/13.93  
% 25.29/13.93  
% 25.29/13.93  %Foreground operators:
% 25.29/13.93  tff('#skF_2', type, '#skF_2': $i > $i).
% 25.29/13.93  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 25.29/13.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 25.29/13.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 25.29/13.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 25.29/13.93  tff('#skF_3', type, '#skF_3': $i).
% 25.29/13.93  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 25.29/13.93  tff(v4_ordinal1, type, v4_ordinal1: $i > $o).
% 25.29/13.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 25.29/13.93  tff('#skF_4', type, '#skF_4': $i).
% 25.29/13.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 25.29/13.93  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 25.29/13.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 25.29/13.93  
% 25.29/13.95  tff(f_104, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (~(~v4_ordinal1(A) & (![B]: (v3_ordinal1(B) => ~(A = k1_ordinal1(B))))) & ~((?[B]: (v3_ordinal1(B) & (A = k1_ordinal1(B)))) & v4_ordinal1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_ordinal1)).
% 25.29/13.95  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 25.29/13.95  tff(f_78, axiom, (![A]: (v3_ordinal1(A) => (v4_ordinal1(A) <=> (![B]: (v3_ordinal1(B) => (r2_hidden(B, A) => r2_hidden(k1_ordinal1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_ordinal1)).
% 25.29/13.95  tff(f_52, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 25.29/13.95  tff(f_44, axiom, (![A]: (v3_ordinal1(A) => (~v1_xboole_0(k1_ordinal1(A)) & v3_ordinal1(k1_ordinal1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_ordinal1)).
% 25.29/13.95  tff(f_67, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 25.29/13.95  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 25.29/13.95  tff(c_34, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 25.29/13.95  tff(c_46, plain, (~v4_ordinal1('#skF_3') | v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 25.29/13.95  tff(c_48, plain, (~v4_ordinal1('#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 25.29/13.95  tff(c_136, plain, (![A_48, B_49]: (r2_hidden('#skF_1'(A_48, B_49), A_48) | r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_37])).
% 25.29/13.95  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 25.29/13.95  tff(c_146, plain, (![A_48]: (r1_tarski(A_48, A_48))), inference(resolution, [status(thm)], [c_136, c_6])).
% 25.29/13.95  tff(c_30, plain, (![A_15]: (v3_ordinal1('#skF_2'(A_15)) | v4_ordinal1(A_15) | ~v3_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_78])).
% 25.29/13.95  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 25.29/13.95  tff(c_20, plain, (![A_10, B_11]: (~r2_hidden(A_10, B_11) | r2_hidden(A_10, k1_ordinal1(B_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 25.29/13.95  tff(c_122, plain, (![A_45, B_46]: (~r2_hidden('#skF_1'(A_45, B_46), B_46) | r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_37])).
% 25.29/13.95  tff(c_408, plain, (![A_77, B_78]: (r1_tarski(A_77, k1_ordinal1(B_78)) | ~r2_hidden('#skF_1'(A_77, k1_ordinal1(B_78)), B_78))), inference(resolution, [status(thm)], [c_20, c_122])).
% 25.29/13.95  tff(c_427, plain, (![A_3]: (r1_tarski(A_3, k1_ordinal1(A_3)))), inference(resolution, [status(thm)], [c_8, c_408])).
% 25.29/13.95  tff(c_10, plain, (![A_8]: (v3_ordinal1(k1_ordinal1(A_8)) | ~v3_ordinal1(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 25.29/13.95  tff(c_248, plain, (![B_71, A_72]: (r2_hidden(B_71, A_72) | B_71=A_72 | r2_hidden(A_72, B_71) | ~v3_ordinal1(B_71) | ~v3_ordinal1(A_72))), inference(cnfTransformation, [status(thm)], [f_67])).
% 25.29/13.95  tff(c_16, plain, (![B_11, A_10]: (B_11=A_10 | r2_hidden(A_10, B_11) | ~r2_hidden(A_10, k1_ordinal1(B_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 25.29/13.95  tff(c_4265, plain, (![B_234, A_235]: (B_234=A_235 | r2_hidden(A_235, B_234) | r2_hidden(k1_ordinal1(B_234), A_235) | k1_ordinal1(B_234)=A_235 | ~v3_ordinal1(k1_ordinal1(B_234)) | ~v3_ordinal1(A_235))), inference(resolution, [status(thm)], [c_248, c_16])).
% 25.29/13.95  tff(c_26, plain, (![A_15]: (~r2_hidden(k1_ordinal1('#skF_2'(A_15)), A_15) | v4_ordinal1(A_15) | ~v3_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_78])).
% 25.29/13.95  tff(c_20601, plain, (![A_526]: (v4_ordinal1(A_526) | '#skF_2'(A_526)=A_526 | r2_hidden(A_526, '#skF_2'(A_526)) | k1_ordinal1('#skF_2'(A_526))=A_526 | ~v3_ordinal1(k1_ordinal1('#skF_2'(A_526))) | ~v3_ordinal1(A_526))), inference(resolution, [status(thm)], [c_4265, c_26])).
% 25.29/13.95  tff(c_56143, plain, (![A_967]: (v4_ordinal1(A_967) | '#skF_2'(A_967)=A_967 | r2_hidden(A_967, '#skF_2'(A_967)) | k1_ordinal1('#skF_2'(A_967))=A_967 | ~v3_ordinal1(A_967) | ~v3_ordinal1('#skF_2'(A_967)))), inference(resolution, [status(thm)], [c_10, c_20601])).
% 25.29/13.95  tff(c_28, plain, (![A_15]: (r2_hidden('#skF_2'(A_15), A_15) | v4_ordinal1(A_15) | ~v3_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_78])).
% 25.29/13.95  tff(c_201, plain, (![C_64, B_65, A_66]: (r2_hidden(C_64, B_65) | ~r2_hidden(C_64, A_66) | ~r1_tarski(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_37])).
% 25.29/13.95  tff(c_975, plain, (![A_109, B_110]: (r2_hidden('#skF_2'(A_109), B_110) | ~r1_tarski(A_109, B_110) | v4_ordinal1(A_109) | ~v3_ordinal1(A_109))), inference(resolution, [status(thm)], [c_28, c_201])).
% 25.29/13.95  tff(c_12453, plain, (![B_397, A_398]: (B_397='#skF_2'(A_398) | r2_hidden('#skF_2'(A_398), B_397) | ~r1_tarski(A_398, k1_ordinal1(B_397)) | v4_ordinal1(A_398) | ~v3_ordinal1(A_398))), inference(resolution, [status(thm)], [c_975, c_16])).
% 25.29/13.95  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 25.29/13.95  tff(c_12509, plain, (![B_397, A_398]: (~r2_hidden(B_397, '#skF_2'(A_398)) | B_397='#skF_2'(A_398) | ~r1_tarski(A_398, k1_ordinal1(B_397)) | v4_ordinal1(A_398) | ~v3_ordinal1(A_398))), inference(resolution, [status(thm)], [c_12453, c_2])).
% 25.29/13.95  tff(c_56211, plain, (![A_967]: (~r1_tarski(A_967, k1_ordinal1(A_967)) | v4_ordinal1(A_967) | '#skF_2'(A_967)=A_967 | k1_ordinal1('#skF_2'(A_967))=A_967 | ~v3_ordinal1(A_967) | ~v3_ordinal1('#skF_2'(A_967)))), inference(resolution, [status(thm)], [c_56143, c_12509])).
% 25.29/13.95  tff(c_56513, plain, (![A_968]: (v4_ordinal1(A_968) | '#skF_2'(A_968)=A_968 | k1_ordinal1('#skF_2'(A_968))=A_968 | ~v3_ordinal1(A_968) | ~v3_ordinal1('#skF_2'(A_968)))), inference(demodulation, [status(thm), theory('equality')], [c_427, c_56211])).
% 25.29/13.95  tff(c_56521, plain, (![A_969]: ('#skF_2'(A_969)=A_969 | k1_ordinal1('#skF_2'(A_969))=A_969 | v4_ordinal1(A_969) | ~v3_ordinal1(A_969))), inference(resolution, [status(thm)], [c_30, c_56513])).
% 25.29/13.95  tff(c_74, plain, (![A_35]: (v3_ordinal1('#skF_2'(A_35)) | v4_ordinal1(A_35) | ~v3_ordinal1(A_35))), inference(cnfTransformation, [status(thm)], [f_78])).
% 25.29/13.95  tff(c_36, plain, (![B_23]: (k1_ordinal1(B_23)!='#skF_3' | ~v3_ordinal1(B_23) | v4_ordinal1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 25.29/13.95  tff(c_58, plain, (![B_23]: (k1_ordinal1(B_23)!='#skF_3' | ~v3_ordinal1(B_23))), inference(negUnitSimplification, [status(thm)], [c_48, c_36])).
% 25.29/13.95  tff(c_78, plain, (![A_35]: (k1_ordinal1('#skF_2'(A_35))!='#skF_3' | v4_ordinal1(A_35) | ~v3_ordinal1(A_35))), inference(resolution, [status(thm)], [c_74, c_58])).
% 25.29/13.95  tff(c_57719, plain, (![A_969]: (A_969!='#skF_3' | v4_ordinal1(A_969) | ~v3_ordinal1(A_969) | '#skF_2'(A_969)=A_969 | v4_ordinal1(A_969) | ~v3_ordinal1(A_969))), inference(superposition, [status(thm), theory('equality')], [c_56521, c_78])).
% 25.29/13.95  tff(c_57904, plain, (![A_972]: (A_972!='#skF_3' | '#skF_2'(A_972)=A_972 | ~v3_ordinal1(A_972) | v4_ordinal1(A_972))), inference(factorization, [status(thm), theory('equality')], [c_57719])).
% 25.29/13.95  tff(c_57910, plain, ('#skF_2'('#skF_3')='#skF_3' | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_57904, c_48])).
% 25.29/13.95  tff(c_57914, plain, ('#skF_2'('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_57910])).
% 25.29/13.95  tff(c_128, plain, (![A_47]: (r2_hidden('#skF_2'(A_47), A_47) | v4_ordinal1(A_47) | ~v3_ordinal1(A_47))), inference(cnfTransformation, [status(thm)], [f_78])).
% 25.29/13.95  tff(c_134, plain, (![A_47]: (~r2_hidden(A_47, '#skF_2'(A_47)) | v4_ordinal1(A_47) | ~v3_ordinal1(A_47))), inference(resolution, [status(thm)], [c_128, c_2])).
% 25.29/13.95  tff(c_1003, plain, (![A_109]: (v4_ordinal1('#skF_2'(A_109)) | ~v3_ordinal1('#skF_2'(A_109)) | ~r1_tarski(A_109, '#skF_2'('#skF_2'(A_109))) | v4_ordinal1(A_109) | ~v3_ordinal1(A_109))), inference(resolution, [status(thm)], [c_975, c_134])).
% 25.29/13.95  tff(c_58007, plain, (v4_ordinal1('#skF_2'('#skF_3')) | ~v3_ordinal1('#skF_2'('#skF_3')) | ~r1_tarski('#skF_3', '#skF_2'('#skF_3')) | v4_ordinal1('#skF_3') | ~v3_ordinal1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_57914, c_1003])).
% 25.29/13.95  tff(c_58149, plain, (v4_ordinal1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_146, c_57914, c_34, c_57914, c_57914, c_58007])).
% 25.29/13.95  tff(c_58151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_58149])).
% 25.29/13.95  tff(c_58153, plain, (v4_ordinal1('#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 25.29/13.95  tff(c_42, plain, (~v4_ordinal1('#skF_3') | k1_ordinal1('#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_104])).
% 25.29/13.95  tff(c_58157, plain, (k1_ordinal1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58153, c_42])).
% 25.29/13.95  tff(c_58152, plain, (v3_ordinal1('#skF_4')), inference(splitRight, [status(thm)], [c_46])).
% 25.29/13.95  tff(c_18, plain, (![B_11]: (r2_hidden(B_11, k1_ordinal1(B_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 25.29/13.95  tff(c_24, plain, (![B_18, A_15]: (r2_hidden(k1_ordinal1(B_18), A_15) | ~r2_hidden(B_18, A_15) | ~v3_ordinal1(B_18) | ~v4_ordinal1(A_15) | ~v3_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_78])).
% 25.29/13.95  tff(c_59076, plain, (![B_1040, A_1041]: (r2_hidden(k1_ordinal1(B_1040), A_1041) | ~r2_hidden(B_1040, A_1041) | ~v3_ordinal1(B_1040) | ~v4_ordinal1(A_1041) | ~v3_ordinal1(A_1041))), inference(cnfTransformation, [status(thm)], [f_78])).
% 25.29/13.95  tff(c_58177, plain, (![B_976, A_977]: (~r2_hidden(B_976, A_977) | ~r2_hidden(A_977, B_976))), inference(cnfTransformation, [status(thm)], [f_30])).
% 25.29/13.95  tff(c_58183, plain, (![B_11]: (~r2_hidden(k1_ordinal1(B_11), B_11))), inference(resolution, [status(thm)], [c_18, c_58177])).
% 25.29/13.95  tff(c_59233, plain, (![A_1043]: (~r2_hidden(A_1043, A_1043) | ~v4_ordinal1(A_1043) | ~v3_ordinal1(A_1043))), inference(resolution, [status(thm)], [c_59076, c_58183])).
% 25.29/13.95  tff(c_59237, plain, (![B_18]: (~r2_hidden(B_18, k1_ordinal1(B_18)) | ~v3_ordinal1(B_18) | ~v4_ordinal1(k1_ordinal1(B_18)) | ~v3_ordinal1(k1_ordinal1(B_18)))), inference(resolution, [status(thm)], [c_24, c_59233])).
% 25.29/13.95  tff(c_59337, plain, (![B_1048]: (~v3_ordinal1(B_1048) | ~v4_ordinal1(k1_ordinal1(B_1048)) | ~v3_ordinal1(k1_ordinal1(B_1048)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_59237])).
% 25.29/13.95  tff(c_59340, plain, (~v3_ordinal1('#skF_4') | ~v4_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_58157, c_59337])).
% 25.29/13.95  tff(c_59343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_58157, c_58153, c_58152, c_59340])).
% 25.29/13.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.29/13.95  
% 25.29/13.95  Inference rules
% 25.29/13.95  ----------------------
% 25.29/13.95  #Ref     : 0
% 25.29/13.95  #Sup     : 13173
% 25.29/13.95  #Fact    : 9
% 25.29/13.95  #Define  : 0
% 25.29/13.95  #Split   : 3
% 25.29/13.95  #Chain   : 0
% 25.29/13.95  #Close   : 0
% 25.29/13.95  
% 25.29/13.95  Ordering : KBO
% 25.29/13.95  
% 25.29/13.95  Simplification rules
% 25.29/13.95  ----------------------
% 25.29/13.95  #Subsume      : 4361
% 25.29/13.95  #Demod        : 693
% 25.29/13.95  #Tautology    : 631
% 25.29/13.95  #SimpNegUnit  : 293
% 25.29/13.95  #BackRed      : 0
% 25.29/13.95  
% 25.29/13.95  #Partial instantiations: 0
% 25.29/13.95  #Strategies tried      : 1
% 25.29/13.95  
% 25.29/13.95  Timing (in seconds)
% 25.29/13.95  ----------------------
% 25.29/13.95  Preprocessing        : 0.31
% 25.29/13.95  Parsing              : 0.17
% 25.29/13.95  CNF conversion       : 0.02
% 25.29/13.95  Main loop            : 12.81
% 25.29/13.95  Inferencing          : 1.57
% 25.29/13.95  Reduction            : 2.30
% 25.29/13.95  Demodulation         : 1.42
% 25.29/13.95  BG Simplification    : 0.23
% 25.29/13.95  Subsumption          : 7.93
% 25.29/13.95  Abstraction          : 0.36
% 25.29/13.95  MUC search           : 0.00
% 25.29/13.95  Cooper               : 0.00
% 25.29/13.95  Total                : 13.16
% 25.29/13.95  Index Insertion      : 0.00
% 25.29/13.95  Index Deletion       : 0.00
% 25.29/13.95  Index Matching       : 0.00
% 25.29/13.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
