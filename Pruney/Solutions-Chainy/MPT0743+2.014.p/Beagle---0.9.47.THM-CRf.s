%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:10 EST 2020

% Result     : Theorem 25.80s
% Output     : CNFRefutation 25.95s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 141 expanded)
%              Number of leaves         :   24 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :  111 ( 306 expanded)
%              Number of equality atoms :    7 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v1_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_59,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( ~ v1_xboole_0(k1_ordinal1(A))
        & v3_ordinal1(k1_ordinal1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_ordinal1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_87,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_82,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_58380,plain,(
    ! [A_2007,B_2008] :
      ( ~ r2_hidden('#skF_1'(A_2007,B_2008),B_2008)
      | r1_tarski(A_2007,B_2008) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_58399,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(resolution,[status(thm)],[c_8,c_58380])).

tff(c_54,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_34,plain,(
    ! [A_17] :
      ( v3_ordinal1(k1_ordinal1(A_17))
      | ~ v3_ordinal1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_62,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r1_ordinal1(k1_ordinal1('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_85,plain,(
    r1_ordinal1(k1_ordinal1('#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_56,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_4'),'#skF_5')
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_89,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_56])).

tff(c_52,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_737,plain,(
    ! [A_106,B_107] :
      ( r1_tarski(A_106,B_107)
      | ~ r1_ordinal1(A_106,B_107)
      | ~ v3_ordinal1(B_107)
      | ~ v3_ordinal1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_95,plain,(
    ! [A_42,B_43] :
      ( ~ r2_hidden(A_42,B_43)
      | r2_hidden(A_42,k1_ordinal1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_50,plain,(
    ! [B_26,A_25] :
      ( ~ r1_tarski(B_26,A_25)
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_107,plain,(
    ! [B_43,A_42] :
      ( ~ r1_tarski(k1_ordinal1(B_43),A_42)
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_95,c_50])).

tff(c_49076,plain,(
    ! [B_1913,B_1914] :
      ( ~ r2_hidden(B_1913,B_1914)
      | ~ r1_ordinal1(k1_ordinal1(B_1914),B_1913)
      | ~ v3_ordinal1(B_1913)
      | ~ v3_ordinal1(k1_ordinal1(B_1914)) ) ),
    inference(resolution,[status(thm)],[c_737,c_107])).

tff(c_49106,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_85,c_49076])).

tff(c_49116,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | ~ v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_49106])).

tff(c_49117,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_49116])).

tff(c_49120,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_49117])).

tff(c_49124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_49120])).

tff(c_49126,plain,(
    v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_49116])).

tff(c_44,plain,(
    ! [B_21] : r2_hidden(B_21,k1_ordinal1(B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_357,plain,(
    ! [C_74,B_75,A_76] :
      ( r2_hidden(C_74,B_75)
      | ~ r2_hidden(C_74,A_76)
      | ~ r1_tarski(A_76,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_375,plain,(
    ! [B_21,B_75] :
      ( r2_hidden(B_21,B_75)
      | ~ r1_tarski(k1_ordinal1(B_21),B_75) ) ),
    inference(resolution,[status(thm)],[c_44,c_357])).

tff(c_58096,plain,(
    ! [B_1972,B_1973] :
      ( r2_hidden(B_1972,B_1973)
      | ~ r1_ordinal1(k1_ordinal1(B_1972),B_1973)
      | ~ v3_ordinal1(B_1973)
      | ~ v3_ordinal1(k1_ordinal1(B_1972)) ) ),
    inference(resolution,[status(thm)],[c_737,c_375])).

tff(c_58130,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_85,c_58096])).

tff(c_58143,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49126,c_52,c_58130])).

tff(c_58145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_58143])).

tff(c_58146,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_58153,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_58146,c_2])).

tff(c_58598,plain,(
    ! [B_2028,A_2029] :
      ( r2_hidden(B_2028,A_2029)
      | r1_ordinal1(A_2029,B_2028)
      | ~ v3_ordinal1(B_2028)
      | ~ v3_ordinal1(A_2029) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_42,plain,(
    ! [B_21,A_20] :
      ( B_21 = A_20
      | r2_hidden(A_20,B_21)
      | ~ r2_hidden(A_20,k1_ordinal1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_66137,plain,(
    ! [B_2416,B_2415] :
      ( B_2416 = B_2415
      | r2_hidden(B_2416,B_2415)
      | r1_ordinal1(k1_ordinal1(B_2415),B_2416)
      | ~ v3_ordinal1(B_2416)
      | ~ v3_ordinal1(k1_ordinal1(B_2415)) ) ),
    inference(resolution,[status(thm)],[c_58598,c_42])).

tff(c_58156,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58146,c_56])).

tff(c_66146,plain,
    ( '#skF_5' = '#skF_4'
    | r2_hidden('#skF_5','#skF_4')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_66137,c_58156])).

tff(c_66155,plain,
    ( '#skF_5' = '#skF_4'
    | r2_hidden('#skF_5','#skF_4')
    | ~ v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_66146])).

tff(c_66156,plain,
    ( '#skF_5' = '#skF_4'
    | ~ v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58153,c_66155])).

tff(c_66157,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_66156])).

tff(c_66160,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_66157])).

tff(c_66164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_66160])).

tff(c_66165,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_66156])).

tff(c_58154,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_58146,c_50])).

tff(c_66211,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66165,c_58154])).

tff(c_66217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58399,c_66211])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n016.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 18:17:49 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 25.80/15.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.80/15.14  
% 25.80/15.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.80/15.14  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v1_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 25.80/15.14  
% 25.80/15.14  %Foreground sorts:
% 25.80/15.14  
% 25.80/15.14  
% 25.80/15.14  %Background operators:
% 25.80/15.14  
% 25.80/15.14  
% 25.80/15.14  %Foreground operators:
% 25.80/15.14  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 25.80/15.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 25.80/15.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 25.80/15.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 25.80/15.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 25.80/15.14  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 25.80/15.14  tff('#skF_5', type, '#skF_5': $i).
% 25.80/15.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 25.80/15.14  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 25.80/15.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 25.80/15.14  tff('#skF_4', type, '#skF_4': $i).
% 25.80/15.14  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 25.80/15.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 25.80/15.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 25.80/15.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 25.80/15.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 25.80/15.14  
% 25.95/15.16  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 25.95/15.16  tff(f_97, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 25.95/15.16  tff(f_59, axiom, (![A]: (v3_ordinal1(A) => (~v1_xboole_0(k1_ordinal1(A)) & v3_ordinal1(k1_ordinal1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_ordinal1)).
% 25.95/15.16  tff(f_67, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 25.95/15.16  tff(f_73, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 25.95/15.16  tff(f_87, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 25.95/15.16  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 25.95/15.16  tff(f_82, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 25.95/15.16  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 25.95/15.16  tff(c_58380, plain, (![A_2007, B_2008]: (~r2_hidden('#skF_1'(A_2007, B_2008), B_2008) | r1_tarski(A_2007, B_2008))), inference(cnfTransformation, [status(thm)], [f_37])).
% 25.95/15.16  tff(c_58399, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(resolution, [status(thm)], [c_8, c_58380])).
% 25.95/15.16  tff(c_54, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 25.95/15.16  tff(c_34, plain, (![A_17]: (v3_ordinal1(k1_ordinal1(A_17)) | ~v3_ordinal1(A_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 25.95/15.16  tff(c_62, plain, (r2_hidden('#skF_4', '#skF_5') | r1_ordinal1(k1_ordinal1('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 25.95/15.16  tff(c_85, plain, (r1_ordinal1(k1_ordinal1('#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_62])).
% 25.95/15.16  tff(c_56, plain, (~r1_ordinal1(k1_ordinal1('#skF_4'), '#skF_5') | ~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 25.95/15.16  tff(c_89, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_56])).
% 25.95/15.16  tff(c_52, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 25.95/15.16  tff(c_737, plain, (![A_106, B_107]: (r1_tarski(A_106, B_107) | ~r1_ordinal1(A_106, B_107) | ~v3_ordinal1(B_107) | ~v3_ordinal1(A_106))), inference(cnfTransformation, [status(thm)], [f_67])).
% 25.95/15.16  tff(c_95, plain, (![A_42, B_43]: (~r2_hidden(A_42, B_43) | r2_hidden(A_42, k1_ordinal1(B_43)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 25.95/15.16  tff(c_50, plain, (![B_26, A_25]: (~r1_tarski(B_26, A_25) | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_87])).
% 25.95/15.16  tff(c_107, plain, (![B_43, A_42]: (~r1_tarski(k1_ordinal1(B_43), A_42) | ~r2_hidden(A_42, B_43))), inference(resolution, [status(thm)], [c_95, c_50])).
% 25.95/15.16  tff(c_49076, plain, (![B_1913, B_1914]: (~r2_hidden(B_1913, B_1914) | ~r1_ordinal1(k1_ordinal1(B_1914), B_1913) | ~v3_ordinal1(B_1913) | ~v3_ordinal1(k1_ordinal1(B_1914)))), inference(resolution, [status(thm)], [c_737, c_107])).
% 25.95/15.16  tff(c_49106, plain, (~r2_hidden('#skF_5', '#skF_4') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1(k1_ordinal1('#skF_4'))), inference(resolution, [status(thm)], [c_85, c_49076])).
% 25.95/15.16  tff(c_49116, plain, (~r2_hidden('#skF_5', '#skF_4') | ~v3_ordinal1(k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_49106])).
% 25.95/15.16  tff(c_49117, plain, (~v3_ordinal1(k1_ordinal1('#skF_4'))), inference(splitLeft, [status(thm)], [c_49116])).
% 25.95/15.16  tff(c_49120, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_49117])).
% 25.95/15.16  tff(c_49124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_49120])).
% 25.95/15.16  tff(c_49126, plain, (v3_ordinal1(k1_ordinal1('#skF_4'))), inference(splitRight, [status(thm)], [c_49116])).
% 25.95/15.16  tff(c_44, plain, (![B_21]: (r2_hidden(B_21, k1_ordinal1(B_21)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 25.95/15.16  tff(c_357, plain, (![C_74, B_75, A_76]: (r2_hidden(C_74, B_75) | ~r2_hidden(C_74, A_76) | ~r1_tarski(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_37])).
% 25.95/15.16  tff(c_375, plain, (![B_21, B_75]: (r2_hidden(B_21, B_75) | ~r1_tarski(k1_ordinal1(B_21), B_75))), inference(resolution, [status(thm)], [c_44, c_357])).
% 25.95/15.16  tff(c_58096, plain, (![B_1972, B_1973]: (r2_hidden(B_1972, B_1973) | ~r1_ordinal1(k1_ordinal1(B_1972), B_1973) | ~v3_ordinal1(B_1973) | ~v3_ordinal1(k1_ordinal1(B_1972)))), inference(resolution, [status(thm)], [c_737, c_375])).
% 25.95/15.16  tff(c_58130, plain, (r2_hidden('#skF_4', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1(k1_ordinal1('#skF_4'))), inference(resolution, [status(thm)], [c_85, c_58096])).
% 25.95/15.16  tff(c_58143, plain, (r2_hidden('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_49126, c_52, c_58130])).
% 25.95/15.16  tff(c_58145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_58143])).
% 25.95/15.16  tff(c_58146, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_62])).
% 25.95/15.16  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 25.95/15.16  tff(c_58153, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_58146, c_2])).
% 25.95/15.16  tff(c_58598, plain, (![B_2028, A_2029]: (r2_hidden(B_2028, A_2029) | r1_ordinal1(A_2029, B_2028) | ~v3_ordinal1(B_2028) | ~v3_ordinal1(A_2029))), inference(cnfTransformation, [status(thm)], [f_82])).
% 25.95/15.16  tff(c_42, plain, (![B_21, A_20]: (B_21=A_20 | r2_hidden(A_20, B_21) | ~r2_hidden(A_20, k1_ordinal1(B_21)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 25.95/15.16  tff(c_66137, plain, (![B_2416, B_2415]: (B_2416=B_2415 | r2_hidden(B_2416, B_2415) | r1_ordinal1(k1_ordinal1(B_2415), B_2416) | ~v3_ordinal1(B_2416) | ~v3_ordinal1(k1_ordinal1(B_2415)))), inference(resolution, [status(thm)], [c_58598, c_42])).
% 25.95/15.16  tff(c_58156, plain, (~r1_ordinal1(k1_ordinal1('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58146, c_56])).
% 25.95/15.16  tff(c_66146, plain, ('#skF_5'='#skF_4' | r2_hidden('#skF_5', '#skF_4') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1(k1_ordinal1('#skF_4'))), inference(resolution, [status(thm)], [c_66137, c_58156])).
% 25.95/15.16  tff(c_66155, plain, ('#skF_5'='#skF_4' | r2_hidden('#skF_5', '#skF_4') | ~v3_ordinal1(k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_66146])).
% 25.95/15.16  tff(c_66156, plain, ('#skF_5'='#skF_4' | ~v3_ordinal1(k1_ordinal1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58153, c_66155])).
% 25.95/15.16  tff(c_66157, plain, (~v3_ordinal1(k1_ordinal1('#skF_4'))), inference(splitLeft, [status(thm)], [c_66156])).
% 25.95/15.16  tff(c_66160, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_66157])).
% 25.95/15.16  tff(c_66164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_66160])).
% 25.95/15.16  tff(c_66165, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_66156])).
% 25.95/15.16  tff(c_58154, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_58146, c_50])).
% 25.95/15.16  tff(c_66211, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66165, c_58154])).
% 25.95/15.16  tff(c_66217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58399, c_66211])).
% 25.95/15.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.95/15.16  
% 25.95/15.16  Inference rules
% 25.95/15.16  ----------------------
% 25.95/15.16  #Ref     : 0
% 25.95/15.16  #Sup     : 13852
% 25.95/15.16  #Fact    : 64
% 25.95/15.16  #Define  : 0
% 25.95/15.16  #Split   : 5
% 25.95/15.16  #Chain   : 0
% 25.95/15.16  #Close   : 0
% 25.95/15.16  
% 25.95/15.16  Ordering : KBO
% 25.95/15.16  
% 25.95/15.16  Simplification rules
% 25.95/15.16  ----------------------
% 25.95/15.16  #Subsume      : 2891
% 25.95/15.16  #Demod        : 619
% 25.95/15.16  #Tautology    : 324
% 25.95/15.16  #SimpNegUnit  : 98
% 25.95/15.16  #BackRed      : 49
% 25.95/15.16  
% 25.95/15.16  #Partial instantiations: 0
% 25.95/15.16  #Strategies tried      : 1
% 25.95/15.16  
% 25.95/15.16  Timing (in seconds)
% 25.95/15.16  ----------------------
% 25.95/15.16  Preprocessing        : 0.29
% 25.95/15.16  Parsing              : 0.15
% 25.95/15.16  CNF conversion       : 0.02
% 25.95/15.16  Main loop            : 14.12
% 25.95/15.16  Inferencing          : 1.72
% 25.95/15.16  Reduction            : 3.87
% 25.95/15.16  Demodulation         : 1.80
% 25.95/15.16  BG Simplification    : 0.20
% 25.95/15.16  Subsumption          : 7.38
% 25.95/15.16  Abstraction          : 0.24
% 25.95/15.16  MUC search           : 0.00
% 25.95/15.16  Cooper               : 0.00
% 25.95/15.16  Total                : 14.45
% 25.95/15.16  Index Insertion      : 0.00
% 25.95/15.16  Index Deletion       : 0.00
% 25.95/15.16  Index Matching       : 0.00
% 25.95/15.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
