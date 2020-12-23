%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:17 EST 2020

% Result     : Theorem 8.24s
% Output     : CNFRefutation 8.24s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 130 expanded)
%              Number of leaves         :   25 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :   98 ( 272 expanded)
%              Number of equality atoms :   10 (  28 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_79,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_94,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_108,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_103,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_54,plain,(
    ! [B_27] : r2_hidden(B_27,k1_ordinal1(B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_66,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_64,plain,(
    v3_ordinal1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_68,plain,
    ( ~ r1_ordinal1('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_101,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_74,plain,
    ( r2_hidden('#skF_6',k1_ordinal1('#skF_7'))
    | r1_ordinal1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_113,plain,(
    r1_ordinal1('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_74])).

tff(c_50,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ r1_ordinal1(A_24,B_25)
      | ~ v3_ordinal1(B_25)
      | ~ v3_ordinal1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1583,plain,(
    ! [B_206,A_207] :
      ( r2_hidden(B_206,A_207)
      | B_206 = A_207
      | r2_hidden(A_207,B_206)
      | ~ v3_ordinal1(B_206)
      | ~ v3_ordinal1(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_62,plain,(
    ! [B_35,A_34] :
      ( ~ r1_tarski(B_35,A_34)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_9985,plain,(
    ! [B_518,A_519] :
      ( ~ r1_tarski(B_518,A_519)
      | r2_hidden(B_518,A_519)
      | B_518 = A_519
      | ~ v3_ordinal1(B_518)
      | ~ v3_ordinal1(A_519) ) ),
    inference(resolution,[status(thm)],[c_1583,c_62])).

tff(c_114,plain,(
    ! [A_50,B_51] :
      ( ~ r2_hidden(A_50,B_51)
      | r2_hidden(A_50,k1_ordinal1(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_132,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_114,c_101])).

tff(c_10490,plain,
    ( ~ r1_tarski('#skF_6','#skF_7')
    | '#skF_7' = '#skF_6'
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_9985,c_132])).

tff(c_10651,plain,
    ( ~ r1_tarski('#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_10490])).

tff(c_10661,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_10651])).

tff(c_10664,plain,
    ( ~ r1_ordinal1('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_10661])).

tff(c_10668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_113,c_10664])).

tff(c_10669,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_10651])).

tff(c_10678,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10669,c_101])).

tff(c_10683,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_10678])).

tff(c_10684,plain,(
    ~ r1_ordinal1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_11284,plain,(
    ! [B_592,A_593] :
      ( r2_hidden(B_592,A_593)
      | r1_ordinal1(A_593,B_592)
      | ~ v3_ordinal1(B_592)
      | ~ v3_ordinal1(A_593) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_10685,plain,(
    r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_11134,plain,(
    ! [B_573,A_574] :
      ( B_573 = A_574
      | r2_hidden(A_574,B_573)
      | ~ r2_hidden(A_574,k1_ordinal1(B_573)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_11150,plain,
    ( '#skF_7' = '#skF_6'
    | r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_10685,c_11134])).

tff(c_11153,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_11150])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_11160,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_11153,c_2])).

tff(c_11304,plain,
    ( r1_ordinal1('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_11284,c_11160])).

tff(c_11416,plain,(
    r1_ordinal1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_11304])).

tff(c_11418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10684,c_11416])).

tff(c_11419,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_11150])).

tff(c_11424,plain,(
    ~ r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11419,c_10684])).

tff(c_11565,plain,(
    ! [B_614,A_615] :
      ( r2_hidden(B_614,A_615)
      | r1_ordinal1(A_615,B_614)
      | ~ v3_ordinal1(B_614)
      | ~ v3_ordinal1(A_615) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_11420,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_11150])).

tff(c_11432,plain,(
    ~ r2_hidden('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11419,c_11420])).

tff(c_11588,plain,
    ( r1_ordinal1('#skF_6','#skF_6')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_11565,c_11432])).

tff(c_11696,plain,(
    r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_11588])).

tff(c_11698,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11424,c_11696])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:57:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.24/3.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.24/3.02  
% 8.24/3.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.24/3.03  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 8.24/3.03  
% 8.24/3.03  %Foreground sorts:
% 8.24/3.03  
% 8.24/3.03  
% 8.24/3.03  %Background operators:
% 8.24/3.03  
% 8.24/3.03  
% 8.24/3.03  %Foreground operators:
% 8.24/3.03  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 8.24/3.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.24/3.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.24/3.03  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.24/3.03  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.24/3.03  tff('#skF_7', type, '#skF_7': $i).
% 8.24/3.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.24/3.03  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 8.24/3.03  tff('#skF_6', type, '#skF_6': $i).
% 8.24/3.03  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.24/3.03  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 8.24/3.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.24/3.03  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.24/3.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.24/3.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.24/3.03  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.24/3.03  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.24/3.03  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.24/3.03  
% 8.24/3.04  tff(f_79, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 8.24/3.04  tff(f_118, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 8.24/3.04  tff(f_73, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 8.24/3.04  tff(f_94, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 8.24/3.04  tff(f_108, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.24/3.04  tff(f_103, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 8.24/3.04  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 8.24/3.04  tff(c_54, plain, (![B_27]: (r2_hidden(B_27, k1_ordinal1(B_27)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.24/3.04  tff(c_66, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.24/3.04  tff(c_64, plain, (v3_ordinal1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.24/3.04  tff(c_68, plain, (~r1_ordinal1('#skF_6', '#skF_7') | ~r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.24/3.04  tff(c_101, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(splitLeft, [status(thm)], [c_68])).
% 8.24/3.04  tff(c_74, plain, (r2_hidden('#skF_6', k1_ordinal1('#skF_7')) | r1_ordinal1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.24/3.04  tff(c_113, plain, (r1_ordinal1('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_101, c_74])).
% 8.24/3.04  tff(c_50, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~r1_ordinal1(A_24, B_25) | ~v3_ordinal1(B_25) | ~v3_ordinal1(A_24))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.24/3.04  tff(c_1583, plain, (![B_206, A_207]: (r2_hidden(B_206, A_207) | B_206=A_207 | r2_hidden(A_207, B_206) | ~v3_ordinal1(B_206) | ~v3_ordinal1(A_207))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.24/3.04  tff(c_62, plain, (![B_35, A_34]: (~r1_tarski(B_35, A_34) | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.24/3.04  tff(c_9985, plain, (![B_518, A_519]: (~r1_tarski(B_518, A_519) | r2_hidden(B_518, A_519) | B_518=A_519 | ~v3_ordinal1(B_518) | ~v3_ordinal1(A_519))), inference(resolution, [status(thm)], [c_1583, c_62])).
% 8.24/3.04  tff(c_114, plain, (![A_50, B_51]: (~r2_hidden(A_50, B_51) | r2_hidden(A_50, k1_ordinal1(B_51)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.24/3.04  tff(c_132, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_114, c_101])).
% 8.24/3.04  tff(c_10490, plain, (~r1_tarski('#skF_6', '#skF_7') | '#skF_7'='#skF_6' | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_9985, c_132])).
% 8.24/3.04  tff(c_10651, plain, (~r1_tarski('#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_66, c_10490])).
% 8.24/3.04  tff(c_10661, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_10651])).
% 8.24/3.04  tff(c_10664, plain, (~r1_ordinal1('#skF_6', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_10661])).
% 8.24/3.04  tff(c_10668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_113, c_10664])).
% 8.24/3.04  tff(c_10669, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_10651])).
% 8.24/3.04  tff(c_10678, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_10669, c_101])).
% 8.24/3.04  tff(c_10683, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_10678])).
% 8.24/3.04  tff(c_10684, plain, (~r1_ordinal1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_68])).
% 8.24/3.04  tff(c_11284, plain, (![B_592, A_593]: (r2_hidden(B_592, A_593) | r1_ordinal1(A_593, B_592) | ~v3_ordinal1(B_592) | ~v3_ordinal1(A_593))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.24/3.04  tff(c_10685, plain, (r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(splitRight, [status(thm)], [c_68])).
% 8.24/3.04  tff(c_11134, plain, (![B_573, A_574]: (B_573=A_574 | r2_hidden(A_574, B_573) | ~r2_hidden(A_574, k1_ordinal1(B_573)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.24/3.04  tff(c_11150, plain, ('#skF_7'='#skF_6' | r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_10685, c_11134])).
% 8.24/3.04  tff(c_11153, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_11150])).
% 8.24/3.04  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 8.24/3.04  tff(c_11160, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_11153, c_2])).
% 8.24/3.04  tff(c_11304, plain, (r1_ordinal1('#skF_6', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_11284, c_11160])).
% 8.24/3.04  tff(c_11416, plain, (r1_ordinal1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_11304])).
% 8.24/3.04  tff(c_11418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10684, c_11416])).
% 8.24/3.04  tff(c_11419, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_11150])).
% 8.24/3.04  tff(c_11424, plain, (~r1_ordinal1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11419, c_10684])).
% 8.24/3.04  tff(c_11565, plain, (![B_614, A_615]: (r2_hidden(B_614, A_615) | r1_ordinal1(A_615, B_614) | ~v3_ordinal1(B_614) | ~v3_ordinal1(A_615))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.24/3.04  tff(c_11420, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_11150])).
% 8.24/3.04  tff(c_11432, plain, (~r2_hidden('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11419, c_11420])).
% 8.24/3.04  tff(c_11588, plain, (r1_ordinal1('#skF_6', '#skF_6') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_11565, c_11432])).
% 8.24/3.04  tff(c_11696, plain, (r1_ordinal1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_11588])).
% 8.24/3.04  tff(c_11698, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11424, c_11696])).
% 8.24/3.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.24/3.04  
% 8.24/3.04  Inference rules
% 8.24/3.04  ----------------------
% 8.24/3.04  #Ref     : 0
% 8.24/3.04  #Sup     : 2400
% 8.24/3.04  #Fact    : 8
% 8.24/3.04  #Define  : 0
% 8.24/3.04  #Split   : 7
% 8.24/3.04  #Chain   : 0
% 8.24/3.04  #Close   : 0
% 8.24/3.04  
% 8.24/3.04  Ordering : KBO
% 8.24/3.04  
% 8.24/3.04  Simplification rules
% 8.24/3.04  ----------------------
% 8.24/3.04  #Subsume      : 362
% 8.24/3.04  #Demod        : 92
% 8.24/3.04  #Tautology    : 111
% 8.24/3.04  #SimpNegUnit  : 67
% 8.24/3.04  #BackRed      : 14
% 8.24/3.04  
% 8.24/3.04  #Partial instantiations: 0
% 8.24/3.04  #Strategies tried      : 1
% 8.24/3.04  
% 8.24/3.04  Timing (in seconds)
% 8.24/3.04  ----------------------
% 8.24/3.04  Preprocessing        : 0.28
% 8.24/3.04  Parsing              : 0.14
% 8.24/3.04  CNF conversion       : 0.02
% 8.24/3.04  Main loop            : 1.93
% 8.24/3.04  Inferencing          : 0.51
% 8.24/3.04  Reduction            : 0.51
% 8.24/3.04  Demodulation         : 0.26
% 8.24/3.04  BG Simplification    : 0.07
% 8.24/3.04  Subsumption          : 0.67
% 8.24/3.04  Abstraction          : 0.08
% 8.24/3.04  MUC search           : 0.00
% 8.24/3.04  Cooper               : 0.00
% 8.24/3.04  Total                : 2.24
% 8.24/3.04  Index Insertion      : 0.00
% 8.24/3.04  Index Deletion       : 0.00
% 8.24/3.04  Index Matching       : 0.00
% 8.24/3.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
