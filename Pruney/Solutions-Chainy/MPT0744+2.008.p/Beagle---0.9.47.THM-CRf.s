%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:15 EST 2020

% Result     : Theorem 17.78s
% Output     : CNFRefutation 17.78s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 114 expanded)
%              Number of leaves         :   21 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  100 ( 241 expanded)
%              Number of equality atoms :   10 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_77,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_86,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_50,plain,(
    ! [B_25] : r2_hidden(B_25,k1_ordinal1(B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_60,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_58,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_68,plain,
    ( r2_hidden('#skF_3',k1_ordinal1('#skF_4'))
    | r1_ordinal1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_126,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_842,plain,(
    ! [B_123,A_124] :
      ( r2_hidden(B_123,A_124)
      | r1_ordinal1(A_124,B_123)
      | ~ v3_ordinal1(B_123)
      | ~ v3_ordinal1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_52,plain,(
    ! [A_24,B_25] :
      ( ~ r2_hidden(A_24,B_25)
      | r2_hidden(A_24,k1_ordinal1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_62,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_174,plain,(
    ~ r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_62])).

tff(c_178,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_174])).

tff(c_916,plain,
    ( r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_842,c_178])).

tff(c_949,plain,(
    r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60,c_916])).

tff(c_46,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ r1_ordinal1(A_22,B_23)
      | ~ v3_ordinal1(B_23)
      | ~ v3_ordinal1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1065,plain,(
    ! [A_131,B_132] :
      ( r1_tarski(A_131,B_132)
      | ~ r1_ordinal1(A_131,B_132)
      | ~ v3_ordinal1(B_132)
      | ~ v3_ordinal1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6846,plain,(
    ! [B_465,A_466] :
      ( B_465 = A_466
      | ~ r1_tarski(B_465,A_466)
      | ~ r1_ordinal1(A_466,B_465)
      | ~ v3_ordinal1(B_465)
      | ~ v3_ordinal1(A_466) ) ),
    inference(resolution,[status(thm)],[c_1065,c_24])).

tff(c_32914,plain,(
    ! [B_1748,A_1749] :
      ( B_1748 = A_1749
      | ~ r1_ordinal1(B_1748,A_1749)
      | ~ r1_ordinal1(A_1749,B_1748)
      | ~ v3_ordinal1(B_1748)
      | ~ v3_ordinal1(A_1749) ) ),
    inference(resolution,[status(thm)],[c_46,c_6846])).

tff(c_32944,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_949,c_32914])).

tff(c_32965,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_126,c_32944])).

tff(c_32973,plain,(
    ~ r2_hidden('#skF_4',k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32965,c_174])).

tff(c_32978,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_32973])).

tff(c_32980,plain,(
    ~ r1_ordinal1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_33690,plain,(
    ! [B_1824,A_1825] :
      ( r2_hidden(B_1824,A_1825)
      | r1_ordinal1(A_1825,B_1824)
      | ~ v3_ordinal1(B_1824)
      | ~ v3_ordinal1(A_1825) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32979,plain,(
    r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_33597,plain,(
    ! [B_1816,A_1817] :
      ( B_1816 = A_1817
      | r2_hidden(A_1817,B_1816)
      | ~ r2_hidden(A_1817,k1_ordinal1(B_1816)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_33618,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_32979,c_33597])).

tff(c_33621,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_33618])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_33628,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_33621,c_2])).

tff(c_33701,plain,
    ( r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_33690,c_33628])).

tff(c_33781,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_33701])).

tff(c_33783,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32980,c_33781])).

tff(c_33784,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_33618])).

tff(c_33789,plain,(
    ~ r1_ordinal1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33784,c_32980])).

tff(c_33798,plain,(
    ! [B_1826,A_1827] :
      ( r2_hidden(B_1826,A_1827)
      | r1_ordinal1(A_1827,B_1826)
      | ~ v3_ordinal1(B_1826)
      | ~ v3_ordinal1(A_1827) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_33785,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_33618])).

tff(c_33797,plain,(
    ~ r2_hidden('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33784,c_33785])).

tff(c_33801,plain,
    ( r1_ordinal1('#skF_4','#skF_4')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_33798,c_33797])).

tff(c_33876,plain,(
    r1_ordinal1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_33801])).

tff(c_33878,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33789,c_33876])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:39:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.78/8.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.78/8.49  
% 17.78/8.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.78/8.49  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 17.78/8.49  
% 17.78/8.49  %Foreground sorts:
% 17.78/8.49  
% 17.78/8.49  
% 17.78/8.49  %Background operators:
% 17.78/8.49  
% 17.78/8.49  
% 17.78/8.49  %Foreground operators:
% 17.78/8.49  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 17.78/8.49  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 17.78/8.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.78/8.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.78/8.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 17.78/8.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.78/8.49  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 17.78/8.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.78/8.49  tff('#skF_3', type, '#skF_3': $i).
% 17.78/8.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 17.78/8.49  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 17.78/8.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.78/8.49  tff('#skF_4', type, '#skF_4': $i).
% 17.78/8.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.78/8.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 17.78/8.49  
% 17.78/8.50  tff(f_77, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 17.78/8.50  tff(f_101, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 17.78/8.50  tff(f_86, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 17.78/8.50  tff(f_71, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 17.78/8.50  tff(f_47, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 17.78/8.50  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 17.78/8.50  tff(c_50, plain, (![B_25]: (r2_hidden(B_25, k1_ordinal1(B_25)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 17.78/8.50  tff(c_60, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 17.78/8.50  tff(c_58, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 17.78/8.50  tff(c_68, plain, (r2_hidden('#skF_3', k1_ordinal1('#skF_4')) | r1_ordinal1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 17.78/8.50  tff(c_126, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_68])).
% 17.78/8.50  tff(c_842, plain, (![B_123, A_124]: (r2_hidden(B_123, A_124) | r1_ordinal1(A_124, B_123) | ~v3_ordinal1(B_123) | ~v3_ordinal1(A_124))), inference(cnfTransformation, [status(thm)], [f_86])).
% 17.78/8.50  tff(c_52, plain, (![A_24, B_25]: (~r2_hidden(A_24, B_25) | r2_hidden(A_24, k1_ordinal1(B_25)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 17.78/8.50  tff(c_62, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 17.78/8.50  tff(c_174, plain, (~r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_62])).
% 17.78/8.50  tff(c_178, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_174])).
% 17.78/8.50  tff(c_916, plain, (r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_842, c_178])).
% 17.78/8.50  tff(c_949, plain, (r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60, c_916])).
% 17.78/8.50  tff(c_46, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~r1_ordinal1(A_22, B_23) | ~v3_ordinal1(B_23) | ~v3_ordinal1(A_22))), inference(cnfTransformation, [status(thm)], [f_71])).
% 17.78/8.50  tff(c_1065, plain, (![A_131, B_132]: (r1_tarski(A_131, B_132) | ~r1_ordinal1(A_131, B_132) | ~v3_ordinal1(B_132) | ~v3_ordinal1(A_131))), inference(cnfTransformation, [status(thm)], [f_71])).
% 17.78/8.50  tff(c_24, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 17.78/8.50  tff(c_6846, plain, (![B_465, A_466]: (B_465=A_466 | ~r1_tarski(B_465, A_466) | ~r1_ordinal1(A_466, B_465) | ~v3_ordinal1(B_465) | ~v3_ordinal1(A_466))), inference(resolution, [status(thm)], [c_1065, c_24])).
% 17.78/8.50  tff(c_32914, plain, (![B_1748, A_1749]: (B_1748=A_1749 | ~r1_ordinal1(B_1748, A_1749) | ~r1_ordinal1(A_1749, B_1748) | ~v3_ordinal1(B_1748) | ~v3_ordinal1(A_1749))), inference(resolution, [status(thm)], [c_46, c_6846])).
% 17.78/8.50  tff(c_32944, plain, ('#skF_3'='#skF_4' | ~r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_949, c_32914])).
% 17.78/8.50  tff(c_32965, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_126, c_32944])).
% 17.78/8.50  tff(c_32973, plain, (~r2_hidden('#skF_4', k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32965, c_174])).
% 17.78/8.50  tff(c_32978, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_32973])).
% 17.78/8.50  tff(c_32980, plain, (~r1_ordinal1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_68])).
% 17.78/8.50  tff(c_33690, plain, (![B_1824, A_1825]: (r2_hidden(B_1824, A_1825) | r1_ordinal1(A_1825, B_1824) | ~v3_ordinal1(B_1824) | ~v3_ordinal1(A_1825))), inference(cnfTransformation, [status(thm)], [f_86])).
% 17.78/8.50  tff(c_32979, plain, (r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(splitRight, [status(thm)], [c_68])).
% 17.78/8.50  tff(c_33597, plain, (![B_1816, A_1817]: (B_1816=A_1817 | r2_hidden(A_1817, B_1816) | ~r2_hidden(A_1817, k1_ordinal1(B_1816)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 17.78/8.50  tff(c_33618, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_32979, c_33597])).
% 17.78/8.50  tff(c_33621, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_33618])).
% 17.78/8.50  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 17.78/8.50  tff(c_33628, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_33621, c_2])).
% 17.78/8.50  tff(c_33701, plain, (r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_33690, c_33628])).
% 17.78/8.50  tff(c_33781, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_33701])).
% 17.78/8.50  tff(c_33783, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32980, c_33781])).
% 17.78/8.50  tff(c_33784, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_33618])).
% 17.78/8.50  tff(c_33789, plain, (~r1_ordinal1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_33784, c_32980])).
% 17.78/8.50  tff(c_33798, plain, (![B_1826, A_1827]: (r2_hidden(B_1826, A_1827) | r1_ordinal1(A_1827, B_1826) | ~v3_ordinal1(B_1826) | ~v3_ordinal1(A_1827))), inference(cnfTransformation, [status(thm)], [f_86])).
% 17.78/8.50  tff(c_33785, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_33618])).
% 17.78/8.50  tff(c_33797, plain, (~r2_hidden('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_33784, c_33785])).
% 17.78/8.50  tff(c_33801, plain, (r1_ordinal1('#skF_4', '#skF_4') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_33798, c_33797])).
% 17.78/8.50  tff(c_33876, plain, (r1_ordinal1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_33801])).
% 17.78/8.50  tff(c_33878, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33789, c_33876])).
% 17.78/8.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.78/8.50  
% 17.78/8.50  Inference rules
% 17.78/8.50  ----------------------
% 17.78/8.50  #Ref     : 0
% 17.78/8.50  #Sup     : 7810
% 17.78/8.50  #Fact    : 46
% 17.78/8.50  #Define  : 0
% 17.78/8.50  #Split   : 3
% 17.78/8.50  #Chain   : 0
% 17.78/8.50  #Close   : 0
% 17.78/8.50  
% 17.78/8.50  Ordering : KBO
% 17.78/8.50  
% 17.78/8.50  Simplification rules
% 17.78/8.50  ----------------------
% 17.78/8.50  #Subsume      : 3386
% 17.78/8.50  #Demod        : 398
% 17.78/8.50  #Tautology    : 219
% 17.78/8.50  #SimpNegUnit  : 83
% 17.78/8.50  #BackRed      : 12
% 17.78/8.50  
% 17.78/8.50  #Partial instantiations: 0
% 17.78/8.50  #Strategies tried      : 1
% 17.78/8.50  
% 17.78/8.50  Timing (in seconds)
% 17.78/8.50  ----------------------
% 17.78/8.50  Preprocessing        : 0.32
% 17.78/8.50  Parsing              : 0.16
% 17.78/8.50  CNF conversion       : 0.02
% 17.78/8.50  Main loop            : 7.42
% 17.78/8.50  Inferencing          : 1.10
% 17.78/8.50  Reduction            : 2.58
% 17.78/8.50  Demodulation         : 1.26
% 17.78/8.50  BG Simplification    : 0.12
% 17.78/8.50  Subsumption          : 3.15
% 17.78/8.50  Abstraction          : 0.15
% 17.78/8.51  MUC search           : 0.00
% 17.78/8.51  Cooper               : 0.00
% 17.78/8.51  Total                : 7.77
% 17.78/8.51  Index Insertion      : 0.00
% 17.78/8.51  Index Deletion       : 0.00
% 17.78/8.51  Index Matching       : 0.00
% 17.78/8.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
