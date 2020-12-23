%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:14 EST 2020

% Result     : Theorem 17.09s
% Output     : CNFRefutation 17.09s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 101 expanded)
%              Number of leaves         :   31 (  49 expanded)
%              Depth                    :    8
%              Number of atoms          :   89 ( 169 expanded)
%              Number of equality atoms :   22 (  33 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_4 > #skF_13 > #skF_5 > #skF_10 > #skF_2 > #skF_8 > #skF_7 > #skF_3 > #skF_1 > #skF_9 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_67,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r1_tarski(A,C) )
       => r1_tarski(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_97,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(A_58,B_59)
      | k4_xboole_0(A_58,B_59) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_82,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_12'),'#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_105,plain,(
    k4_xboole_0(k1_setfam_1('#skF_12'),'#skF_13') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_97,c_82])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_226,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_1'(A_89,B_90),A_89)
      | r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_261,plain,(
    ! [A_89] : r1_tarski(A_89,A_89) ),
    inference(resolution,[status(thm)],[c_226,c_4])).

tff(c_86,plain,(
    r2_hidden('#skF_11','#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_44739,plain,(
    ! [C_925,D_926,A_927] :
      ( r2_hidden(C_925,D_926)
      | ~ r2_hidden(D_926,A_927)
      | ~ r2_hidden(C_925,k1_setfam_1(A_927))
      | k1_xboole_0 = A_927 ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_44769,plain,(
    ! [C_925] :
      ( r2_hidden(C_925,'#skF_11')
      | ~ r2_hidden(C_925,k1_setfam_1('#skF_12'))
      | k1_xboole_0 = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_86,c_44739])).

tff(c_44821,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_44769])).

tff(c_409,plain,(
    ! [C_102,B_103,A_104] :
      ( r2_hidden(C_102,B_103)
      | ~ r2_hidden(C_102,A_104)
      | ~ r1_tarski(A_104,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_419,plain,(
    ! [B_105] :
      ( r2_hidden('#skF_11',B_105)
      | ~ r1_tarski('#skF_12',B_105) ) ),
    inference(resolution,[status(thm)],[c_86,c_409])).

tff(c_262,plain,(
    ! [A_91] : r1_tarski(A_91,A_91) ),
    inference(resolution,[status(thm)],[c_226,c_4])).

tff(c_52,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_336,plain,(
    ! [A_95] : k4_xboole_0(A_95,A_95) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_262,c_52])).

tff(c_28,plain,(
    ! [D_17,B_13,A_12] :
      ( ~ r2_hidden(D_17,B_13)
      | ~ r2_hidden(D_17,k4_xboole_0(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_390,plain,(
    ! [D_98,A_99] :
      ( ~ r2_hidden(D_98,A_99)
      | ~ r2_hidden(D_98,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_28])).

tff(c_399,plain,(
    ~ r2_hidden('#skF_11',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_86,c_390])).

tff(c_452,plain,(
    ~ r1_tarski('#skF_12',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_419,c_399])).

tff(c_44837,plain,(
    ~ r1_tarski('#skF_12','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44821,c_452])).

tff(c_44850,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_44837])).

tff(c_44853,plain,(
    ! [C_931] :
      ( r2_hidden(C_931,'#skF_11')
      | ~ r2_hidden(C_931,k1_setfam_1('#skF_12')) ) ),
    inference(splitRight,[status(thm)],[c_44769])).

tff(c_75558,plain,(
    ! [B_1572] :
      ( r2_hidden('#skF_1'(k1_setfam_1('#skF_12'),B_1572),'#skF_11')
      | r1_tarski(k1_setfam_1('#skF_12'),B_1572) ) ),
    inference(resolution,[status(thm)],[c_6,c_44853])).

tff(c_75579,plain,(
    r1_tarski(k1_setfam_1('#skF_12'),'#skF_11') ),
    inference(resolution,[status(thm)],[c_75558,c_4])).

tff(c_84,plain,(
    r1_tarski('#skF_11','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_110,plain,(
    ! [A_60,B_61] :
      ( k2_xboole_0(A_60,B_61) = B_61
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_118,plain,(
    k2_xboole_0('#skF_11','#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_84,c_110])).

tff(c_43928,plain,(
    ! [A_884,C_885,B_886] :
      ( r1_tarski(k2_xboole_0(A_884,C_885),k2_xboole_0(B_886,C_885))
      | ~ r1_tarski(A_884,B_886) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_44361,plain,(
    ! [A_906] :
      ( r1_tarski(k2_xboole_0(A_906,'#skF_13'),'#skF_13')
      | ~ r1_tarski(A_906,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_43928])).

tff(c_46,plain,(
    ! [A_21,B_22] :
      ( k2_xboole_0(A_21,B_22) = B_22
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_58815,plain,(
    ! [A_1282] :
      ( k2_xboole_0(k2_xboole_0(A_1282,'#skF_13'),'#skF_13') = '#skF_13'
      | ~ r1_tarski(A_1282,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_44361,c_46])).

tff(c_44,plain,(
    ! [A_18,C_20,B_19] :
      ( r1_tarski(A_18,C_20)
      | ~ r1_tarski(k2_xboole_0(A_18,B_19),C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_349,plain,(
    ! [A_96,B_97] : r1_tarski(A_96,k2_xboole_0(A_96,B_97)) ),
    inference(resolution,[status(thm)],[c_262,c_44])).

tff(c_44572,plain,(
    ! [A_918,B_919,B_920] : r1_tarski(A_918,k2_xboole_0(k2_xboole_0(A_918,B_919),B_920)) ),
    inference(resolution,[status(thm)],[c_349,c_44])).

tff(c_44630,plain,(
    ! [A_918,B_919,B_920] : k4_xboole_0(A_918,k2_xboole_0(k2_xboole_0(A_918,B_919),B_920)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44572,c_52])).

tff(c_58913,plain,(
    ! [A_1282] :
      ( k4_xboole_0(A_1282,'#skF_13') = k1_xboole_0
      | ~ r1_tarski(A_1282,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58815,c_44630])).

tff(c_75585,plain,(
    k4_xboole_0(k1_setfam_1('#skF_12'),'#skF_13') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_75579,c_58913])).

tff(c_75604,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_75585])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.09/9.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.09/9.36  
% 17.09/9.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.09/9.36  %$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_4 > #skF_13 > #skF_5 > #skF_10 > #skF_2 > #skF_8 > #skF_7 > #skF_3 > #skF_1 > #skF_9 > #skF_12
% 17.09/9.36  
% 17.09/9.36  %Foreground sorts:
% 17.09/9.36  
% 17.09/9.36  
% 17.09/9.36  %Background operators:
% 17.09/9.36  
% 17.09/9.36  
% 17.09/9.36  %Foreground operators:
% 17.09/9.36  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 17.09/9.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.09/9.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.09/9.36  tff('#skF_11', type, '#skF_11': $i).
% 17.09/9.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.09/9.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.09/9.36  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 17.09/9.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.09/9.36  tff('#skF_13', type, '#skF_13': $i).
% 17.09/9.36  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 17.09/9.36  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 17.09/9.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 17.09/9.36  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 17.09/9.36  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 17.09/9.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.09/9.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 17.09/9.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.09/9.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.09/9.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 17.09/9.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.09/9.36  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 17.09/9.36  tff('#skF_12', type, '#skF_12': $i).
% 17.09/9.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 17.09/9.36  
% 17.09/9.38  tff(f_67, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 17.09/9.38  tff(f_110, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r1_tarski(A, C)) => r1_tarski(k1_setfam_1(B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_setfam_1)).
% 17.09/9.38  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 17.09/9.38  tff(f_103, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 17.09/9.38  tff(f_51, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 17.09/9.38  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 17.09/9.38  tff(f_71, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_xboole_1)).
% 17.09/9.38  tff(f_55, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 17.09/9.38  tff(c_97, plain, (![A_58, B_59]: (r1_tarski(A_58, B_59) | k4_xboole_0(A_58, B_59)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 17.09/9.38  tff(c_82, plain, (~r1_tarski(k1_setfam_1('#skF_12'), '#skF_13')), inference(cnfTransformation, [status(thm)], [f_110])).
% 17.09/9.38  tff(c_105, plain, (k4_xboole_0(k1_setfam_1('#skF_12'), '#skF_13')!=k1_xboole_0), inference(resolution, [status(thm)], [c_97, c_82])).
% 17.09/9.38  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.09/9.38  tff(c_226, plain, (![A_89, B_90]: (r2_hidden('#skF_1'(A_89, B_90), A_89) | r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.09/9.38  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.09/9.38  tff(c_261, plain, (![A_89]: (r1_tarski(A_89, A_89))), inference(resolution, [status(thm)], [c_226, c_4])).
% 17.09/9.38  tff(c_86, plain, (r2_hidden('#skF_11', '#skF_12')), inference(cnfTransformation, [status(thm)], [f_110])).
% 17.09/9.38  tff(c_44739, plain, (![C_925, D_926, A_927]: (r2_hidden(C_925, D_926) | ~r2_hidden(D_926, A_927) | ~r2_hidden(C_925, k1_setfam_1(A_927)) | k1_xboole_0=A_927)), inference(cnfTransformation, [status(thm)], [f_103])).
% 17.09/9.38  tff(c_44769, plain, (![C_925]: (r2_hidden(C_925, '#skF_11') | ~r2_hidden(C_925, k1_setfam_1('#skF_12')) | k1_xboole_0='#skF_12')), inference(resolution, [status(thm)], [c_86, c_44739])).
% 17.09/9.38  tff(c_44821, plain, (k1_xboole_0='#skF_12'), inference(splitLeft, [status(thm)], [c_44769])).
% 17.09/9.38  tff(c_409, plain, (![C_102, B_103, A_104]: (r2_hidden(C_102, B_103) | ~r2_hidden(C_102, A_104) | ~r1_tarski(A_104, B_103))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.09/9.38  tff(c_419, plain, (![B_105]: (r2_hidden('#skF_11', B_105) | ~r1_tarski('#skF_12', B_105))), inference(resolution, [status(thm)], [c_86, c_409])).
% 17.09/9.38  tff(c_262, plain, (![A_91]: (r1_tarski(A_91, A_91))), inference(resolution, [status(thm)], [c_226, c_4])).
% 17.09/9.38  tff(c_52, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_67])).
% 17.09/9.38  tff(c_336, plain, (![A_95]: (k4_xboole_0(A_95, A_95)=k1_xboole_0)), inference(resolution, [status(thm)], [c_262, c_52])).
% 17.09/9.38  tff(c_28, plain, (![D_17, B_13, A_12]: (~r2_hidden(D_17, B_13) | ~r2_hidden(D_17, k4_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.09/9.38  tff(c_390, plain, (![D_98, A_99]: (~r2_hidden(D_98, A_99) | ~r2_hidden(D_98, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_336, c_28])).
% 17.09/9.38  tff(c_399, plain, (~r2_hidden('#skF_11', k1_xboole_0)), inference(resolution, [status(thm)], [c_86, c_390])).
% 17.09/9.38  tff(c_452, plain, (~r1_tarski('#skF_12', k1_xboole_0)), inference(resolution, [status(thm)], [c_419, c_399])).
% 17.09/9.38  tff(c_44837, plain, (~r1_tarski('#skF_12', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_44821, c_452])).
% 17.09/9.38  tff(c_44850, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_261, c_44837])).
% 17.09/9.38  tff(c_44853, plain, (![C_931]: (r2_hidden(C_931, '#skF_11') | ~r2_hidden(C_931, k1_setfam_1('#skF_12')))), inference(splitRight, [status(thm)], [c_44769])).
% 17.09/9.38  tff(c_75558, plain, (![B_1572]: (r2_hidden('#skF_1'(k1_setfam_1('#skF_12'), B_1572), '#skF_11') | r1_tarski(k1_setfam_1('#skF_12'), B_1572))), inference(resolution, [status(thm)], [c_6, c_44853])).
% 17.09/9.38  tff(c_75579, plain, (r1_tarski(k1_setfam_1('#skF_12'), '#skF_11')), inference(resolution, [status(thm)], [c_75558, c_4])).
% 17.09/9.38  tff(c_84, plain, (r1_tarski('#skF_11', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_110])).
% 17.09/9.38  tff(c_110, plain, (![A_60, B_61]: (k2_xboole_0(A_60, B_61)=B_61 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_59])).
% 17.09/9.38  tff(c_118, plain, (k2_xboole_0('#skF_11', '#skF_13')='#skF_13'), inference(resolution, [status(thm)], [c_84, c_110])).
% 17.09/9.38  tff(c_43928, plain, (![A_884, C_885, B_886]: (r1_tarski(k2_xboole_0(A_884, C_885), k2_xboole_0(B_886, C_885)) | ~r1_tarski(A_884, B_886))), inference(cnfTransformation, [status(thm)], [f_71])).
% 17.09/9.38  tff(c_44361, plain, (![A_906]: (r1_tarski(k2_xboole_0(A_906, '#skF_13'), '#skF_13') | ~r1_tarski(A_906, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_118, c_43928])).
% 17.09/9.38  tff(c_46, plain, (![A_21, B_22]: (k2_xboole_0(A_21, B_22)=B_22 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_59])).
% 17.09/9.38  tff(c_58815, plain, (![A_1282]: (k2_xboole_0(k2_xboole_0(A_1282, '#skF_13'), '#skF_13')='#skF_13' | ~r1_tarski(A_1282, '#skF_11'))), inference(resolution, [status(thm)], [c_44361, c_46])).
% 17.09/9.38  tff(c_44, plain, (![A_18, C_20, B_19]: (r1_tarski(A_18, C_20) | ~r1_tarski(k2_xboole_0(A_18, B_19), C_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 17.09/9.38  tff(c_349, plain, (![A_96, B_97]: (r1_tarski(A_96, k2_xboole_0(A_96, B_97)))), inference(resolution, [status(thm)], [c_262, c_44])).
% 17.09/9.38  tff(c_44572, plain, (![A_918, B_919, B_920]: (r1_tarski(A_918, k2_xboole_0(k2_xboole_0(A_918, B_919), B_920)))), inference(resolution, [status(thm)], [c_349, c_44])).
% 17.09/9.38  tff(c_44630, plain, (![A_918, B_919, B_920]: (k4_xboole_0(A_918, k2_xboole_0(k2_xboole_0(A_918, B_919), B_920))=k1_xboole_0)), inference(resolution, [status(thm)], [c_44572, c_52])).
% 17.09/9.38  tff(c_58913, plain, (![A_1282]: (k4_xboole_0(A_1282, '#skF_13')=k1_xboole_0 | ~r1_tarski(A_1282, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_58815, c_44630])).
% 17.09/9.38  tff(c_75585, plain, (k4_xboole_0(k1_setfam_1('#skF_12'), '#skF_13')=k1_xboole_0), inference(resolution, [status(thm)], [c_75579, c_58913])).
% 17.09/9.38  tff(c_75604, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_75585])).
% 17.09/9.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.09/9.38  
% 17.09/9.38  Inference rules
% 17.09/9.38  ----------------------
% 17.09/9.38  #Ref     : 0
% 17.09/9.38  #Sup     : 18248
% 17.09/9.38  #Fact    : 0
% 17.09/9.38  #Define  : 0
% 17.09/9.38  #Split   : 9
% 17.09/9.38  #Chain   : 0
% 17.09/9.38  #Close   : 0
% 17.09/9.38  
% 17.09/9.38  Ordering : KBO
% 17.09/9.38  
% 17.09/9.38  Simplification rules
% 17.09/9.38  ----------------------
% 17.09/9.38  #Subsume      : 3821
% 17.09/9.38  #Demod        : 11853
% 17.09/9.38  #Tautology    : 9282
% 17.09/9.38  #SimpNegUnit  : 139
% 17.09/9.38  #BackRed      : 190
% 17.09/9.38  
% 17.09/9.38  #Partial instantiations: 0
% 17.09/9.38  #Strategies tried      : 1
% 17.09/9.38  
% 17.09/9.38  Timing (in seconds)
% 17.09/9.38  ----------------------
% 17.09/9.38  Preprocessing        : 0.32
% 17.09/9.38  Parsing              : 0.17
% 17.09/9.38  CNF conversion       : 0.03
% 17.09/9.38  Main loop            : 8.30
% 17.09/9.38  Inferencing          : 1.50
% 17.09/9.38  Reduction            : 3.74
% 17.09/9.38  Demodulation         : 3.00
% 17.09/9.38  BG Simplification    : 0.14
% 17.09/9.38  Subsumption          : 2.48
% 17.09/9.38  Abstraction          : 0.19
% 17.09/9.38  MUC search           : 0.00
% 17.09/9.38  Cooper               : 0.00
% 17.09/9.38  Total                : 8.65
% 17.09/9.38  Index Insertion      : 0.00
% 17.09/9.38  Index Deletion       : 0.00
% 17.09/9.38  Index Matching       : 0.00
% 17.09/9.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
