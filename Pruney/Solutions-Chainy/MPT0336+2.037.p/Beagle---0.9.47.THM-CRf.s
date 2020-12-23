%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:05 EST 2020

% Result     : Theorem 4.04s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 125 expanded)
%              Number of leaves         :   28 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :   95 ( 235 expanded)
%              Number of equality atoms :    9 (  23 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_78,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

tff(c_46,plain,(
    r1_xboole_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_62,plain,(
    ! [B_33,A_34] :
      ( r1_xboole_0(B_33,A_34)
      | ~ r1_xboole_0(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_65,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_62])).

tff(c_254,plain,(
    ! [A_77,C_78,B_79] :
      ( ~ r1_xboole_0(A_77,C_78)
      | ~ r1_xboole_0(A_77,B_79)
      | r1_xboole_0(A_77,k2_xboole_0(B_79,C_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( r1_xboole_0(B_9,A_8)
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_913,plain,(
    ! [B_1057,C_1058,A_1059] :
      ( r1_xboole_0(k2_xboole_0(B_1057,C_1058),A_1059)
      | ~ r1_xboole_0(A_1059,C_1058)
      | ~ r1_xboole_0(A_1059,B_1057) ) ),
    inference(resolution,[status(thm)],[c_254,c_10])).

tff(c_44,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_5','#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_928,plain,
    ( ~ r1_xboole_0('#skF_6','#skF_7')
    | ~ r1_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_913,c_44])).

tff(c_936,plain,(
    ~ r1_xboole_0('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_928])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_138,plain,(
    ! [A_50,B_51] :
      ( ~ r2_hidden('#skF_1'(A_50,B_51),B_51)
      | r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_143,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(resolution,[status(thm)],[c_8,c_138])).

tff(c_48,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_168,plain,(
    ! [C_63,B_64,A_65] :
      ( r2_hidden(C_63,B_64)
      | ~ r2_hidden(C_63,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_183,plain,(
    ! [B_64] :
      ( r2_hidden('#skF_8',B_64)
      | ~ r1_tarski('#skF_7',B_64) ) ),
    inference(resolution,[status(thm)],[c_48,c_168])).

tff(c_194,plain,(
    ! [A_68,B_69,C_70] :
      ( ~ r1_xboole_0(A_68,B_69)
      | ~ r2_hidden(C_70,B_69)
      | ~ r2_hidden(C_70,A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_201,plain,(
    ! [C_71] :
      ( ~ r2_hidden(C_71,'#skF_6')
      | ~ r2_hidden(C_71,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_46,c_194])).

tff(c_205,plain,
    ( ~ r2_hidden('#skF_8','#skF_6')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_183,c_201])).

tff(c_223,plain,(
    ~ r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_205])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_50,plain,(
    r1_tarski(k3_xboole_0('#skF_5','#skF_6'),k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_51,plain,(
    r1_tarski(k3_xboole_0('#skF_6','#skF_5'),k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_50])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_2'(A_10,B_11),A_10)
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1933,plain,(
    ! [A_2175,B_2176,B_2177] :
      ( r2_hidden('#skF_2'(A_2175,B_2176),B_2177)
      | ~ r1_tarski(A_2175,B_2177)
      | r1_xboole_0(A_2175,B_2176) ) ),
    inference(resolution,[status(thm)],[c_16,c_168])).

tff(c_26,plain,(
    ! [C_24,A_20] :
      ( C_24 = A_20
      | ~ r2_hidden(C_24,k1_tarski(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2163,plain,(
    ! [A_2345,A_2346,B_2347] :
      ( A_2345 = '#skF_2'(A_2346,B_2347)
      | ~ r1_tarski(A_2346,k1_tarski(A_2345))
      | r1_xboole_0(A_2346,B_2347) ) ),
    inference(resolution,[status(thm)],[c_1933,c_26])).

tff(c_2300,plain,(
    ! [B_2419] :
      ( '#skF_2'(k3_xboole_0('#skF_6','#skF_5'),B_2419) = '#skF_8'
      | r1_xboole_0(k3_xboole_0('#skF_6','#skF_5'),B_2419) ) ),
    inference(resolution,[status(thm)],[c_51,c_2163])).

tff(c_124,plain,(
    ! [A_43,B_44] :
      ( ~ r1_xboole_0(k3_xboole_0(A_43,B_44),B_44)
      | r1_xboole_0(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_130,plain,(
    ! [A_1,B_2] :
      ( ~ r1_xboole_0(k3_xboole_0(A_1,B_2),A_1)
      | r1_xboole_0(B_2,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_124])).

tff(c_2323,plain,
    ( r1_xboole_0('#skF_5','#skF_6')
    | '#skF_2'(k3_xboole_0('#skF_6','#skF_5'),'#skF_6') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2300,c_130])).

tff(c_2517,plain,(
    '#skF_2'(k3_xboole_0('#skF_6','#skF_5'),'#skF_6') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_2323])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_2'(A_10,B_11),B_11)
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2536,plain,
    ( r2_hidden('#skF_8','#skF_6')
    | r1_xboole_0(k3_xboole_0('#skF_6','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2517,c_14])).

tff(c_2541,plain,(
    r1_xboole_0(k3_xboole_0('#skF_6','#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_223,c_2536])).

tff(c_2553,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_2541,c_130])).

tff(c_2558,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_2553,c_10])).

tff(c_2563,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_936,c_2558])).

tff(c_2564,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_2323])).

tff(c_2587,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_2564,c_10])).

tff(c_2592,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_936,c_2587])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:18:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.04/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.04/1.74  
% 4.04/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.04/1.74  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 4.04/1.74  
% 4.04/1.74  %Foreground sorts:
% 4.04/1.74  
% 4.04/1.74  
% 4.04/1.74  %Background operators:
% 4.04/1.74  
% 4.04/1.74  
% 4.04/1.74  %Foreground operators:
% 4.04/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.04/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.04/1.74  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.04/1.74  tff('#skF_7', type, '#skF_7': $i).
% 4.04/1.74  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.04/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.04/1.74  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.04/1.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.04/1.74  tff('#skF_5', type, '#skF_5': $i).
% 4.04/1.74  tff('#skF_6', type, '#skF_6': $i).
% 4.04/1.74  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.04/1.74  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.04/1.74  tff('#skF_8', type, '#skF_8': $i).
% 4.04/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.04/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.04/1.74  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.04/1.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.04/1.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.04/1.74  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.04/1.74  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.04/1.74  
% 4.04/1.75  tff(f_100, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 4.04/1.75  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.04/1.75  tff(f_72, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 4.04/1.75  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.04/1.75  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.04/1.75  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.04/1.75  tff(f_85, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.04/1.75  tff(f_78, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 4.04/1.75  tff(c_46, plain, (r1_xboole_0('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.04/1.75  tff(c_62, plain, (![B_33, A_34]: (r1_xboole_0(B_33, A_34) | ~r1_xboole_0(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.04/1.75  tff(c_65, plain, (r1_xboole_0('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_46, c_62])).
% 4.04/1.75  tff(c_254, plain, (![A_77, C_78, B_79]: (~r1_xboole_0(A_77, C_78) | ~r1_xboole_0(A_77, B_79) | r1_xboole_0(A_77, k2_xboole_0(B_79, C_78)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.04/1.75  tff(c_10, plain, (![B_9, A_8]: (r1_xboole_0(B_9, A_8) | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.04/1.75  tff(c_913, plain, (![B_1057, C_1058, A_1059]: (r1_xboole_0(k2_xboole_0(B_1057, C_1058), A_1059) | ~r1_xboole_0(A_1059, C_1058) | ~r1_xboole_0(A_1059, B_1057))), inference(resolution, [status(thm)], [c_254, c_10])).
% 4.04/1.75  tff(c_44, plain, (~r1_xboole_0(k2_xboole_0('#skF_5', '#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.04/1.75  tff(c_928, plain, (~r1_xboole_0('#skF_6', '#skF_7') | ~r1_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_913, c_44])).
% 4.04/1.75  tff(c_936, plain, (~r1_xboole_0('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_928])).
% 4.04/1.75  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.04/1.75  tff(c_138, plain, (![A_50, B_51]: (~r2_hidden('#skF_1'(A_50, B_51), B_51) | r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.04/1.75  tff(c_143, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(resolution, [status(thm)], [c_8, c_138])).
% 4.04/1.75  tff(c_48, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.04/1.75  tff(c_168, plain, (![C_63, B_64, A_65]: (r2_hidden(C_63, B_64) | ~r2_hidden(C_63, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.04/1.75  tff(c_183, plain, (![B_64]: (r2_hidden('#skF_8', B_64) | ~r1_tarski('#skF_7', B_64))), inference(resolution, [status(thm)], [c_48, c_168])).
% 4.04/1.75  tff(c_194, plain, (![A_68, B_69, C_70]: (~r1_xboole_0(A_68, B_69) | ~r2_hidden(C_70, B_69) | ~r2_hidden(C_70, A_68))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.04/1.75  tff(c_201, plain, (![C_71]: (~r2_hidden(C_71, '#skF_6') | ~r2_hidden(C_71, '#skF_7'))), inference(resolution, [status(thm)], [c_46, c_194])).
% 4.04/1.75  tff(c_205, plain, (~r2_hidden('#skF_8', '#skF_6') | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_183, c_201])).
% 4.04/1.75  tff(c_223, plain, (~r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_205])).
% 4.04/1.75  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.04/1.75  tff(c_50, plain, (r1_tarski(k3_xboole_0('#skF_5', '#skF_6'), k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.04/1.75  tff(c_51, plain, (r1_tarski(k3_xboole_0('#skF_6', '#skF_5'), k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_50])).
% 4.04/1.75  tff(c_16, plain, (![A_10, B_11]: (r2_hidden('#skF_2'(A_10, B_11), A_10) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.04/1.75  tff(c_1933, plain, (![A_2175, B_2176, B_2177]: (r2_hidden('#skF_2'(A_2175, B_2176), B_2177) | ~r1_tarski(A_2175, B_2177) | r1_xboole_0(A_2175, B_2176))), inference(resolution, [status(thm)], [c_16, c_168])).
% 4.04/1.75  tff(c_26, plain, (![C_24, A_20]: (C_24=A_20 | ~r2_hidden(C_24, k1_tarski(A_20)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.04/1.75  tff(c_2163, plain, (![A_2345, A_2346, B_2347]: (A_2345='#skF_2'(A_2346, B_2347) | ~r1_tarski(A_2346, k1_tarski(A_2345)) | r1_xboole_0(A_2346, B_2347))), inference(resolution, [status(thm)], [c_1933, c_26])).
% 4.04/1.75  tff(c_2300, plain, (![B_2419]: ('#skF_2'(k3_xboole_0('#skF_6', '#skF_5'), B_2419)='#skF_8' | r1_xboole_0(k3_xboole_0('#skF_6', '#skF_5'), B_2419))), inference(resolution, [status(thm)], [c_51, c_2163])).
% 4.04/1.75  tff(c_124, plain, (![A_43, B_44]: (~r1_xboole_0(k3_xboole_0(A_43, B_44), B_44) | r1_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.04/1.75  tff(c_130, plain, (![A_1, B_2]: (~r1_xboole_0(k3_xboole_0(A_1, B_2), A_1) | r1_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_124])).
% 4.04/1.75  tff(c_2323, plain, (r1_xboole_0('#skF_5', '#skF_6') | '#skF_2'(k3_xboole_0('#skF_6', '#skF_5'), '#skF_6')='#skF_8'), inference(resolution, [status(thm)], [c_2300, c_130])).
% 4.04/1.75  tff(c_2517, plain, ('#skF_2'(k3_xboole_0('#skF_6', '#skF_5'), '#skF_6')='#skF_8'), inference(splitLeft, [status(thm)], [c_2323])).
% 4.04/1.75  tff(c_14, plain, (![A_10, B_11]: (r2_hidden('#skF_2'(A_10, B_11), B_11) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.04/1.75  tff(c_2536, plain, (r2_hidden('#skF_8', '#skF_6') | r1_xboole_0(k3_xboole_0('#skF_6', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2517, c_14])).
% 4.04/1.75  tff(c_2541, plain, (r1_xboole_0(k3_xboole_0('#skF_6', '#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_223, c_2536])).
% 4.04/1.75  tff(c_2553, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_2541, c_130])).
% 4.04/1.75  tff(c_2558, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_2553, c_10])).
% 4.04/1.75  tff(c_2563, plain, $false, inference(negUnitSimplification, [status(thm)], [c_936, c_2558])).
% 4.04/1.75  tff(c_2564, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_2323])).
% 4.04/1.75  tff(c_2587, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_2564, c_10])).
% 4.04/1.75  tff(c_2592, plain, $false, inference(negUnitSimplification, [status(thm)], [c_936, c_2587])).
% 4.04/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.04/1.75  
% 4.04/1.75  Inference rules
% 4.04/1.75  ----------------------
% 4.04/1.75  #Ref     : 0
% 4.04/1.75  #Sup     : 458
% 4.04/1.75  #Fact    : 0
% 4.04/1.75  #Define  : 0
% 4.04/1.75  #Split   : 7
% 4.04/1.75  #Chain   : 0
% 4.04/1.75  #Close   : 0
% 4.04/1.75  
% 4.04/1.75  Ordering : KBO
% 4.04/1.75  
% 4.04/1.75  Simplification rules
% 4.04/1.75  ----------------------
% 4.04/1.75  #Subsume      : 93
% 4.04/1.75  #Demod        : 27
% 4.04/1.75  #Tautology    : 61
% 4.04/1.75  #SimpNegUnit  : 11
% 4.04/1.75  #BackRed      : 0
% 4.04/1.75  
% 4.04/1.76  #Partial instantiations: 1638
% 4.04/1.76  #Strategies tried      : 1
% 4.04/1.76  
% 4.04/1.76  Timing (in seconds)
% 4.04/1.76  ----------------------
% 4.04/1.76  Preprocessing        : 0.32
% 4.04/1.76  Parsing              : 0.17
% 4.04/1.76  CNF conversion       : 0.02
% 4.04/1.76  Main loop            : 0.68
% 4.04/1.76  Inferencing          : 0.29
% 4.04/1.76  Reduction            : 0.17
% 4.04/1.76  Demodulation         : 0.11
% 4.04/1.76  BG Simplification    : 0.03
% 4.04/1.76  Subsumption          : 0.14
% 4.04/1.76  Abstraction          : 0.03
% 4.04/1.76  MUC search           : 0.00
% 4.04/1.76  Cooper               : 0.00
% 4.04/1.76  Total                : 1.03
% 4.04/1.76  Index Insertion      : 0.00
% 4.04/1.76  Index Deletion       : 0.00
% 4.04/1.76  Index Matching       : 0.00
% 4.04/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
