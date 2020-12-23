%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:13 EST 2020

% Result     : Theorem 4.91s
% Output     : CNFRefutation 5.24s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 103 expanded)
%              Number of leaves         :   29 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :   97 ( 183 expanded)
%              Number of equality atoms :   14 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_99,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_110,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

tff(c_109,plain,(
    ! [A_42,B_43] :
      ( r1_xboole_0(A_42,B_43)
      | k4_xboole_0(A_42,B_43) != A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    ! [B_43,A_42] :
      ( r1_xboole_0(B_43,A_42)
      | k4_xboole_0(A_42,B_43) != A_42 ) ),
    inference(resolution,[status(thm)],[c_109,c_4])).

tff(c_44,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_59,plain,(
    ! [B_36,A_37] :
      ( r1_xboole_0(B_36,A_37)
      | ~ r1_xboole_0(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_59])).

tff(c_725,plain,(
    ! [A_112,C_113,B_114] :
      ( ~ r1_xboole_0(A_112,C_113)
      | ~ r1_xboole_0(A_112,B_114)
      | r1_xboole_0(A_112,k2_xboole_0(B_114,C_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2510,plain,(
    ! [B_163,C_164,A_165] :
      ( r1_xboole_0(k2_xboole_0(B_163,C_164),A_165)
      | ~ r1_xboole_0(A_165,C_164)
      | ~ r1_xboole_0(A_165,B_163) ) ),
    inference(resolution,[status(thm)],[c_725,c_4])).

tff(c_42,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2538,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_2510,c_42])).

tff(c_2549,plain,(
    ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2538])).

tff(c_2560,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_115,c_2549])).

tff(c_46,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_392,plain,(
    ! [A_83,B_84,C_85] :
      ( ~ r1_xboole_0(A_83,B_84)
      | ~ r2_hidden(C_85,B_84)
      | ~ r2_hidden(C_85,A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_414,plain,(
    ! [C_86] :
      ( ~ r2_hidden(C_86,'#skF_4')
      | ~ r2_hidden(C_86,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_392])).

tff(c_428,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_414])).

tff(c_40,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,k1_tarski(B_34)) = A_33
      | r2_hidden(B_34,A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_30,plain,(
    ! [A_25,B_26] :
      ( r1_xboole_0(A_25,B_26)
      | k4_xboole_0(A_25,B_26) != A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_49,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_48])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_243,plain,(
    ! [A_64,B_65,C_66] :
      ( ~ r1_xboole_0(A_64,B_65)
      | ~ r2_hidden(C_66,k3_xboole_0(A_64,B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_254,plain,(
    ! [A_64,B_65,A_5] :
      ( ~ r1_xboole_0(A_64,B_65)
      | r1_xboole_0(A_5,k3_xboole_0(A_64,B_65)) ) ),
    inference(resolution,[status(thm)],[c_8,c_243])).

tff(c_793,plain,(
    ! [A_115,B_116,C_117] :
      ( ~ r1_xboole_0(A_115,k3_xboole_0(B_116,C_117))
      | ~ r1_tarski(A_115,C_117)
      | r1_xboole_0(A_115,B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1329,plain,(
    ! [A_128,B_129,A_130] :
      ( ~ r1_tarski(A_128,B_129)
      | r1_xboole_0(A_128,A_130)
      | ~ r1_xboole_0(A_130,B_129) ) ),
    inference(resolution,[status(thm)],[c_254,c_793])).

tff(c_1333,plain,(
    ! [A_131] :
      ( r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),A_131)
      | ~ r1_xboole_0(A_131,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_49,c_1329])).

tff(c_2345,plain,(
    ! [A_159] :
      ( r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),A_159)
      | k4_xboole_0(A_159,k1_tarski('#skF_6')) != A_159 ) ),
    inference(resolution,[status(thm)],[c_30,c_1333])).

tff(c_198,plain,(
    ! [A_55,B_56] :
      ( ~ r1_xboole_0(k3_xboole_0(A_55,B_56),B_56)
      | r1_xboole_0(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_212,plain,(
    ! [A_1,B_2] :
      ( ~ r1_xboole_0(k3_xboole_0(A_1,B_2),A_1)
      | r1_xboole_0(B_2,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_198])).

tff(c_2380,plain,
    ( r1_xboole_0('#skF_3','#skF_4')
    | k4_xboole_0('#skF_4',k1_tarski('#skF_6')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_2345,c_212])).

tff(c_3796,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_6')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2380])).

tff(c_3800,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_3796])).

tff(c_3804,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_428,c_3800])).

tff(c_3805,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_2380])).

tff(c_28,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = A_25
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3811,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3805,c_28])).

tff(c_3818,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2560,c_3811])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.91/1.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.91/1.98  
% 4.91/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.91/1.98  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.91/1.98  
% 4.91/1.98  %Foreground sorts:
% 4.91/1.98  
% 4.91/1.98  
% 4.91/1.98  %Background operators:
% 4.91/1.98  
% 4.91/1.98  
% 4.91/1.98  %Foreground operators:
% 4.91/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.91/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.91/1.98  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.91/1.98  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.91/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.91/1.98  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.91/1.98  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.91/1.98  tff('#skF_5', type, '#skF_5': $i).
% 4.91/1.98  tff('#skF_6', type, '#skF_6': $i).
% 4.91/1.98  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.91/1.98  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.91/1.98  tff('#skF_3', type, '#skF_3': $i).
% 4.91/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.91/1.98  tff('#skF_4', type, '#skF_4': $i).
% 4.91/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.91/1.98  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.91/1.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.91/1.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.91/1.98  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.91/1.98  
% 5.24/1.99  tff(f_99, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.24/1.99  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.24/1.99  tff(f_119, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 5.24/1.99  tff(f_81, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 5.24/1.99  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.24/1.99  tff(f_110, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 5.24/1.99  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.24/1.99  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.24/1.99  tff(f_95, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 5.24/1.99  tff(f_87, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 5.24/1.99  tff(c_109, plain, (![A_42, B_43]: (r1_xboole_0(A_42, B_43) | k4_xboole_0(A_42, B_43)!=A_42)), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.24/1.99  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.24/1.99  tff(c_115, plain, (![B_43, A_42]: (r1_xboole_0(B_43, A_42) | k4_xboole_0(A_42, B_43)!=A_42)), inference(resolution, [status(thm)], [c_109, c_4])).
% 5.24/1.99  tff(c_44, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.24/1.99  tff(c_59, plain, (![B_36, A_37]: (r1_xboole_0(B_36, A_37) | ~r1_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.24/1.99  tff(c_62, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_59])).
% 5.24/1.99  tff(c_725, plain, (![A_112, C_113, B_114]: (~r1_xboole_0(A_112, C_113) | ~r1_xboole_0(A_112, B_114) | r1_xboole_0(A_112, k2_xboole_0(B_114, C_113)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.24/1.99  tff(c_2510, plain, (![B_163, C_164, A_165]: (r1_xboole_0(k2_xboole_0(B_163, C_164), A_165) | ~r1_xboole_0(A_165, C_164) | ~r1_xboole_0(A_165, B_163))), inference(resolution, [status(thm)], [c_725, c_4])).
% 5.24/2.00  tff(c_42, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.24/2.00  tff(c_2538, plain, (~r1_xboole_0('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_2510, c_42])).
% 5.24/2.00  tff(c_2549, plain, (~r1_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2538])).
% 5.24/2.00  tff(c_2560, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(resolution, [status(thm)], [c_115, c_2549])).
% 5.24/2.00  tff(c_46, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.24/2.00  tff(c_392, plain, (![A_83, B_84, C_85]: (~r1_xboole_0(A_83, B_84) | ~r2_hidden(C_85, B_84) | ~r2_hidden(C_85, A_83))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.24/2.00  tff(c_414, plain, (![C_86]: (~r2_hidden(C_86, '#skF_4') | ~r2_hidden(C_86, '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_392])).
% 5.24/2.00  tff(c_428, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_414])).
% 5.24/2.00  tff(c_40, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k1_tarski(B_34))=A_33 | r2_hidden(B_34, A_33))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.24/2.00  tff(c_30, plain, (![A_25, B_26]: (r1_xboole_0(A_25, B_26) | k4_xboole_0(A_25, B_26)!=A_25)), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.24/2.00  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.24/2.00  tff(c_48, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.24/2.00  tff(c_49, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_48])).
% 5.24/2.00  tff(c_8, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.24/2.00  tff(c_243, plain, (![A_64, B_65, C_66]: (~r1_xboole_0(A_64, B_65) | ~r2_hidden(C_66, k3_xboole_0(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.24/2.00  tff(c_254, plain, (![A_64, B_65, A_5]: (~r1_xboole_0(A_64, B_65) | r1_xboole_0(A_5, k3_xboole_0(A_64, B_65)))), inference(resolution, [status(thm)], [c_8, c_243])).
% 5.24/2.00  tff(c_793, plain, (![A_115, B_116, C_117]: (~r1_xboole_0(A_115, k3_xboole_0(B_116, C_117)) | ~r1_tarski(A_115, C_117) | r1_xboole_0(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.24/2.00  tff(c_1329, plain, (![A_128, B_129, A_130]: (~r1_tarski(A_128, B_129) | r1_xboole_0(A_128, A_130) | ~r1_xboole_0(A_130, B_129))), inference(resolution, [status(thm)], [c_254, c_793])).
% 5.24/2.00  tff(c_1333, plain, (![A_131]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), A_131) | ~r1_xboole_0(A_131, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_49, c_1329])).
% 5.24/2.00  tff(c_2345, plain, (![A_159]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), A_159) | k4_xboole_0(A_159, k1_tarski('#skF_6'))!=A_159)), inference(resolution, [status(thm)], [c_30, c_1333])).
% 5.24/2.00  tff(c_198, plain, (![A_55, B_56]: (~r1_xboole_0(k3_xboole_0(A_55, B_56), B_56) | r1_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.24/2.00  tff(c_212, plain, (![A_1, B_2]: (~r1_xboole_0(k3_xboole_0(A_1, B_2), A_1) | r1_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_198])).
% 5.24/2.00  tff(c_2380, plain, (r1_xboole_0('#skF_3', '#skF_4') | k4_xboole_0('#skF_4', k1_tarski('#skF_6'))!='#skF_4'), inference(resolution, [status(thm)], [c_2345, c_212])).
% 5.24/2.00  tff(c_3796, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_6'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_2380])).
% 5.24/2.00  tff(c_3800, plain, (r2_hidden('#skF_6', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_40, c_3796])).
% 5.24/2.00  tff(c_3804, plain, $false, inference(negUnitSimplification, [status(thm)], [c_428, c_3800])).
% 5.24/2.00  tff(c_3805, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_2380])).
% 5.24/2.00  tff(c_28, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=A_25 | ~r1_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.24/2.00  tff(c_3811, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_3805, c_28])).
% 5.24/2.00  tff(c_3818, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2560, c_3811])).
% 5.24/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.24/2.00  
% 5.24/2.00  Inference rules
% 5.24/2.00  ----------------------
% 5.24/2.00  #Ref     : 0
% 5.24/2.00  #Sup     : 906
% 5.24/2.00  #Fact    : 0
% 5.24/2.00  #Define  : 0
% 5.24/2.00  #Split   : 6
% 5.24/2.00  #Chain   : 0
% 5.24/2.00  #Close   : 0
% 5.24/2.00  
% 5.24/2.00  Ordering : KBO
% 5.24/2.00  
% 5.24/2.00  Simplification rules
% 5.24/2.00  ----------------------
% 5.24/2.00  #Subsume      : 201
% 5.24/2.00  #Demod        : 328
% 5.24/2.00  #Tautology    : 319
% 5.24/2.00  #SimpNegUnit  : 22
% 5.24/2.00  #BackRed      : 3
% 5.24/2.00  
% 5.24/2.00  #Partial instantiations: 0
% 5.24/2.00  #Strategies tried      : 1
% 5.24/2.00  
% 5.24/2.00  Timing (in seconds)
% 5.24/2.00  ----------------------
% 5.24/2.00  Preprocessing        : 0.33
% 5.24/2.00  Parsing              : 0.18
% 5.24/2.00  CNF conversion       : 0.02
% 5.24/2.00  Main loop            : 0.85
% 5.24/2.00  Inferencing          : 0.26
% 5.24/2.00  Reduction            : 0.30
% 5.24/2.00  Demodulation         : 0.22
% 5.24/2.00  BG Simplification    : 0.03
% 5.24/2.00  Subsumption          : 0.18
% 5.24/2.00  Abstraction          : 0.04
% 5.24/2.00  MUC search           : 0.00
% 5.24/2.00  Cooper               : 0.00
% 5.24/2.00  Total                : 1.21
% 5.24/2.00  Index Insertion      : 0.00
% 5.24/2.00  Index Deletion       : 0.00
% 5.24/2.00  Index Matching       : 0.00
% 5.24/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
