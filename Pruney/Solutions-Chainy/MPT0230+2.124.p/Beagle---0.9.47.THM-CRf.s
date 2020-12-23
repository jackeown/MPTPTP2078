%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:11 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   58 (  99 expanded)
%              Number of leaves         :   28 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 153 expanded)
%              Number of equality atoms :   29 (  67 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_58,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_56,plain,(
    '#skF_6' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_40,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_71,plain,(
    ! [D_32,B_33] : r2_hidden(D_32,k2_tarski(D_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_74,plain,(
    ! [A_18] : r2_hidden(A_18,k1_tarski(A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_71])).

tff(c_81,plain,(
    ! [B_37,A_38] :
      ( ~ r2_hidden(B_37,A_38)
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    ! [A_18] : ~ v1_xboole_0(k1_tarski(A_18)) ),
    inference(resolution,[status(thm)],[c_74,c_81])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_142,plain,(
    ! [D_51,B_52,A_53] :
      ( D_51 = B_52
      | D_51 = A_53
      | ~ r2_hidden(D_51,k2_tarski(A_53,B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_163,plain,(
    ! [D_54,A_55] :
      ( D_54 = A_55
      | D_54 = A_55
      | ~ r2_hidden(D_54,k1_tarski(A_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_142])).

tff(c_167,plain,(
    ! [A_55] :
      ( '#skF_1'(k1_tarski(A_55)) = A_55
      | v1_xboole_0(k1_tarski(A_55)) ) ),
    inference(resolution,[status(thm)],[c_4,c_163])).

tff(c_173,plain,(
    ! [A_55] : '#skF_1'(k1_tarski(A_55)) = A_55 ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_167])).

tff(c_52,plain,(
    ! [B_29,C_30] :
      ( k4_xboole_0(k2_tarski(B_29,B_29),C_30) = k1_tarski(B_29)
      | r2_hidden(B_29,C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_61,plain,(
    ! [B_29,C_30] :
      ( k4_xboole_0(k1_tarski(B_29),C_30) = k1_tarski(B_29)
      | r2_hidden(B_29,C_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_52])).

tff(c_60,plain,(
    r1_tarski(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_112,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,B_46) = A_45
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_116,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6')) = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_112])).

tff(c_18,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_138,plain,(
    k5_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) = k4_xboole_0(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_18])).

tff(c_343,plain,(
    ! [A_87,C_88,B_89] :
      ( ~ r2_hidden(A_87,C_88)
      | ~ r2_hidden(A_87,B_89)
      | ~ r2_hidden(A_87,k5_xboole_0(B_89,C_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_426,plain,(
    ! [A_108] :
      ( ~ r2_hidden(A_108,k1_tarski('#skF_4'))
      | ~ r2_hidden(A_108,k1_tarski('#skF_4'))
      | ~ r2_hidden(A_108,k4_xboole_0(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_343])).

tff(c_429,plain,(
    ! [A_108] :
      ( ~ r2_hidden(A_108,k1_tarski('#skF_4'))
      | ~ r2_hidden(A_108,k1_tarski('#skF_4'))
      | ~ r2_hidden(A_108,k1_tarski('#skF_4'))
      | r2_hidden('#skF_4',k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_426])).

tff(c_1603,plain,(
    ! [A_1814] :
      ( ~ r2_hidden(A_1814,k1_tarski('#skF_4'))
      | ~ r2_hidden(A_1814,k1_tarski('#skF_4'))
      | ~ r2_hidden(A_1814,k1_tarski('#skF_4')) ) ),
    inference(splitLeft,[status(thm)],[c_429])).

tff(c_1624,plain,
    ( ~ r2_hidden('#skF_1'(k1_tarski('#skF_4')),k1_tarski('#skF_4'))
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_1603])).

tff(c_1637,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_173,c_1624])).

tff(c_1639,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1637])).

tff(c_1640,plain,(
    r2_hidden('#skF_4',k2_tarski('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_429])).

tff(c_22,plain,(
    ! [D_17,B_13,A_12] :
      ( D_17 = B_13
      | D_17 = A_12
      | ~ r2_hidden(D_17,k2_tarski(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1643,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1640,c_22])).

tff(c_1650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_56,c_1643])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:58:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.57  
% 3.38/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.57  %$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 3.38/1.57  
% 3.38/1.57  %Foreground sorts:
% 3.38/1.57  
% 3.38/1.57  
% 3.38/1.57  %Background operators:
% 3.38/1.57  
% 3.38/1.57  
% 3.38/1.57  %Foreground operators:
% 3.38/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.38/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.38/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.38/1.57  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.38/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.38/1.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.38/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.38/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.38/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.38/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.38/1.57  tff('#skF_6', type, '#skF_6': $i).
% 3.38/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.38/1.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.38/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.38/1.57  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.38/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.38/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.38/1.57  
% 3.38/1.58  tff(f_80, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 3.38/1.58  tff(f_55, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.38/1.58  tff(f_53, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.38/1.58  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.38/1.58  tff(f_70, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 3.38/1.58  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.38/1.58  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.38/1.58  tff(f_38, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.38/1.58  tff(c_58, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.38/1.58  tff(c_56, plain, ('#skF_6'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.38/1.58  tff(c_40, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.38/1.58  tff(c_71, plain, (![D_32, B_33]: (r2_hidden(D_32, k2_tarski(D_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.38/1.58  tff(c_74, plain, (![A_18]: (r2_hidden(A_18, k1_tarski(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_71])).
% 3.38/1.58  tff(c_81, plain, (![B_37, A_38]: (~r2_hidden(B_37, A_38) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.38/1.58  tff(c_92, plain, (![A_18]: (~v1_xboole_0(k1_tarski(A_18)))), inference(resolution, [status(thm)], [c_74, c_81])).
% 3.38/1.58  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.38/1.58  tff(c_142, plain, (![D_51, B_52, A_53]: (D_51=B_52 | D_51=A_53 | ~r2_hidden(D_51, k2_tarski(A_53, B_52)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.38/1.58  tff(c_163, plain, (![D_54, A_55]: (D_54=A_55 | D_54=A_55 | ~r2_hidden(D_54, k1_tarski(A_55)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_142])).
% 3.38/1.58  tff(c_167, plain, (![A_55]: ('#skF_1'(k1_tarski(A_55))=A_55 | v1_xboole_0(k1_tarski(A_55)))), inference(resolution, [status(thm)], [c_4, c_163])).
% 3.38/1.58  tff(c_173, plain, (![A_55]: ('#skF_1'(k1_tarski(A_55))=A_55)), inference(negUnitSimplification, [status(thm)], [c_92, c_167])).
% 3.38/1.58  tff(c_52, plain, (![B_29, C_30]: (k4_xboole_0(k2_tarski(B_29, B_29), C_30)=k1_tarski(B_29) | r2_hidden(B_29, C_30))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.38/1.58  tff(c_61, plain, (![B_29, C_30]: (k4_xboole_0(k1_tarski(B_29), C_30)=k1_tarski(B_29) | r2_hidden(B_29, C_30))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_52])).
% 3.38/1.58  tff(c_60, plain, (r1_tarski(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.38/1.58  tff(c_112, plain, (![A_45, B_46]: (k3_xboole_0(A_45, B_46)=A_45 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.38/1.58  tff(c_116, plain, (k3_xboole_0(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6'))=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_60, c_112])).
% 3.38/1.58  tff(c_18, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.38/1.58  tff(c_138, plain, (k5_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))=k4_xboole_0(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_18])).
% 3.38/1.58  tff(c_343, plain, (![A_87, C_88, B_89]: (~r2_hidden(A_87, C_88) | ~r2_hidden(A_87, B_89) | ~r2_hidden(A_87, k5_xboole_0(B_89, C_88)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.38/1.58  tff(c_426, plain, (![A_108]: (~r2_hidden(A_108, k1_tarski('#skF_4')) | ~r2_hidden(A_108, k1_tarski('#skF_4')) | ~r2_hidden(A_108, k4_xboole_0(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_138, c_343])).
% 3.38/1.58  tff(c_429, plain, (![A_108]: (~r2_hidden(A_108, k1_tarski('#skF_4')) | ~r2_hidden(A_108, k1_tarski('#skF_4')) | ~r2_hidden(A_108, k1_tarski('#skF_4')) | r2_hidden('#skF_4', k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_61, c_426])).
% 3.38/1.58  tff(c_1603, plain, (![A_1814]: (~r2_hidden(A_1814, k1_tarski('#skF_4')) | ~r2_hidden(A_1814, k1_tarski('#skF_4')) | ~r2_hidden(A_1814, k1_tarski('#skF_4')))), inference(splitLeft, [status(thm)], [c_429])).
% 3.38/1.58  tff(c_1624, plain, (~r2_hidden('#skF_1'(k1_tarski('#skF_4')), k1_tarski('#skF_4')) | v1_xboole_0(k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_4, c_1603])).
% 3.38/1.58  tff(c_1637, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_173, c_1624])).
% 3.38/1.58  tff(c_1639, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_1637])).
% 3.38/1.58  tff(c_1640, plain, (r2_hidden('#skF_4', k2_tarski('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_429])).
% 3.38/1.58  tff(c_22, plain, (![D_17, B_13, A_12]: (D_17=B_13 | D_17=A_12 | ~r2_hidden(D_17, k2_tarski(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.38/1.58  tff(c_1643, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_1640, c_22])).
% 3.38/1.58  tff(c_1650, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_56, c_1643])).
% 3.38/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.58  
% 3.38/1.58  Inference rules
% 3.38/1.58  ----------------------
% 3.38/1.58  #Ref     : 0
% 3.38/1.58  #Sup     : 267
% 3.38/1.58  #Fact    : 6
% 3.38/1.58  #Define  : 0
% 3.38/1.58  #Split   : 2
% 3.38/1.58  #Chain   : 0
% 3.38/1.58  #Close   : 0
% 3.38/1.58  
% 3.38/1.58  Ordering : KBO
% 3.38/1.58  
% 3.38/1.58  Simplification rules
% 3.38/1.58  ----------------------
% 3.38/1.59  #Subsume      : 33
% 3.38/1.59  #Demod        : 39
% 3.38/1.59  #Tautology    : 70
% 3.38/1.59  #SimpNegUnit  : 10
% 3.38/1.59  #BackRed      : 0
% 3.38/1.59  
% 3.38/1.59  #Partial instantiations: 826
% 3.38/1.59  #Strategies tried      : 1
% 3.38/1.59  
% 3.38/1.59  Timing (in seconds)
% 3.38/1.59  ----------------------
% 3.38/1.59  Preprocessing        : 0.31
% 3.38/1.59  Parsing              : 0.15
% 3.38/1.59  CNF conversion       : 0.02
% 3.38/1.59  Main loop            : 0.50
% 3.38/1.59  Inferencing          : 0.22
% 3.38/1.59  Reduction            : 0.13
% 3.38/1.59  Demodulation         : 0.09
% 3.38/1.59  BG Simplification    : 0.03
% 3.38/1.59  Subsumption          : 0.10
% 3.38/1.59  Abstraction          : 0.02
% 3.38/1.59  MUC search           : 0.00
% 3.38/1.59  Cooper               : 0.00
% 3.38/1.59  Total                : 0.83
% 3.38/1.59  Index Insertion      : 0.00
% 3.38/1.59  Index Deletion       : 0.00
% 3.38/1.59  Index Matching       : 0.00
% 3.38/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
