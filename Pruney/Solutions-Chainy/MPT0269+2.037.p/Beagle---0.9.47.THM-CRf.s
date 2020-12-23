%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:48 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 320 expanded)
%              Number of leaves         :   20 ( 116 expanded)
%              Depth                    :   13
%              Number of atoms          :  104 ( 659 expanded)
%              Number of equality atoms :   55 ( 331 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_38,plain,(
    k1_tarski('#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_446,plain,(
    ! [A_495,B_496] :
      ( '#skF_3'(A_495,B_496) = A_495
      | r2_hidden('#skF_4'(A_495,B_496),B_496)
      | k1_tarski(A_495) = B_496 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,(
    ! [C_14] : r2_hidden(C_14,k1_tarski(C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_22,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_87,plain,(
    ! [D_27,B_28,A_29] :
      ( ~ r2_hidden(D_27,B_28)
      | ~ r2_hidden(D_27,k4_xboole_0(A_29,B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_94,plain,(
    ! [D_30,A_31] :
      ( ~ r2_hidden(D_30,A_31)
      | ~ r2_hidden(D_30,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_87])).

tff(c_97,plain,(
    ! [C_14] : ~ r2_hidden(C_14,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_94])).

tff(c_42,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_99,plain,(
    ! [D_33,A_34,B_35] :
      ( r2_hidden(D_33,k4_xboole_0(A_34,B_35))
      | r2_hidden(D_33,B_35)
      | ~ r2_hidden(D_33,A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_108,plain,(
    ! [D_33] :
      ( r2_hidden(D_33,k1_xboole_0)
      | r2_hidden(D_33,k1_tarski('#skF_6'))
      | ~ r2_hidden(D_33,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_99])).

tff(c_290,plain,(
    ! [D_334] :
      ( r2_hidden(D_334,k1_tarski('#skF_6'))
      | ~ r2_hidden(D_334,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_108])).

tff(c_24,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_324,plain,(
    ! [D_334] :
      ( D_334 = '#skF_6'
      | ~ r2_hidden(D_334,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_290,c_24])).

tff(c_579,plain,(
    ! [A_556] :
      ( '#skF_4'(A_556,'#skF_5') = '#skF_6'
      | '#skF_3'(A_556,'#skF_5') = A_556
      | k1_tarski(A_556) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_446,c_324])).

tff(c_639,plain,
    ( '#skF_4'('#skF_6','#skF_5') = '#skF_6'
    | '#skF_3'('#skF_6','#skF_5') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_579,c_38])).

tff(c_644,plain,(
    '#skF_3'('#skF_6','#skF_5') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_639])).

tff(c_28,plain,(
    ! [A_10,B_11] :
      ( ~ r2_hidden('#skF_3'(A_10,B_11),B_11)
      | '#skF_4'(A_10,B_11) != A_10
      | k1_tarski(A_10) = B_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_648,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | '#skF_4'('#skF_6','#skF_5') != '#skF_6'
    | k1_tarski('#skF_6') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_644,c_28])).

tff(c_665,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | '#skF_4'('#skF_6','#skF_5') != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_648])).

tff(c_673,plain,(
    '#skF_4'('#skF_6','#skF_5') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_665])).

tff(c_674,plain,(
    ! [A_614,B_615] :
      ( ~ r2_hidden('#skF_3'(A_614,B_615),B_615)
      | r2_hidden('#skF_4'(A_614,B_615),B_615)
      | k1_tarski(A_614) = B_615 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_677,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | r2_hidden('#skF_4'('#skF_6','#skF_5'),'#skF_5')
    | k1_tarski('#skF_6') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_644,c_674])).

tff(c_719,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | r2_hidden('#skF_4'('#skF_6','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_677])).

tff(c_725,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_719])).

tff(c_1112,plain,(
    ! [A_840,B_841,C_842] :
      ( r2_hidden('#skF_1'(A_840,B_841,C_842),A_840)
      | r2_hidden('#skF_2'(A_840,B_841,C_842),C_842)
      | k4_xboole_0(A_840,B_841) = C_842 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1129,plain,(
    ! [B_841,C_842] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_841,C_842),C_842)
      | k4_xboole_0(k1_xboole_0,B_841) = C_842 ) ),
    inference(resolution,[status(thm)],[c_1112,c_97])).

tff(c_1176,plain,(
    ! [B_862,C_863] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_862,C_863),C_863)
      | k1_xboole_0 = C_863 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1129])).

tff(c_1185,plain,(
    ! [B_862] :
      ( '#skF_2'(k1_xboole_0,B_862,'#skF_5') = '#skF_6'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_1176,c_324])).

tff(c_1215,plain,(
    ! [B_883] : '#skF_2'(k1_xboole_0,B_883,'#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1185])).

tff(c_1168,plain,(
    ! [B_841,C_842] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_841,C_842),C_842)
      | k1_xboole_0 = C_842 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1129])).

tff(c_1220,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1215,c_1168])).

tff(c_1227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_725,c_1220])).

tff(c_1228,plain,(
    r2_hidden('#skF_4'('#skF_6','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_719])).

tff(c_1238,plain,(
    '#skF_4'('#skF_6','#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1228,c_324])).

tff(c_1242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_673,c_1238])).

tff(c_1243,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_665])).

tff(c_1499,plain,(
    ! [A_1123,B_1124,C_1125] :
      ( r2_hidden('#skF_1'(A_1123,B_1124,C_1125),A_1123)
      | r2_hidden('#skF_2'(A_1123,B_1124,C_1125),C_1125)
      | k4_xboole_0(A_1123,B_1124) = C_1125 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1512,plain,(
    ! [B_1124,C_1125] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_1124,C_1125),C_1125)
      | k4_xboole_0(k1_xboole_0,B_1124) = C_1125 ) ),
    inference(resolution,[status(thm)],[c_1499,c_97])).

tff(c_1558,plain,(
    ! [B_1145,C_1146] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_1145,C_1146),C_1146)
      | k1_xboole_0 = C_1146 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1512])).

tff(c_1567,plain,(
    ! [B_1145] :
      ( '#skF_2'(k1_xboole_0,B_1145,'#skF_5') = '#skF_6'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_1558,c_324])).

tff(c_1597,plain,(
    ! [B_1166] : '#skF_2'(k1_xboole_0,B_1166,'#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1567])).

tff(c_1550,plain,(
    ! [B_1124,C_1125] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_1124,C_1125),C_1125)
      | k1_xboole_0 = C_1125 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1512])).

tff(c_1602,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1597,c_1550])).

tff(c_1609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1243,c_1602])).

tff(c_1610,plain,(
    '#skF_4'('#skF_6','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_639])).

tff(c_118,plain,(
    ! [A_36,B_37] :
      ( '#skF_3'(A_36,B_37) = A_36
      | '#skF_4'(A_36,B_37) != A_36
      | k1_tarski(A_36) = B_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_248,plain,(
    ! [B_37] :
      ( B_37 != '#skF_5'
      | '#skF_3'('#skF_6',B_37) = '#skF_6'
      | '#skF_4'('#skF_6',B_37) != '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_38])).

tff(c_1611,plain,(
    '#skF_3'('#skF_6','#skF_5') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_639])).

tff(c_1631,plain,(
    '#skF_4'('#skF_6','#skF_5') != '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_1611])).

tff(c_1640,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1610,c_1631])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:26:09 EST 2020
% 0.19/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.48  
% 3.20/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.48  %$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.20/1.48  
% 3.20/1.48  %Foreground sorts:
% 3.20/1.48  
% 3.20/1.48  
% 3.20/1.48  %Background operators:
% 3.20/1.48  
% 3.20/1.48  
% 3.20/1.48  %Foreground operators:
% 3.20/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.20/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.20/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.20/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.20/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.20/1.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.20/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.20/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.20/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.20/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.20/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.20/1.48  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.20/1.48  
% 3.20/1.50  tff(f_58, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 3.20/1.50  tff(f_46, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.20/1.50  tff(f_39, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.20/1.50  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.20/1.50  tff(c_40, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.20/1.50  tff(c_38, plain, (k1_tarski('#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.20/1.50  tff(c_446, plain, (![A_495, B_496]: ('#skF_3'(A_495, B_496)=A_495 | r2_hidden('#skF_4'(A_495, B_496), B_496) | k1_tarski(A_495)=B_496)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.20/1.50  tff(c_26, plain, (![C_14]: (r2_hidden(C_14, k1_tarski(C_14)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.20/1.50  tff(c_22, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.20/1.50  tff(c_87, plain, (![D_27, B_28, A_29]: (~r2_hidden(D_27, B_28) | ~r2_hidden(D_27, k4_xboole_0(A_29, B_28)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.20/1.50  tff(c_94, plain, (![D_30, A_31]: (~r2_hidden(D_30, A_31) | ~r2_hidden(D_30, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_87])).
% 3.20/1.50  tff(c_97, plain, (![C_14]: (~r2_hidden(C_14, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_94])).
% 3.20/1.50  tff(c_42, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.20/1.50  tff(c_99, plain, (![D_33, A_34, B_35]: (r2_hidden(D_33, k4_xboole_0(A_34, B_35)) | r2_hidden(D_33, B_35) | ~r2_hidden(D_33, A_34))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.20/1.50  tff(c_108, plain, (![D_33]: (r2_hidden(D_33, k1_xboole_0) | r2_hidden(D_33, k1_tarski('#skF_6')) | ~r2_hidden(D_33, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_99])).
% 3.20/1.50  tff(c_290, plain, (![D_334]: (r2_hidden(D_334, k1_tarski('#skF_6')) | ~r2_hidden(D_334, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_97, c_108])).
% 3.20/1.50  tff(c_24, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.20/1.50  tff(c_324, plain, (![D_334]: (D_334='#skF_6' | ~r2_hidden(D_334, '#skF_5'))), inference(resolution, [status(thm)], [c_290, c_24])).
% 3.20/1.50  tff(c_579, plain, (![A_556]: ('#skF_4'(A_556, '#skF_5')='#skF_6' | '#skF_3'(A_556, '#skF_5')=A_556 | k1_tarski(A_556)='#skF_5')), inference(resolution, [status(thm)], [c_446, c_324])).
% 3.20/1.50  tff(c_639, plain, ('#skF_4'('#skF_6', '#skF_5')='#skF_6' | '#skF_3'('#skF_6', '#skF_5')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_579, c_38])).
% 3.20/1.50  tff(c_644, plain, ('#skF_3'('#skF_6', '#skF_5')='#skF_6'), inference(splitLeft, [status(thm)], [c_639])).
% 3.20/1.50  tff(c_28, plain, (![A_10, B_11]: (~r2_hidden('#skF_3'(A_10, B_11), B_11) | '#skF_4'(A_10, B_11)!=A_10 | k1_tarski(A_10)=B_11)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.20/1.50  tff(c_648, plain, (~r2_hidden('#skF_6', '#skF_5') | '#skF_4'('#skF_6', '#skF_5')!='#skF_6' | k1_tarski('#skF_6')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_644, c_28])).
% 3.20/1.50  tff(c_665, plain, (~r2_hidden('#skF_6', '#skF_5') | '#skF_4'('#skF_6', '#skF_5')!='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_38, c_648])).
% 3.20/1.50  tff(c_673, plain, ('#skF_4'('#skF_6', '#skF_5')!='#skF_6'), inference(splitLeft, [status(thm)], [c_665])).
% 3.20/1.50  tff(c_674, plain, (![A_614, B_615]: (~r2_hidden('#skF_3'(A_614, B_615), B_615) | r2_hidden('#skF_4'(A_614, B_615), B_615) | k1_tarski(A_614)=B_615)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.20/1.50  tff(c_677, plain, (~r2_hidden('#skF_6', '#skF_5') | r2_hidden('#skF_4'('#skF_6', '#skF_5'), '#skF_5') | k1_tarski('#skF_6')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_644, c_674])).
% 3.20/1.50  tff(c_719, plain, (~r2_hidden('#skF_6', '#skF_5') | r2_hidden('#skF_4'('#skF_6', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_38, c_677])).
% 3.20/1.50  tff(c_725, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_719])).
% 3.20/1.50  tff(c_1112, plain, (![A_840, B_841, C_842]: (r2_hidden('#skF_1'(A_840, B_841, C_842), A_840) | r2_hidden('#skF_2'(A_840, B_841, C_842), C_842) | k4_xboole_0(A_840, B_841)=C_842)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.20/1.50  tff(c_1129, plain, (![B_841, C_842]: (r2_hidden('#skF_2'(k1_xboole_0, B_841, C_842), C_842) | k4_xboole_0(k1_xboole_0, B_841)=C_842)), inference(resolution, [status(thm)], [c_1112, c_97])).
% 3.20/1.50  tff(c_1176, plain, (![B_862, C_863]: (r2_hidden('#skF_2'(k1_xboole_0, B_862, C_863), C_863) | k1_xboole_0=C_863)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1129])).
% 3.20/1.50  tff(c_1185, plain, (![B_862]: ('#skF_2'(k1_xboole_0, B_862, '#skF_5')='#skF_6' | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_1176, c_324])).
% 3.20/1.50  tff(c_1215, plain, (![B_883]: ('#skF_2'(k1_xboole_0, B_883, '#skF_5')='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_40, c_1185])).
% 3.20/1.50  tff(c_1168, plain, (![B_841, C_842]: (r2_hidden('#skF_2'(k1_xboole_0, B_841, C_842), C_842) | k1_xboole_0=C_842)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1129])).
% 3.20/1.50  tff(c_1220, plain, (r2_hidden('#skF_6', '#skF_5') | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1215, c_1168])).
% 3.20/1.50  tff(c_1227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_725, c_1220])).
% 3.20/1.50  tff(c_1228, plain, (r2_hidden('#skF_4'('#skF_6', '#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_719])).
% 3.20/1.50  tff(c_1238, plain, ('#skF_4'('#skF_6', '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_1228, c_324])).
% 3.20/1.50  tff(c_1242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_673, c_1238])).
% 3.20/1.50  tff(c_1243, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_665])).
% 3.20/1.50  tff(c_1499, plain, (![A_1123, B_1124, C_1125]: (r2_hidden('#skF_1'(A_1123, B_1124, C_1125), A_1123) | r2_hidden('#skF_2'(A_1123, B_1124, C_1125), C_1125) | k4_xboole_0(A_1123, B_1124)=C_1125)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.20/1.50  tff(c_1512, plain, (![B_1124, C_1125]: (r2_hidden('#skF_2'(k1_xboole_0, B_1124, C_1125), C_1125) | k4_xboole_0(k1_xboole_0, B_1124)=C_1125)), inference(resolution, [status(thm)], [c_1499, c_97])).
% 3.20/1.50  tff(c_1558, plain, (![B_1145, C_1146]: (r2_hidden('#skF_2'(k1_xboole_0, B_1145, C_1146), C_1146) | k1_xboole_0=C_1146)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1512])).
% 3.20/1.50  tff(c_1567, plain, (![B_1145]: ('#skF_2'(k1_xboole_0, B_1145, '#skF_5')='#skF_6' | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_1558, c_324])).
% 3.20/1.50  tff(c_1597, plain, (![B_1166]: ('#skF_2'(k1_xboole_0, B_1166, '#skF_5')='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_40, c_1567])).
% 3.20/1.50  tff(c_1550, plain, (![B_1124, C_1125]: (r2_hidden('#skF_2'(k1_xboole_0, B_1124, C_1125), C_1125) | k1_xboole_0=C_1125)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1512])).
% 3.20/1.50  tff(c_1602, plain, (r2_hidden('#skF_6', '#skF_5') | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1597, c_1550])).
% 3.20/1.50  tff(c_1609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_1243, c_1602])).
% 3.20/1.50  tff(c_1610, plain, ('#skF_4'('#skF_6', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_639])).
% 3.20/1.50  tff(c_118, plain, (![A_36, B_37]: ('#skF_3'(A_36, B_37)=A_36 | '#skF_4'(A_36, B_37)!=A_36 | k1_tarski(A_36)=B_37)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.20/1.50  tff(c_248, plain, (![B_37]: (B_37!='#skF_5' | '#skF_3'('#skF_6', B_37)='#skF_6' | '#skF_4'('#skF_6', B_37)!='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_118, c_38])).
% 3.20/1.50  tff(c_1611, plain, ('#skF_3'('#skF_6', '#skF_5')!='#skF_6'), inference(splitRight, [status(thm)], [c_639])).
% 3.20/1.50  tff(c_1631, plain, ('#skF_4'('#skF_6', '#skF_5')!='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_248, c_1611])).
% 3.20/1.50  tff(c_1640, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1610, c_1631])).
% 3.20/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.50  
% 3.20/1.50  Inference rules
% 3.20/1.50  ----------------------
% 3.20/1.50  #Ref     : 0
% 3.20/1.50  #Sup     : 269
% 3.20/1.50  #Fact    : 0
% 3.20/1.50  #Define  : 0
% 3.20/1.50  #Split   : 6
% 3.20/1.50  #Chain   : 0
% 3.20/1.50  #Close   : 0
% 3.20/1.50  
% 3.20/1.50  Ordering : KBO
% 3.20/1.50  
% 3.20/1.50  Simplification rules
% 3.20/1.50  ----------------------
% 3.20/1.50  #Subsume      : 38
% 3.20/1.50  #Demod        : 43
% 3.20/1.50  #Tautology    : 106
% 3.20/1.50  #SimpNegUnit  : 30
% 3.20/1.50  #BackRed      : 0
% 3.20/1.50  
% 3.20/1.50  #Partial instantiations: 708
% 3.20/1.50  #Strategies tried      : 1
% 3.20/1.50  
% 3.20/1.50  Timing (in seconds)
% 3.20/1.50  ----------------------
% 3.20/1.50  Preprocessing        : 0.29
% 3.31/1.50  Parsing              : 0.15
% 3.31/1.50  CNF conversion       : 0.02
% 3.31/1.50  Main loop            : 0.45
% 3.31/1.50  Inferencing          : 0.21
% 3.31/1.50  Reduction            : 0.10
% 3.31/1.50  Demodulation         : 0.07
% 3.31/1.50  BG Simplification    : 0.03
% 3.31/1.50  Subsumption          : 0.08
% 3.31/1.50  Abstraction          : 0.02
% 3.31/1.50  MUC search           : 0.00
% 3.31/1.50  Cooper               : 0.00
% 3.31/1.50  Total                : 0.77
% 3.31/1.50  Index Insertion      : 0.00
% 3.31/1.50  Index Deletion       : 0.00
% 3.31/1.50  Index Matching       : 0.00
% 3.31/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
