%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:26 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :   52 (  55 expanded)
%              Number of leaves         :   32 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 (  59 expanded)
%              Number of equality atoms :   26 (  31 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_84,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_82,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_64,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_62,plain,(
    '#skF_6' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_60,plain,(
    ! [A_61,B_62] : r1_tarski(k1_tarski(A_61),k2_tarski(A_61,B_62)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_66,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_908,plain,(
    ! [A_129,C_130,B_131] :
      ( r1_tarski(A_129,C_130)
      | ~ r1_tarski(B_131,C_130)
      | ~ r1_tarski(A_129,B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_993,plain,(
    ! [A_138] :
      ( r1_tarski(A_138,k2_tarski('#skF_5','#skF_6'))
      | ~ r1_tarski(A_138,k2_tarski('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_66,c_908])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1333,plain,(
    ! [A_147] :
      ( k4_xboole_0(A_147,k2_tarski('#skF_5','#skF_6')) = k1_xboole_0
      | ~ r1_tarski(A_147,k2_tarski('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_993,c_8])).

tff(c_1343,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_1333])).

tff(c_253,plain,(
    ! [A_87,B_88] :
      ( r1_tarski(A_87,B_88)
      | k4_xboole_0(A_87,B_88) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_257,plain,(
    ! [A_87,B_88] :
      ( k3_xboole_0(A_87,B_88) = A_87
      | k4_xboole_0(A_87,B_88) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_253,c_16])).

tff(c_1353,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_5','#skF_6')) = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1343,c_257])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1130,plain,(
    ! [B_141,A_142] :
      ( r2_hidden(B_141,A_142)
      | k3_xboole_0(A_142,k1_tarski(B_141)) != k1_tarski(B_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2444,plain,(
    ! [B_184,B_185] :
      ( r2_hidden(B_184,B_185)
      | k3_xboole_0(k1_tarski(B_184),B_185) != k1_tarski(B_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1130])).

tff(c_2470,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1353,c_2444])).

tff(c_24,plain,(
    ! [D_26,B_22,A_21] :
      ( D_26 = B_22
      | D_26 = A_21
      | ~ r2_hidden(D_26,k2_tarski(A_21,B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2488,plain,
    ( '#skF_6' = '#skF_3'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2470,c_24])).

tff(c_2492,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_62,c_2488])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:16:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.91/1.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.68  
% 3.91/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.68  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.91/1.68  
% 3.91/1.68  %Foreground sorts:
% 3.91/1.68  
% 3.91/1.68  
% 3.91/1.68  %Background operators:
% 3.91/1.68  
% 3.91/1.68  
% 3.91/1.68  %Foreground operators:
% 3.91/1.68  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.91/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.91/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.91/1.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.91/1.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.91/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.91/1.68  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.91/1.68  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.91/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.91/1.68  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.91/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.91/1.68  tff('#skF_5', type, '#skF_5': $i).
% 3.91/1.68  tff('#skF_6', type, '#skF_6': $i).
% 3.91/1.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.91/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.91/1.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.91/1.68  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.91/1.68  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.91/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.91/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.91/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.91/1.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.91/1.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.91/1.68  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.91/1.68  
% 4.11/1.69  tff(f_94, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 4.11/1.69  tff(f_84, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 4.11/1.69  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.11/1.69  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.11/1.69  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.11/1.69  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.11/1.69  tff(f_82, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 4.11/1.69  tff(f_62, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 4.11/1.69  tff(c_64, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.11/1.69  tff(c_62, plain, ('#skF_6'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.11/1.69  tff(c_60, plain, (![A_61, B_62]: (r1_tarski(k1_tarski(A_61), k2_tarski(A_61, B_62)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.11/1.69  tff(c_66, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.11/1.69  tff(c_908, plain, (![A_129, C_130, B_131]: (r1_tarski(A_129, C_130) | ~r1_tarski(B_131, C_130) | ~r1_tarski(A_129, B_131))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.11/1.69  tff(c_993, plain, (![A_138]: (r1_tarski(A_138, k2_tarski('#skF_5', '#skF_6')) | ~r1_tarski(A_138, k2_tarski('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_66, c_908])).
% 4.11/1.69  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.11/1.69  tff(c_1333, plain, (![A_147]: (k4_xboole_0(A_147, k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0 | ~r1_tarski(A_147, k2_tarski('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_993, c_8])).
% 4.11/1.69  tff(c_1343, plain, (k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_1333])).
% 4.11/1.69  tff(c_253, plain, (![A_87, B_88]: (r1_tarski(A_87, B_88) | k4_xboole_0(A_87, B_88)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.11/1.69  tff(c_16, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.11/1.69  tff(c_257, plain, (![A_87, B_88]: (k3_xboole_0(A_87, B_88)=A_87 | k4_xboole_0(A_87, B_88)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_253, c_16])).
% 4.11/1.69  tff(c_1353, plain, (k3_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_5', '#skF_6'))=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1343, c_257])).
% 4.11/1.69  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.11/1.69  tff(c_1130, plain, (![B_141, A_142]: (r2_hidden(B_141, A_142) | k3_xboole_0(A_142, k1_tarski(B_141))!=k1_tarski(B_141))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.11/1.69  tff(c_2444, plain, (![B_184, B_185]: (r2_hidden(B_184, B_185) | k3_xboole_0(k1_tarski(B_184), B_185)!=k1_tarski(B_184))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1130])).
% 4.11/1.69  tff(c_2470, plain, (r2_hidden('#skF_3', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1353, c_2444])).
% 4.11/1.69  tff(c_24, plain, (![D_26, B_22, A_21]: (D_26=B_22 | D_26=A_21 | ~r2_hidden(D_26, k2_tarski(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.11/1.69  tff(c_2488, plain, ('#skF_6'='#skF_3' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_2470, c_24])).
% 4.11/1.69  tff(c_2492, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_62, c_2488])).
% 4.11/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.11/1.69  
% 4.11/1.69  Inference rules
% 4.11/1.69  ----------------------
% 4.11/1.69  #Ref     : 0
% 4.11/1.69  #Sup     : 622
% 4.11/1.69  #Fact    : 0
% 4.11/1.69  #Define  : 0
% 4.11/1.69  #Split   : 0
% 4.11/1.69  #Chain   : 0
% 4.11/1.69  #Close   : 0
% 4.11/1.69  
% 4.11/1.69  Ordering : KBO
% 4.11/1.69  
% 4.11/1.69  Simplification rules
% 4.11/1.69  ----------------------
% 4.11/1.69  #Subsume      : 47
% 4.11/1.69  #Demod        : 458
% 4.11/1.69  #Tautology    : 375
% 4.11/1.69  #SimpNegUnit  : 1
% 4.11/1.69  #BackRed      : 0
% 4.11/1.69  
% 4.11/1.69  #Partial instantiations: 0
% 4.11/1.69  #Strategies tried      : 1
% 4.11/1.69  
% 4.11/1.69  Timing (in seconds)
% 4.11/1.69  ----------------------
% 4.11/1.70  Preprocessing        : 0.34
% 4.11/1.70  Parsing              : 0.18
% 4.11/1.70  CNF conversion       : 0.02
% 4.11/1.70  Main loop            : 0.60
% 4.11/1.70  Inferencing          : 0.18
% 4.11/1.70  Reduction            : 0.27
% 4.11/1.70  Demodulation         : 0.22
% 4.11/1.70  BG Simplification    : 0.03
% 4.11/1.70  Subsumption          : 0.09
% 4.11/1.70  Abstraction          : 0.03
% 4.11/1.70  MUC search           : 0.00
% 4.11/1.70  Cooper               : 0.00
% 4.11/1.70  Total                : 0.97
% 4.11/1.70  Index Insertion      : 0.00
% 4.11/1.70  Index Deletion       : 0.00
% 4.11/1.70  Index Matching       : 0.00
% 4.11/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
