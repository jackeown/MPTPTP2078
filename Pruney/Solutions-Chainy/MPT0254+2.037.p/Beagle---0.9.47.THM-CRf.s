%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:24 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 106 expanded)
%              Number of leaves         :   30 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :   50 ( 108 expanded)
%              Number of equality atoms :   20 (  53 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_34,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_18,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_202,plain,(
    ! [A_56,B_57] :
      ( k2_xboole_0(A_56,B_57) = B_57
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_256,plain,(
    ! [A_61] : k2_xboole_0(k1_xboole_0,A_61) = A_61 ),
    inference(resolution,[status(thm)],[c_18,c_202])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_269,plain,(
    ! [A_61] : k2_xboole_0(A_61,k1_xboole_0) = A_61 ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_2])).

tff(c_52,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_109,plain,(
    ! [B_49,A_50] : k2_xboole_0(B_49,A_50) = k2_xboole_0(A_50,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_165,plain,(
    ! [A_52,B_53] : r1_tarski(A_52,k2_xboole_0(B_53,A_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_22])).

tff(c_174,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_165])).

tff(c_221,plain,(
    k2_xboole_0('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_174,c_202])).

tff(c_352,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_221])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_361,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_8])).

tff(c_360,plain,(
    ! [A_11] : r1_tarski('#skF_5',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_18])).

tff(c_69,plain,(
    ! [A_36,B_37] : r1_tarski(A_36,k2_xboole_0(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_72,plain,(
    r1_tarski(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_69])).

tff(c_357,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_72])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_446,plain,
    ( k1_tarski('#skF_4') = '#skF_5'
    | ~ r1_tarski('#skF_5',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_357,c_10])).

tff(c_452,plain,(
    k1_tarski('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_446])).

tff(c_44,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_74,plain,(
    ! [D_40,B_41] : r2_hidden(D_40,k2_tarski(D_40,B_41)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_91,plain,(
    ! [D_43,B_44] : ~ v1_xboole_0(k2_tarski(D_43,B_44)) ),
    inference(resolution,[status(thm)],[c_74,c_4])).

tff(c_93,plain,(
    ! [A_23] : ~ v1_xboole_0(k1_tarski(A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_91])).

tff(c_493,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_93])).

tff(c_498,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_493])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.25  
% 2.23/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.25  %$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.23/1.25  
% 2.23/1.25  %Foreground sorts:
% 2.23/1.25  
% 2.23/1.25  
% 2.23/1.25  %Background operators:
% 2.23/1.25  
% 2.23/1.25  
% 2.23/1.25  %Foreground operators:
% 2.23/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.23/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.23/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.23/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.23/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.23/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.23/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.23/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.23/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.23/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.25  
% 2.28/1.26  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.28/1.26  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.28/1.26  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.28/1.26  tff(f_73, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.28/1.26  tff(f_50, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.28/1.26  tff(f_34, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.28/1.26  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.28/1.26  tff(f_63, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.28/1.26  tff(f_61, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.28/1.26  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.28/1.26  tff(c_18, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.28/1.26  tff(c_202, plain, (![A_56, B_57]: (k2_xboole_0(A_56, B_57)=B_57 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.28/1.26  tff(c_256, plain, (![A_61]: (k2_xboole_0(k1_xboole_0, A_61)=A_61)), inference(resolution, [status(thm)], [c_18, c_202])).
% 2.28/1.26  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.28/1.26  tff(c_269, plain, (![A_61]: (k2_xboole_0(A_61, k1_xboole_0)=A_61)), inference(superposition, [status(thm), theory('equality')], [c_256, c_2])).
% 2.28/1.26  tff(c_52, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.28/1.26  tff(c_109, plain, (![B_49, A_50]: (k2_xboole_0(B_49, A_50)=k2_xboole_0(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.28/1.26  tff(c_22, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.28/1.26  tff(c_165, plain, (![A_52, B_53]: (r1_tarski(A_52, k2_xboole_0(B_53, A_52)))), inference(superposition, [status(thm), theory('equality')], [c_109, c_22])).
% 2.28/1.26  tff(c_174, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_52, c_165])).
% 2.28/1.26  tff(c_221, plain, (k2_xboole_0('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_174, c_202])).
% 2.28/1.26  tff(c_352, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_269, c_221])).
% 2.28/1.26  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.28/1.26  tff(c_361, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_352, c_8])).
% 2.28/1.26  tff(c_360, plain, (![A_11]: (r1_tarski('#skF_5', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_352, c_18])).
% 2.28/1.26  tff(c_69, plain, (![A_36, B_37]: (r1_tarski(A_36, k2_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.28/1.26  tff(c_72, plain, (r1_tarski(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_52, c_69])).
% 2.28/1.26  tff(c_357, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_352, c_72])).
% 2.28/1.26  tff(c_10, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.28/1.26  tff(c_446, plain, (k1_tarski('#skF_4')='#skF_5' | ~r1_tarski('#skF_5', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_357, c_10])).
% 2.28/1.26  tff(c_452, plain, (k1_tarski('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_360, c_446])).
% 2.28/1.26  tff(c_44, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.28/1.26  tff(c_74, plain, (![D_40, B_41]: (r2_hidden(D_40, k2_tarski(D_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.28/1.26  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.28/1.26  tff(c_91, plain, (![D_43, B_44]: (~v1_xboole_0(k2_tarski(D_43, B_44)))), inference(resolution, [status(thm)], [c_74, c_4])).
% 2.28/1.26  tff(c_93, plain, (![A_23]: (~v1_xboole_0(k1_tarski(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_91])).
% 2.28/1.26  tff(c_493, plain, (~v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_452, c_93])).
% 2.28/1.26  tff(c_498, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_361, c_493])).
% 2.28/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.26  
% 2.28/1.26  Inference rules
% 2.28/1.26  ----------------------
% 2.28/1.26  #Ref     : 0
% 2.28/1.26  #Sup     : 108
% 2.28/1.26  #Fact    : 0
% 2.28/1.26  #Define  : 0
% 2.28/1.26  #Split   : 0
% 2.28/1.26  #Chain   : 0
% 2.28/1.26  #Close   : 0
% 2.28/1.26  
% 2.28/1.26  Ordering : KBO
% 2.28/1.26  
% 2.28/1.26  Simplification rules
% 2.28/1.26  ----------------------
% 2.28/1.26  #Subsume      : 2
% 2.28/1.26  #Demod        : 48
% 2.28/1.26  #Tautology    : 75
% 2.28/1.26  #SimpNegUnit  : 0
% 2.28/1.26  #BackRed      : 11
% 2.28/1.26  
% 2.28/1.26  #Partial instantiations: 0
% 2.28/1.26  #Strategies tried      : 1
% 2.28/1.26  
% 2.28/1.26  Timing (in seconds)
% 2.28/1.26  ----------------------
% 2.28/1.26  Preprocessing        : 0.30
% 2.28/1.27  Parsing              : 0.15
% 2.28/1.27  CNF conversion       : 0.02
% 2.28/1.27  Main loop            : 0.21
% 2.28/1.27  Inferencing          : 0.07
% 2.28/1.27  Reduction            : 0.08
% 2.28/1.27  Demodulation         : 0.06
% 2.28/1.27  BG Simplification    : 0.01
% 2.28/1.27  Subsumption          : 0.03
% 2.28/1.27  Abstraction          : 0.01
% 2.28/1.27  MUC search           : 0.00
% 2.28/1.27  Cooper               : 0.00
% 2.28/1.27  Total                : 0.54
% 2.28/1.27  Index Insertion      : 0.00
% 2.28/1.27  Index Deletion       : 0.00
% 2.28/1.27  Index Matching       : 0.00
% 2.28/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
