%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:34 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 129 expanded)
%              Number of leaves         :   34 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 ( 155 expanded)
%              Number of equality atoms :   21 (  53 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_52,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_62,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_106,plain,(
    ! [B_59,A_60] :
      ( ~ v1_xboole_0(k2_xboole_0(B_59,A_60))
      | v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_109,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_106])).

tff(c_111,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_109])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_115,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_111,c_4])).

tff(c_22,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_120,plain,(
    ! [A_11] : r1_xboole_0(A_11,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_22])).

tff(c_200,plain,(
    ! [A_71,B_72] :
      ( ~ r2_hidden(A_71,B_72)
      | ~ r1_xboole_0(k1_tarski(A_71),B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_205,plain,(
    ! [A_71] : ~ r2_hidden(A_71,'#skF_4') ),
    inference(resolution,[status(thm)],[c_120,c_200])).

tff(c_20,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_119,plain,(
    ! [A_10] : k4_xboole_0('#skF_4',A_10) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_115,c_20])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | k4_xboole_0(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_127,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | k4_xboole_0(A_6,B_7) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_14])).

tff(c_97,plain,(
    ! [A_55,B_56] : r1_tarski(A_55,k2_xboole_0(A_55,B_56)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_100,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_97])).

tff(c_116,plain,(
    r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_100])).

tff(c_308,plain,(
    ! [B_84,A_85] :
      ( B_84 = A_85
      | ~ r1_tarski(B_84,A_85)
      | ~ r1_tarski(A_85,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_320,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_116,c_308])).

tff(c_327,plain,(
    ~ r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_320])).

tff(c_330,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_127,c_327])).

tff(c_334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_330])).

tff(c_335,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_320])).

tff(c_80,plain,(
    ! [A_53] : k2_tarski(A_53,A_53) = k1_tarski(A_53) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_30,plain,(
    ! [D_19,B_15] : r2_hidden(D_19,k2_tarski(D_19,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_86,plain,(
    ! [A_53] : r2_hidden(A_53,k1_tarski(A_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_30])).

tff(c_360,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_86])).

tff(c_364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_205,c_360])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.25  
% 2.20/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.25  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.20/1.25  
% 2.20/1.25  %Foreground sorts:
% 2.20/1.25  
% 2.20/1.25  
% 2.20/1.25  %Background operators:
% 2.20/1.25  
% 2.20/1.25  
% 2.20/1.25  %Foreground operators:
% 2.20/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.20/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.20/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.20/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.20/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.20/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.20/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.20/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.20/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.20/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.20/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.20/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.20/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.20/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.20/1.25  
% 2.20/1.26  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.20/1.26  tff(f_88, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.20/1.26  tff(f_42, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_xboole_0)).
% 2.20/1.26  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.20/1.26  tff(f_52, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.20/1.26  tff(f_80, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.20/1.26  tff(f_50, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.20/1.26  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.20/1.26  tff(f_54, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.20/1.26  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.20/1.26  tff(f_69, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.20/1.26  tff(f_63, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.20/1.26  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.20/1.26  tff(c_62, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.20/1.26  tff(c_106, plain, (![B_59, A_60]: (~v1_xboole_0(k2_xboole_0(B_59, A_60)) | v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.20/1.26  tff(c_109, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_62, c_106])).
% 2.20/1.26  tff(c_111, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_109])).
% 2.20/1.26  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.20/1.26  tff(c_115, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_111, c_4])).
% 2.20/1.26  tff(c_22, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.20/1.26  tff(c_120, plain, (![A_11]: (r1_xboole_0(A_11, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_22])).
% 2.20/1.26  tff(c_200, plain, (![A_71, B_72]: (~r2_hidden(A_71, B_72) | ~r1_xboole_0(k1_tarski(A_71), B_72))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.20/1.26  tff(c_205, plain, (![A_71]: (~r2_hidden(A_71, '#skF_4'))), inference(resolution, [status(thm)], [c_120, c_200])).
% 2.20/1.26  tff(c_20, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.20/1.26  tff(c_119, plain, (![A_10]: (k4_xboole_0('#skF_4', A_10)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_115, c_115, c_20])).
% 2.20/1.26  tff(c_14, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | k4_xboole_0(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.20/1.26  tff(c_127, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | k4_xboole_0(A_6, B_7)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_115, c_14])).
% 2.20/1.26  tff(c_97, plain, (![A_55, B_56]: (r1_tarski(A_55, k2_xboole_0(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.20/1.26  tff(c_100, plain, (r1_tarski(k1_tarski('#skF_3'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_62, c_97])).
% 2.20/1.26  tff(c_116, plain, (r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_115, c_100])).
% 2.20/1.26  tff(c_308, plain, (![B_84, A_85]: (B_84=A_85 | ~r1_tarski(B_84, A_85) | ~r1_tarski(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.20/1.26  tff(c_320, plain, (k1_tarski('#skF_3')='#skF_4' | ~r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_116, c_308])).
% 2.20/1.26  tff(c_327, plain, (~r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_320])).
% 2.20/1.26  tff(c_330, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))!='#skF_4'), inference(resolution, [status(thm)], [c_127, c_327])).
% 2.20/1.26  tff(c_334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_330])).
% 2.20/1.26  tff(c_335, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_320])).
% 2.20/1.26  tff(c_80, plain, (![A_53]: (k2_tarski(A_53, A_53)=k1_tarski(A_53))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.20/1.26  tff(c_30, plain, (![D_19, B_15]: (r2_hidden(D_19, k2_tarski(D_19, B_15)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.20/1.26  tff(c_86, plain, (![A_53]: (r2_hidden(A_53, k1_tarski(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_30])).
% 2.20/1.26  tff(c_360, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_335, c_86])).
% 2.20/1.26  tff(c_364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_205, c_360])).
% 2.20/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.26  
% 2.20/1.26  Inference rules
% 2.20/1.26  ----------------------
% 2.20/1.26  #Ref     : 0
% 2.20/1.26  #Sup     : 73
% 2.20/1.26  #Fact    : 0
% 2.20/1.26  #Define  : 0
% 2.20/1.26  #Split   : 1
% 2.20/1.26  #Chain   : 0
% 2.20/1.26  #Close   : 0
% 2.20/1.26  
% 2.20/1.26  Ordering : KBO
% 2.20/1.26  
% 2.20/1.26  Simplification rules
% 2.20/1.26  ----------------------
% 2.20/1.26  #Subsume      : 1
% 2.20/1.27  #Demod        : 27
% 2.20/1.27  #Tautology    : 52
% 2.20/1.27  #SimpNegUnit  : 1
% 2.20/1.27  #BackRed      : 9
% 2.20/1.27  
% 2.20/1.27  #Partial instantiations: 0
% 2.20/1.27  #Strategies tried      : 1
% 2.20/1.27  
% 2.20/1.27  Timing (in seconds)
% 2.20/1.27  ----------------------
% 2.20/1.27  Preprocessing        : 0.32
% 2.20/1.27  Parsing              : 0.17
% 2.20/1.27  CNF conversion       : 0.02
% 2.20/1.27  Main loop            : 0.19
% 2.20/1.27  Inferencing          : 0.06
% 2.20/1.27  Reduction            : 0.07
% 2.20/1.27  Demodulation         : 0.05
% 2.20/1.27  BG Simplification    : 0.02
% 2.20/1.27  Subsumption          : 0.03
% 2.20/1.27  Abstraction          : 0.01
% 2.20/1.27  MUC search           : 0.00
% 2.20/1.27  Cooper               : 0.00
% 2.20/1.27  Total                : 0.53
% 2.20/1.27  Index Insertion      : 0.00
% 2.20/1.27  Index Deletion       : 0.00
% 2.20/1.27  Index Matching       : 0.00
% 2.20/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
