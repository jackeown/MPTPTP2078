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
% DateTime   : Thu Dec  3 09:59:51 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   48 (  52 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 (  62 expanded)
%              Number of equality atoms :   24 (  28 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B)
        & ! [D] :
            ( ( r1_tarski(A,D)
              & r1_tarski(C,D) )
           => r1_tarski(B,D) ) )
     => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_62,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_36,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [C_5,A_3,B_4] :
      ( r1_tarski(C_5,'#skF_1'(A_3,B_4,C_5))
      | k2_xboole_0(A_3,C_5) = B_4
      | ~ r1_tarski(C_5,B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_341,plain,(
    ! [B_85,A_86,C_87] :
      ( ~ r1_tarski(B_85,'#skF_1'(A_86,B_85,C_87))
      | k2_xboole_0(A_86,C_87) = B_85
      | ~ r1_tarski(C_87,B_85)
      | ~ r1_tarski(A_86,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_345,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(B_4,B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_341])).

tff(c_349,plain,(
    ! [A_88,B_89] :
      ( k2_xboole_0(A_88,B_89) = B_89
      | ~ r1_tarski(A_88,B_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_345])).

tff(c_361,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36,c_349])).

tff(c_14,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_389,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_14])).

tff(c_16,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_83,plain,(
    ! [A_43,B_44] : k1_setfam_1(k2_tarski(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_224,plain,(
    ! [B_57,A_58] : k1_setfam_1(k2_tarski(B_57,A_58)) = k3_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_83])).

tff(c_30,plain,(
    ! [A_33,B_34] : k1_setfam_1(k2_tarski(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_230,plain,(
    ! [B_57,A_58] : k3_xboole_0(B_57,A_58) = k3_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_30])).

tff(c_440,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_230])).

tff(c_38,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_299,plain,(
    ! [C_68,A_69,B_70] :
      ( k7_relat_1(k7_relat_1(C_68,A_69),B_70) = k7_relat_1(C_68,k3_xboole_0(A_69,B_70))
      | ~ v1_relat_1(C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_34,plain,(
    k7_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') != k7_relat_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_308,plain,
    ( k7_relat_1('#skF_4',k3_xboole_0('#skF_3','#skF_2')) != k7_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_34])).

tff(c_317,plain,(
    k7_relat_1('#skF_4',k3_xboole_0('#skF_3','#skF_2')) != k7_relat_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_308])).

tff(c_458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_317])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n011.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 19:08:42 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.18/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.31  
% 2.01/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.31  %$ r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.01/1.31  
% 2.01/1.31  %Foreground sorts:
% 2.01/1.31  
% 2.01/1.31  
% 2.01/1.31  %Background operators:
% 2.01/1.31  
% 2.01/1.31  
% 2.01/1.31  %Foreground operators:
% 2.01/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.01/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.01/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.01/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.01/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.01/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.01/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.01/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.01/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.01/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.01/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.01/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.01/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.01/1.31  
% 2.35/1.32  tff(f_73, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 2.35/1.32  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.35/1.32  tff(f_44, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 2.35/1.32  tff(f_46, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.35/1.32  tff(f_48, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.35/1.32  tff(f_62, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.35/1.32  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 2.35/1.32  tff(c_36, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.35/1.32  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.35/1.32  tff(c_10, plain, (![C_5, A_3, B_4]: (r1_tarski(C_5, '#skF_1'(A_3, B_4, C_5)) | k2_xboole_0(A_3, C_5)=B_4 | ~r1_tarski(C_5, B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.35/1.32  tff(c_341, plain, (![B_85, A_86, C_87]: (~r1_tarski(B_85, '#skF_1'(A_86, B_85, C_87)) | k2_xboole_0(A_86, C_87)=B_85 | ~r1_tarski(C_87, B_85) | ~r1_tarski(A_86, B_85))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.35/1.32  tff(c_345, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(B_4, B_4) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_10, c_341])).
% 2.35/1.32  tff(c_349, plain, (![A_88, B_89]: (k2_xboole_0(A_88, B_89)=B_89 | ~r1_tarski(A_88, B_89))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_345])).
% 2.35/1.32  tff(c_361, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_36, c_349])).
% 2.35/1.32  tff(c_14, plain, (![A_7, B_8]: (k3_xboole_0(A_7, k2_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.35/1.32  tff(c_389, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_361, c_14])).
% 2.35/1.32  tff(c_16, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.35/1.32  tff(c_83, plain, (![A_43, B_44]: (k1_setfam_1(k2_tarski(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.35/1.32  tff(c_224, plain, (![B_57, A_58]: (k1_setfam_1(k2_tarski(B_57, A_58))=k3_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_16, c_83])).
% 2.35/1.32  tff(c_30, plain, (![A_33, B_34]: (k1_setfam_1(k2_tarski(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.35/1.32  tff(c_230, plain, (![B_57, A_58]: (k3_xboole_0(B_57, A_58)=k3_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_224, c_30])).
% 2.35/1.32  tff(c_440, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_389, c_230])).
% 2.35/1.32  tff(c_38, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.35/1.32  tff(c_299, plain, (![C_68, A_69, B_70]: (k7_relat_1(k7_relat_1(C_68, A_69), B_70)=k7_relat_1(C_68, k3_xboole_0(A_69, B_70)) | ~v1_relat_1(C_68))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.35/1.32  tff(c_34, plain, (k7_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')!=k7_relat_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.35/1.32  tff(c_308, plain, (k7_relat_1('#skF_4', k3_xboole_0('#skF_3', '#skF_2'))!=k7_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_299, c_34])).
% 2.35/1.32  tff(c_317, plain, (k7_relat_1('#skF_4', k3_xboole_0('#skF_3', '#skF_2'))!=k7_relat_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_308])).
% 2.35/1.32  tff(c_458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_440, c_317])).
% 2.35/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.32  
% 2.35/1.32  Inference rules
% 2.35/1.32  ----------------------
% 2.35/1.32  #Ref     : 0
% 2.35/1.32  #Sup     : 103
% 2.35/1.32  #Fact    : 0
% 2.35/1.32  #Define  : 0
% 2.35/1.32  #Split   : 1
% 2.35/1.32  #Chain   : 0
% 2.35/1.32  #Close   : 0
% 2.35/1.32  
% 2.35/1.32  Ordering : KBO
% 2.35/1.32  
% 2.35/1.32  Simplification rules
% 2.35/1.32  ----------------------
% 2.35/1.32  #Subsume      : 2
% 2.35/1.32  #Demod        : 22
% 2.35/1.32  #Tautology    : 78
% 2.35/1.32  #SimpNegUnit  : 0
% 2.35/1.32  #BackRed      : 1
% 2.35/1.32  
% 2.35/1.32  #Partial instantiations: 0
% 2.35/1.32  #Strategies tried      : 1
% 2.35/1.32  
% 2.35/1.32  Timing (in seconds)
% 2.35/1.32  ----------------------
% 2.35/1.32  Preprocessing        : 0.29
% 2.35/1.32  Parsing              : 0.15
% 2.35/1.32  CNF conversion       : 0.02
% 2.35/1.32  Main loop            : 0.22
% 2.35/1.32  Inferencing          : 0.08
% 2.35/1.32  Reduction            : 0.08
% 2.35/1.32  Demodulation         : 0.06
% 2.35/1.32  BG Simplification    : 0.01
% 2.35/1.32  Subsumption          : 0.04
% 2.35/1.32  Abstraction          : 0.01
% 2.35/1.32  MUC search           : 0.00
% 2.35/1.32  Cooper               : 0.00
% 2.35/1.32  Total                : 0.54
% 2.35/1.32  Index Insertion      : 0.00
% 2.35/1.32  Index Deletion       : 0.00
% 2.35/1.32  Index Matching       : 0.00
% 2.35/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
