%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:40 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   53 (  59 expanded)
%              Number of leaves         :   31 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   50 (  57 expanded)
%              Number of equality atoms :   26 (  28 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_wellord1 > k2_tarski > #nlpp > k3_relat_1 > k1_wellord2 > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_71,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k2_wellord1(A,k3_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_wellord1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k2_wellord1(A,B) = k3_xboole_0(A,k2_zfmisc_1(B,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

tff(f_74,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_44,plain,(
    ! [A_28] : v1_relat_1(k1_wellord2(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_111,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(A_39,B_40) = k1_xboole_0
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_119,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_111])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_136,plain,(
    ! [A_44,B_45] : k5_xboole_0(A_44,k3_xboole_0(A_44,B_45)) = k4_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_145,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_136])).

tff(c_148,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_145])).

tff(c_38,plain,(
    ! [A_20] :
      ( k3_relat_1(k1_wellord2(A_20)) = A_20
      | ~ v1_relat_1(k1_wellord2(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_52,plain,(
    ! [A_20] : k3_relat_1(k1_wellord2(A_20)) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38])).

tff(c_74,plain,(
    ! [A_33] :
      ( k2_wellord1(A_33,k3_relat_1(A_33)) = A_33
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_83,plain,(
    ! [A_20] :
      ( k2_wellord1(k1_wellord2(A_20),A_20) = k1_wellord2(A_20)
      | ~ v1_relat_1(k1_wellord2(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_74])).

tff(c_87,plain,(
    ! [A_20] : k2_wellord1(k1_wellord2(A_20),A_20) = k1_wellord2(A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_83])).

tff(c_187,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,k2_zfmisc_1(B_55,B_55)) = k2_wellord1(A_54,B_55)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_226,plain,(
    ! [A_60,B_61] :
      ( k5_xboole_0(A_60,k2_wellord1(A_60,B_61)) = k4_xboole_0(A_60,k2_zfmisc_1(B_61,B_61))
      | ~ v1_relat_1(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_14])).

tff(c_243,plain,(
    ! [A_20] :
      ( k5_xboole_0(k1_wellord2(A_20),k1_wellord2(A_20)) = k4_xboole_0(k1_wellord2(A_20),k2_zfmisc_1(A_20,A_20))
      | ~ v1_relat_1(k1_wellord2(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_226])).

tff(c_249,plain,(
    ! [A_20] : k4_xboole_0(k1_wellord2(A_20),k2_zfmisc_1(A_20,A_20)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_148,c_243])).

tff(c_97,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | k4_xboole_0(A_35,B_36) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,(
    ~ r1_tarski(k1_wellord2('#skF_3'),k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_101,plain,(
    k4_xboole_0(k1_wellord2('#skF_3'),k2_zfmisc_1('#skF_3','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_97,c_46])).

tff(c_252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_101])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n008.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 11:03:45 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.35  
% 2.21/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.35  %$ r2_hidden > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_wellord1 > k2_tarski > #nlpp > k3_relat_1 > k1_wellord2 > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 2.21/1.35  
% 2.21/1.35  %Foreground sorts:
% 2.21/1.35  
% 2.21/1.35  
% 2.21/1.35  %Background operators:
% 2.21/1.35  
% 2.21/1.35  
% 2.21/1.35  %Foreground operators:
% 2.21/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.21/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.21/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.35  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.21/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.21/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.21/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.35  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.21/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.21/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.21/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.21/1.35  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.21/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.21/1.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.21/1.35  
% 2.21/1.36  tff(f_71, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 2.21/1.36  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.21/1.36  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.21/1.36  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.21/1.36  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.21/1.36  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 2.21/1.36  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k2_wellord1(A, k3_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_wellord1)).
% 2.21/1.36  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (k2_wellord1(A, B) = k3_xboole_0(A, k2_zfmisc_1(B, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_wellord1)).
% 2.21/1.36  tff(f_74, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_wellord2)).
% 2.21/1.36  tff(c_44, plain, (![A_28]: (v1_relat_1(k1_wellord2(A_28)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.21/1.36  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.21/1.36  tff(c_111, plain, (![A_39, B_40]: (k4_xboole_0(A_39, B_40)=k1_xboole_0 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.21/1.36  tff(c_119, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_111])).
% 2.21/1.36  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.21/1.36  tff(c_136, plain, (![A_44, B_45]: (k5_xboole_0(A_44, k3_xboole_0(A_44, B_45))=k4_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.21/1.36  tff(c_145, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_136])).
% 2.21/1.36  tff(c_148, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_119, c_145])).
% 2.21/1.36  tff(c_38, plain, (![A_20]: (k3_relat_1(k1_wellord2(A_20))=A_20 | ~v1_relat_1(k1_wellord2(A_20)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.21/1.36  tff(c_52, plain, (![A_20]: (k3_relat_1(k1_wellord2(A_20))=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38])).
% 2.21/1.36  tff(c_74, plain, (![A_33]: (k2_wellord1(A_33, k3_relat_1(A_33))=A_33 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.21/1.36  tff(c_83, plain, (![A_20]: (k2_wellord1(k1_wellord2(A_20), A_20)=k1_wellord2(A_20) | ~v1_relat_1(k1_wellord2(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_74])).
% 2.21/1.36  tff(c_87, plain, (![A_20]: (k2_wellord1(k1_wellord2(A_20), A_20)=k1_wellord2(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_83])).
% 2.21/1.36  tff(c_187, plain, (![A_54, B_55]: (k3_xboole_0(A_54, k2_zfmisc_1(B_55, B_55))=k2_wellord1(A_54, B_55) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.21/1.36  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.21/1.36  tff(c_226, plain, (![A_60, B_61]: (k5_xboole_0(A_60, k2_wellord1(A_60, B_61))=k4_xboole_0(A_60, k2_zfmisc_1(B_61, B_61)) | ~v1_relat_1(A_60))), inference(superposition, [status(thm), theory('equality')], [c_187, c_14])).
% 2.21/1.36  tff(c_243, plain, (![A_20]: (k5_xboole_0(k1_wellord2(A_20), k1_wellord2(A_20))=k4_xboole_0(k1_wellord2(A_20), k2_zfmisc_1(A_20, A_20)) | ~v1_relat_1(k1_wellord2(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_226])).
% 2.21/1.36  tff(c_249, plain, (![A_20]: (k4_xboole_0(k1_wellord2(A_20), k2_zfmisc_1(A_20, A_20))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_148, c_243])).
% 2.21/1.36  tff(c_97, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | k4_xboole_0(A_35, B_36)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.21/1.36  tff(c_46, plain, (~r1_tarski(k1_wellord2('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.21/1.36  tff(c_101, plain, (k4_xboole_0(k1_wellord2('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_97, c_46])).
% 2.21/1.36  tff(c_252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_249, c_101])).
% 2.21/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.36  
% 2.21/1.36  Inference rules
% 2.21/1.36  ----------------------
% 2.21/1.36  #Ref     : 0
% 2.21/1.36  #Sup     : 43
% 2.21/1.36  #Fact    : 0
% 2.21/1.36  #Define  : 0
% 2.21/1.36  #Split   : 0
% 2.21/1.36  #Chain   : 0
% 2.21/1.36  #Close   : 0
% 2.21/1.36  
% 2.21/1.36  Ordering : KBO
% 2.21/1.36  
% 2.21/1.36  Simplification rules
% 2.21/1.36  ----------------------
% 2.21/1.36  #Subsume      : 0
% 2.21/1.36  #Demod        : 18
% 2.21/1.36  #Tautology    : 35
% 2.21/1.36  #SimpNegUnit  : 0
% 2.21/1.36  #BackRed      : 1
% 2.21/1.36  
% 2.21/1.36  #Partial instantiations: 0
% 2.21/1.36  #Strategies tried      : 1
% 2.21/1.36  
% 2.21/1.36  Timing (in seconds)
% 2.21/1.36  ----------------------
% 2.21/1.36  Preprocessing        : 0.39
% 2.21/1.36  Parsing              : 0.19
% 2.21/1.36  CNF conversion       : 0.02
% 2.21/1.36  Main loop            : 0.16
% 2.21/1.36  Inferencing          : 0.06
% 2.21/1.36  Reduction            : 0.05
% 2.21/1.36  Demodulation         : 0.04
% 2.21/1.36  BG Simplification    : 0.02
% 2.21/1.36  Subsumption          : 0.03
% 2.21/1.36  Abstraction          : 0.01
% 2.21/1.36  MUC search           : 0.00
% 2.21/1.36  Cooper               : 0.00
% 2.21/1.36  Total                : 0.58
% 2.21/1.36  Index Insertion      : 0.00
% 2.21/1.36  Index Deletion       : 0.00
% 2.21/1.36  Index Matching       : 0.00
% 2.21/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
