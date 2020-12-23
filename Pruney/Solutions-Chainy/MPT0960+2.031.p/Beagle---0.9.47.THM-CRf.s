%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:41 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   57 (  63 expanded)
%              Number of leaves         :   35 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  55 expanded)
%              Number of equality atoms :   25 (  27 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k1_wellord2 > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_73,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_71,axiom,(
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

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k2_wellord1(A,k3_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_wellord1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k2_wellord1(A,B) = k3_xboole_0(A,k2_zfmisc_1(B,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

tff(f_76,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_46,plain,(
    ! [A_39] : v1_relat_1(k1_wellord2(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_75,plain,(
    ! [A_46,B_47] :
      ( k4_xboole_0(A_46,B_47) = k1_xboole_0
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_79,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_75])).

tff(c_8,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_146,plain,(
    ! [A_60,B_61] : k5_xboole_0(A_60,k3_xboole_0(A_60,B_61)) = k4_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_155,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_146])).

tff(c_158,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_155])).

tff(c_40,plain,(
    ! [A_31] :
      ( k3_relat_1(k1_wellord2(A_31)) = A_31
      | ~ v1_relat_1(k1_wellord2(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_54,plain,(
    ! [A_31] : k3_relat_1(k1_wellord2(A_31)) = A_31 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40])).

tff(c_105,plain,(
    ! [A_54] :
      ( k2_wellord1(A_54,k3_relat_1(A_54)) = A_54
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_114,plain,(
    ! [A_31] :
      ( k2_wellord1(k1_wellord2(A_31),A_31) = k1_wellord2(A_31)
      | ~ v1_relat_1(k1_wellord2(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_105])).

tff(c_118,plain,(
    ! [A_31] : k2_wellord1(k1_wellord2(A_31),A_31) = k1_wellord2(A_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_114])).

tff(c_175,plain,(
    ! [A_66,B_67] :
      ( k3_xboole_0(A_66,k2_zfmisc_1(B_67,B_67)) = k2_wellord1(A_66,B_67)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_207,plain,(
    ! [A_73,B_74] :
      ( k5_xboole_0(A_73,k2_wellord1(A_73,B_74)) = k4_xboole_0(A_73,k2_zfmisc_1(B_74,B_74))
      | ~ v1_relat_1(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_6])).

tff(c_222,plain,(
    ! [A_31] :
      ( k5_xboole_0(k1_wellord2(A_31),k1_wellord2(A_31)) = k4_xboole_0(k1_wellord2(A_31),k2_zfmisc_1(A_31,A_31))
      | ~ v1_relat_1(k1_wellord2(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_207])).

tff(c_228,plain,(
    ! [A_31] : k4_xboole_0(k1_wellord2(A_31),k2_zfmisc_1(A_31,A_31)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_158,c_222])).

tff(c_128,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | k4_xboole_0(A_56,B_57) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    ~ r1_tarski(k1_wellord2('#skF_3'),k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_136,plain,(
    k4_xboole_0(k1_wellord2('#skF_3'),k2_zfmisc_1('#skF_3','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_128,c_48])).

tff(c_231,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:34:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.30  
% 2.12/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.30  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k1_wellord2 > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 2.12/1.30  
% 2.12/1.30  %Foreground sorts:
% 2.12/1.30  
% 2.12/1.30  
% 2.12/1.30  %Background operators:
% 2.12/1.30  
% 2.12/1.30  
% 2.12/1.30  %Foreground operators:
% 2.12/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.12/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.12/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.12/1.30  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.12/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.12/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.12/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.12/1.30  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.12/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.12/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.12/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.12/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.12/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.12/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.12/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.12/1.30  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.12/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.12/1.30  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.12/1.30  
% 2.12/1.31  tff(f_73, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 2.12/1.31  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.12/1.31  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.12/1.31  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.12/1.31  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.12/1.31  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 2.12/1.31  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (k2_wellord1(A, k3_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_wellord1)).
% 2.12/1.31  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (k2_wellord1(A, B) = k3_xboole_0(A, k2_zfmisc_1(B, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_wellord1)).
% 2.12/1.31  tff(f_76, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_wellord2)).
% 2.12/1.31  tff(c_46, plain, (![A_39]: (v1_relat_1(k1_wellord2(A_39)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.12/1.31  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.12/1.31  tff(c_75, plain, (![A_46, B_47]: (k4_xboole_0(A_46, B_47)=k1_xboole_0 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.31  tff(c_79, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_75])).
% 2.12/1.31  tff(c_8, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.12/1.31  tff(c_146, plain, (![A_60, B_61]: (k5_xboole_0(A_60, k3_xboole_0(A_60, B_61))=k4_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.31  tff(c_155, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_146])).
% 2.12/1.31  tff(c_158, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_79, c_155])).
% 2.12/1.31  tff(c_40, plain, (![A_31]: (k3_relat_1(k1_wellord2(A_31))=A_31 | ~v1_relat_1(k1_wellord2(A_31)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.12/1.31  tff(c_54, plain, (![A_31]: (k3_relat_1(k1_wellord2(A_31))=A_31)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40])).
% 2.12/1.31  tff(c_105, plain, (![A_54]: (k2_wellord1(A_54, k3_relat_1(A_54))=A_54 | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.12/1.31  tff(c_114, plain, (![A_31]: (k2_wellord1(k1_wellord2(A_31), A_31)=k1_wellord2(A_31) | ~v1_relat_1(k1_wellord2(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_105])).
% 2.12/1.31  tff(c_118, plain, (![A_31]: (k2_wellord1(k1_wellord2(A_31), A_31)=k1_wellord2(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_114])).
% 2.12/1.31  tff(c_175, plain, (![A_66, B_67]: (k3_xboole_0(A_66, k2_zfmisc_1(B_67, B_67))=k2_wellord1(A_66, B_67) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.12/1.31  tff(c_6, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.31  tff(c_207, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k2_wellord1(A_73, B_74))=k4_xboole_0(A_73, k2_zfmisc_1(B_74, B_74)) | ~v1_relat_1(A_73))), inference(superposition, [status(thm), theory('equality')], [c_175, c_6])).
% 2.12/1.31  tff(c_222, plain, (![A_31]: (k5_xboole_0(k1_wellord2(A_31), k1_wellord2(A_31))=k4_xboole_0(k1_wellord2(A_31), k2_zfmisc_1(A_31, A_31)) | ~v1_relat_1(k1_wellord2(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_118, c_207])).
% 2.12/1.31  tff(c_228, plain, (![A_31]: (k4_xboole_0(k1_wellord2(A_31), k2_zfmisc_1(A_31, A_31))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_158, c_222])).
% 2.12/1.31  tff(c_128, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | k4_xboole_0(A_56, B_57)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.31  tff(c_48, plain, (~r1_tarski(k1_wellord2('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.12/1.31  tff(c_136, plain, (k4_xboole_0(k1_wellord2('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_128, c_48])).
% 2.12/1.31  tff(c_231, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_228, c_136])).
% 2.12/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.31  
% 2.12/1.31  Inference rules
% 2.12/1.31  ----------------------
% 2.12/1.31  #Ref     : 0
% 2.12/1.31  #Sup     : 39
% 2.12/1.31  #Fact    : 0
% 2.12/1.31  #Define  : 0
% 2.12/1.31  #Split   : 0
% 2.12/1.31  #Chain   : 0
% 2.12/1.31  #Close   : 0
% 2.12/1.31  
% 2.12/1.31  Ordering : KBO
% 2.12/1.31  
% 2.12/1.32  Simplification rules
% 2.12/1.32  ----------------------
% 2.12/1.32  #Subsume      : 0
% 2.12/1.32  #Demod        : 14
% 2.12/1.32  #Tautology    : 35
% 2.12/1.32  #SimpNegUnit  : 0
% 2.12/1.32  #BackRed      : 1
% 2.12/1.32  
% 2.12/1.32  #Partial instantiations: 0
% 2.12/1.32  #Strategies tried      : 1
% 2.12/1.32  
% 2.12/1.32  Timing (in seconds)
% 2.12/1.32  ----------------------
% 2.12/1.32  Preprocessing        : 0.35
% 2.12/1.32  Parsing              : 0.19
% 2.12/1.32  CNF conversion       : 0.02
% 2.12/1.32  Main loop            : 0.15
% 2.12/1.32  Inferencing          : 0.06
% 2.12/1.32  Reduction            : 0.05
% 2.12/1.32  Demodulation         : 0.04
% 2.12/1.32  BG Simplification    : 0.02
% 2.12/1.32  Subsumption          : 0.02
% 2.12/1.32  Abstraction          : 0.01
% 2.12/1.32  MUC search           : 0.00
% 2.12/1.32  Cooper               : 0.00
% 2.12/1.32  Total                : 0.53
% 2.12/1.32  Index Insertion      : 0.00
% 2.12/1.32  Index Deletion       : 0.00
% 2.12/1.32  Index Matching       : 0.00
% 2.12/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
