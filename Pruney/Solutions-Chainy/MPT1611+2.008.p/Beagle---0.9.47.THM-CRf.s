%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:32 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 193 expanded)
%              Number of leaves         :   31 (  82 expanded)
%              Depth                    :   10
%              Number of atoms          :   71 ( 253 expanded)
%              Number of equality atoms :   45 ( 165 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k4_yellow_0,type,(
    k4_yellow_0: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A] : k4_yellow_0(k3_yellow_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_69,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_52,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_51,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(c_42,plain,(
    k4_yellow_0(k3_yellow_1('#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    ! [A_15] : k3_tarski(k1_zfmisc_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36,plain,(
    ! [A_16] : k9_setfam_1(A_16) = k1_zfmisc_1(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_40,plain,(
    ! [A_18] : k2_yellow_1(k9_setfam_1(A_18)) = k3_yellow_1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_43,plain,(
    ! [A_18] : k2_yellow_1(k1_zfmisc_1(A_18)) = k3_yellow_1(A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_40])).

tff(c_16,plain,(
    ! [C_10,A_6] :
      ( r2_hidden(C_10,k1_zfmisc_1(A_6))
      | ~ r1_tarski(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_139,plain,(
    ! [A_38] :
      ( k4_yellow_0(k2_yellow_1(A_38)) = k3_tarski(A_38)
      | ~ r2_hidden(k3_tarski(A_38),A_38)
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_150,plain,(
    ! [A_6] :
      ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_6))) = k3_tarski(k1_zfmisc_1(A_6))
      | v1_xboole_0(k1_zfmisc_1(A_6))
      | ~ r1_tarski(k3_tarski(k1_zfmisc_1(A_6)),A_6) ) ),
    inference(resolution,[status(thm)],[c_16,c_139])).

tff(c_166,plain,(
    ! [A_39] :
      ( k4_yellow_0(k3_yellow_1(A_39)) = A_39
      | v1_xboole_0(k1_zfmisc_1(A_39)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_34,c_43,c_34,c_150])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_330,plain,(
    ! [A_615] :
      ( k1_zfmisc_1(A_615) = k1_xboole_0
      | k4_yellow_0(k3_yellow_1(A_615)) = A_615 ) ),
    inference(resolution,[status(thm)],[c_166,c_2])).

tff(c_349,plain,(
    k1_zfmisc_1('#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_42])).

tff(c_368,plain,(
    k3_tarski(k1_xboole_0) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_34])).

tff(c_30,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_387,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_30])).

tff(c_10,plain,(
    ! [A_4] : k2_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_78,plain,(
    k3_tarski(k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_34])).

tff(c_100,plain,(
    ! [A_27] : k2_yellow_1(k1_zfmisc_1(A_27)) = k3_yellow_1(A_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_40])).

tff(c_109,plain,(
    k2_yellow_1(k1_tarski(k1_xboole_0)) = k3_yellow_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_100])).

tff(c_92,plain,(
    ! [C_25,A_26] :
      ( r2_hidden(C_25,k1_zfmisc_1(A_26))
      | ~ r1_tarski(C_25,A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_95,plain,(
    ! [C_25] :
      ( r2_hidden(C_25,k1_tarski(k1_xboole_0))
      | ~ r1_tarski(C_25,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_92])).

tff(c_143,plain,
    ( k4_yellow_0(k2_yellow_1(k1_tarski(k1_xboole_0))) = k3_tarski(k1_tarski(k1_xboole_0))
    | v1_xboole_0(k1_tarski(k1_xboole_0))
    | ~ r1_tarski(k3_tarski(k1_tarski(k1_xboole_0)),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_95,c_139])).

tff(c_159,plain,
    ( k4_yellow_0(k3_yellow_1(k1_xboole_0)) = k1_xboole_0
    | v1_xboole_0(k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_78,c_109,c_78,c_143])).

tff(c_174,plain,(
    v1_xboole_0(k1_tarski(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_178,plain,(
    k1_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_174,c_2])).

tff(c_26,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | k2_xboole_0(k1_tarski(A_11),k1_tarski(B_12)) != k1_tarski(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_192,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | k2_xboole_0(k1_tarski(A_11),k1_xboole_0) != k1_tarski(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_26])).

tff(c_219,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_192])).

tff(c_200,plain,(
    ! [A_11] : k1_xboole_0 = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_192])).

tff(c_272,plain,(
    ! [A_327] : A_327 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_200])).

tff(c_319,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_42])).

tff(c_320,plain,(
    k4_yellow_0(k3_yellow_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_400,plain,(
    k4_yellow_0(k3_yellow_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_387,c_320])).

tff(c_411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_400])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:49:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.28  
% 2.07/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.29  %$ r2_hidden > r1_tarski > v1_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 2.07/1.29  
% 2.07/1.29  %Foreground sorts:
% 2.07/1.29  
% 2.07/1.29  
% 2.07/1.29  %Background operators:
% 2.07/1.29  
% 2.07/1.29  
% 2.07/1.29  %Foreground operators:
% 2.07/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.07/1.29  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.07/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.29  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.07/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.29  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 2.07/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.07/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.07/1.29  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 2.07/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.07/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.07/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.07/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.07/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.07/1.29  
% 2.07/1.30  tff(f_72, negated_conjecture, ~(![A]: (k4_yellow_0(k3_yellow_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_yellow_1)).
% 2.07/1.30  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.07/1.30  tff(f_58, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.07/1.30  tff(f_60, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 2.07/1.30  tff(f_69, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 2.07/1.30  tff(f_46, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.07/1.30  tff(f_67, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 2.07/1.30  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.07/1.30  tff(f_52, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.07/1.30  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.07/1.30  tff(f_51, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.07/1.30  tff(f_50, axiom, (![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.07/1.30  tff(c_42, plain, (k4_yellow_0(k3_yellow_1('#skF_3'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.07/1.30  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.07/1.30  tff(c_34, plain, (![A_15]: (k3_tarski(k1_zfmisc_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.07/1.30  tff(c_36, plain, (![A_16]: (k9_setfam_1(A_16)=k1_zfmisc_1(A_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.07/1.30  tff(c_40, plain, (![A_18]: (k2_yellow_1(k9_setfam_1(A_18))=k3_yellow_1(A_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.07/1.30  tff(c_43, plain, (![A_18]: (k2_yellow_1(k1_zfmisc_1(A_18))=k3_yellow_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_40])).
% 2.07/1.30  tff(c_16, plain, (![C_10, A_6]: (r2_hidden(C_10, k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.07/1.30  tff(c_139, plain, (![A_38]: (k4_yellow_0(k2_yellow_1(A_38))=k3_tarski(A_38) | ~r2_hidden(k3_tarski(A_38), A_38) | v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.07/1.30  tff(c_150, plain, (![A_6]: (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_6)))=k3_tarski(k1_zfmisc_1(A_6)) | v1_xboole_0(k1_zfmisc_1(A_6)) | ~r1_tarski(k3_tarski(k1_zfmisc_1(A_6)), A_6))), inference(resolution, [status(thm)], [c_16, c_139])).
% 2.07/1.30  tff(c_166, plain, (![A_39]: (k4_yellow_0(k3_yellow_1(A_39))=A_39 | v1_xboole_0(k1_zfmisc_1(A_39)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_34, c_43, c_34, c_150])).
% 2.07/1.30  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.30  tff(c_330, plain, (![A_615]: (k1_zfmisc_1(A_615)=k1_xboole_0 | k4_yellow_0(k3_yellow_1(A_615))=A_615)), inference(resolution, [status(thm)], [c_166, c_2])).
% 2.07/1.30  tff(c_349, plain, (k1_zfmisc_1('#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_330, c_42])).
% 2.07/1.30  tff(c_368, plain, (k3_tarski(k1_xboole_0)='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_349, c_34])).
% 2.07/1.30  tff(c_30, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.07/1.30  tff(c_387, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_368, c_30])).
% 2.07/1.30  tff(c_10, plain, (![A_4]: (k2_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.07/1.30  tff(c_28, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.07/1.30  tff(c_78, plain, (k3_tarski(k1_tarski(k1_xboole_0))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_28, c_34])).
% 2.07/1.30  tff(c_100, plain, (![A_27]: (k2_yellow_1(k1_zfmisc_1(A_27))=k3_yellow_1(A_27))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_40])).
% 2.07/1.30  tff(c_109, plain, (k2_yellow_1(k1_tarski(k1_xboole_0))=k3_yellow_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_100])).
% 2.07/1.30  tff(c_92, plain, (![C_25, A_26]: (r2_hidden(C_25, k1_zfmisc_1(A_26)) | ~r1_tarski(C_25, A_26))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.07/1.30  tff(c_95, plain, (![C_25]: (r2_hidden(C_25, k1_tarski(k1_xboole_0)) | ~r1_tarski(C_25, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_92])).
% 2.07/1.30  tff(c_143, plain, (k4_yellow_0(k2_yellow_1(k1_tarski(k1_xboole_0)))=k3_tarski(k1_tarski(k1_xboole_0)) | v1_xboole_0(k1_tarski(k1_xboole_0)) | ~r1_tarski(k3_tarski(k1_tarski(k1_xboole_0)), k1_xboole_0)), inference(resolution, [status(thm)], [c_95, c_139])).
% 2.07/1.30  tff(c_159, plain, (k4_yellow_0(k3_yellow_1(k1_xboole_0))=k1_xboole_0 | v1_xboole_0(k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_78, c_109, c_78, c_143])).
% 2.07/1.30  tff(c_174, plain, (v1_xboole_0(k1_tarski(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_159])).
% 2.07/1.30  tff(c_178, plain, (k1_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_174, c_2])).
% 2.07/1.30  tff(c_26, plain, (![B_12, A_11]: (B_12=A_11 | k2_xboole_0(k1_tarski(A_11), k1_tarski(B_12))!=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.07/1.30  tff(c_192, plain, (![A_11]: (k1_xboole_0=A_11 | k2_xboole_0(k1_tarski(A_11), k1_xboole_0)!=k1_tarski(A_11))), inference(superposition, [status(thm), theory('equality')], [c_178, c_26])).
% 2.07/1.30  tff(c_219, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_192])).
% 2.07/1.30  tff(c_200, plain, (![A_11]: (k1_xboole_0=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_192])).
% 2.07/1.30  tff(c_272, plain, (![A_327]: (A_327='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_219, c_200])).
% 2.07/1.30  tff(c_319, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_272, c_42])).
% 2.07/1.30  tff(c_320, plain, (k4_yellow_0(k3_yellow_1(k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_159])).
% 2.07/1.30  tff(c_400, plain, (k4_yellow_0(k3_yellow_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_387, c_387, c_320])).
% 2.07/1.30  tff(c_411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_400])).
% 2.07/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.30  
% 2.07/1.30  Inference rules
% 2.07/1.30  ----------------------
% 2.07/1.30  #Ref     : 0
% 2.07/1.30  #Sup     : 107
% 2.07/1.30  #Fact    : 0
% 2.07/1.30  #Define  : 0
% 2.07/1.30  #Split   : 1
% 2.07/1.30  #Chain   : 0
% 2.07/1.30  #Close   : 0
% 2.07/1.30  
% 2.07/1.30  Ordering : KBO
% 2.07/1.30  
% 2.07/1.30  Simplification rules
% 2.07/1.30  ----------------------
% 2.07/1.30  #Subsume      : 10
% 2.07/1.30  #Demod        : 56
% 2.07/1.30  #Tautology    : 40
% 2.07/1.30  #SimpNegUnit  : 3
% 2.07/1.30  #BackRed      : 21
% 2.07/1.30  
% 2.07/1.30  #Partial instantiations: 18
% 2.07/1.30  #Strategies tried      : 1
% 2.07/1.30  
% 2.07/1.30  Timing (in seconds)
% 2.07/1.30  ----------------------
% 2.07/1.30  Preprocessing        : 0.29
% 2.07/1.30  Parsing              : 0.16
% 2.07/1.30  CNF conversion       : 0.02
% 2.07/1.30  Main loop            : 0.22
% 2.07/1.30  Inferencing          : 0.09
% 2.07/1.30  Reduction            : 0.06
% 2.07/1.30  Demodulation         : 0.05
% 2.07/1.30  BG Simplification    : 0.01
% 2.07/1.30  Subsumption          : 0.03
% 2.07/1.30  Abstraction          : 0.01
% 2.07/1.30  MUC search           : 0.00
% 2.07/1.30  Cooper               : 0.00
% 2.07/1.30  Total                : 0.55
% 2.07/1.30  Index Insertion      : 0.00
% 2.07/1.30  Index Deletion       : 0.00
% 2.07/1.30  Index Matching       : 0.00
% 2.07/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
