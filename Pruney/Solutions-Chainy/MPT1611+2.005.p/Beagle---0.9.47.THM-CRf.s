%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:32 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   59 (  65 expanded)
%              Number of leaves         :   40 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 (  58 expanded)
%              Number of equality atoms :   24 (  28 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k3_lattice3 > k2_yellow_1 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_lattice3 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_lattice3,type,(
    k3_lattice3: $i > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_lattice3,type,(
    k1_lattice3: $i > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_71,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_82,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_80,axiom,(
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

tff(f_85,negated_conjecture,(
    ~ ! [A] : k4_yellow_0(k3_yellow_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_157,plain,(
    ! [B_66,A_67] :
      ( ~ r2_hidden(B_66,A_67)
      | k4_xboole_0(A_67,k1_tarski(B_66)) != A_67 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_162,plain,(
    ! [B_66] : ~ r2_hidden(B_66,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_157])).

tff(c_44,plain,(
    ! [A_42] : k3_tarski(k1_zfmisc_1(A_42)) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_48,plain,(
    ! [A_45] : k9_setfam_1(A_45) = k1_zfmisc_1(A_45) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_54,plain,(
    ! [A_48] : k2_yellow_1(k9_setfam_1(A_48)) = k3_yellow_1(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_57,plain,(
    ! [A_48] : k2_yellow_1(k1_zfmisc_1(A_48)) = k3_yellow_1(A_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_54])).

tff(c_30,plain,(
    ! [C_39,A_35] :
      ( r2_hidden(C_39,k1_zfmisc_1(A_35))
      | ~ r1_tarski(C_39,A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_239,plain,(
    ! [A_83] :
      ( k4_yellow_0(k2_yellow_1(A_83)) = k3_tarski(A_83)
      | ~ r2_hidden(k3_tarski(A_83),A_83)
      | v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_243,plain,(
    ! [A_35] :
      ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_35))) = k3_tarski(k1_zfmisc_1(A_35))
      | v1_xboole_0(k1_zfmisc_1(A_35))
      | ~ r1_tarski(k3_tarski(k1_zfmisc_1(A_35)),A_35) ) ),
    inference(resolution,[status(thm)],[c_30,c_239])).

tff(c_251,plain,(
    ! [A_84] :
      ( k4_yellow_0(k3_yellow_1(A_84)) = A_84
      | v1_xboole_0(k1_zfmisc_1(A_84)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_44,c_57,c_44,c_243])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_257,plain,(
    ! [A_85] :
      ( k1_zfmisc_1(A_85) = k1_xboole_0
      | k4_yellow_0(k3_yellow_1(A_85)) = A_85 ) ),
    inference(resolution,[status(thm)],[c_251,c_2])).

tff(c_56,plain,(
    k4_yellow_0(k3_yellow_1('#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_268,plain,(
    k1_zfmisc_1('#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_56])).

tff(c_284,plain,(
    ! [C_39] :
      ( r2_hidden(C_39,k1_xboole_0)
      | ~ r1_tarski(C_39,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_30])).

tff(c_301,plain,(
    ! [C_88] : ~ r1_tarski(C_88,'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_284])).

tff(c_306,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_8,c_301])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:03:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.24  
% 2.23/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.25  %$ r2_hidden > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k3_lattice3 > k2_yellow_1 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_lattice3 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 2.23/1.25  
% 2.23/1.25  %Foreground sorts:
% 2.23/1.25  
% 2.23/1.25  
% 2.23/1.25  %Background operators:
% 2.23/1.25  
% 2.23/1.25  
% 2.23/1.25  %Foreground operators:
% 2.23/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.25  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.23/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.23/1.25  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.23/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.25  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.23/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.23/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.23/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.23/1.25  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 2.23/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.25  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.23/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.23/1.25  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 2.23/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.23/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.23/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.25  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.23/1.25  
% 2.23/1.26  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.23/1.26  tff(f_39, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.23/1.26  tff(f_65, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.23/1.26  tff(f_67, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.23/1.26  tff(f_71, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 2.23/1.26  tff(f_82, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 2.23/1.26  tff(f_60, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.23/1.26  tff(f_80, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 2.23/1.26  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.23/1.26  tff(f_85, negated_conjecture, ~(![A]: (k4_yellow_0(k3_yellow_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_yellow_1)).
% 2.23/1.26  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.23/1.26  tff(c_12, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.23/1.26  tff(c_157, plain, (![B_66, A_67]: (~r2_hidden(B_66, A_67) | k4_xboole_0(A_67, k1_tarski(B_66))!=A_67)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.23/1.26  tff(c_162, plain, (![B_66]: (~r2_hidden(B_66, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_157])).
% 2.23/1.26  tff(c_44, plain, (![A_42]: (k3_tarski(k1_zfmisc_1(A_42))=A_42)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.23/1.26  tff(c_48, plain, (![A_45]: (k9_setfam_1(A_45)=k1_zfmisc_1(A_45))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.23/1.26  tff(c_54, plain, (![A_48]: (k2_yellow_1(k9_setfam_1(A_48))=k3_yellow_1(A_48))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.23/1.26  tff(c_57, plain, (![A_48]: (k2_yellow_1(k1_zfmisc_1(A_48))=k3_yellow_1(A_48))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_54])).
% 2.23/1.26  tff(c_30, plain, (![C_39, A_35]: (r2_hidden(C_39, k1_zfmisc_1(A_35)) | ~r1_tarski(C_39, A_35))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.23/1.26  tff(c_239, plain, (![A_83]: (k4_yellow_0(k2_yellow_1(A_83))=k3_tarski(A_83) | ~r2_hidden(k3_tarski(A_83), A_83) | v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.23/1.26  tff(c_243, plain, (![A_35]: (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_35)))=k3_tarski(k1_zfmisc_1(A_35)) | v1_xboole_0(k1_zfmisc_1(A_35)) | ~r1_tarski(k3_tarski(k1_zfmisc_1(A_35)), A_35))), inference(resolution, [status(thm)], [c_30, c_239])).
% 2.23/1.26  tff(c_251, plain, (![A_84]: (k4_yellow_0(k3_yellow_1(A_84))=A_84 | v1_xboole_0(k1_zfmisc_1(A_84)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_44, c_57, c_44, c_243])).
% 2.23/1.26  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.26  tff(c_257, plain, (![A_85]: (k1_zfmisc_1(A_85)=k1_xboole_0 | k4_yellow_0(k3_yellow_1(A_85))=A_85)), inference(resolution, [status(thm)], [c_251, c_2])).
% 2.23/1.26  tff(c_56, plain, (k4_yellow_0(k3_yellow_1('#skF_3'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.23/1.26  tff(c_268, plain, (k1_zfmisc_1('#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_257, c_56])).
% 2.23/1.26  tff(c_284, plain, (![C_39]: (r2_hidden(C_39, k1_xboole_0) | ~r1_tarski(C_39, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_268, c_30])).
% 2.23/1.26  tff(c_301, plain, (![C_88]: (~r1_tarski(C_88, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_162, c_284])).
% 2.23/1.26  tff(c_306, plain, $false, inference(resolution, [status(thm)], [c_8, c_301])).
% 2.23/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.26  
% 2.23/1.26  Inference rules
% 2.23/1.26  ----------------------
% 2.23/1.26  #Ref     : 0
% 2.23/1.26  #Sup     : 55
% 2.23/1.26  #Fact    : 0
% 2.23/1.26  #Define  : 0
% 2.23/1.26  #Split   : 0
% 2.23/1.26  #Chain   : 0
% 2.23/1.26  #Close   : 0
% 2.23/1.26  
% 2.23/1.26  Ordering : KBO
% 2.23/1.26  
% 2.23/1.26  Simplification rules
% 2.23/1.26  ----------------------
% 2.23/1.26  #Subsume      : 1
% 2.23/1.26  #Demod        : 10
% 2.23/1.26  #Tautology    : 42
% 2.23/1.26  #SimpNegUnit  : 4
% 2.23/1.26  #BackRed      : 0
% 2.23/1.26  
% 2.23/1.26  #Partial instantiations: 0
% 2.23/1.26  #Strategies tried      : 1
% 2.23/1.26  
% 2.23/1.26  Timing (in seconds)
% 2.23/1.26  ----------------------
% 2.23/1.26  Preprocessing        : 0.34
% 2.23/1.26  Parsing              : 0.18
% 2.23/1.26  CNF conversion       : 0.02
% 2.23/1.26  Main loop            : 0.17
% 2.23/1.26  Inferencing          : 0.06
% 2.23/1.26  Reduction            : 0.06
% 2.23/1.26  Demodulation         : 0.04
% 2.23/1.26  BG Simplification    : 0.02
% 2.23/1.26  Subsumption          : 0.02
% 2.23/1.26  Abstraction          : 0.01
% 2.23/1.26  MUC search           : 0.00
% 2.23/1.26  Cooper               : 0.00
% 2.23/1.26  Total                : 0.53
% 2.23/1.26  Index Insertion      : 0.00
% 2.23/1.26  Index Deletion       : 0.00
% 2.23/1.26  Index Matching       : 0.00
% 2.23/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
