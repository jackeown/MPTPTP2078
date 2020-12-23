%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:26 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   59 (  78 expanded)
%              Number of leaves         :   37 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  82 expanded)
%              Number of equality atoms :   27 (  40 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k3_xboole_0(B,k2_zfmisc_1(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_83,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_44,plain,(
    ! [A_45] :
      ( r2_hidden('#skF_1'(A_45),A_45)
      | v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_231,plain,(
    ! [A_85,B_86] :
      ( r1_tarski(k1_tarski(A_85),B_86)
      | ~ r2_hidden(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_253,plain,(
    ! [A_89] :
      ( k1_tarski(A_89) = k1_xboole_0
      | ~ r2_hidden(A_89,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_231,c_6])).

tff(c_258,plain,
    ( k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_44,c_253])).

tff(c_259,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_258])).

tff(c_425,plain,(
    ! [B_110,A_111] :
      ( k3_xboole_0(B_110,k2_zfmisc_1(k1_relat_1(B_110),A_111)) = k8_relat_1(A_111,B_110)
      | ~ v1_relat_1(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_284,plain,(
    ! [A_92,B_93] : k5_xboole_0(A_92,k3_xboole_0(A_92,B_93)) = k4_xboole_0(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_92,plain,(
    ! [B_70,A_71] : k5_xboole_0(B_70,A_71) = k5_xboole_0(A_71,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_108,plain,(
    ! [A_71] : k5_xboole_0(k1_xboole_0,A_71) = A_71 ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_10])).

tff(c_291,plain,(
    ! [B_93] : k4_xboole_0(k1_xboole_0,B_93) = k3_xboole_0(k1_xboole_0,B_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_108])).

tff(c_309,plain,(
    ! [B_93] : k3_xboole_0(k1_xboole_0,B_93) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_291])).

tff(c_432,plain,(
    ! [A_111] :
      ( k8_relat_1(A_111,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_309])).

tff(c_445,plain,(
    ! [A_111] : k8_relat_1(A_111,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_432])).

tff(c_48,plain,(
    k8_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_451,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_48])).

tff(c_452,plain,(
    k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_34,plain,(
    ! [B_42] : k4_xboole_0(k1_tarski(B_42),k1_tarski(B_42)) != k1_tarski(B_42) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_492,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1'(k1_xboole_0))) != k1_tarski('#skF_1'(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_34])).

tff(c_501,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_8,c_492])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:31:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.31  
% 2.06/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.31  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.06/1.31  
% 2.06/1.31  %Foreground sorts:
% 2.06/1.31  
% 2.06/1.31  
% 2.06/1.31  %Background operators:
% 2.06/1.31  
% 2.06/1.31  
% 2.06/1.31  %Foreground operators:
% 2.06/1.31  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.06/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.06/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.06/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.06/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.06/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.06/1.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.06/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.06/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.06/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.06/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.06/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.06/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.06/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.06/1.31  
% 2.06/1.32  tff(f_76, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.06/1.32  tff(f_57, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.06/1.32  tff(f_33, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.06/1.32  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k3_xboole_0(B, k2_zfmisc_1(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_relat_1)).
% 2.06/1.32  tff(f_35, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.06/1.32  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.06/1.32  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.06/1.32  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.06/1.32  tff(f_83, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_relat_1)).
% 2.06/1.32  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.06/1.32  tff(c_44, plain, (![A_45]: (r2_hidden('#skF_1'(A_45), A_45) | v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.06/1.32  tff(c_231, plain, (![A_85, B_86]: (r1_tarski(k1_tarski(A_85), B_86) | ~r2_hidden(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.06/1.32  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.32  tff(c_253, plain, (![A_89]: (k1_tarski(A_89)=k1_xboole_0 | ~r2_hidden(A_89, k1_xboole_0))), inference(resolution, [status(thm)], [c_231, c_6])).
% 2.06/1.32  tff(c_258, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0 | v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_253])).
% 2.06/1.32  tff(c_259, plain, (v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_258])).
% 2.06/1.32  tff(c_425, plain, (![B_110, A_111]: (k3_xboole_0(B_110, k2_zfmisc_1(k1_relat_1(B_110), A_111))=k8_relat_1(A_111, B_110) | ~v1_relat_1(B_110))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.06/1.32  tff(c_8, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.06/1.32  tff(c_284, plain, (![A_92, B_93]: (k5_xboole_0(A_92, k3_xboole_0(A_92, B_93))=k4_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.06/1.32  tff(c_92, plain, (![B_70, A_71]: (k5_xboole_0(B_70, A_71)=k5_xboole_0(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.06/1.32  tff(c_10, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.06/1.32  tff(c_108, plain, (![A_71]: (k5_xboole_0(k1_xboole_0, A_71)=A_71)), inference(superposition, [status(thm), theory('equality')], [c_92, c_10])).
% 2.06/1.32  tff(c_291, plain, (![B_93]: (k4_xboole_0(k1_xboole_0, B_93)=k3_xboole_0(k1_xboole_0, B_93))), inference(superposition, [status(thm), theory('equality')], [c_284, c_108])).
% 2.06/1.32  tff(c_309, plain, (![B_93]: (k3_xboole_0(k1_xboole_0, B_93)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_291])).
% 2.06/1.32  tff(c_432, plain, (![A_111]: (k8_relat_1(A_111, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_425, c_309])).
% 2.06/1.32  tff(c_445, plain, (![A_111]: (k8_relat_1(A_111, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_259, c_432])).
% 2.06/1.32  tff(c_48, plain, (k8_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.06/1.32  tff(c_451, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_445, c_48])).
% 2.06/1.32  tff(c_452, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_258])).
% 2.06/1.32  tff(c_34, plain, (![B_42]: (k4_xboole_0(k1_tarski(B_42), k1_tarski(B_42))!=k1_tarski(B_42))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.06/1.32  tff(c_492, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'(k1_xboole_0)))!=k1_tarski('#skF_1'(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_452, c_34])).
% 2.06/1.32  tff(c_501, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_452, c_8, c_492])).
% 2.06/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.32  
% 2.06/1.32  Inference rules
% 2.06/1.32  ----------------------
% 2.06/1.32  #Ref     : 0
% 2.06/1.32  #Sup     : 102
% 2.06/1.32  #Fact    : 0
% 2.06/1.32  #Define  : 0
% 2.06/1.32  #Split   : 1
% 2.06/1.32  #Chain   : 0
% 2.06/1.32  #Close   : 0
% 2.06/1.32  
% 2.06/1.32  Ordering : KBO
% 2.06/1.32  
% 2.06/1.32  Simplification rules
% 2.06/1.32  ----------------------
% 2.06/1.32  #Subsume      : 0
% 2.06/1.32  #Demod        : 36
% 2.06/1.32  #Tautology    : 79
% 2.06/1.32  #SimpNegUnit  : 1
% 2.06/1.32  #BackRed      : 3
% 2.06/1.32  
% 2.06/1.32  #Partial instantiations: 0
% 2.06/1.32  #Strategies tried      : 1
% 2.06/1.32  
% 2.06/1.32  Timing (in seconds)
% 2.06/1.32  ----------------------
% 2.06/1.32  Preprocessing        : 0.29
% 2.06/1.32  Parsing              : 0.15
% 2.06/1.32  CNF conversion       : 0.02
% 2.06/1.32  Main loop            : 0.20
% 2.06/1.32  Inferencing          : 0.08
% 2.06/1.32  Reduction            : 0.07
% 2.06/1.32  Demodulation         : 0.05
% 2.06/1.32  BG Simplification    : 0.02
% 2.06/1.32  Subsumption          : 0.02
% 2.06/1.32  Abstraction          : 0.02
% 2.06/1.32  MUC search           : 0.00
% 2.06/1.32  Cooper               : 0.00
% 2.06/1.32  Total                : 0.52
% 2.06/1.32  Index Insertion      : 0.00
% 2.06/1.32  Index Deletion       : 0.00
% 2.06/1.32  Index Matching       : 0.00
% 2.06/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
