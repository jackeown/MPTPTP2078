%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:19 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   58 (  59 expanded)
%              Number of leaves         :   35 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   51 (  53 expanded)
%              Number of equality atoms :   27 (  28 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_64,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_66,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_42,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_44,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_201,plain,(
    ! [A_76,B_77,C_78] :
      ( r2_hidden('#skF_2'(A_76,B_77,C_78),B_77)
      | ~ r2_hidden(A_76,k10_relat_1(C_78,B_77))
      | ~ v1_relat_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30,plain,(
    ! [A_32] : k1_setfam_1(k1_tarski(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_82,plain,(
    ! [A_50,B_51] : k1_setfam_1(k2_tarski(A_50,B_51)) = k3_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_91,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = k1_setfam_1(k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_82])).

tff(c_94,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_91])).

tff(c_122,plain,(
    ! [A_57,B_58] : k5_xboole_0(A_57,k3_xboole_0(A_57,B_58)) = k4_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_131,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_122])).

tff(c_134,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_131])).

tff(c_26,plain,(
    ! [B_31] : k4_xboole_0(k1_tarski(B_31),k1_tarski(B_31)) != k1_tarski(B_31) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_144,plain,(
    ! [B_31] : k1_tarski(B_31) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_26])).

tff(c_104,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(k1_tarski(A_53),B_54)
      | ~ r2_hidden(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_113,plain,(
    ! [A_53] :
      ( k1_tarski(A_53) = k1_xboole_0
      | ~ r2_hidden(A_53,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_104,c_6])).

tff(c_152,plain,(
    ! [A_53] : ~ r2_hidden(A_53,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_113])).

tff(c_207,plain,(
    ! [A_79,C_80] :
      ( ~ r2_hidden(A_79,k10_relat_1(C_80,k1_xboole_0))
      | ~ v1_relat_1(C_80) ) ),
    inference(resolution,[status(thm)],[c_201,c_152])).

tff(c_218,plain,(
    ! [C_81] :
      ( ~ v1_relat_1(C_81)
      | k10_relat_1(C_81,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_207])).

tff(c_221,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_218])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_221])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:33:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.22  
% 1.95/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.22  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.08/1.22  
% 2.08/1.22  %Foreground sorts:
% 2.08/1.22  
% 2.08/1.22  
% 2.08/1.22  %Background operators:
% 2.08/1.22  
% 2.08/1.22  
% 2.08/1.22  %Foreground operators:
% 2.08/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.08/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.22  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.08/1.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.08/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.08/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.08/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.08/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.08/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.08/1.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.08/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.22  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.08/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.08/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.08/1.22  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.08/1.22  
% 2.08/1.23  tff(f_82, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 2.08/1.23  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.08/1.23  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.08/1.23  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.08/1.23  tff(f_64, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.08/1.23  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.08/1.23  tff(f_66, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.08/1.23  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.08/1.23  tff(f_62, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.08/1.23  tff(f_57, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.08/1.23  tff(f_39, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.08/1.23  tff(c_42, plain, (k10_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.08/1.23  tff(c_44, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.08/1.23  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.08/1.23  tff(c_201, plain, (![A_76, B_77, C_78]: (r2_hidden('#skF_2'(A_76, B_77, C_78), B_77) | ~r2_hidden(A_76, k10_relat_1(C_78, B_77)) | ~v1_relat_1(C_78))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.08/1.23  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.08/1.23  tff(c_30, plain, (![A_32]: (k1_setfam_1(k1_tarski(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.08/1.23  tff(c_10, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.08/1.23  tff(c_82, plain, (![A_50, B_51]: (k1_setfam_1(k2_tarski(A_50, B_51))=k3_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.08/1.23  tff(c_91, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=k1_setfam_1(k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_82])).
% 2.08/1.23  tff(c_94, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_91])).
% 2.08/1.23  tff(c_122, plain, (![A_57, B_58]: (k5_xboole_0(A_57, k3_xboole_0(A_57, B_58))=k4_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.08/1.23  tff(c_131, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_94, c_122])).
% 2.08/1.23  tff(c_134, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_131])).
% 2.08/1.23  tff(c_26, plain, (![B_31]: (k4_xboole_0(k1_tarski(B_31), k1_tarski(B_31))!=k1_tarski(B_31))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.08/1.23  tff(c_144, plain, (![B_31]: (k1_tarski(B_31)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_134, c_26])).
% 2.08/1.23  tff(c_104, plain, (![A_53, B_54]: (r1_tarski(k1_tarski(A_53), B_54) | ~r2_hidden(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.08/1.23  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.08/1.23  tff(c_113, plain, (![A_53]: (k1_tarski(A_53)=k1_xboole_0 | ~r2_hidden(A_53, k1_xboole_0))), inference(resolution, [status(thm)], [c_104, c_6])).
% 2.08/1.23  tff(c_152, plain, (![A_53]: (~r2_hidden(A_53, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_144, c_113])).
% 2.08/1.23  tff(c_207, plain, (![A_79, C_80]: (~r2_hidden(A_79, k10_relat_1(C_80, k1_xboole_0)) | ~v1_relat_1(C_80))), inference(resolution, [status(thm)], [c_201, c_152])).
% 2.08/1.23  tff(c_218, plain, (![C_81]: (~v1_relat_1(C_81) | k10_relat_1(C_81, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_207])).
% 2.08/1.23  tff(c_221, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_218])).
% 2.08/1.23  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_221])).
% 2.08/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.23  
% 2.08/1.23  Inference rules
% 2.08/1.23  ----------------------
% 2.08/1.23  #Ref     : 0
% 2.08/1.23  #Sup     : 36
% 2.08/1.23  #Fact    : 0
% 2.08/1.23  #Define  : 0
% 2.08/1.23  #Split   : 0
% 2.08/1.23  #Chain   : 0
% 2.08/1.23  #Close   : 0
% 2.08/1.23  
% 2.08/1.23  Ordering : KBO
% 2.08/1.23  
% 2.08/1.23  Simplification rules
% 2.08/1.23  ----------------------
% 2.08/1.23  #Subsume      : 0
% 2.08/1.23  #Demod        : 3
% 2.08/1.23  #Tautology    : 29
% 2.08/1.23  #SimpNegUnit  : 4
% 2.08/1.23  #BackRed      : 2
% 2.08/1.23  
% 2.08/1.23  #Partial instantiations: 0
% 2.08/1.23  #Strategies tried      : 1
% 2.08/1.23  
% 2.08/1.23  Timing (in seconds)
% 2.08/1.23  ----------------------
% 2.08/1.24  Preprocessing        : 0.33
% 2.08/1.24  Parsing              : 0.17
% 2.08/1.24  CNF conversion       : 0.02
% 2.08/1.24  Main loop            : 0.14
% 2.08/1.24  Inferencing          : 0.06
% 2.08/1.24  Reduction            : 0.04
% 2.08/1.24  Demodulation         : 0.03
% 2.08/1.24  BG Simplification    : 0.01
% 2.08/1.24  Subsumption          : 0.02
% 2.08/1.24  Abstraction          : 0.01
% 2.08/1.24  MUC search           : 0.00
% 2.08/1.24  Cooper               : 0.00
% 2.08/1.24  Total                : 0.50
% 2.08/1.24  Index Insertion      : 0.00
% 2.08/1.24  Index Deletion       : 0.00
% 2.08/1.24  Index Matching       : 0.00
% 2.08/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
