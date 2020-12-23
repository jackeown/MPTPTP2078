%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:28 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   59 (  95 expanded)
%              Number of leaves         :   36 (  49 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 ( 135 expanded)
%              Number of equality atoms :   26 (  46 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_106,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_36,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_38,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_109,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_112,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_54,plain,(
    ! [A_33] :
      ( r2_hidden('#skF_4'(A_33),A_33)
      | v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_207,plain,(
    ! [C_84,B_85,A_86] :
      ( r2_hidden(C_84,B_85)
      | ~ r2_hidden(C_84,A_86)
      | ~ r1_tarski(A_86,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_224,plain,(
    ! [A_88,B_89] :
      ( r2_hidden('#skF_4'(A_88),B_89)
      | ~ r1_tarski(A_88,B_89)
      | v1_relat_1(A_88) ) ),
    inference(resolution,[status(thm)],[c_54,c_207])).

tff(c_16,plain,(
    ! [C_17,A_13] :
      ( C_17 = A_13
      | ~ r2_hidden(C_17,k1_tarski(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_320,plain,(
    ! [A_111,A_112] :
      ( A_111 = '#skF_4'(A_112)
      | ~ r1_tarski(A_112,k1_tarski(A_111))
      | v1_relat_1(A_112) ) ),
    inference(resolution,[status(thm)],[c_224,c_16])).

tff(c_340,plain,(
    ! [A_111] :
      ( A_111 = '#skF_4'(k1_xboole_0)
      | v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_320])).

tff(c_341,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_340])).

tff(c_58,plain,(
    ! [A_53] :
      ( k10_relat_1(A_53,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_346,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_341,c_58])).

tff(c_159,plain,(
    ! [A_77,B_78] : k4_xboole_0(A_77,k4_xboole_0(A_77,B_78)) = k3_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_169,plain,(
    ! [B_78] : k3_xboole_0(k1_xboole_0,B_78) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_12])).

tff(c_60,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_377,plain,(
    ! [B_117,A_118] :
      ( k10_relat_1(B_117,k3_xboole_0(k2_relat_1(B_117),A_118)) = k10_relat_1(B_117,A_118)
      | ~ v1_relat_1(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_386,plain,(
    ! [A_118] :
      ( k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_118)) = k10_relat_1(k1_xboole_0,A_118)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_377])).

tff(c_390,plain,(
    ! [A_118] : k10_relat_1(k1_xboole_0,A_118) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_346,c_169,c_386])).

tff(c_64,plain,(
    k10_relat_1(k1_xboole_0,'#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_394,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_64])).

tff(c_401,plain,(
    '#skF_4'(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_340])).

tff(c_395,plain,(
    ! [A_111] : A_111 = '#skF_4'(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_340])).

tff(c_623,plain,(
    ! [A_1117] : k1_xboole_0 = A_1117 ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_395])).

tff(c_692,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:50:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.57  
% 2.91/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.57  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5
% 2.91/1.57  
% 2.91/1.57  %Foreground sorts:
% 2.91/1.57  
% 2.91/1.57  
% 2.91/1.57  %Background operators:
% 2.91/1.57  
% 2.91/1.57  
% 2.91/1.57  %Foreground operators:
% 2.91/1.57  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.91/1.57  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.91/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.91/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.91/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.91/1.57  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.91/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.91/1.57  tff('#skF_7', type, '#skF_7': $i).
% 2.91/1.57  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.91/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.91/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.91/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.91/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.91/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.57  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.91/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.91/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.91/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.91/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.91/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.91/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.91/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.91/1.57  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.91/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.91/1.57  
% 2.91/1.58  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.91/1.58  tff(f_98, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.91/1.58  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.91/1.58  tff(f_55, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.91/1.58  tff(f_106, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 2.91/1.58  tff(f_36, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.91/1.58  tff(f_38, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.91/1.58  tff(f_109, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.91/1.58  tff(f_102, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 2.91/1.58  tff(f_112, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.91/1.58  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.91/1.58  tff(c_54, plain, (![A_33]: (r2_hidden('#skF_4'(A_33), A_33) | v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.91/1.58  tff(c_207, plain, (![C_84, B_85, A_86]: (r2_hidden(C_84, B_85) | ~r2_hidden(C_84, A_86) | ~r1_tarski(A_86, B_85))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.91/1.58  tff(c_224, plain, (![A_88, B_89]: (r2_hidden('#skF_4'(A_88), B_89) | ~r1_tarski(A_88, B_89) | v1_relat_1(A_88))), inference(resolution, [status(thm)], [c_54, c_207])).
% 2.91/1.58  tff(c_16, plain, (![C_17, A_13]: (C_17=A_13 | ~r2_hidden(C_17, k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.91/1.58  tff(c_320, plain, (![A_111, A_112]: (A_111='#skF_4'(A_112) | ~r1_tarski(A_112, k1_tarski(A_111)) | v1_relat_1(A_112))), inference(resolution, [status(thm)], [c_224, c_16])).
% 2.91/1.58  tff(c_340, plain, (![A_111]: (A_111='#skF_4'(k1_xboole_0) | v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_320])).
% 2.91/1.58  tff(c_341, plain, (v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_340])).
% 2.91/1.58  tff(c_58, plain, (![A_53]: (k10_relat_1(A_53, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.91/1.58  tff(c_346, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_341, c_58])).
% 2.91/1.58  tff(c_159, plain, (![A_77, B_78]: (k4_xboole_0(A_77, k4_xboole_0(A_77, B_78))=k3_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.91/1.58  tff(c_12, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.91/1.58  tff(c_169, plain, (![B_78]: (k3_xboole_0(k1_xboole_0, B_78)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_159, c_12])).
% 2.91/1.58  tff(c_60, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.91/1.58  tff(c_377, plain, (![B_117, A_118]: (k10_relat_1(B_117, k3_xboole_0(k2_relat_1(B_117), A_118))=k10_relat_1(B_117, A_118) | ~v1_relat_1(B_117))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.91/1.58  tff(c_386, plain, (![A_118]: (k10_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_118))=k10_relat_1(k1_xboole_0, A_118) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_60, c_377])).
% 2.91/1.58  tff(c_390, plain, (![A_118]: (k10_relat_1(k1_xboole_0, A_118)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_341, c_346, c_169, c_386])).
% 2.91/1.58  tff(c_64, plain, (k10_relat_1(k1_xboole_0, '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.91/1.58  tff(c_394, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_390, c_64])).
% 2.91/1.58  tff(c_401, plain, ('#skF_4'(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_340])).
% 2.91/1.58  tff(c_395, plain, (![A_111]: (A_111='#skF_4'(k1_xboole_0))), inference(splitRight, [status(thm)], [c_340])).
% 2.91/1.58  tff(c_623, plain, (![A_1117]: (k1_xboole_0=A_1117)), inference(superposition, [status(thm), theory('equality')], [c_401, c_395])).
% 2.91/1.58  tff(c_692, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_623, c_64])).
% 2.91/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.58  
% 2.91/1.58  Inference rules
% 2.91/1.58  ----------------------
% 2.91/1.58  #Ref     : 0
% 2.91/1.58  #Sup     : 164
% 2.91/1.58  #Fact    : 0
% 2.91/1.58  #Define  : 0
% 2.91/1.58  #Split   : 2
% 2.91/1.58  #Chain   : 0
% 2.91/1.58  #Close   : 0
% 2.91/1.58  
% 2.91/1.58  Ordering : KBO
% 2.91/1.58  
% 2.91/1.58  Simplification rules
% 2.91/1.58  ----------------------
% 2.91/1.58  #Subsume      : 41
% 2.91/1.58  #Demod        : 27
% 2.91/1.58  #Tautology    : 45
% 2.91/1.58  #SimpNegUnit  : 27
% 2.91/1.58  #BackRed      : 1
% 2.91/1.58  
% 2.91/1.58  #Partial instantiations: 271
% 2.91/1.58  #Strategies tried      : 1
% 2.91/1.58  
% 2.91/1.58  Timing (in seconds)
% 2.91/1.58  ----------------------
% 2.91/1.59  Preprocessing        : 0.42
% 2.91/1.59  Parsing              : 0.22
% 2.91/1.59  CNF conversion       : 0.03
% 2.91/1.59  Main loop            : 0.29
% 2.91/1.59  Inferencing          : 0.12
% 2.91/1.59  Reduction            : 0.08
% 2.91/1.59  Demodulation         : 0.06
% 2.91/1.59  BG Simplification    : 0.02
% 2.91/1.59  Subsumption          : 0.04
% 2.91/1.59  Abstraction          : 0.02
% 2.91/1.59  MUC search           : 0.00
% 2.91/1.59  Cooper               : 0.00
% 2.91/1.59  Total                : 0.74
% 2.91/1.59  Index Insertion      : 0.00
% 2.91/1.59  Index Deletion       : 0.00
% 2.91/1.59  Index Matching       : 0.00
% 2.91/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
