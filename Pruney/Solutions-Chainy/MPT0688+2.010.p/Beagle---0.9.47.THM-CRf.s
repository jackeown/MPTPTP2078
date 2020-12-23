%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:39 EST 2020

% Result     : Theorem 5.47s
% Output     : CNFRefutation 5.47s
% Verified   : 
% Statistics : Number of formulae       :   53 (  81 expanded)
%              Number of leaves         :   26 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :   69 ( 148 expanded)
%              Number of equality atoms :   30 (  56 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( ! [C] :
              ~ ( r2_hidden(C,A)
                & k10_relat_1(B,k1_tarski(C)) = k1_xboole_0 )
         => r1_tarski(A,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_funct_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(c_99,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | k4_xboole_0(A_38,B_39) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_44,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_107,plain,(
    k4_xboole_0('#skF_3',k2_relat_1('#skF_4')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_99,c_44])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_254,plain,(
    ! [A_70,B_71,C_72] :
      ( ~ r2_hidden('#skF_1'(A_70,B_71,C_72),B_71)
      | r2_hidden('#skF_2'(A_70,B_71,C_72),C_72)
      | k4_xboole_0(A_70,B_71) = C_72 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_267,plain,(
    ! [A_73,C_74] :
      ( r2_hidden('#skF_2'(A_73,A_73,C_74),C_74)
      | k4_xboole_0(A_73,A_73) = C_74 ) ),
    inference(resolution,[status(thm)],[c_18,c_254])).

tff(c_34,plain,(
    ! [A_19] : k2_zfmisc_1(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_71,plain,(
    ! [A_29,B_30] : ~ r2_hidden(A_29,k2_zfmisc_1(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_77,plain,(
    ! [A_19] : ~ r2_hidden(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_71])).

tff(c_287,plain,(
    ! [A_73] : k4_xboole_0(A_73,A_73) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_267,c_77])).

tff(c_336,plain,(
    ! [A_78,B_79,C_80] :
      ( ~ r2_hidden('#skF_1'(A_78,B_79,C_80),C_80)
      | r2_hidden('#skF_2'(A_78,B_79,C_80),C_80)
      | k4_xboole_0(A_78,B_79) = C_80 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_352,plain,(
    ! [A_81,B_82] :
      ( r2_hidden('#skF_2'(A_81,B_82,A_81),A_81)
      | k4_xboole_0(A_81,B_82) = A_81 ) ),
    inference(resolution,[status(thm)],[c_18,c_336])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_370,plain,(
    ! [A_1,B_2,B_82] :
      ( r2_hidden('#skF_2'(k4_xboole_0(A_1,B_2),B_82,k4_xboole_0(A_1,B_2)),A_1)
      | k4_xboole_0(k4_xboole_0(A_1,B_2),B_82) = k4_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_352,c_6])).

tff(c_48,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_40,plain,(
    ! [A_23,B_24] :
      ( r2_hidden(A_23,k2_relat_1(B_24))
      | k10_relat_1(B_24,k1_tarski(A_23)) = k1_xboole_0
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_264,plain,(
    ! [A_1,C_3] :
      ( r2_hidden('#skF_2'(A_1,A_1,C_3),C_3)
      | k4_xboole_0(A_1,A_1) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_254])).

tff(c_314,plain,(
    ! [A_76,C_77] :
      ( r2_hidden('#skF_2'(A_76,A_76,C_77),C_77)
      | k1_xboole_0 = C_77 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_264])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_374,plain,(
    ! [A_83,A_84,B_85] :
      ( ~ r2_hidden('#skF_2'(A_83,A_83,k4_xboole_0(A_84,B_85)),B_85)
      | k4_xboole_0(A_84,B_85) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_314,c_4])).

tff(c_4433,plain,(
    ! [A_249,B_250,A_251] :
      ( k4_xboole_0(A_249,k2_relat_1(B_250)) = k1_xboole_0
      | k10_relat_1(B_250,k1_tarski('#skF_2'(A_251,A_251,k4_xboole_0(A_249,k2_relat_1(B_250))))) = k1_xboole_0
      | ~ v1_relat_1(B_250) ) ),
    inference(resolution,[status(thm)],[c_40,c_374])).

tff(c_46,plain,(
    ! [C_26] :
      ( k10_relat_1('#skF_4',k1_tarski(C_26)) != k1_xboole_0
      | ~ r2_hidden(C_26,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4440,plain,(
    ! [A_251,A_249] :
      ( ~ r2_hidden('#skF_2'(A_251,A_251,k4_xboole_0(A_249,k2_relat_1('#skF_4'))),'#skF_3')
      | k4_xboole_0(A_249,k2_relat_1('#skF_4')) = k1_xboole_0
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4433,c_46])).

tff(c_6038,plain,(
    ! [A_272,A_273] :
      ( ~ r2_hidden('#skF_2'(A_272,A_272,k4_xboole_0(A_273,k2_relat_1('#skF_4'))),'#skF_3')
      | k4_xboole_0(A_273,k2_relat_1('#skF_4')) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4440])).

tff(c_6050,plain,
    ( k4_xboole_0('#skF_3',k2_relat_1('#skF_4')) = k1_xboole_0
    | k4_xboole_0(k4_xboole_0('#skF_3',k2_relat_1('#skF_4')),k4_xboole_0('#skF_3',k2_relat_1('#skF_4'))) = k4_xboole_0('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_370,c_6038])).

tff(c_6094,plain,
    ( k4_xboole_0('#skF_3',k2_relat_1('#skF_4')) = k1_xboole_0
    | k4_xboole_0('#skF_3',k2_relat_1('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_6050])).

tff(c_6096,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_107,c_6094])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.47/2.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.47/2.18  
% 5.47/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.47/2.18  %$ r2_hidden > r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 5.47/2.18  
% 5.47/2.18  %Foreground sorts:
% 5.47/2.18  
% 5.47/2.18  
% 5.47/2.18  %Background operators:
% 5.47/2.18  
% 5.47/2.18  
% 5.47/2.18  %Foreground operators:
% 5.47/2.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.47/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.47/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.47/2.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.47/2.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.47/2.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.47/2.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.47/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.47/2.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.47/2.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.47/2.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.47/2.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.47/2.18  tff('#skF_3', type, '#skF_3': $i).
% 5.47/2.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.47/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.47/2.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.47/2.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.47/2.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.47/2.18  tff('#skF_4', type, '#skF_4': $i).
% 5.47/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.47/2.18  
% 5.47/2.19  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.47/2.19  tff(f_74, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((![C]: ~(r2_hidden(C, A) & (k10_relat_1(B, k1_tarski(C)) = k1_xboole_0))) => r1_tarski(A, k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_funct_1)).
% 5.47/2.19  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.47/2.19  tff(f_53, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.47/2.19  tff(f_56, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 5.47/2.19  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 5.47/2.19  tff(c_99, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | k4_xboole_0(A_38, B_39)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.47/2.19  tff(c_44, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.47/2.19  tff(c_107, plain, (k4_xboole_0('#skF_3', k2_relat_1('#skF_4'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_99, c_44])).
% 5.47/2.19  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.47/2.19  tff(c_254, plain, (![A_70, B_71, C_72]: (~r2_hidden('#skF_1'(A_70, B_71, C_72), B_71) | r2_hidden('#skF_2'(A_70, B_71, C_72), C_72) | k4_xboole_0(A_70, B_71)=C_72)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.47/2.19  tff(c_267, plain, (![A_73, C_74]: (r2_hidden('#skF_2'(A_73, A_73, C_74), C_74) | k4_xboole_0(A_73, A_73)=C_74)), inference(resolution, [status(thm)], [c_18, c_254])).
% 5.47/2.19  tff(c_34, plain, (![A_19]: (k2_zfmisc_1(A_19, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.47/2.19  tff(c_71, plain, (![A_29, B_30]: (~r2_hidden(A_29, k2_zfmisc_1(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.47/2.19  tff(c_77, plain, (![A_19]: (~r2_hidden(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_71])).
% 5.47/2.19  tff(c_287, plain, (![A_73]: (k4_xboole_0(A_73, A_73)=k1_xboole_0)), inference(resolution, [status(thm)], [c_267, c_77])).
% 5.47/2.19  tff(c_336, plain, (![A_78, B_79, C_80]: (~r2_hidden('#skF_1'(A_78, B_79, C_80), C_80) | r2_hidden('#skF_2'(A_78, B_79, C_80), C_80) | k4_xboole_0(A_78, B_79)=C_80)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.47/2.19  tff(c_352, plain, (![A_81, B_82]: (r2_hidden('#skF_2'(A_81, B_82, A_81), A_81) | k4_xboole_0(A_81, B_82)=A_81)), inference(resolution, [status(thm)], [c_18, c_336])).
% 5.47/2.19  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.47/2.19  tff(c_370, plain, (![A_1, B_2, B_82]: (r2_hidden('#skF_2'(k4_xboole_0(A_1, B_2), B_82, k4_xboole_0(A_1, B_2)), A_1) | k4_xboole_0(k4_xboole_0(A_1, B_2), B_82)=k4_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_352, c_6])).
% 5.47/2.19  tff(c_48, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.47/2.19  tff(c_40, plain, (![A_23, B_24]: (r2_hidden(A_23, k2_relat_1(B_24)) | k10_relat_1(B_24, k1_tarski(A_23))=k1_xboole_0 | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.47/2.19  tff(c_264, plain, (![A_1, C_3]: (r2_hidden('#skF_2'(A_1, A_1, C_3), C_3) | k4_xboole_0(A_1, A_1)=C_3)), inference(resolution, [status(thm)], [c_18, c_254])).
% 5.47/2.19  tff(c_314, plain, (![A_76, C_77]: (r2_hidden('#skF_2'(A_76, A_76, C_77), C_77) | k1_xboole_0=C_77)), inference(demodulation, [status(thm), theory('equality')], [c_287, c_264])).
% 5.47/2.19  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.47/2.19  tff(c_374, plain, (![A_83, A_84, B_85]: (~r2_hidden('#skF_2'(A_83, A_83, k4_xboole_0(A_84, B_85)), B_85) | k4_xboole_0(A_84, B_85)=k1_xboole_0)), inference(resolution, [status(thm)], [c_314, c_4])).
% 5.47/2.19  tff(c_4433, plain, (![A_249, B_250, A_251]: (k4_xboole_0(A_249, k2_relat_1(B_250))=k1_xboole_0 | k10_relat_1(B_250, k1_tarski('#skF_2'(A_251, A_251, k4_xboole_0(A_249, k2_relat_1(B_250)))))=k1_xboole_0 | ~v1_relat_1(B_250))), inference(resolution, [status(thm)], [c_40, c_374])).
% 5.47/2.19  tff(c_46, plain, (![C_26]: (k10_relat_1('#skF_4', k1_tarski(C_26))!=k1_xboole_0 | ~r2_hidden(C_26, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.47/2.19  tff(c_4440, plain, (![A_251, A_249]: (~r2_hidden('#skF_2'(A_251, A_251, k4_xboole_0(A_249, k2_relat_1('#skF_4'))), '#skF_3') | k4_xboole_0(A_249, k2_relat_1('#skF_4'))=k1_xboole_0 | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4433, c_46])).
% 5.47/2.19  tff(c_6038, plain, (![A_272, A_273]: (~r2_hidden('#skF_2'(A_272, A_272, k4_xboole_0(A_273, k2_relat_1('#skF_4'))), '#skF_3') | k4_xboole_0(A_273, k2_relat_1('#skF_4'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4440])).
% 5.47/2.19  tff(c_6050, plain, (k4_xboole_0('#skF_3', k2_relat_1('#skF_4'))=k1_xboole_0 | k4_xboole_0(k4_xboole_0('#skF_3', k2_relat_1('#skF_4')), k4_xboole_0('#skF_3', k2_relat_1('#skF_4')))=k4_xboole_0('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_370, c_6038])).
% 5.47/2.19  tff(c_6094, plain, (k4_xboole_0('#skF_3', k2_relat_1('#skF_4'))=k1_xboole_0 | k4_xboole_0('#skF_3', k2_relat_1('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_287, c_6050])).
% 5.47/2.19  tff(c_6096, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_107, c_6094])).
% 5.47/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.47/2.19  
% 5.47/2.19  Inference rules
% 5.47/2.19  ----------------------
% 5.47/2.19  #Ref     : 0
% 5.47/2.19  #Sup     : 1433
% 5.47/2.19  #Fact    : 0
% 5.47/2.19  #Define  : 0
% 5.47/2.19  #Split   : 0
% 5.47/2.19  #Chain   : 0
% 5.47/2.19  #Close   : 0
% 5.47/2.19  
% 5.47/2.19  Ordering : KBO
% 5.47/2.19  
% 5.47/2.19  Simplification rules
% 5.47/2.19  ----------------------
% 5.47/2.19  #Subsume      : 471
% 5.47/2.19  #Demod        : 1280
% 5.47/2.19  #Tautology    : 536
% 5.47/2.19  #SimpNegUnit  : 36
% 5.47/2.19  #BackRed      : 2
% 5.47/2.19  
% 5.47/2.19  #Partial instantiations: 0
% 5.47/2.19  #Strategies tried      : 1
% 5.47/2.19  
% 5.47/2.19  Timing (in seconds)
% 5.47/2.19  ----------------------
% 5.47/2.20  Preprocessing        : 0.33
% 5.47/2.20  Parsing              : 0.17
% 5.47/2.20  CNF conversion       : 0.02
% 5.47/2.20  Main loop            : 1.10
% 5.47/2.20  Inferencing          : 0.39
% 5.47/2.20  Reduction            : 0.39
% 5.47/2.20  Demodulation         : 0.29
% 5.47/2.20  BG Simplification    : 0.04
% 5.47/2.20  Subsumption          : 0.22
% 5.47/2.20  Abstraction          : 0.07
% 5.47/2.20  MUC search           : 0.00
% 5.47/2.20  Cooper               : 0.00
% 5.47/2.20  Total                : 1.46
% 5.47/2.20  Index Insertion      : 0.00
% 5.47/2.20  Index Deletion       : 0.00
% 5.47/2.20  Index Matching       : 0.00
% 5.47/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
