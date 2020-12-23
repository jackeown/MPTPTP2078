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
% DateTime   : Thu Dec  3 10:01:41 EST 2020

% Result     : Theorem 26.15s
% Output     : CNFRefutation 26.26s
% Verified   : 
% Statistics : Number of formulae       :   73 (  95 expanded)
%              Number of leaves         :   38 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  106 ( 168 expanded)
%              Number of equality atoms :   13 (  26 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_119,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_66,plain,
    ( k10_relat_1('#skF_6','#skF_5') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_133,plain,(
    r1_xboole_0(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_60,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_6'),'#skF_5')
    | k10_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_170,plain,(
    k10_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_60])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_58,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_48,plain,(
    ! [A_51,B_52,C_53] :
      ( r2_hidden('#skF_4'(A_51,B_52,C_53),B_52)
      | ~ r2_hidden(A_51,k10_relat_1(C_53,B_52))
      | ~ v1_relat_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_682,plain,(
    ! [A_153,B_154,C_155] :
      ( r2_hidden('#skF_4'(A_153,B_154,C_155),k2_relat_1(C_155))
      | ~ r2_hidden(A_153,k10_relat_1(C_155,B_154))
      | ~ v1_relat_1(C_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_193,plain,(
    ! [A_84,B_85,C_86] :
      ( ~ r1_xboole_0(A_84,B_85)
      | ~ r2_hidden(C_86,B_85)
      | ~ r2_hidden(C_86,A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_202,plain,(
    ! [C_86] :
      ( ~ r2_hidden(C_86,'#skF_5')
      | ~ r2_hidden(C_86,k2_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_133,c_193])).

tff(c_686,plain,(
    ! [A_153,B_154] :
      ( ~ r2_hidden('#skF_4'(A_153,B_154,'#skF_6'),'#skF_5')
      | ~ r2_hidden(A_153,k10_relat_1('#skF_6',B_154))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_682,c_202])).

tff(c_707,plain,(
    ! [A_158,B_159] :
      ( ~ r2_hidden('#skF_4'(A_158,B_159,'#skF_6'),'#skF_5')
      | ~ r2_hidden(A_158,k10_relat_1('#skF_6',B_159)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_686])).

tff(c_711,plain,(
    ! [A_51] :
      ( ~ r2_hidden(A_51,k10_relat_1('#skF_6','#skF_5'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_707])).

tff(c_715,plain,(
    ! [A_160] : ~ r2_hidden(A_160,k10_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_711])).

tff(c_739,plain,(
    k10_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_715])).

tff(c_748,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_739])).

tff(c_750,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_44,plain,(
    ! [A_50] :
      ( k9_relat_1(A_50,k1_relat_1(A_50)) = k2_relat_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_83,plain,(
    ! [C_62,B_63] : ~ r2_hidden(C_62,k4_xboole_0(B_63,k1_tarski(C_62))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_86,plain,(
    ! [C_62] : ~ r2_hidden(C_62,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_83])).

tff(c_749,plain,(
    k10_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_40,plain,(
    ! [A_44,B_45,C_46] :
      ( r2_hidden(k4_tarski('#skF_3'(A_44,B_45,C_46),A_44),C_46)
      | ~ r2_hidden(A_44,k9_relat_1(C_46,B_45))
      | ~ v1_relat_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1817,plain,(
    ! [A_313,C_314,B_315,D_316] :
      ( r2_hidden(A_313,k10_relat_1(C_314,B_315))
      | ~ r2_hidden(D_316,B_315)
      | ~ r2_hidden(k4_tarski(A_313,D_316),C_314)
      | ~ r2_hidden(D_316,k2_relat_1(C_314))
      | ~ v1_relat_1(C_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6048,plain,(
    ! [A_644,C_645,B_646,A_647] :
      ( r2_hidden(A_644,k10_relat_1(C_645,B_646))
      | ~ r2_hidden(k4_tarski(A_644,'#skF_1'(A_647,B_646)),C_645)
      | ~ r2_hidden('#skF_1'(A_647,B_646),k2_relat_1(C_645))
      | ~ v1_relat_1(C_645)
      | r1_xboole_0(A_647,B_646) ) ),
    inference(resolution,[status(thm)],[c_4,c_1817])).

tff(c_49592,plain,(
    ! [A_2482,B_2483,B_2484,C_2485] :
      ( r2_hidden('#skF_3'('#skF_1'(A_2482,B_2483),B_2484,C_2485),k10_relat_1(C_2485,B_2483))
      | ~ r2_hidden('#skF_1'(A_2482,B_2483),k2_relat_1(C_2485))
      | r1_xboole_0(A_2482,B_2483)
      | ~ r2_hidden('#skF_1'(A_2482,B_2483),k9_relat_1(C_2485,B_2484))
      | ~ v1_relat_1(C_2485) ) ),
    inference(resolution,[status(thm)],[c_40,c_6048])).

tff(c_49788,plain,(
    ! [A_2482,B_2484] :
      ( r2_hidden('#skF_3'('#skF_1'(A_2482,'#skF_5'),B_2484,'#skF_6'),k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_2482,'#skF_5'),k2_relat_1('#skF_6'))
      | r1_xboole_0(A_2482,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_2482,'#skF_5'),k9_relat_1('#skF_6',B_2484))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_749,c_49592])).

tff(c_49849,plain,(
    ! [A_2482,B_2484] :
      ( r2_hidden('#skF_3'('#skF_1'(A_2482,'#skF_5'),B_2484,'#skF_6'),k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_2482,'#skF_5'),k2_relat_1('#skF_6'))
      | r1_xboole_0(A_2482,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_2482,'#skF_5'),k9_relat_1('#skF_6',B_2484)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_49788])).

tff(c_49852,plain,(
    ! [A_2486,B_2487] :
      ( ~ r2_hidden('#skF_1'(A_2486,'#skF_5'),k2_relat_1('#skF_6'))
      | r1_xboole_0(A_2486,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_2486,'#skF_5'),k9_relat_1('#skF_6',B_2487)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_49849])).

tff(c_49958,plain,(
    ! [A_2486] :
      ( ~ r2_hidden('#skF_1'(A_2486,'#skF_5'),k2_relat_1('#skF_6'))
      | r1_xboole_0(A_2486,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_2486,'#skF_5'),k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_49852])).

tff(c_50018,plain,(
    ! [A_2488] :
      ( r1_xboole_0(A_2488,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_2488,'#skF_5'),k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_49958])).

tff(c_50042,plain,(
    r1_xboole_0(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_50018])).

tff(c_50058,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_750,c_750,c_50042])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:16:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 26.15/17.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.15/17.45  
% 26.15/17.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.15/17.45  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_1
% 26.15/17.45  
% 26.15/17.45  %Foreground sorts:
% 26.15/17.45  
% 26.15/17.45  
% 26.15/17.45  %Background operators:
% 26.15/17.45  
% 26.15/17.45  
% 26.15/17.45  %Foreground operators:
% 26.15/17.45  tff('#skF_2', type, '#skF_2': $i > $i).
% 26.15/17.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 26.15/17.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 26.15/17.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 26.15/17.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 26.15/17.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 26.15/17.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 26.15/17.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 26.15/17.45  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 26.15/17.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 26.15/17.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 26.15/17.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 26.15/17.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 26.15/17.45  tff('#skF_5', type, '#skF_5': $i).
% 26.15/17.45  tff('#skF_6', type, '#skF_6': $i).
% 26.15/17.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 26.15/17.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 26.15/17.45  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 26.15/17.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 26.15/17.45  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 26.15/17.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 26.15/17.45  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 26.15/17.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 26.15/17.45  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 26.15/17.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 26.15/17.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 26.15/17.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 26.15/17.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 26.15/17.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 26.15/17.45  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 26.15/17.45  
% 26.26/17.47  tff(f_119, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 26.26/17.47  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 26.26/17.47  tff(f_104, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 26.26/17.47  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 26.26/17.47  tff(f_93, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 26.26/17.47  tff(f_55, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 26.26/17.47  tff(f_76, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 26.26/17.47  tff(f_89, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 26.26/17.47  tff(c_66, plain, (k10_relat_1('#skF_6', '#skF_5')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 26.26/17.47  tff(c_133, plain, (r1_xboole_0(k2_relat_1('#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_66])).
% 26.26/17.47  tff(c_60, plain, (~r1_xboole_0(k2_relat_1('#skF_6'), '#skF_5') | k10_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_119])).
% 26.26/17.47  tff(c_170, plain, (k10_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_133, c_60])).
% 26.26/17.47  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 26.26/17.47  tff(c_58, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_119])).
% 26.26/17.47  tff(c_48, plain, (![A_51, B_52, C_53]: (r2_hidden('#skF_4'(A_51, B_52, C_53), B_52) | ~r2_hidden(A_51, k10_relat_1(C_53, B_52)) | ~v1_relat_1(C_53))), inference(cnfTransformation, [status(thm)], [f_104])).
% 26.26/17.47  tff(c_682, plain, (![A_153, B_154, C_155]: (r2_hidden('#skF_4'(A_153, B_154, C_155), k2_relat_1(C_155)) | ~r2_hidden(A_153, k10_relat_1(C_155, B_154)) | ~v1_relat_1(C_155))), inference(cnfTransformation, [status(thm)], [f_104])).
% 26.26/17.47  tff(c_193, plain, (![A_84, B_85, C_86]: (~r1_xboole_0(A_84, B_85) | ~r2_hidden(C_86, B_85) | ~r2_hidden(C_86, A_84))), inference(cnfTransformation, [status(thm)], [f_43])).
% 26.26/17.47  tff(c_202, plain, (![C_86]: (~r2_hidden(C_86, '#skF_5') | ~r2_hidden(C_86, k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_133, c_193])).
% 26.26/17.47  tff(c_686, plain, (![A_153, B_154]: (~r2_hidden('#skF_4'(A_153, B_154, '#skF_6'), '#skF_5') | ~r2_hidden(A_153, k10_relat_1('#skF_6', B_154)) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_682, c_202])).
% 26.26/17.47  tff(c_707, plain, (![A_158, B_159]: (~r2_hidden('#skF_4'(A_158, B_159, '#skF_6'), '#skF_5') | ~r2_hidden(A_158, k10_relat_1('#skF_6', B_159)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_686])).
% 26.26/17.47  tff(c_711, plain, (![A_51]: (~r2_hidden(A_51, k10_relat_1('#skF_6', '#skF_5')) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_707])).
% 26.26/17.47  tff(c_715, plain, (![A_160]: (~r2_hidden(A_160, k10_relat_1('#skF_6', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_711])).
% 26.26/17.47  tff(c_739, plain, (k10_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_715])).
% 26.26/17.47  tff(c_748, plain, $false, inference(negUnitSimplification, [status(thm)], [c_170, c_739])).
% 26.26/17.47  tff(c_750, plain, (~r1_xboole_0(k2_relat_1('#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_66])).
% 26.26/17.47  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 26.26/17.47  tff(c_44, plain, (![A_50]: (k9_relat_1(A_50, k1_relat_1(A_50))=k2_relat_1(A_50) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_93])).
% 26.26/17.47  tff(c_12, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 26.26/17.47  tff(c_83, plain, (![C_62, B_63]: (~r2_hidden(C_62, k4_xboole_0(B_63, k1_tarski(C_62))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 26.26/17.47  tff(c_86, plain, (![C_62]: (~r2_hidden(C_62, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_83])).
% 26.26/17.47  tff(c_749, plain, (k10_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_66])).
% 26.26/17.47  tff(c_40, plain, (![A_44, B_45, C_46]: (r2_hidden(k4_tarski('#skF_3'(A_44, B_45, C_46), A_44), C_46) | ~r2_hidden(A_44, k9_relat_1(C_46, B_45)) | ~v1_relat_1(C_46))), inference(cnfTransformation, [status(thm)], [f_89])).
% 26.26/17.47  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 26.26/17.47  tff(c_1817, plain, (![A_313, C_314, B_315, D_316]: (r2_hidden(A_313, k10_relat_1(C_314, B_315)) | ~r2_hidden(D_316, B_315) | ~r2_hidden(k4_tarski(A_313, D_316), C_314) | ~r2_hidden(D_316, k2_relat_1(C_314)) | ~v1_relat_1(C_314))), inference(cnfTransformation, [status(thm)], [f_104])).
% 26.26/17.47  tff(c_6048, plain, (![A_644, C_645, B_646, A_647]: (r2_hidden(A_644, k10_relat_1(C_645, B_646)) | ~r2_hidden(k4_tarski(A_644, '#skF_1'(A_647, B_646)), C_645) | ~r2_hidden('#skF_1'(A_647, B_646), k2_relat_1(C_645)) | ~v1_relat_1(C_645) | r1_xboole_0(A_647, B_646))), inference(resolution, [status(thm)], [c_4, c_1817])).
% 26.26/17.47  tff(c_49592, plain, (![A_2482, B_2483, B_2484, C_2485]: (r2_hidden('#skF_3'('#skF_1'(A_2482, B_2483), B_2484, C_2485), k10_relat_1(C_2485, B_2483)) | ~r2_hidden('#skF_1'(A_2482, B_2483), k2_relat_1(C_2485)) | r1_xboole_0(A_2482, B_2483) | ~r2_hidden('#skF_1'(A_2482, B_2483), k9_relat_1(C_2485, B_2484)) | ~v1_relat_1(C_2485))), inference(resolution, [status(thm)], [c_40, c_6048])).
% 26.26/17.47  tff(c_49788, plain, (![A_2482, B_2484]: (r2_hidden('#skF_3'('#skF_1'(A_2482, '#skF_5'), B_2484, '#skF_6'), k1_xboole_0) | ~r2_hidden('#skF_1'(A_2482, '#skF_5'), k2_relat_1('#skF_6')) | r1_xboole_0(A_2482, '#skF_5') | ~r2_hidden('#skF_1'(A_2482, '#skF_5'), k9_relat_1('#skF_6', B_2484)) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_749, c_49592])).
% 26.26/17.47  tff(c_49849, plain, (![A_2482, B_2484]: (r2_hidden('#skF_3'('#skF_1'(A_2482, '#skF_5'), B_2484, '#skF_6'), k1_xboole_0) | ~r2_hidden('#skF_1'(A_2482, '#skF_5'), k2_relat_1('#skF_6')) | r1_xboole_0(A_2482, '#skF_5') | ~r2_hidden('#skF_1'(A_2482, '#skF_5'), k9_relat_1('#skF_6', B_2484)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_49788])).
% 26.26/17.47  tff(c_49852, plain, (![A_2486, B_2487]: (~r2_hidden('#skF_1'(A_2486, '#skF_5'), k2_relat_1('#skF_6')) | r1_xboole_0(A_2486, '#skF_5') | ~r2_hidden('#skF_1'(A_2486, '#skF_5'), k9_relat_1('#skF_6', B_2487)))), inference(negUnitSimplification, [status(thm)], [c_86, c_49849])).
% 26.26/17.47  tff(c_49958, plain, (![A_2486]: (~r2_hidden('#skF_1'(A_2486, '#skF_5'), k2_relat_1('#skF_6')) | r1_xboole_0(A_2486, '#skF_5') | ~r2_hidden('#skF_1'(A_2486, '#skF_5'), k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_49852])).
% 26.26/17.47  tff(c_50018, plain, (![A_2488]: (r1_xboole_0(A_2488, '#skF_5') | ~r2_hidden('#skF_1'(A_2488, '#skF_5'), k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_49958])).
% 26.26/17.47  tff(c_50042, plain, (r1_xboole_0(k2_relat_1('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_6, c_50018])).
% 26.26/17.47  tff(c_50058, plain, $false, inference(negUnitSimplification, [status(thm)], [c_750, c_750, c_50042])).
% 26.26/17.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.26/17.47  
% 26.26/17.47  Inference rules
% 26.26/17.47  ----------------------
% 26.26/17.47  #Ref     : 0
% 26.26/17.47  #Sup     : 11777
% 26.26/17.47  #Fact    : 0
% 26.26/17.47  #Define  : 0
% 26.26/17.47  #Split   : 16
% 26.26/17.47  #Chain   : 0
% 26.26/17.47  #Close   : 0
% 26.26/17.47  
% 26.26/17.47  Ordering : KBO
% 26.26/17.47  
% 26.26/17.47  Simplification rules
% 26.26/17.47  ----------------------
% 26.26/17.47  #Subsume      : 4856
% 26.26/17.47  #Demod        : 4649
% 26.26/17.47  #Tautology    : 2502
% 26.26/17.47  #SimpNegUnit  : 235
% 26.26/17.47  #BackRed      : 0
% 26.26/17.47  
% 26.26/17.47  #Partial instantiations: 0
% 26.26/17.47  #Strategies tried      : 1
% 26.26/17.47  
% 26.26/17.47  Timing (in seconds)
% 26.26/17.47  ----------------------
% 26.26/17.47  Preprocessing        : 0.34
% 26.26/17.47  Parsing              : 0.18
% 26.26/17.47  CNF conversion       : 0.02
% 26.26/17.47  Main loop            : 16.38
% 26.26/17.47  Inferencing          : 2.10
% 26.26/17.47  Reduction            : 1.91
% 26.26/17.47  Demodulation         : 1.33
% 26.26/17.47  BG Simplification    : 0.14
% 26.26/17.47  Subsumption          : 11.79
% 26.26/17.47  Abstraction          : 0.23
% 26.26/17.47  MUC search           : 0.00
% 26.26/17.47  Cooper               : 0.00
% 26.26/17.47  Total                : 16.75
% 26.26/17.47  Index Insertion      : 0.00
% 26.26/17.47  Index Deletion       : 0.00
% 26.26/17.47  Index Matching       : 0.00
% 26.26/17.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
