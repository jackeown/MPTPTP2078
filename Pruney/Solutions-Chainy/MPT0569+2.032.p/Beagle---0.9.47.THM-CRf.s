%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:40 EST 2020

% Result     : Theorem 8.67s
% Output     : CNFRefutation 8.88s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 130 expanded)
%              Number of leaves         :   37 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  113 ( 217 expanded)
%              Number of equality atoms :   35 (  67 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

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

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_977,plain,(
    ! [A_150,B_151,C_152] :
      ( ~ r1_xboole_0(A_150,B_151)
      | ~ r2_hidden(C_152,B_151)
      | ~ r2_hidden(C_152,A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1032,plain,(
    ! [C_161,B_162,A_163] :
      ( ~ r2_hidden(C_161,B_162)
      | ~ r2_hidden(C_161,A_163)
      | k4_xboole_0(A_163,B_162) != A_163 ) ),
    inference(resolution,[status(thm)],[c_16,c_977])).

tff(c_5342,plain,(
    ! [A_372,B_373,A_374] :
      ( ~ r2_hidden('#skF_1'(A_372,B_373),A_374)
      | k4_xboole_0(A_374,A_372) != A_374
      | r1_xboole_0(A_372,B_373) ) ),
    inference(resolution,[status(thm)],[c_6,c_1032])).

tff(c_5352,plain,(
    ! [B_375,A_376] :
      ( k4_xboole_0(B_375,A_376) != B_375
      | r1_xboole_0(A_376,B_375) ) ),
    inference(resolution,[status(thm)],[c_4,c_5342])).

tff(c_58,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_8'),'#skF_7')
    | k10_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_120,plain,(
    k10_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_56,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_185,plain,(
    ! [A_76,B_77] : k4_xboole_0(A_76,k4_xboole_0(A_76,B_77)) = k3_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_214,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_185])).

tff(c_218,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_214])).

tff(c_64,plain,
    ( k10_relat_1('#skF_8','#skF_7') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_176,plain,(
    r1_xboole_0(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_64])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_180,plain,(
    k4_xboole_0(k2_relat_1('#skF_8'),'#skF_7') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_176,c_14])).

tff(c_204,plain,(
    k4_xboole_0(k2_relat_1('#skF_8'),k2_relat_1('#skF_8')) = k3_xboole_0(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_185])).

tff(c_314,plain,(
    k3_xboole_0(k2_relat_1('#skF_8'),'#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_204])).

tff(c_389,plain,(
    ! [B_98,A_99] :
      ( k10_relat_1(B_98,k3_xboole_0(k2_relat_1(B_98),A_99)) = k10_relat_1(B_98,A_99)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_398,plain,
    ( k10_relat_1('#skF_8',k1_xboole_0) = k10_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_389])).

tff(c_410,plain,(
    k10_relat_1('#skF_8',k1_xboole_0) = k10_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_398])).

tff(c_656,plain,(
    ! [A_116,B_117,C_118] :
      ( r2_hidden('#skF_6'(A_116,B_117,C_118),B_117)
      | ~ r2_hidden(A_116,k10_relat_1(C_118,B_117))
      | ~ v1_relat_1(C_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_26,plain,(
    ! [A_21] : k2_zfmisc_1(A_21,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_103,plain,(
    ! [A_58,B_59] : ~ r2_hidden(A_58,k2_zfmisc_1(A_58,B_59)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_106,plain,(
    ! [A_21] : ~ r2_hidden(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_103])).

tff(c_675,plain,(
    ! [A_121,C_122] :
      ( ~ r2_hidden(A_121,k10_relat_1(C_122,k1_xboole_0))
      | ~ v1_relat_1(C_122) ) ),
    inference(resolution,[status(thm)],[c_656,c_106])).

tff(c_686,plain,(
    ! [A_121] :
      ( ~ r2_hidden(A_121,k10_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_675])).

tff(c_701,plain,(
    ! [A_123] : ~ r2_hidden(A_123,k10_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_686])).

tff(c_722,plain,(
    ! [A_124] : r1_xboole_0(A_124,k10_relat_1('#skF_8','#skF_7')) ),
    inference(resolution,[status(thm)],[c_4,c_701])).

tff(c_760,plain,(
    ! [A_129] : k4_xboole_0(A_129,k10_relat_1('#skF_8','#skF_7')) = A_129 ),
    inference(resolution,[status(thm)],[c_722,c_14])).

tff(c_770,plain,(
    k10_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_760,c_218])).

tff(c_792,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_770])).

tff(c_793,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_5363,plain,(
    k4_xboole_0('#skF_7',k2_relat_1('#skF_8')) != '#skF_7' ),
    inference(resolution,[status(thm)],[c_5352,c_793])).

tff(c_795,plain,(
    k10_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_793,c_64])).

tff(c_34,plain,(
    ! [A_27,C_42] :
      ( r2_hidden(k4_tarski('#skF_5'(A_27,k2_relat_1(A_27),C_42),C_42),A_27)
      | ~ r2_hidden(C_42,k2_relat_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1528,plain,(
    ! [A_215,C_216,B_217,D_218] :
      ( r2_hidden(A_215,k10_relat_1(C_216,B_217))
      | ~ r2_hidden(D_218,B_217)
      | ~ r2_hidden(k4_tarski(A_215,D_218),C_216)
      | ~ r2_hidden(D_218,k2_relat_1(C_216))
      | ~ v1_relat_1(C_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2727,plain,(
    ! [A_273,C_274,A_275,B_276] :
      ( r2_hidden(A_273,k10_relat_1(C_274,A_275))
      | ~ r2_hidden(k4_tarski(A_273,'#skF_1'(A_275,B_276)),C_274)
      | ~ r2_hidden('#skF_1'(A_275,B_276),k2_relat_1(C_274))
      | ~ v1_relat_1(C_274)
      | r1_xboole_0(A_275,B_276) ) ),
    inference(resolution,[status(thm)],[c_6,c_1528])).

tff(c_15387,plain,(
    ! [A_538,A_539,B_540] :
      ( r2_hidden('#skF_5'(A_538,k2_relat_1(A_538),'#skF_1'(A_539,B_540)),k10_relat_1(A_538,A_539))
      | ~ v1_relat_1(A_538)
      | r1_xboole_0(A_539,B_540)
      | ~ r2_hidden('#skF_1'(A_539,B_540),k2_relat_1(A_538)) ) ),
    inference(resolution,[status(thm)],[c_34,c_2727])).

tff(c_15511,plain,(
    ! [B_540] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),'#skF_1'('#skF_7',B_540)),k1_xboole_0)
      | ~ v1_relat_1('#skF_8')
      | r1_xboole_0('#skF_7',B_540)
      | ~ r2_hidden('#skF_1'('#skF_7',B_540),k2_relat_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_795,c_15387])).

tff(c_15566,plain,(
    ! [B_540] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),'#skF_1'('#skF_7',B_540)),k1_xboole_0)
      | r1_xboole_0('#skF_7',B_540)
      | ~ r2_hidden('#skF_1'('#skF_7',B_540),k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_15511])).

tff(c_15568,plain,(
    ! [B_541] :
      ( r1_xboole_0('#skF_7',B_541)
      | ~ r2_hidden('#skF_1'('#skF_7',B_541),k2_relat_1('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_15566])).

tff(c_15582,plain,(
    r1_xboole_0('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_4,c_15568])).

tff(c_15587,plain,(
    k4_xboole_0('#skF_7',k2_relat_1('#skF_8')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_15582,c_14])).

tff(c_15601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5363,c_15587])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:59:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.67/3.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.67/3.18  
% 8.67/3.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.67/3.18  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 8.67/3.18  
% 8.67/3.18  %Foreground sorts:
% 8.67/3.18  
% 8.67/3.18  
% 8.67/3.18  %Background operators:
% 8.67/3.18  
% 8.67/3.18  
% 8.67/3.18  %Foreground operators:
% 8.67/3.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.67/3.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.67/3.18  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 8.67/3.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.67/3.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.67/3.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.67/3.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.67/3.18  tff('#skF_7', type, '#skF_7': $i).
% 8.67/3.18  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.67/3.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.67/3.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.67/3.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.67/3.18  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.67/3.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.67/3.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.67/3.18  tff('#skF_8', type, '#skF_8': $i).
% 8.67/3.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.67/3.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 8.67/3.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.67/3.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.67/3.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.67/3.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.67/3.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.67/3.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.67/3.18  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.67/3.18  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.67/3.18  
% 8.88/3.20  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.88/3.20  tff(f_53, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 8.88/3.20  tff(f_100, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 8.88/3.20  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 8.88/3.20  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.88/3.20  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.88/3.20  tff(f_93, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 8.88/3.20  tff(f_89, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 8.88/3.20  tff(f_65, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.88/3.20  tff(f_68, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 8.88/3.20  tff(f_78, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 8.88/3.20  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.88/3.20  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.88/3.20  tff(c_16, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k4_xboole_0(A_10, B_11)!=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.88/3.20  tff(c_977, plain, (![A_150, B_151, C_152]: (~r1_xboole_0(A_150, B_151) | ~r2_hidden(C_152, B_151) | ~r2_hidden(C_152, A_150))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.88/3.20  tff(c_1032, plain, (![C_161, B_162, A_163]: (~r2_hidden(C_161, B_162) | ~r2_hidden(C_161, A_163) | k4_xboole_0(A_163, B_162)!=A_163)), inference(resolution, [status(thm)], [c_16, c_977])).
% 8.88/3.20  tff(c_5342, plain, (![A_372, B_373, A_374]: (~r2_hidden('#skF_1'(A_372, B_373), A_374) | k4_xboole_0(A_374, A_372)!=A_374 | r1_xboole_0(A_372, B_373))), inference(resolution, [status(thm)], [c_6, c_1032])).
% 8.88/3.20  tff(c_5352, plain, (![B_375, A_376]: (k4_xboole_0(B_375, A_376)!=B_375 | r1_xboole_0(A_376, B_375))), inference(resolution, [status(thm)], [c_4, c_5342])).
% 8.88/3.20  tff(c_58, plain, (~r1_xboole_0(k2_relat_1('#skF_8'), '#skF_7') | k10_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.88/3.20  tff(c_120, plain, (k10_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_58])).
% 8.88/3.20  tff(c_56, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.88/3.20  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.88/3.20  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.88/3.20  tff(c_185, plain, (![A_76, B_77]: (k4_xboole_0(A_76, k4_xboole_0(A_76, B_77))=k3_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.88/3.20  tff(c_214, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_185])).
% 8.88/3.20  tff(c_218, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_214])).
% 8.88/3.20  tff(c_64, plain, (k10_relat_1('#skF_8', '#skF_7')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.88/3.20  tff(c_176, plain, (r1_xboole_0(k2_relat_1('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_120, c_64])).
% 8.88/3.20  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.88/3.20  tff(c_180, plain, (k4_xboole_0(k2_relat_1('#skF_8'), '#skF_7')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_176, c_14])).
% 8.88/3.20  tff(c_204, plain, (k4_xboole_0(k2_relat_1('#skF_8'), k2_relat_1('#skF_8'))=k3_xboole_0(k2_relat_1('#skF_8'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_180, c_185])).
% 8.88/3.20  tff(c_314, plain, (k3_xboole_0(k2_relat_1('#skF_8'), '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_218, c_204])).
% 8.88/3.20  tff(c_389, plain, (![B_98, A_99]: (k10_relat_1(B_98, k3_xboole_0(k2_relat_1(B_98), A_99))=k10_relat_1(B_98, A_99) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.88/3.20  tff(c_398, plain, (k10_relat_1('#skF_8', k1_xboole_0)=k10_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_314, c_389])).
% 8.88/3.20  tff(c_410, plain, (k10_relat_1('#skF_8', k1_xboole_0)=k10_relat_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_398])).
% 8.88/3.20  tff(c_656, plain, (![A_116, B_117, C_118]: (r2_hidden('#skF_6'(A_116, B_117, C_118), B_117) | ~r2_hidden(A_116, k10_relat_1(C_118, B_117)) | ~v1_relat_1(C_118))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.88/3.20  tff(c_26, plain, (![A_21]: (k2_zfmisc_1(A_21, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.88/3.20  tff(c_103, plain, (![A_58, B_59]: (~r2_hidden(A_58, k2_zfmisc_1(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.88/3.20  tff(c_106, plain, (![A_21]: (~r2_hidden(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_103])).
% 8.88/3.20  tff(c_675, plain, (![A_121, C_122]: (~r2_hidden(A_121, k10_relat_1(C_122, k1_xboole_0)) | ~v1_relat_1(C_122))), inference(resolution, [status(thm)], [c_656, c_106])).
% 8.88/3.20  tff(c_686, plain, (![A_121]: (~r2_hidden(A_121, k10_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_410, c_675])).
% 8.88/3.20  tff(c_701, plain, (![A_123]: (~r2_hidden(A_123, k10_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_686])).
% 8.88/3.20  tff(c_722, plain, (![A_124]: (r1_xboole_0(A_124, k10_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_4, c_701])).
% 8.88/3.20  tff(c_760, plain, (![A_129]: (k4_xboole_0(A_129, k10_relat_1('#skF_8', '#skF_7'))=A_129)), inference(resolution, [status(thm)], [c_722, c_14])).
% 8.88/3.20  tff(c_770, plain, (k10_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_760, c_218])).
% 8.88/3.20  tff(c_792, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_770])).
% 8.88/3.20  tff(c_793, plain, (~r1_xboole_0(k2_relat_1('#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_58])).
% 8.88/3.20  tff(c_5363, plain, (k4_xboole_0('#skF_7', k2_relat_1('#skF_8'))!='#skF_7'), inference(resolution, [status(thm)], [c_5352, c_793])).
% 8.88/3.20  tff(c_795, plain, (k10_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_793, c_64])).
% 8.88/3.20  tff(c_34, plain, (![A_27, C_42]: (r2_hidden(k4_tarski('#skF_5'(A_27, k2_relat_1(A_27), C_42), C_42), A_27) | ~r2_hidden(C_42, k2_relat_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.88/3.20  tff(c_1528, plain, (![A_215, C_216, B_217, D_218]: (r2_hidden(A_215, k10_relat_1(C_216, B_217)) | ~r2_hidden(D_218, B_217) | ~r2_hidden(k4_tarski(A_215, D_218), C_216) | ~r2_hidden(D_218, k2_relat_1(C_216)) | ~v1_relat_1(C_216))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.88/3.20  tff(c_2727, plain, (![A_273, C_274, A_275, B_276]: (r2_hidden(A_273, k10_relat_1(C_274, A_275)) | ~r2_hidden(k4_tarski(A_273, '#skF_1'(A_275, B_276)), C_274) | ~r2_hidden('#skF_1'(A_275, B_276), k2_relat_1(C_274)) | ~v1_relat_1(C_274) | r1_xboole_0(A_275, B_276))), inference(resolution, [status(thm)], [c_6, c_1528])).
% 8.88/3.20  tff(c_15387, plain, (![A_538, A_539, B_540]: (r2_hidden('#skF_5'(A_538, k2_relat_1(A_538), '#skF_1'(A_539, B_540)), k10_relat_1(A_538, A_539)) | ~v1_relat_1(A_538) | r1_xboole_0(A_539, B_540) | ~r2_hidden('#skF_1'(A_539, B_540), k2_relat_1(A_538)))), inference(resolution, [status(thm)], [c_34, c_2727])).
% 8.88/3.20  tff(c_15511, plain, (![B_540]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), '#skF_1'('#skF_7', B_540)), k1_xboole_0) | ~v1_relat_1('#skF_8') | r1_xboole_0('#skF_7', B_540) | ~r2_hidden('#skF_1'('#skF_7', B_540), k2_relat_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_795, c_15387])).
% 8.88/3.20  tff(c_15566, plain, (![B_540]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), '#skF_1'('#skF_7', B_540)), k1_xboole_0) | r1_xboole_0('#skF_7', B_540) | ~r2_hidden('#skF_1'('#skF_7', B_540), k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_15511])).
% 8.88/3.20  tff(c_15568, plain, (![B_541]: (r1_xboole_0('#skF_7', B_541) | ~r2_hidden('#skF_1'('#skF_7', B_541), k2_relat_1('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_106, c_15566])).
% 8.88/3.20  tff(c_15582, plain, (r1_xboole_0('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_4, c_15568])).
% 8.88/3.20  tff(c_15587, plain, (k4_xboole_0('#skF_7', k2_relat_1('#skF_8'))='#skF_7'), inference(resolution, [status(thm)], [c_15582, c_14])).
% 8.88/3.20  tff(c_15601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5363, c_15587])).
% 8.88/3.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.88/3.20  
% 8.88/3.20  Inference rules
% 8.88/3.20  ----------------------
% 8.88/3.20  #Ref     : 0
% 8.88/3.20  #Sup     : 3804
% 8.88/3.20  #Fact    : 0
% 8.88/3.20  #Define  : 0
% 8.88/3.20  #Split   : 6
% 8.88/3.20  #Chain   : 0
% 8.88/3.20  #Close   : 0
% 8.88/3.20  
% 8.88/3.20  Ordering : KBO
% 8.88/3.20  
% 8.88/3.20  Simplification rules
% 8.88/3.20  ----------------------
% 8.88/3.20  #Subsume      : 1405
% 8.88/3.20  #Demod        : 2026
% 8.88/3.20  #Tautology    : 1777
% 8.88/3.20  #SimpNegUnit  : 59
% 8.88/3.20  #BackRed      : 10
% 8.88/3.20  
% 8.88/3.20  #Partial instantiations: 0
% 8.88/3.20  #Strategies tried      : 1
% 8.88/3.20  
% 8.88/3.20  Timing (in seconds)
% 8.88/3.20  ----------------------
% 8.88/3.20  Preprocessing        : 0.36
% 8.88/3.20  Parsing              : 0.19
% 8.88/3.20  CNF conversion       : 0.03
% 8.88/3.20  Main loop            : 2.02
% 8.88/3.20  Inferencing          : 0.61
% 8.88/3.20  Reduction            : 0.71
% 8.88/3.20  Demodulation         : 0.51
% 8.88/3.20  BG Simplification    : 0.06
% 8.88/3.20  Subsumption          : 0.52
% 8.88/3.20  Abstraction          : 0.10
% 8.88/3.20  MUC search           : 0.00
% 8.88/3.20  Cooper               : 0.00
% 8.88/3.20  Total                : 2.41
% 8.88/3.20  Index Insertion      : 0.00
% 8.88/3.20  Index Deletion       : 0.00
% 8.88/3.20  Index Matching       : 0.00
% 8.88/3.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
