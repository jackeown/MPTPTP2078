%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:06 EST 2020

% Result     : Theorem 5.94s
% Output     : CNFRefutation 5.94s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 139 expanded)
%              Number of leaves         :   38 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :  116 ( 188 expanded)
%              Number of equality atoms :   51 (  91 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_38,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_42,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_28,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(f_93,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_52,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_99,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_54,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_100,plain,(
    ! [A_57] :
      ( v1_relat_1(A_57)
      | ~ v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_104,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_100])).

tff(c_40,plain,(
    ! [A_43,B_44] :
      ( v1_relat_1(k5_relat_1(A_43,B_44))
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_124,plain,(
    ! [A_64,B_65] : k5_xboole_0(A_64,k3_xboole_0(A_64,B_65)) = k4_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_136,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_124])).

tff(c_139,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_136])).

tff(c_308,plain,(
    ! [A_84,C_85,B_86] : k4_xboole_0(k2_zfmisc_1(A_84,C_85),k2_zfmisc_1(B_86,C_85)) = k2_zfmisc_1(k4_xboole_0(A_84,B_86),C_85) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_315,plain,(
    ! [B_86,C_85] : k2_zfmisc_1(k4_xboole_0(B_86,B_86),C_85) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_139])).

tff(c_324,plain,(
    ! [C_85] : k2_zfmisc_1(k1_xboole_0,C_85) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_315])).

tff(c_50,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_230,plain,(
    ! [A_75,B_76] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_75,B_76)),k1_relat_1(A_75))
      | ~ v1_relat_1(B_76)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_235,plain,(
    ! [B_76] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_76)),k1_xboole_0)
      | ~ v1_relat_1(B_76)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_230])).

tff(c_243,plain,(
    ! [B_77] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_77)),k1_xboole_0)
      | ~ v1_relat_1(B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_235])).

tff(c_16,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_166,plain,(
    ! [B_68,A_69] :
      ( B_68 = A_69
      | ~ r1_tarski(B_68,A_69)
      | ~ r1_tarski(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_175,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_166])).

tff(c_253,plain,(
    ! [B_78] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_78)) = k1_xboole_0
      | ~ v1_relat_1(B_78) ) ),
    inference(resolution,[status(thm)],[c_243,c_175])).

tff(c_42,plain,(
    ! [A_45] :
      ( k3_xboole_0(A_45,k2_zfmisc_1(k1_relat_1(A_45),k2_relat_1(A_45))) = A_45
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_268,plain,(
    ! [B_78] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_78),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_78)))) = k5_relat_1(k1_xboole_0,B_78)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_78))
      | ~ v1_relat_1(B_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_42])).

tff(c_5170,plain,(
    ! [B_214] :
      ( k5_relat_1(k1_xboole_0,B_214) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_214))
      | ~ v1_relat_1(B_214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_324,c_268])).

tff(c_5177,plain,(
    ! [B_44] :
      ( k5_relat_1(k1_xboole_0,B_44) = k1_xboole_0
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_40,c_5170])).

tff(c_5183,plain,(
    ! [B_215] :
      ( k5_relat_1(k1_xboole_0,B_215) = k1_xboole_0
      | ~ v1_relat_1(B_215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_5177])).

tff(c_5192,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_5183])).

tff(c_5199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_5192])).

tff(c_5200,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_5202,plain,(
    ! [A_216] :
      ( v1_relat_1(A_216)
      | ~ v1_xboole_0(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_5206,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_5202])).

tff(c_5229,plain,(
    ! [A_221,B_222] : k5_xboole_0(A_221,k3_xboole_0(A_221,B_222)) = k4_xboole_0(A_221,B_222) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_5241,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_5229])).

tff(c_5244,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_5241])).

tff(c_5434,plain,(
    ! [C_243,A_244,B_245] : k4_xboole_0(k2_zfmisc_1(C_243,A_244),k2_zfmisc_1(C_243,B_245)) = k2_zfmisc_1(C_243,k4_xboole_0(A_244,B_245)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_5441,plain,(
    ! [C_243,B_245] : k2_zfmisc_1(C_243,k4_xboole_0(B_245,B_245)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5434,c_5244])).

tff(c_5450,plain,(
    ! [C_243] : k2_zfmisc_1(C_243,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5244,c_5441])).

tff(c_48,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_5798,plain,(
    ! [B_272,A_273] :
      ( k2_relat_1(k5_relat_1(B_272,A_273)) = k2_relat_1(A_273)
      | ~ r1_tarski(k1_relat_1(A_273),k2_relat_1(B_272))
      | ~ v1_relat_1(B_272)
      | ~ v1_relat_1(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_5804,plain,(
    ! [B_272] :
      ( k2_relat_1(k5_relat_1(B_272,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_272))
      | ~ v1_relat_1(B_272)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_5798])).

tff(c_5814,plain,(
    ! [B_274] :
      ( k2_relat_1(k5_relat_1(B_274,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_274) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5206,c_16,c_48,c_5804])).

tff(c_5826,plain,(
    ! [B_274] :
      ( k3_xboole_0(k5_relat_1(B_274,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_274,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_274,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_274,k1_xboole_0))
      | ~ v1_relat_1(B_274) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5814,c_42])).

tff(c_5834,plain,(
    ! [B_275] :
      ( k5_relat_1(B_275,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_275,k1_xboole_0))
      | ~ v1_relat_1(B_275) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_5450,c_5826])).

tff(c_5838,plain,(
    ! [A_43] :
      ( k5_relat_1(A_43,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_43) ) ),
    inference(resolution,[status(thm)],[c_40,c_5834])).

tff(c_5842,plain,(
    ! [A_276] :
      ( k5_relat_1(A_276,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_276) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5206,c_5838])).

tff(c_5851,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_5842])).

tff(c_5857,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5200,c_5851])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:45:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.94/2.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.94/2.16  
% 5.94/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.94/2.16  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 5.94/2.16  
% 5.94/2.16  %Foreground sorts:
% 5.94/2.16  
% 5.94/2.16  
% 5.94/2.16  %Background operators:
% 5.94/2.16  
% 5.94/2.16  
% 5.94/2.16  %Foreground operators:
% 5.94/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.94/2.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.94/2.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.94/2.16  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.94/2.16  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.94/2.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.94/2.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.94/2.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.94/2.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.94/2.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.94/2.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.94/2.16  tff('#skF_1', type, '#skF_1': $i).
% 5.94/2.16  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.94/2.16  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.94/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.94/2.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.94/2.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.94/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.94/2.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.94/2.16  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.94/2.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.94/2.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.94/2.16  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.94/2.16  
% 5.94/2.18  tff(f_100, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 5.94/2.18  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.94/2.18  tff(f_64, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 5.94/2.18  tff(f_70, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 5.94/2.18  tff(f_38, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 5.94/2.18  tff(f_42, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.94/2.18  tff(f_28, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.94/2.18  tff(f_36, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.94/2.18  tff(f_58, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 5.94/2.18  tff(f_93, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 5.94/2.18  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 5.94/2.18  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.94/2.18  tff(f_34, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.94/2.18  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 5.94/2.18  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 5.94/2.18  tff(c_52, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.94/2.18  tff(c_99, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 5.94/2.18  tff(c_54, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.94/2.18  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.94/2.18  tff(c_100, plain, (![A_57]: (v1_relat_1(A_57) | ~v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.94/2.18  tff(c_104, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_100])).
% 5.94/2.18  tff(c_40, plain, (![A_43, B_44]: (v1_relat_1(k5_relat_1(A_43, B_44)) | ~v1_relat_1(B_44) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.94/2.18  tff(c_14, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.94/2.18  tff(c_18, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.94/2.18  tff(c_4, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 5.94/2.18  tff(c_124, plain, (![A_64, B_65]: (k5_xboole_0(A_64, k3_xboole_0(A_64, B_65))=k4_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.94/2.18  tff(c_136, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_4, c_124])).
% 5.94/2.18  tff(c_139, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_136])).
% 5.94/2.18  tff(c_308, plain, (![A_84, C_85, B_86]: (k4_xboole_0(k2_zfmisc_1(A_84, C_85), k2_zfmisc_1(B_86, C_85))=k2_zfmisc_1(k4_xboole_0(A_84, B_86), C_85))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.94/2.18  tff(c_315, plain, (![B_86, C_85]: (k2_zfmisc_1(k4_xboole_0(B_86, B_86), C_85)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_308, c_139])).
% 5.94/2.18  tff(c_324, plain, (![C_85]: (k2_zfmisc_1(k1_xboole_0, C_85)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_139, c_315])).
% 5.94/2.18  tff(c_50, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.94/2.18  tff(c_230, plain, (![A_75, B_76]: (r1_tarski(k1_relat_1(k5_relat_1(A_75, B_76)), k1_relat_1(A_75)) | ~v1_relat_1(B_76) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.94/2.18  tff(c_235, plain, (![B_76]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_76)), k1_xboole_0) | ~v1_relat_1(B_76) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_230])).
% 5.94/2.18  tff(c_243, plain, (![B_77]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_77)), k1_xboole_0) | ~v1_relat_1(B_77))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_235])).
% 5.94/2.18  tff(c_16, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.94/2.18  tff(c_166, plain, (![B_68, A_69]: (B_68=A_69 | ~r1_tarski(B_68, A_69) | ~r1_tarski(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.94/2.18  tff(c_175, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_166])).
% 5.94/2.18  tff(c_253, plain, (![B_78]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_78))=k1_xboole_0 | ~v1_relat_1(B_78))), inference(resolution, [status(thm)], [c_243, c_175])).
% 5.94/2.18  tff(c_42, plain, (![A_45]: (k3_xboole_0(A_45, k2_zfmisc_1(k1_relat_1(A_45), k2_relat_1(A_45)))=A_45 | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.94/2.18  tff(c_268, plain, (![B_78]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_78), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_78))))=k5_relat_1(k1_xboole_0, B_78) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_78)) | ~v1_relat_1(B_78))), inference(superposition, [status(thm), theory('equality')], [c_253, c_42])).
% 5.94/2.18  tff(c_5170, plain, (![B_214]: (k5_relat_1(k1_xboole_0, B_214)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_214)) | ~v1_relat_1(B_214))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_324, c_268])).
% 5.94/2.18  tff(c_5177, plain, (![B_44]: (k5_relat_1(k1_xboole_0, B_44)=k1_xboole_0 | ~v1_relat_1(B_44) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_40, c_5170])).
% 5.94/2.18  tff(c_5183, plain, (![B_215]: (k5_relat_1(k1_xboole_0, B_215)=k1_xboole_0 | ~v1_relat_1(B_215))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_5177])).
% 5.94/2.18  tff(c_5192, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_5183])).
% 5.94/2.18  tff(c_5199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_5192])).
% 5.94/2.18  tff(c_5200, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 5.94/2.18  tff(c_5202, plain, (![A_216]: (v1_relat_1(A_216) | ~v1_xboole_0(A_216))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.94/2.18  tff(c_5206, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_5202])).
% 5.94/2.18  tff(c_5229, plain, (![A_221, B_222]: (k5_xboole_0(A_221, k3_xboole_0(A_221, B_222))=k4_xboole_0(A_221, B_222))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.94/2.18  tff(c_5241, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_4, c_5229])).
% 5.94/2.18  tff(c_5244, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_5241])).
% 5.94/2.18  tff(c_5434, plain, (![C_243, A_244, B_245]: (k4_xboole_0(k2_zfmisc_1(C_243, A_244), k2_zfmisc_1(C_243, B_245))=k2_zfmisc_1(C_243, k4_xboole_0(A_244, B_245)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.94/2.18  tff(c_5441, plain, (![C_243, B_245]: (k2_zfmisc_1(C_243, k4_xboole_0(B_245, B_245))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5434, c_5244])).
% 5.94/2.18  tff(c_5450, plain, (![C_243]: (k2_zfmisc_1(C_243, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5244, c_5441])).
% 5.94/2.18  tff(c_48, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.94/2.18  tff(c_5798, plain, (![B_272, A_273]: (k2_relat_1(k5_relat_1(B_272, A_273))=k2_relat_1(A_273) | ~r1_tarski(k1_relat_1(A_273), k2_relat_1(B_272)) | ~v1_relat_1(B_272) | ~v1_relat_1(A_273))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.94/2.18  tff(c_5804, plain, (![B_272]: (k2_relat_1(k5_relat_1(B_272, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_272)) | ~v1_relat_1(B_272) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_5798])).
% 5.94/2.18  tff(c_5814, plain, (![B_274]: (k2_relat_1(k5_relat_1(B_274, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_274))), inference(demodulation, [status(thm), theory('equality')], [c_5206, c_16, c_48, c_5804])).
% 5.94/2.18  tff(c_5826, plain, (![B_274]: (k3_xboole_0(k5_relat_1(B_274, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_274, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_274, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_274, k1_xboole_0)) | ~v1_relat_1(B_274))), inference(superposition, [status(thm), theory('equality')], [c_5814, c_42])).
% 5.94/2.18  tff(c_5834, plain, (![B_275]: (k5_relat_1(B_275, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_275, k1_xboole_0)) | ~v1_relat_1(B_275))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_5450, c_5826])).
% 5.94/2.18  tff(c_5838, plain, (![A_43]: (k5_relat_1(A_43, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_43))), inference(resolution, [status(thm)], [c_40, c_5834])).
% 5.94/2.18  tff(c_5842, plain, (![A_276]: (k5_relat_1(A_276, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_276))), inference(demodulation, [status(thm), theory('equality')], [c_5206, c_5838])).
% 5.94/2.18  tff(c_5851, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_5842])).
% 5.94/2.18  tff(c_5857, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5200, c_5851])).
% 5.94/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.94/2.18  
% 5.94/2.18  Inference rules
% 5.94/2.18  ----------------------
% 5.94/2.18  #Ref     : 0
% 5.94/2.18  #Sup     : 1391
% 5.94/2.18  #Fact    : 0
% 5.94/2.18  #Define  : 0
% 5.94/2.18  #Split   : 1
% 5.94/2.18  #Chain   : 0
% 5.94/2.18  #Close   : 0
% 5.94/2.18  
% 5.94/2.18  Ordering : KBO
% 5.94/2.18  
% 5.94/2.18  Simplification rules
% 5.94/2.18  ----------------------
% 5.94/2.18  #Subsume      : 88
% 5.94/2.18  #Demod        : 1650
% 5.94/2.18  #Tautology    : 630
% 5.94/2.18  #SimpNegUnit  : 2
% 5.94/2.18  #BackRed      : 4
% 5.94/2.18  
% 5.94/2.18  #Partial instantiations: 0
% 5.94/2.18  #Strategies tried      : 1
% 5.94/2.18  
% 5.94/2.18  Timing (in seconds)
% 5.94/2.18  ----------------------
% 5.94/2.18  Preprocessing        : 0.33
% 5.94/2.18  Parsing              : 0.18
% 5.94/2.18  CNF conversion       : 0.02
% 5.94/2.18  Main loop            : 1.10
% 5.94/2.18  Inferencing          : 0.35
% 5.94/2.18  Reduction            : 0.48
% 5.94/2.18  Demodulation         : 0.39
% 5.94/2.18  BG Simplification    : 0.05
% 5.94/2.18  Subsumption          : 0.16
% 5.94/2.18  Abstraction          : 0.07
% 5.94/2.18  MUC search           : 0.00
% 5.94/2.18  Cooper               : 0.00
% 5.94/2.18  Total                : 1.46
% 5.94/2.18  Index Insertion      : 0.00
% 5.94/2.18  Index Deletion       : 0.00
% 5.94/2.18  Index Matching       : 0.00
% 5.94/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
