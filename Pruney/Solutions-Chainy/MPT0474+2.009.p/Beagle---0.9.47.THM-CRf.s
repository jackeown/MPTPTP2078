%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:28 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 126 expanded)
%              Number of leaves         :   47 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :   67 ( 139 expanded)
%              Number of equality atoms :   33 (  71 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k3_tarski > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_40,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_94,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).

tff(f_62,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_64,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_42,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_56,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k6_subset_1(A,B)) = k6_subset_1(k4_relat_1(A),k4_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).

tff(c_54,plain,(
    ! [A_40] :
      ( r2_hidden('#skF_3'(A_40),A_40)
      | v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_209,plain,(
    ! [D_104,A_105,B_106] :
      ( r2_hidden(D_104,A_105)
      | ~ r2_hidden(D_104,k4_xboole_0(A_105,B_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_318,plain,(
    ! [A_126,B_127] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_126,B_127)),A_126)
      | v1_relat_1(k4_xboole_0(A_126,B_127)) ) ),
    inference(resolution,[status(thm)],[c_54,c_209])).

tff(c_24,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_195,plain,(
    ! [D_99,B_100,A_101] :
      ( ~ r2_hidden(D_99,B_100)
      | ~ r2_hidden(D_99,k4_xboole_0(A_101,B_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_298,plain,(
    ! [A_123,B_124] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_123,B_124)),B_124)
      | v1_relat_1(k4_xboole_0(A_123,B_124)) ) ),
    inference(resolution,[status(thm)],[c_54,c_195])).

tff(c_307,plain,(
    ! [A_9] :
      ( ~ r2_hidden('#skF_3'(A_9),k1_xboole_0)
      | v1_relat_1(k4_xboole_0(A_9,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_298])).

tff(c_310,plain,(
    ! [A_9] :
      ( ~ r2_hidden('#skF_3'(A_9),k1_xboole_0)
      | v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_307])).

tff(c_350,plain,(
    ! [B_127] : v1_relat_1(k4_xboole_0(k1_xboole_0,B_127)) ),
    inference(resolution,[status(thm)],[c_318,c_310])).

tff(c_74,plain,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_46,plain,(
    ! [A_37] : k1_setfam_1(k1_tarski(A_37)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_28,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_142,plain,(
    ! [A_91,B_92] : k1_setfam_1(k2_tarski(A_91,B_92)) = k3_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_151,plain,(
    ! [A_11] : k3_xboole_0(A_11,A_11) = k1_setfam_1(k1_tarski(A_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_142])).

tff(c_154,plain,(
    ! [A_11] : k3_xboole_0(A_11,A_11) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_151])).

tff(c_26,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_40,plain,(
    ! [A_32] : k3_tarski(k1_tarski(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_164,plain,(
    ! [A_94,B_95] : k3_tarski(k2_tarski(A_94,B_95)) = k2_xboole_0(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_173,plain,(
    ! [A_11] : k3_tarski(k1_tarski(A_11)) = k2_xboole_0(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_164])).

tff(c_176,plain,(
    ! [A_11] : k2_xboole_0(A_11,A_11) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_173])).

tff(c_235,plain,(
    ! [A_114,B_115] : k4_xboole_0(k2_xboole_0(A_114,B_115),k3_xboole_0(A_114,B_115)) = k5_xboole_0(A_114,B_115) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_250,plain,(
    ! [A_11] : k4_xboole_0(A_11,k3_xboole_0(A_11,A_11)) = k5_xboole_0(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_235])).

tff(c_256,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_26,c_250])).

tff(c_44,plain,(
    ! [A_35,B_36] : k6_subset_1(A_35,B_36) = k4_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_68,plain,(
    ! [A_77,B_79] :
      ( k6_subset_1(k4_relat_1(A_77),k4_relat_1(B_79)) = k4_relat_1(k6_subset_1(A_77,B_79))
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_585,plain,(
    ! [A_165,B_166] :
      ( k4_xboole_0(k4_relat_1(A_165),k4_relat_1(B_166)) = k4_relat_1(k4_xboole_0(A_165,B_166))
      | ~ v1_relat_1(B_166)
      | ~ v1_relat_1(A_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_68])).

tff(c_604,plain,(
    ! [B_166] :
      ( k4_relat_1(k4_xboole_0(B_166,B_166)) = k1_xboole_0
      | ~ v1_relat_1(B_166)
      | ~ v1_relat_1(B_166) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_256])).

tff(c_619,plain,(
    ! [B_166] :
      ( k4_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_166)
      | ~ v1_relat_1(B_166) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_604])).

tff(c_624,plain,(
    ! [B_167] :
      ( ~ v1_relat_1(B_167)
      | ~ v1_relat_1(B_167) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_619])).

tff(c_630,plain,(
    ! [B_127] : ~ v1_relat_1(k4_xboole_0(k1_xboole_0,B_127)) ),
    inference(resolution,[status(thm)],[c_350,c_624])).

tff(c_638,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_630])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:51:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.41  
% 2.62/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.41  %$ r2_hidden > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k3_tarski > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_5 > #skF_4
% 2.62/1.41  
% 2.62/1.41  %Foreground sorts:
% 2.62/1.41  
% 2.62/1.41  
% 2.62/1.41  %Background operators:
% 2.62/1.41  
% 2.62/1.41  
% 2.62/1.41  %Foreground operators:
% 2.62/1.41  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.62/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.62/1.41  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 2.62/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.62/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.62/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.62/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.62/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.62/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.62/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.62/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.62/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.62/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.62/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.62/1.41  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.62/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.62/1.41  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 2.62/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.62/1.41  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 2.62/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.62/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.41  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.62/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.62/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.62/1.41  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.62/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.62/1.41  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.62/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.62/1.41  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.62/1.41  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.62/1.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.62/1.41  
% 2.62/1.43  tff(f_74, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.62/1.43  tff(f_36, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.62/1.43  tff(f_40, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.62/1.43  tff(f_94, negated_conjecture, ~(k4_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_relat_1)).
% 2.62/1.43  tff(f_62, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.62/1.43  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.62/1.43  tff(f_64, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.62/1.43  tff(f_42, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.62/1.43  tff(f_56, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 2.62/1.43  tff(f_58, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_zfmisc_1)).
% 2.62/1.43  tff(f_38, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t101_xboole_1)).
% 2.62/1.43  tff(f_60, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.62/1.43  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k6_subset_1(A, B)) = k6_subset_1(k4_relat_1(A), k4_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_relat_1)).
% 2.62/1.43  tff(c_54, plain, (![A_40]: (r2_hidden('#skF_3'(A_40), A_40) | v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.62/1.43  tff(c_209, plain, (![D_104, A_105, B_106]: (r2_hidden(D_104, A_105) | ~r2_hidden(D_104, k4_xboole_0(A_105, B_106)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.62/1.43  tff(c_318, plain, (![A_126, B_127]: (r2_hidden('#skF_3'(k4_xboole_0(A_126, B_127)), A_126) | v1_relat_1(k4_xboole_0(A_126, B_127)))), inference(resolution, [status(thm)], [c_54, c_209])).
% 2.62/1.43  tff(c_24, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.62/1.43  tff(c_195, plain, (![D_99, B_100, A_101]: (~r2_hidden(D_99, B_100) | ~r2_hidden(D_99, k4_xboole_0(A_101, B_100)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.62/1.43  tff(c_298, plain, (![A_123, B_124]: (~r2_hidden('#skF_3'(k4_xboole_0(A_123, B_124)), B_124) | v1_relat_1(k4_xboole_0(A_123, B_124)))), inference(resolution, [status(thm)], [c_54, c_195])).
% 2.62/1.43  tff(c_307, plain, (![A_9]: (~r2_hidden('#skF_3'(A_9), k1_xboole_0) | v1_relat_1(k4_xboole_0(A_9, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_298])).
% 2.62/1.43  tff(c_310, plain, (![A_9]: (~r2_hidden('#skF_3'(A_9), k1_xboole_0) | v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_307])).
% 2.62/1.43  tff(c_350, plain, (![B_127]: (v1_relat_1(k4_xboole_0(k1_xboole_0, B_127)))), inference(resolution, [status(thm)], [c_318, c_310])).
% 2.62/1.43  tff(c_74, plain, (k4_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.62/1.43  tff(c_46, plain, (![A_37]: (k1_setfam_1(k1_tarski(A_37))=A_37)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.62/1.43  tff(c_28, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.62/1.43  tff(c_142, plain, (![A_91, B_92]: (k1_setfam_1(k2_tarski(A_91, B_92))=k3_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.62/1.43  tff(c_151, plain, (![A_11]: (k3_xboole_0(A_11, A_11)=k1_setfam_1(k1_tarski(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_142])).
% 2.62/1.43  tff(c_154, plain, (![A_11]: (k3_xboole_0(A_11, A_11)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_151])).
% 2.62/1.43  tff(c_26, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.62/1.43  tff(c_40, plain, (![A_32]: (k3_tarski(k1_tarski(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.62/1.43  tff(c_164, plain, (![A_94, B_95]: (k3_tarski(k2_tarski(A_94, B_95))=k2_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.62/1.43  tff(c_173, plain, (![A_11]: (k3_tarski(k1_tarski(A_11))=k2_xboole_0(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_28, c_164])).
% 2.62/1.43  tff(c_176, plain, (![A_11]: (k2_xboole_0(A_11, A_11)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_173])).
% 2.62/1.43  tff(c_235, plain, (![A_114, B_115]: (k4_xboole_0(k2_xboole_0(A_114, B_115), k3_xboole_0(A_114, B_115))=k5_xboole_0(A_114, B_115))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.62/1.43  tff(c_250, plain, (![A_11]: (k4_xboole_0(A_11, k3_xboole_0(A_11, A_11))=k5_xboole_0(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_176, c_235])).
% 2.62/1.43  tff(c_256, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_154, c_26, c_250])).
% 2.62/1.43  tff(c_44, plain, (![A_35, B_36]: (k6_subset_1(A_35, B_36)=k4_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.62/1.43  tff(c_68, plain, (![A_77, B_79]: (k6_subset_1(k4_relat_1(A_77), k4_relat_1(B_79))=k4_relat_1(k6_subset_1(A_77, B_79)) | ~v1_relat_1(B_79) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.62/1.43  tff(c_585, plain, (![A_165, B_166]: (k4_xboole_0(k4_relat_1(A_165), k4_relat_1(B_166))=k4_relat_1(k4_xboole_0(A_165, B_166)) | ~v1_relat_1(B_166) | ~v1_relat_1(A_165))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_68])).
% 2.62/1.43  tff(c_604, plain, (![B_166]: (k4_relat_1(k4_xboole_0(B_166, B_166))=k1_xboole_0 | ~v1_relat_1(B_166) | ~v1_relat_1(B_166))), inference(superposition, [status(thm), theory('equality')], [c_585, c_256])).
% 2.62/1.43  tff(c_619, plain, (![B_166]: (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_166) | ~v1_relat_1(B_166))), inference(demodulation, [status(thm), theory('equality')], [c_256, c_604])).
% 2.62/1.43  tff(c_624, plain, (![B_167]: (~v1_relat_1(B_167) | ~v1_relat_1(B_167))), inference(negUnitSimplification, [status(thm)], [c_74, c_619])).
% 2.62/1.43  tff(c_630, plain, (![B_127]: (~v1_relat_1(k4_xboole_0(k1_xboole_0, B_127)))), inference(resolution, [status(thm)], [c_350, c_624])).
% 2.62/1.43  tff(c_638, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_350, c_630])).
% 2.62/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.43  
% 2.62/1.43  Inference rules
% 2.62/1.43  ----------------------
% 2.62/1.43  #Ref     : 1
% 2.62/1.43  #Sup     : 128
% 2.62/1.43  #Fact    : 0
% 2.62/1.43  #Define  : 0
% 2.62/1.43  #Split   : 1
% 2.62/1.43  #Chain   : 0
% 2.62/1.43  #Close   : 0
% 2.62/1.43  
% 2.62/1.43  Ordering : KBO
% 2.62/1.43  
% 2.62/1.43  Simplification rules
% 2.62/1.43  ----------------------
% 2.62/1.43  #Subsume      : 15
% 2.62/1.43  #Demod        : 51
% 2.62/1.43  #Tautology    : 65
% 2.62/1.43  #SimpNegUnit  : 7
% 2.62/1.43  #BackRed      : 0
% 2.62/1.43  
% 2.62/1.43  #Partial instantiations: 0
% 2.62/1.43  #Strategies tried      : 1
% 2.62/1.43  
% 2.62/1.43  Timing (in seconds)
% 2.62/1.43  ----------------------
% 2.62/1.43  Preprocessing        : 0.36
% 2.62/1.43  Parsing              : 0.19
% 2.62/1.43  CNF conversion       : 0.03
% 2.62/1.43  Main loop            : 0.27
% 2.62/1.43  Inferencing          : 0.10
% 2.62/1.43  Reduction            : 0.09
% 2.62/1.43  Demodulation         : 0.06
% 2.62/1.43  BG Simplification    : 0.02
% 2.62/1.43  Subsumption          : 0.05
% 2.62/1.43  Abstraction          : 0.02
% 2.62/1.43  MUC search           : 0.00
% 2.62/1.43  Cooper               : 0.00
% 2.62/1.43  Total                : 0.67
% 2.62/1.43  Index Insertion      : 0.00
% 2.62/1.43  Index Deletion       : 0.00
% 2.62/1.43  Index Matching       : 0.00
% 2.62/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
