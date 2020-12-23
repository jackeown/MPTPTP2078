%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:01 EST 2020

% Result     : Theorem 6.67s
% Output     : CNFRefutation 6.67s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 661 expanded)
%              Number of leaves         :   33 ( 233 expanded)
%              Depth                    :   16
%              Number of atoms          :  135 (1308 expanded)
%              Number of equality atoms :   18 ( 186 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_63,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_104,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_57,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_44,plain,(
    ! [B_19] : r1_tarski(B_19,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_162,plain,(
    ! [A_55,B_56] :
      ( k3_xboole_0(A_55,B_56) = A_55
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_166,plain,(
    ! [B_19] : k3_xboole_0(B_19,B_19) = B_19 ),
    inference(resolution,[status(thm)],[c_44,c_162])).

tff(c_266,plain,(
    ! [A_71,B_72] : k5_xboole_0(A_71,k3_xboole_0(A_71,B_72)) = k4_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_275,plain,(
    ! [B_19] : k5_xboole_0(B_19,B_19) = k4_xboole_0(B_19,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_266])).

tff(c_72,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_84,plain,(
    ! [B_41,A_42] :
      ( ~ r2_hidden(B_41,A_42)
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_88,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_84])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_209,plain,(
    ! [D_63,B_64,A_65] :
      ( r2_hidden(D_63,B_64)
      | ~ r2_hidden(D_63,k3_xboole_0(A_65,B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_525,plain,(
    ! [A_104,B_105] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_104,B_105)),B_105)
      | v1_xboole_0(k3_xboole_0(A_104,B_105)) ) ),
    inference(resolution,[status(thm)],[c_6,c_209])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_559,plain,(
    ! [B_106,A_107] :
      ( ~ v1_xboole_0(B_106)
      | v1_xboole_0(k3_xboole_0(A_107,B_106)) ) ),
    inference(resolution,[status(thm)],[c_525,c_4])).

tff(c_181,plain,(
    ! [B_60,A_61] :
      ( m1_subset_1(B_60,A_61)
      | ~ r2_hidden(B_60,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_193,plain,
    ( m1_subset_1('#skF_5','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_181])).

tff(c_199,plain,(
    m1_subset_1('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_193])).

tff(c_339,plain,(
    ! [B_80,A_81] :
      ( m1_subset_1(k1_tarski(B_80),k1_zfmisc_1(A_81))
      | k1_xboole_0 = A_81
      | ~ m1_subset_1(B_80,A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_70,plain,(
    ~ m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_345,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ m1_subset_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_339,c_70])).

tff(c_349,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_345])).

tff(c_38,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_4'(A_16),A_16)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_241,plain,(
    ! [D_68,A_69,B_70] :
      ( r2_hidden(D_68,A_69)
      | ~ r2_hidden(D_68,k3_xboole_0(A_69,B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_264,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_4'(k3_xboole_0(A_69,B_70)),A_69)
      | k3_xboole_0(A_69,B_70) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_241])).

tff(c_445,plain,(
    ! [A_92,B_93] :
      ( r2_hidden('#skF_4'(k3_xboole_0(A_92,B_93)),A_92)
      | k3_xboole_0(A_92,B_93) = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_264])).

tff(c_477,plain,(
    ! [A_92,B_93] :
      ( ~ v1_xboole_0(A_92)
      | k3_xboole_0(A_92,B_93) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_445,c_4])).

tff(c_621,plain,(
    ! [A_113,B_114,B_115] :
      ( k3_xboole_0(k3_xboole_0(A_113,B_114),B_115) = '#skF_6'
      | ~ v1_xboole_0(B_114) ) ),
    inference(resolution,[status(thm)],[c_559,c_477])).

tff(c_557,plain,(
    ! [B_105,A_104] :
      ( ~ v1_xboole_0(B_105)
      | v1_xboole_0(k3_xboole_0(A_104,B_105)) ) ),
    inference(resolution,[status(thm)],[c_525,c_4])).

tff(c_633,plain,(
    ! [B_115,B_114] :
      ( ~ v1_xboole_0(B_115)
      | v1_xboole_0('#skF_6')
      | ~ v1_xboole_0(B_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_621,c_557])).

tff(c_697,plain,(
    ! [B_115,B_114] :
      ( ~ v1_xboole_0(B_115)
      | ~ v1_xboole_0(B_114) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_633])).

tff(c_699,plain,(
    ! [B_114] : ~ v1_xboole_0(B_114) ),
    inference(splitLeft,[status(thm)],[c_697])).

tff(c_710,plain,(
    ! [A_117] : r2_hidden('#skF_1'(A_117),A_117) ),
    inference(negUnitSimplification,[status(thm)],[c_699,c_6])).

tff(c_32,plain,(
    ! [A_13,B_14,C_15] :
      ( r2_hidden(A_13,B_14)
      | r2_hidden(A_13,C_15)
      | ~ r2_hidden(A_13,k5_xboole_0(B_14,C_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_723,plain,(
    ! [B_14,C_15] :
      ( r2_hidden('#skF_1'(k5_xboole_0(B_14,C_15)),B_14)
      | r2_hidden('#skF_1'(k5_xboole_0(B_14,C_15)),C_15) ) ),
    inference(resolution,[status(thm)],[c_710,c_32])).

tff(c_3103,plain,(
    ! [B_14] : r2_hidden('#skF_1'(k5_xboole_0(B_14,B_14)),B_14) ),
    inference(factorization,[status(thm),theory(equality)],[c_723])).

tff(c_3179,plain,(
    ! [B_291] : r2_hidden('#skF_1'(k4_xboole_0(B_291,B_291)),B_291) ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_3103])).

tff(c_60,plain,(
    ! [B_36,A_35] :
      ( m1_subset_1(B_36,A_35)
      | ~ r2_hidden(B_36,A_35)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_705,plain,(
    ! [B_36,A_35] :
      ( m1_subset_1(B_36,A_35)
      | ~ r2_hidden(B_36,A_35) ) ),
    inference(negUnitSimplification,[status(thm)],[c_699,c_60])).

tff(c_3204,plain,(
    ! [B_291] : m1_subset_1('#skF_1'(k4_xboole_0(B_291,B_291)),B_291) ),
    inference(resolution,[status(thm)],[c_3179,c_705])).

tff(c_3105,plain,(
    ! [B_14] : r2_hidden('#skF_1'(k4_xboole_0(B_14,B_14)),B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_3103])).

tff(c_62,plain,(
    ! [B_36,A_35] :
      ( r2_hidden(B_36,A_35)
      | ~ m1_subset_1(B_36,A_35)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_706,plain,(
    ! [B_36,A_35] :
      ( r2_hidden(B_36,A_35)
      | ~ m1_subset_1(B_36,A_35) ) ),
    inference(negUnitSimplification,[status(thm)],[c_699,c_62])).

tff(c_708,plain,(
    ! [A_3] : r2_hidden('#skF_1'(A_3),A_3) ),
    inference(negUnitSimplification,[status(thm)],[c_699,c_6])).

tff(c_993,plain,(
    ! [A_144,C_145,B_146] :
      ( ~ r2_hidden(A_144,C_145)
      | ~ r2_hidden(A_144,B_146)
      | ~ r2_hidden(A_144,k5_xboole_0(B_146,C_145)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3057,plain,(
    ! [B_287,C_288] :
      ( ~ r2_hidden('#skF_1'(k5_xboole_0(B_287,C_288)),C_288)
      | ~ r2_hidden('#skF_1'(k5_xboole_0(B_287,C_288)),B_287) ) ),
    inference(resolution,[status(thm)],[c_708,c_993])).

tff(c_4091,plain,(
    ! [B_320,A_321] :
      ( ~ r2_hidden('#skF_1'(k5_xboole_0(B_320,A_321)),B_320)
      | ~ m1_subset_1('#skF_1'(k5_xboole_0(B_320,A_321)),A_321) ) ),
    inference(resolution,[status(thm)],[c_706,c_3057])).

tff(c_4115,plain,(
    ! [B_19] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(B_19,B_19)),B_19)
      | ~ m1_subset_1('#skF_1'(k5_xboole_0(B_19,B_19)),B_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_4091])).

tff(c_4128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3204,c_275,c_3105,c_4115])).

tff(c_4129,plain,(
    ! [B_115] : ~ v1_xboole_0(B_115) ),
    inference(splitRight,[status(thm)],[c_697])).

tff(c_4140,plain,(
    ! [A_323] : r2_hidden('#skF_1'(A_323),A_323) ),
    inference(negUnitSimplification,[status(thm)],[c_4129,c_6])).

tff(c_4153,plain,(
    ! [B_14,C_15] :
      ( r2_hidden('#skF_1'(k5_xboole_0(B_14,C_15)),B_14)
      | r2_hidden('#skF_1'(k5_xboole_0(B_14,C_15)),C_15) ) ),
    inference(resolution,[status(thm)],[c_4140,c_32])).

tff(c_6525,plain,(
    ! [B_14] : r2_hidden('#skF_1'(k5_xboole_0(B_14,B_14)),B_14) ),
    inference(factorization,[status(thm),theory(equality)],[c_4153])).

tff(c_6601,plain,(
    ! [B_497] : r2_hidden('#skF_1'(k4_xboole_0(B_497,B_497)),B_497) ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_6525])).

tff(c_4135,plain,(
    ! [B_36,A_35] :
      ( m1_subset_1(B_36,A_35)
      | ~ r2_hidden(B_36,A_35) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4129,c_60])).

tff(c_6626,plain,(
    ! [B_497] : m1_subset_1('#skF_1'(k4_xboole_0(B_497,B_497)),B_497) ),
    inference(resolution,[status(thm)],[c_6601,c_4135])).

tff(c_6527,plain,(
    ! [B_14] : r2_hidden('#skF_1'(k4_xboole_0(B_14,B_14)),B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_6525])).

tff(c_4136,plain,(
    ! [B_36,A_35] :
      ( r2_hidden(B_36,A_35)
      | ~ m1_subset_1(B_36,A_35) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4129,c_62])).

tff(c_4138,plain,(
    ! [A_3] : r2_hidden('#skF_1'(A_3),A_3) ),
    inference(negUnitSimplification,[status(thm)],[c_4129,c_6])).

tff(c_4316,plain,(
    ! [A_341,C_342,B_343] :
      ( ~ r2_hidden(A_341,C_342)
      | ~ r2_hidden(A_341,B_343)
      | ~ r2_hidden(A_341,k5_xboole_0(B_343,C_342)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6483,plain,(
    ! [B_493,C_494] :
      ( ~ r2_hidden('#skF_1'(k5_xboole_0(B_493,C_494)),C_494)
      | ~ r2_hidden('#skF_1'(k5_xboole_0(B_493,C_494)),B_493) ) ),
    inference(resolution,[status(thm)],[c_4138,c_4316])).

tff(c_7596,plain,(
    ! [B_528,A_529] :
      ( ~ r2_hidden('#skF_1'(k5_xboole_0(B_528,A_529)),B_528)
      | ~ m1_subset_1('#skF_1'(k5_xboole_0(B_528,A_529)),A_529) ) ),
    inference(resolution,[status(thm)],[c_4136,c_6483])).

tff(c_7623,plain,(
    ! [B_19] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(B_19,B_19)),B_19)
      | ~ m1_subset_1('#skF_1'(k5_xboole_0(B_19,B_19)),B_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_7596])).

tff(c_7639,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6626,c_275,c_6527,c_7623])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:26:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.67/2.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.67/2.36  
% 6.67/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.67/2.36  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 6.67/2.36  
% 6.67/2.36  %Foreground sorts:
% 6.67/2.36  
% 6.67/2.36  
% 6.67/2.36  %Background operators:
% 6.67/2.36  
% 6.67/2.36  
% 6.67/2.36  %Foreground operators:
% 6.67/2.36  tff('#skF_4', type, '#skF_4': $i > $i).
% 6.67/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.67/2.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.67/2.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.67/2.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.67/2.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.67/2.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.67/2.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.67/2.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.67/2.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.67/2.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.67/2.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.67/2.36  tff('#skF_5', type, '#skF_5': $i).
% 6.67/2.36  tff('#skF_6', type, '#skF_6': $i).
% 6.67/2.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.67/2.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.67/2.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.67/2.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.67/2.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.67/2.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.67/2.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.67/2.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.67/2.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.67/2.36  
% 6.67/2.38  tff(f_63, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.67/2.38  tff(f_69, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.67/2.38  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.67/2.38  tff(f_104, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 6.67/2.38  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.67/2.38  tff(f_42, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 6.67/2.38  tff(f_92, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 6.67/2.38  tff(f_99, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 6.67/2.38  tff(f_57, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.67/2.38  tff(f_49, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 6.67/2.38  tff(c_44, plain, (![B_19]: (r1_tarski(B_19, B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.67/2.38  tff(c_162, plain, (![A_55, B_56]: (k3_xboole_0(A_55, B_56)=A_55 | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.67/2.38  tff(c_166, plain, (![B_19]: (k3_xboole_0(B_19, B_19)=B_19)), inference(resolution, [status(thm)], [c_44, c_162])).
% 6.67/2.38  tff(c_266, plain, (![A_71, B_72]: (k5_xboole_0(A_71, k3_xboole_0(A_71, B_72))=k4_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.67/2.38  tff(c_275, plain, (![B_19]: (k5_xboole_0(B_19, B_19)=k4_xboole_0(B_19, B_19))), inference(superposition, [status(thm), theory('equality')], [c_166, c_266])).
% 6.67/2.38  tff(c_72, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.67/2.38  tff(c_84, plain, (![B_41, A_42]: (~r2_hidden(B_41, A_42) | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.67/2.38  tff(c_88, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_72, c_84])).
% 6.67/2.38  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.67/2.38  tff(c_209, plain, (![D_63, B_64, A_65]: (r2_hidden(D_63, B_64) | ~r2_hidden(D_63, k3_xboole_0(A_65, B_64)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.67/2.38  tff(c_525, plain, (![A_104, B_105]: (r2_hidden('#skF_1'(k3_xboole_0(A_104, B_105)), B_105) | v1_xboole_0(k3_xboole_0(A_104, B_105)))), inference(resolution, [status(thm)], [c_6, c_209])).
% 6.67/2.38  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.67/2.38  tff(c_559, plain, (![B_106, A_107]: (~v1_xboole_0(B_106) | v1_xboole_0(k3_xboole_0(A_107, B_106)))), inference(resolution, [status(thm)], [c_525, c_4])).
% 6.67/2.38  tff(c_181, plain, (![B_60, A_61]: (m1_subset_1(B_60, A_61) | ~r2_hidden(B_60, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.67/2.38  tff(c_193, plain, (m1_subset_1('#skF_5', '#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_72, c_181])).
% 6.67/2.38  tff(c_199, plain, (m1_subset_1('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_88, c_193])).
% 6.67/2.38  tff(c_339, plain, (![B_80, A_81]: (m1_subset_1(k1_tarski(B_80), k1_zfmisc_1(A_81)) | k1_xboole_0=A_81 | ~m1_subset_1(B_80, A_81))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.67/2.38  tff(c_70, plain, (~m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.67/2.38  tff(c_345, plain, (k1_xboole_0='#skF_6' | ~m1_subset_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_339, c_70])).
% 6.67/2.38  tff(c_349, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_199, c_345])).
% 6.67/2.38  tff(c_38, plain, (![A_16]: (r2_hidden('#skF_4'(A_16), A_16) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.67/2.38  tff(c_241, plain, (![D_68, A_69, B_70]: (r2_hidden(D_68, A_69) | ~r2_hidden(D_68, k3_xboole_0(A_69, B_70)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.67/2.38  tff(c_264, plain, (![A_69, B_70]: (r2_hidden('#skF_4'(k3_xboole_0(A_69, B_70)), A_69) | k3_xboole_0(A_69, B_70)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_241])).
% 6.67/2.38  tff(c_445, plain, (![A_92, B_93]: (r2_hidden('#skF_4'(k3_xboole_0(A_92, B_93)), A_92) | k3_xboole_0(A_92, B_93)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_349, c_264])).
% 6.67/2.38  tff(c_477, plain, (![A_92, B_93]: (~v1_xboole_0(A_92) | k3_xboole_0(A_92, B_93)='#skF_6')), inference(resolution, [status(thm)], [c_445, c_4])).
% 6.67/2.38  tff(c_621, plain, (![A_113, B_114, B_115]: (k3_xboole_0(k3_xboole_0(A_113, B_114), B_115)='#skF_6' | ~v1_xboole_0(B_114))), inference(resolution, [status(thm)], [c_559, c_477])).
% 6.67/2.38  tff(c_557, plain, (![B_105, A_104]: (~v1_xboole_0(B_105) | v1_xboole_0(k3_xboole_0(A_104, B_105)))), inference(resolution, [status(thm)], [c_525, c_4])).
% 6.67/2.38  tff(c_633, plain, (![B_115, B_114]: (~v1_xboole_0(B_115) | v1_xboole_0('#skF_6') | ~v1_xboole_0(B_114))), inference(superposition, [status(thm), theory('equality')], [c_621, c_557])).
% 6.67/2.38  tff(c_697, plain, (![B_115, B_114]: (~v1_xboole_0(B_115) | ~v1_xboole_0(B_114))), inference(negUnitSimplification, [status(thm)], [c_88, c_633])).
% 6.67/2.38  tff(c_699, plain, (![B_114]: (~v1_xboole_0(B_114))), inference(splitLeft, [status(thm)], [c_697])).
% 6.67/2.38  tff(c_710, plain, (![A_117]: (r2_hidden('#skF_1'(A_117), A_117))), inference(negUnitSimplification, [status(thm)], [c_699, c_6])).
% 6.67/2.38  tff(c_32, plain, (![A_13, B_14, C_15]: (r2_hidden(A_13, B_14) | r2_hidden(A_13, C_15) | ~r2_hidden(A_13, k5_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.67/2.38  tff(c_723, plain, (![B_14, C_15]: (r2_hidden('#skF_1'(k5_xboole_0(B_14, C_15)), B_14) | r2_hidden('#skF_1'(k5_xboole_0(B_14, C_15)), C_15))), inference(resolution, [status(thm)], [c_710, c_32])).
% 6.67/2.38  tff(c_3103, plain, (![B_14]: (r2_hidden('#skF_1'(k5_xboole_0(B_14, B_14)), B_14))), inference(factorization, [status(thm), theory('equality')], [c_723])).
% 6.67/2.38  tff(c_3179, plain, (![B_291]: (r2_hidden('#skF_1'(k4_xboole_0(B_291, B_291)), B_291))), inference(demodulation, [status(thm), theory('equality')], [c_275, c_3103])).
% 6.67/2.38  tff(c_60, plain, (![B_36, A_35]: (m1_subset_1(B_36, A_35) | ~r2_hidden(B_36, A_35) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.67/2.38  tff(c_705, plain, (![B_36, A_35]: (m1_subset_1(B_36, A_35) | ~r2_hidden(B_36, A_35))), inference(negUnitSimplification, [status(thm)], [c_699, c_60])).
% 6.67/2.38  tff(c_3204, plain, (![B_291]: (m1_subset_1('#skF_1'(k4_xboole_0(B_291, B_291)), B_291))), inference(resolution, [status(thm)], [c_3179, c_705])).
% 6.67/2.38  tff(c_3105, plain, (![B_14]: (r2_hidden('#skF_1'(k4_xboole_0(B_14, B_14)), B_14))), inference(demodulation, [status(thm), theory('equality')], [c_275, c_3103])).
% 6.67/2.38  tff(c_62, plain, (![B_36, A_35]: (r2_hidden(B_36, A_35) | ~m1_subset_1(B_36, A_35) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.67/2.38  tff(c_706, plain, (![B_36, A_35]: (r2_hidden(B_36, A_35) | ~m1_subset_1(B_36, A_35))), inference(negUnitSimplification, [status(thm)], [c_699, c_62])).
% 6.67/2.38  tff(c_708, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), A_3))), inference(negUnitSimplification, [status(thm)], [c_699, c_6])).
% 6.67/2.38  tff(c_993, plain, (![A_144, C_145, B_146]: (~r2_hidden(A_144, C_145) | ~r2_hidden(A_144, B_146) | ~r2_hidden(A_144, k5_xboole_0(B_146, C_145)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.67/2.38  tff(c_3057, plain, (![B_287, C_288]: (~r2_hidden('#skF_1'(k5_xboole_0(B_287, C_288)), C_288) | ~r2_hidden('#skF_1'(k5_xboole_0(B_287, C_288)), B_287))), inference(resolution, [status(thm)], [c_708, c_993])).
% 6.67/2.38  tff(c_4091, plain, (![B_320, A_321]: (~r2_hidden('#skF_1'(k5_xboole_0(B_320, A_321)), B_320) | ~m1_subset_1('#skF_1'(k5_xboole_0(B_320, A_321)), A_321))), inference(resolution, [status(thm)], [c_706, c_3057])).
% 6.67/2.38  tff(c_4115, plain, (![B_19]: (~r2_hidden('#skF_1'(k4_xboole_0(B_19, B_19)), B_19) | ~m1_subset_1('#skF_1'(k5_xboole_0(B_19, B_19)), B_19))), inference(superposition, [status(thm), theory('equality')], [c_275, c_4091])).
% 6.67/2.38  tff(c_4128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3204, c_275, c_3105, c_4115])).
% 6.67/2.38  tff(c_4129, plain, (![B_115]: (~v1_xboole_0(B_115))), inference(splitRight, [status(thm)], [c_697])).
% 6.67/2.38  tff(c_4140, plain, (![A_323]: (r2_hidden('#skF_1'(A_323), A_323))), inference(negUnitSimplification, [status(thm)], [c_4129, c_6])).
% 6.67/2.38  tff(c_4153, plain, (![B_14, C_15]: (r2_hidden('#skF_1'(k5_xboole_0(B_14, C_15)), B_14) | r2_hidden('#skF_1'(k5_xboole_0(B_14, C_15)), C_15))), inference(resolution, [status(thm)], [c_4140, c_32])).
% 6.67/2.38  tff(c_6525, plain, (![B_14]: (r2_hidden('#skF_1'(k5_xboole_0(B_14, B_14)), B_14))), inference(factorization, [status(thm), theory('equality')], [c_4153])).
% 6.67/2.38  tff(c_6601, plain, (![B_497]: (r2_hidden('#skF_1'(k4_xboole_0(B_497, B_497)), B_497))), inference(demodulation, [status(thm), theory('equality')], [c_275, c_6525])).
% 6.67/2.38  tff(c_4135, plain, (![B_36, A_35]: (m1_subset_1(B_36, A_35) | ~r2_hidden(B_36, A_35))), inference(negUnitSimplification, [status(thm)], [c_4129, c_60])).
% 6.67/2.38  tff(c_6626, plain, (![B_497]: (m1_subset_1('#skF_1'(k4_xboole_0(B_497, B_497)), B_497))), inference(resolution, [status(thm)], [c_6601, c_4135])).
% 6.67/2.38  tff(c_6527, plain, (![B_14]: (r2_hidden('#skF_1'(k4_xboole_0(B_14, B_14)), B_14))), inference(demodulation, [status(thm), theory('equality')], [c_275, c_6525])).
% 6.67/2.38  tff(c_4136, plain, (![B_36, A_35]: (r2_hidden(B_36, A_35) | ~m1_subset_1(B_36, A_35))), inference(negUnitSimplification, [status(thm)], [c_4129, c_62])).
% 6.67/2.38  tff(c_4138, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), A_3))), inference(negUnitSimplification, [status(thm)], [c_4129, c_6])).
% 6.67/2.38  tff(c_4316, plain, (![A_341, C_342, B_343]: (~r2_hidden(A_341, C_342) | ~r2_hidden(A_341, B_343) | ~r2_hidden(A_341, k5_xboole_0(B_343, C_342)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.67/2.38  tff(c_6483, plain, (![B_493, C_494]: (~r2_hidden('#skF_1'(k5_xboole_0(B_493, C_494)), C_494) | ~r2_hidden('#skF_1'(k5_xboole_0(B_493, C_494)), B_493))), inference(resolution, [status(thm)], [c_4138, c_4316])).
% 6.67/2.38  tff(c_7596, plain, (![B_528, A_529]: (~r2_hidden('#skF_1'(k5_xboole_0(B_528, A_529)), B_528) | ~m1_subset_1('#skF_1'(k5_xboole_0(B_528, A_529)), A_529))), inference(resolution, [status(thm)], [c_4136, c_6483])).
% 6.67/2.38  tff(c_7623, plain, (![B_19]: (~r2_hidden('#skF_1'(k4_xboole_0(B_19, B_19)), B_19) | ~m1_subset_1('#skF_1'(k5_xboole_0(B_19, B_19)), B_19))), inference(superposition, [status(thm), theory('equality')], [c_275, c_7596])).
% 6.67/2.38  tff(c_7639, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6626, c_275, c_6527, c_7623])).
% 6.67/2.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.67/2.38  
% 6.67/2.38  Inference rules
% 6.67/2.38  ----------------------
% 6.67/2.38  #Ref     : 0
% 6.67/2.38  #Sup     : 1614
% 6.67/2.38  #Fact    : 4
% 6.67/2.38  #Define  : 0
% 6.67/2.38  #Split   : 2
% 6.67/2.38  #Chain   : 0
% 6.67/2.38  #Close   : 0
% 6.67/2.38  
% 6.67/2.38  Ordering : KBO
% 6.67/2.38  
% 6.67/2.38  Simplification rules
% 6.67/2.38  ----------------------
% 6.67/2.38  #Subsume      : 171
% 6.67/2.38  #Demod        : 664
% 6.67/2.38  #Tautology    : 651
% 6.67/2.38  #SimpNegUnit  : 37
% 6.67/2.38  #BackRed      : 17
% 6.67/2.38  
% 6.67/2.38  #Partial instantiations: 0
% 6.67/2.38  #Strategies tried      : 1
% 6.67/2.38  
% 6.67/2.38  Timing (in seconds)
% 6.67/2.38  ----------------------
% 6.67/2.38  Preprocessing        : 0.33
% 6.67/2.38  Parsing              : 0.17
% 6.67/2.38  CNF conversion       : 0.03
% 6.67/2.38  Main loop            : 1.28
% 6.67/2.38  Inferencing          : 0.38
% 6.67/2.38  Reduction            : 0.51
% 6.67/2.38  Demodulation         : 0.41
% 6.67/2.38  BG Simplification    : 0.05
% 6.67/2.38  Subsumption          : 0.25
% 6.67/2.38  Abstraction          : 0.05
% 6.67/2.38  MUC search           : 0.00
% 6.67/2.38  Cooper               : 0.00
% 6.67/2.38  Total                : 1.66
% 6.67/2.38  Index Insertion      : 0.00
% 6.67/2.38  Index Deletion       : 0.00
% 6.67/2.38  Index Matching       : 0.00
% 6.67/2.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
