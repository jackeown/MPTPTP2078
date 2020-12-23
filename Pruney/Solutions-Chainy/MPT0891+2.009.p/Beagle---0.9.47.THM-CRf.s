%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:41 EST 2020

% Result     : Theorem 7.19s
% Output     : CNFRefutation 7.19s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 319 expanded)
%              Number of leaves         :   45 ( 130 expanded)
%              Depth                    :   11
%              Number of atoms          :  213 ( 667 expanded)
%              Number of equality atoms :  156 ( 465 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_167,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ~ ! [D] :
                ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
               => ( D != k5_mcart_1(A,B,C,D)
                  & D != k6_mcart_1(A,B,C,D)
                  & D != k7_mcart_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).

tff(f_57,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_59,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_103,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_40,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_36,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_143,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_87,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_139,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

tff(c_100,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_98,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_96,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_50,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_173,plain,(
    ! [A_89,B_90] : k1_enumset1(A_89,A_89,B_90) = k2_tarski(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28,plain,(
    ! [E_17,A_11,B_12] : r2_hidden(E_17,k1_enumset1(A_11,B_12,E_17)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_182,plain,(
    ! [B_90,A_89] : r2_hidden(B_90,k2_tarski(A_89,B_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_28])).

tff(c_74,plain,(
    ! [A_38] :
      ( r2_hidden('#skF_5'(A_38),A_38)
      | k1_xboole_0 = A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_7186,plain,(
    ! [D_724,B_725,A_726] :
      ( r2_hidden(D_724,B_725)
      | ~ r2_hidden(D_724,k3_xboole_0(A_726,B_725)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_7326,plain,(
    ! [A_751,B_752] :
      ( r2_hidden('#skF_5'(k3_xboole_0(A_751,B_752)),B_752)
      | k3_xboole_0(A_751,B_752) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_74,c_7186])).

tff(c_24,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_158,plain,(
    ! [C_76,B_77] : ~ r2_hidden(C_76,k4_xboole_0(B_77,k1_tarski(C_76))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_161,plain,(
    ! [C_76] : ~ r2_hidden(C_76,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_158])).

tff(c_7349,plain,(
    ! [A_751] : k3_xboole_0(A_751,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7326,c_161])).

tff(c_20,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3937,plain,(
    ! [A_422,B_423] : k4_xboole_0(A_422,k4_xboole_0(A_422,B_423)) = k3_xboole_0(A_422,B_423) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3956,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_3937])).

tff(c_7381,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7349,c_3956])).

tff(c_7493,plain,(
    ! [B_760,C_761,A_762] :
      ( ~ r2_hidden(B_760,C_761)
      | k4_xboole_0(k2_tarski(A_762,B_760),C_761) != k2_tarski(A_762,B_760) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_7497,plain,(
    ! [B_760,A_762] :
      ( ~ r2_hidden(B_760,k2_tarski(A_762,B_760))
      | k2_tarski(A_762,B_760) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7381,c_7493])).

tff(c_7513,plain,(
    ! [A_763,B_764] : k2_tarski(A_763,B_764) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_7497])).

tff(c_7515,plain,(
    ! [A_18] : k1_tarski(A_18) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_7513])).

tff(c_7627,plain,(
    ! [A_782,B_783,C_784] :
      ( r2_hidden(A_782,k4_xboole_0(B_783,k1_tarski(C_784)))
      | C_784 = A_782
      | ~ r2_hidden(A_782,B_783) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_7640,plain,(
    ! [A_782,C_784] :
      ( r2_hidden(A_782,k1_xboole_0)
      | C_784 = A_782
      | ~ r2_hidden(A_782,k1_tarski(C_784)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7381,c_7627])).

tff(c_7651,plain,(
    ! [C_785,A_786] :
      ( C_785 = A_786
      | ~ r2_hidden(A_786,k1_tarski(C_785)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_7640])).

tff(c_7666,plain,(
    ! [C_785] :
      ( '#skF_5'(k1_tarski(C_785)) = C_785
      | k1_tarski(C_785) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_74,c_7651])).

tff(c_7673,plain,(
    ! [C_785] : '#skF_5'(k1_tarski(C_785)) = C_785 ),
    inference(negUnitSimplification,[status(thm)],[c_7515,c_7666])).

tff(c_30,plain,(
    ! [E_17,A_11,C_13] : r2_hidden(E_17,k1_enumset1(A_11,E_17,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_191,plain,(
    ! [A_91,B_92] : r2_hidden(A_91,k2_tarski(A_91,B_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_30])).

tff(c_194,plain,(
    ! [A_18] : r2_hidden(A_18,k1_tarski(A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_191])).

tff(c_7351,plain,(
    ! [D_753,A_754,C_755,E_756] :
      ( ~ r2_hidden(D_753,A_754)
      | k3_mcart_1(C_755,D_753,E_756) != '#skF_5'(A_754)
      | k1_xboole_0 = A_754 ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_7373,plain,(
    ! [C_755,A_18,E_756] :
      ( k3_mcart_1(C_755,A_18,E_756) != '#skF_5'(k1_tarski(A_18))
      | k1_tarski(A_18) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_194,c_7351])).

tff(c_7602,plain,(
    ! [C_755,A_18,E_756] : k3_mcart_1(C_755,A_18,E_756) != '#skF_5'(k1_tarski(A_18)) ),
    inference(negUnitSimplification,[status(thm)],[c_7515,c_7373])).

tff(c_7674,plain,(
    ! [C_755,A_18,E_756] : k3_mcart_1(C_755,A_18,E_756) != A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7673,c_7602])).

tff(c_94,plain,(
    m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_4079,plain,(
    ! [A_437,B_438,C_439] : k4_tarski(k4_tarski(A_437,B_438),C_439) = k3_mcart_1(A_437,B_438,C_439) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_90,plain,(
    ! [A_62,B_63] : k2_mcart_1(k4_tarski(A_62,B_63)) = B_63 ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_70,plain,(
    ! [B_36,C_37] : k2_mcart_1(k4_tarski(B_36,C_37)) != k4_tarski(B_36,C_37) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_102,plain,(
    ! [B_36,C_37] : k4_tarski(B_36,C_37) != C_37 ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_70])).

tff(c_4097,plain,(
    ! [A_437,B_438,C_439] : k3_mcart_1(A_437,B_438,C_439) != C_439 ),
    inference(superposition,[status(thm),theory(equality)],[c_4079,c_102])).

tff(c_256,plain,(
    ! [D_102,B_103,A_104] :
      ( r2_hidden(D_102,B_103)
      | ~ r2_hidden(D_102,k3_xboole_0(A_104,B_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_547,plain,(
    ! [A_144,B_145] :
      ( r2_hidden('#skF_5'(k3_xboole_0(A_144,B_145)),B_145)
      | k3_xboole_0(A_144,B_145) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_74,c_256])).

tff(c_570,plain,(
    ! [A_144] : k3_xboole_0(A_144,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_547,c_161])).

tff(c_179,plain,(
    ! [A_89,B_90] : r2_hidden(A_89,k2_tarski(A_89,B_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_30])).

tff(c_207,plain,(
    ! [A_96,B_97] : k4_xboole_0(A_96,k4_xboole_0(A_96,B_97)) = k3_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_226,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_207])).

tff(c_397,plain,(
    ! [A_126,C_127,B_128] :
      ( ~ r2_hidden(A_126,C_127)
      | k4_xboole_0(k2_tarski(A_126,B_128),C_127) != k2_tarski(A_126,B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_405,plain,(
    ! [A_126,B_128] :
      ( ~ r2_hidden(A_126,k2_tarski(A_126,B_128))
      | k3_xboole_0(k2_tarski(A_126,B_128),k1_xboole_0) != k2_tarski(A_126,B_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_397])).

tff(c_430,plain,(
    ! [A_132,B_133] : k3_xboole_0(k2_tarski(A_132,B_133),k1_xboole_0) != k2_tarski(A_132,B_133) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_405])).

tff(c_433,plain,(
    ! [A_18] : k3_xboole_0(k1_tarski(A_18),k1_xboole_0) != k2_tarski(A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_430])).

tff(c_434,plain,(
    ! [A_18] : k3_xboole_0(k1_tarski(A_18),k1_xboole_0) != k1_tarski(A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_433])).

tff(c_592,plain,(
    ! [A_18] : k1_tarski(A_18) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_434])).

tff(c_690,plain,(
    ! [A_154] : k4_xboole_0(A_154,A_154) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_226])).

tff(c_54,plain,(
    ! [A_21,B_22,C_23] :
      ( r2_hidden(A_21,k4_xboole_0(B_22,k1_tarski(C_23)))
      | C_23 = A_21
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_696,plain,(
    ! [A_21,C_23] :
      ( r2_hidden(A_21,k1_xboole_0)
      | C_23 = A_21
      | ~ r2_hidden(A_21,k1_tarski(C_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_690,c_54])).

tff(c_768,plain,(
    ! [C_158,A_159] :
      ( C_158 = A_159
      | ~ r2_hidden(A_159,k1_tarski(C_158)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_696])).

tff(c_783,plain,(
    ! [C_158] :
      ( '#skF_5'(k1_tarski(C_158)) = C_158
      | k1_tarski(C_158) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_74,c_768])).

tff(c_790,plain,(
    ! [C_158] : '#skF_5'(k1_tarski(C_158)) = C_158 ),
    inference(negUnitSimplification,[status(thm)],[c_592,c_783])).

tff(c_805,plain,(
    ! [C_161,A_162,D_163,E_164] :
      ( ~ r2_hidden(C_161,A_162)
      | k3_mcart_1(C_161,D_163,E_164) != '#skF_5'(A_162)
      | k1_xboole_0 = A_162 ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_817,plain,(
    ! [A_18,D_163,E_164] :
      ( k3_mcart_1(A_18,D_163,E_164) != '#skF_5'(k1_tarski(A_18))
      | k1_tarski(A_18) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_194,c_805])).

tff(c_836,plain,(
    ! [A_18,D_163,E_164] :
      ( k3_mcart_1(A_18,D_163,E_164) != A_18
      | k1_tarski(A_18) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_817])).

tff(c_837,plain,(
    ! [A_18,D_163,E_164] : k3_mcart_1(A_18,D_163,E_164) != A_18 ),
    inference(negUnitSimplification,[status(thm)],[c_592,c_836])).

tff(c_92,plain,
    ( k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_195,plain,(
    k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_2067,plain,(
    ! [A_304,B_305,C_306,D_307] :
      ( k7_mcart_1(A_304,B_305,C_306,D_307) = k2_mcart_1(D_307)
      | ~ m1_subset_1(D_307,k3_zfmisc_1(A_304,B_305,C_306))
      | k1_xboole_0 = C_306
      | k1_xboole_0 = B_305
      | k1_xboole_0 = A_304 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2073,plain,
    ( k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_94,c_2067])).

tff(c_2076,plain,(
    k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_98,c_96,c_2073])).

tff(c_3845,plain,(
    ! [A_415,B_416,C_417,D_418] :
      ( k3_mcart_1(k5_mcart_1(A_415,B_416,C_417,D_418),k6_mcart_1(A_415,B_416,C_417,D_418),k7_mcart_1(A_415,B_416,C_417,D_418)) = D_418
      | ~ m1_subset_1(D_418,k3_zfmisc_1(A_415,B_416,C_417))
      | k1_xboole_0 = C_417
      | k1_xboole_0 = B_416
      | k1_xboole_0 = A_415 ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_3914,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k2_mcart_1('#skF_9')) = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_2076,c_3845])).

tff(c_3925,plain,
    ( k3_mcart_1('#skF_9',k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k2_mcart_1('#skF_9')) = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_195,c_3914])).

tff(c_3927,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_98,c_96,c_837,c_3925])).

tff(c_3928,plain,
    ( k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_3986,plain,(
    k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_3928])).

tff(c_7063,plain,(
    ! [A_718,B_719,C_720,D_721] :
      ( k3_mcart_1(k5_mcart_1(A_718,B_719,C_720,D_721),k6_mcart_1(A_718,B_719,C_720,D_721),k7_mcart_1(A_718,B_719,C_720,D_721)) = D_721
      | ~ m1_subset_1(D_721,k3_zfmisc_1(A_718,B_719,C_720))
      | k1_xboole_0 = C_720
      | k1_xboole_0 = B_719
      | k1_xboole_0 = A_718 ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_7132,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9') = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_3986,c_7063])).

tff(c_7140,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_7132])).

tff(c_7142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_98,c_96,c_4097,c_7140])).

tff(c_7143,plain,(
    k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_3928])).

tff(c_8965,plain,(
    ! [A_925,B_926,C_927,D_928] :
      ( k7_mcart_1(A_925,B_926,C_927,D_928) = k2_mcart_1(D_928)
      | ~ m1_subset_1(D_928,k3_zfmisc_1(A_925,B_926,C_927))
      | k1_xboole_0 = C_927
      | k1_xboole_0 = B_926
      | k1_xboole_0 = A_925 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_8971,plain,
    ( k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_94,c_8965])).

tff(c_8974,plain,(
    k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_98,c_96,c_8971])).

tff(c_11228,plain,(
    ! [A_1059,B_1060,C_1061,D_1062] :
      ( k3_mcart_1(k5_mcart_1(A_1059,B_1060,C_1061,D_1062),k6_mcart_1(A_1059,B_1060,C_1061,D_1062),k7_mcart_1(A_1059,B_1060,C_1061,D_1062)) = D_1062
      | ~ m1_subset_1(D_1062,k3_zfmisc_1(A_1059,B_1060,C_1061))
      | k1_xboole_0 = C_1061
      | k1_xboole_0 = B_1060
      | k1_xboole_0 = A_1059 ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_11297,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k2_mcart_1('#skF_9')) = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_8974,c_11228])).

tff(c_11308,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9',k2_mcart_1('#skF_9')) = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_7143,c_11297])).

tff(c_11310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_98,c_96,c_7674,c_11308])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.19/2.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.19/2.70  
% 7.19/2.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.19/2.70  %$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 7.19/2.70  
% 7.19/2.70  %Foreground sorts:
% 7.19/2.70  
% 7.19/2.70  
% 7.19/2.70  %Background operators:
% 7.19/2.70  
% 7.19/2.70  
% 7.19/2.70  %Foreground operators:
% 7.19/2.70  tff('#skF_5', type, '#skF_5': $i > $i).
% 7.19/2.70  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.19/2.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.19/2.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.19/2.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.19/2.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.19/2.70  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.19/2.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.19/2.70  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 7.19/2.70  tff('#skF_7', type, '#skF_7': $i).
% 7.19/2.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.19/2.70  tff('#skF_6', type, '#skF_6': $i).
% 7.19/2.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.19/2.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.19/2.70  tff('#skF_9', type, '#skF_9': $i).
% 7.19/2.70  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 7.19/2.70  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 7.19/2.70  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 7.19/2.70  tff('#skF_8', type, '#skF_8': $i).
% 7.19/2.70  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 7.19/2.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.19/2.70  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 7.19/2.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.19/2.70  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 7.19/2.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.19/2.70  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 7.19/2.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.19/2.70  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 7.19/2.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.19/2.70  
% 7.19/2.72  tff(f_167, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_mcart_1)).
% 7.19/2.72  tff(f_57, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.19/2.72  tff(f_59, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 7.19/2.72  tff(f_55, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 7.19/2.72  tff(f_103, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 7.19/2.72  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.19/2.72  tff(f_40, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 7.19/2.72  tff(f_66, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 7.19/2.72  tff(f_36, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.19/2.72  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.19/2.72  tff(f_74, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 7.19/2.72  tff(f_76, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 7.19/2.72  tff(f_143, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 7.19/2.72  tff(f_87, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 7.19/2.72  tff(f_139, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 7.19/2.72  tff(f_119, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 7.19/2.72  tff(c_100, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.19/2.72  tff(c_98, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.19/2.72  tff(c_96, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.19/2.72  tff(c_50, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.19/2.72  tff(c_173, plain, (![A_89, B_90]: (k1_enumset1(A_89, A_89, B_90)=k2_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.19/2.72  tff(c_28, plain, (![E_17, A_11, B_12]: (r2_hidden(E_17, k1_enumset1(A_11, B_12, E_17)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.19/2.72  tff(c_182, plain, (![B_90, A_89]: (r2_hidden(B_90, k2_tarski(A_89, B_90)))), inference(superposition, [status(thm), theory('equality')], [c_173, c_28])).
% 7.19/2.72  tff(c_74, plain, (![A_38]: (r2_hidden('#skF_5'(A_38), A_38) | k1_xboole_0=A_38)), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.19/2.72  tff(c_7186, plain, (![D_724, B_725, A_726]: (r2_hidden(D_724, B_725) | ~r2_hidden(D_724, k3_xboole_0(A_726, B_725)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.19/2.72  tff(c_7326, plain, (![A_751, B_752]: (r2_hidden('#skF_5'(k3_xboole_0(A_751, B_752)), B_752) | k3_xboole_0(A_751, B_752)=k1_xboole_0)), inference(resolution, [status(thm)], [c_74, c_7186])).
% 7.19/2.72  tff(c_24, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.19/2.72  tff(c_158, plain, (![C_76, B_77]: (~r2_hidden(C_76, k4_xboole_0(B_77, k1_tarski(C_76))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.19/2.72  tff(c_161, plain, (![C_76]: (~r2_hidden(C_76, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_158])).
% 7.19/2.72  tff(c_7349, plain, (![A_751]: (k3_xboole_0(A_751, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_7326, c_161])).
% 7.19/2.72  tff(c_20, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.19/2.72  tff(c_3937, plain, (![A_422, B_423]: (k4_xboole_0(A_422, k4_xboole_0(A_422, B_423))=k3_xboole_0(A_422, B_423))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.19/2.72  tff(c_3956, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_3937])).
% 7.19/2.72  tff(c_7381, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7349, c_3956])).
% 7.19/2.72  tff(c_7493, plain, (![B_760, C_761, A_762]: (~r2_hidden(B_760, C_761) | k4_xboole_0(k2_tarski(A_762, B_760), C_761)!=k2_tarski(A_762, B_760))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.19/2.72  tff(c_7497, plain, (![B_760, A_762]: (~r2_hidden(B_760, k2_tarski(A_762, B_760)) | k2_tarski(A_762, B_760)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7381, c_7493])).
% 7.19/2.72  tff(c_7513, plain, (![A_763, B_764]: (k2_tarski(A_763, B_764)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_182, c_7497])).
% 7.19/2.72  tff(c_7515, plain, (![A_18]: (k1_tarski(A_18)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_7513])).
% 7.19/2.72  tff(c_7627, plain, (![A_782, B_783, C_784]: (r2_hidden(A_782, k4_xboole_0(B_783, k1_tarski(C_784))) | C_784=A_782 | ~r2_hidden(A_782, B_783))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.19/2.72  tff(c_7640, plain, (![A_782, C_784]: (r2_hidden(A_782, k1_xboole_0) | C_784=A_782 | ~r2_hidden(A_782, k1_tarski(C_784)))), inference(superposition, [status(thm), theory('equality')], [c_7381, c_7627])).
% 7.19/2.72  tff(c_7651, plain, (![C_785, A_786]: (C_785=A_786 | ~r2_hidden(A_786, k1_tarski(C_785)))), inference(negUnitSimplification, [status(thm)], [c_161, c_7640])).
% 7.19/2.72  tff(c_7666, plain, (![C_785]: ('#skF_5'(k1_tarski(C_785))=C_785 | k1_tarski(C_785)=k1_xboole_0)), inference(resolution, [status(thm)], [c_74, c_7651])).
% 7.19/2.72  tff(c_7673, plain, (![C_785]: ('#skF_5'(k1_tarski(C_785))=C_785)), inference(negUnitSimplification, [status(thm)], [c_7515, c_7666])).
% 7.19/2.72  tff(c_30, plain, (![E_17, A_11, C_13]: (r2_hidden(E_17, k1_enumset1(A_11, E_17, C_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.19/2.72  tff(c_191, plain, (![A_91, B_92]: (r2_hidden(A_91, k2_tarski(A_91, B_92)))), inference(superposition, [status(thm), theory('equality')], [c_173, c_30])).
% 7.19/2.72  tff(c_194, plain, (![A_18]: (r2_hidden(A_18, k1_tarski(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_191])).
% 7.19/2.72  tff(c_7351, plain, (![D_753, A_754, C_755, E_756]: (~r2_hidden(D_753, A_754) | k3_mcart_1(C_755, D_753, E_756)!='#skF_5'(A_754) | k1_xboole_0=A_754)), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.19/2.72  tff(c_7373, plain, (![C_755, A_18, E_756]: (k3_mcart_1(C_755, A_18, E_756)!='#skF_5'(k1_tarski(A_18)) | k1_tarski(A_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_194, c_7351])).
% 7.19/2.72  tff(c_7602, plain, (![C_755, A_18, E_756]: (k3_mcart_1(C_755, A_18, E_756)!='#skF_5'(k1_tarski(A_18)))), inference(negUnitSimplification, [status(thm)], [c_7515, c_7373])).
% 7.19/2.72  tff(c_7674, plain, (![C_755, A_18, E_756]: (k3_mcart_1(C_755, A_18, E_756)!=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_7673, c_7602])).
% 7.19/2.72  tff(c_94, plain, (m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.19/2.72  tff(c_4079, plain, (![A_437, B_438, C_439]: (k4_tarski(k4_tarski(A_437, B_438), C_439)=k3_mcart_1(A_437, B_438, C_439))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.19/2.72  tff(c_90, plain, (![A_62, B_63]: (k2_mcart_1(k4_tarski(A_62, B_63))=B_63)), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.19/2.72  tff(c_70, plain, (![B_36, C_37]: (k2_mcart_1(k4_tarski(B_36, C_37))!=k4_tarski(B_36, C_37))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.19/2.72  tff(c_102, plain, (![B_36, C_37]: (k4_tarski(B_36, C_37)!=C_37)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_70])).
% 7.19/2.72  tff(c_4097, plain, (![A_437, B_438, C_439]: (k3_mcart_1(A_437, B_438, C_439)!=C_439)), inference(superposition, [status(thm), theory('equality')], [c_4079, c_102])).
% 7.19/2.72  tff(c_256, plain, (![D_102, B_103, A_104]: (r2_hidden(D_102, B_103) | ~r2_hidden(D_102, k3_xboole_0(A_104, B_103)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.19/2.72  tff(c_547, plain, (![A_144, B_145]: (r2_hidden('#skF_5'(k3_xboole_0(A_144, B_145)), B_145) | k3_xboole_0(A_144, B_145)=k1_xboole_0)), inference(resolution, [status(thm)], [c_74, c_256])).
% 7.19/2.72  tff(c_570, plain, (![A_144]: (k3_xboole_0(A_144, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_547, c_161])).
% 7.19/2.72  tff(c_179, plain, (![A_89, B_90]: (r2_hidden(A_89, k2_tarski(A_89, B_90)))), inference(superposition, [status(thm), theory('equality')], [c_173, c_30])).
% 7.19/2.72  tff(c_207, plain, (![A_96, B_97]: (k4_xboole_0(A_96, k4_xboole_0(A_96, B_97))=k3_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.19/2.72  tff(c_226, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_207])).
% 7.19/2.72  tff(c_397, plain, (![A_126, C_127, B_128]: (~r2_hidden(A_126, C_127) | k4_xboole_0(k2_tarski(A_126, B_128), C_127)!=k2_tarski(A_126, B_128))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.19/2.72  tff(c_405, plain, (![A_126, B_128]: (~r2_hidden(A_126, k2_tarski(A_126, B_128)) | k3_xboole_0(k2_tarski(A_126, B_128), k1_xboole_0)!=k2_tarski(A_126, B_128))), inference(superposition, [status(thm), theory('equality')], [c_226, c_397])).
% 7.19/2.72  tff(c_430, plain, (![A_132, B_133]: (k3_xboole_0(k2_tarski(A_132, B_133), k1_xboole_0)!=k2_tarski(A_132, B_133))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_405])).
% 7.19/2.72  tff(c_433, plain, (![A_18]: (k3_xboole_0(k1_tarski(A_18), k1_xboole_0)!=k2_tarski(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_50, c_430])).
% 7.19/2.72  tff(c_434, plain, (![A_18]: (k3_xboole_0(k1_tarski(A_18), k1_xboole_0)!=k1_tarski(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_433])).
% 7.19/2.72  tff(c_592, plain, (![A_18]: (k1_tarski(A_18)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_570, c_434])).
% 7.19/2.72  tff(c_690, plain, (![A_154]: (k4_xboole_0(A_154, A_154)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_570, c_226])).
% 7.19/2.72  tff(c_54, plain, (![A_21, B_22, C_23]: (r2_hidden(A_21, k4_xboole_0(B_22, k1_tarski(C_23))) | C_23=A_21 | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.19/2.72  tff(c_696, plain, (![A_21, C_23]: (r2_hidden(A_21, k1_xboole_0) | C_23=A_21 | ~r2_hidden(A_21, k1_tarski(C_23)))), inference(superposition, [status(thm), theory('equality')], [c_690, c_54])).
% 7.19/2.72  tff(c_768, plain, (![C_158, A_159]: (C_158=A_159 | ~r2_hidden(A_159, k1_tarski(C_158)))), inference(negUnitSimplification, [status(thm)], [c_161, c_696])).
% 7.19/2.72  tff(c_783, plain, (![C_158]: ('#skF_5'(k1_tarski(C_158))=C_158 | k1_tarski(C_158)=k1_xboole_0)), inference(resolution, [status(thm)], [c_74, c_768])).
% 7.19/2.72  tff(c_790, plain, (![C_158]: ('#skF_5'(k1_tarski(C_158))=C_158)), inference(negUnitSimplification, [status(thm)], [c_592, c_783])).
% 7.19/2.72  tff(c_805, plain, (![C_161, A_162, D_163, E_164]: (~r2_hidden(C_161, A_162) | k3_mcart_1(C_161, D_163, E_164)!='#skF_5'(A_162) | k1_xboole_0=A_162)), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.19/2.72  tff(c_817, plain, (![A_18, D_163, E_164]: (k3_mcart_1(A_18, D_163, E_164)!='#skF_5'(k1_tarski(A_18)) | k1_tarski(A_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_194, c_805])).
% 7.19/2.72  tff(c_836, plain, (![A_18, D_163, E_164]: (k3_mcart_1(A_18, D_163, E_164)!=A_18 | k1_tarski(A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_790, c_817])).
% 7.19/2.72  tff(c_837, plain, (![A_18, D_163, E_164]: (k3_mcart_1(A_18, D_163, E_164)!=A_18)), inference(negUnitSimplification, [status(thm)], [c_592, c_836])).
% 7.19/2.72  tff(c_92, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.19/2.72  tff(c_195, plain, (k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitLeft, [status(thm)], [c_92])).
% 7.19/2.72  tff(c_2067, plain, (![A_304, B_305, C_306, D_307]: (k7_mcart_1(A_304, B_305, C_306, D_307)=k2_mcart_1(D_307) | ~m1_subset_1(D_307, k3_zfmisc_1(A_304, B_305, C_306)) | k1_xboole_0=C_306 | k1_xboole_0=B_305 | k1_xboole_0=A_304)), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.19/2.72  tff(c_2073, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_94, c_2067])).
% 7.19/2.72  tff(c_2076, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_100, c_98, c_96, c_2073])).
% 7.19/2.72  tff(c_3845, plain, (![A_415, B_416, C_417, D_418]: (k3_mcart_1(k5_mcart_1(A_415, B_416, C_417, D_418), k6_mcart_1(A_415, B_416, C_417, D_418), k7_mcart_1(A_415, B_416, C_417, D_418))=D_418 | ~m1_subset_1(D_418, k3_zfmisc_1(A_415, B_416, C_417)) | k1_xboole_0=C_417 | k1_xboole_0=B_416 | k1_xboole_0=A_415)), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.19/2.72  tff(c_3914, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k2_mcart_1('#skF_9'))='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_2076, c_3845])).
% 7.19/2.72  tff(c_3925, plain, (k3_mcart_1('#skF_9', k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k2_mcart_1('#skF_9'))='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_195, c_3914])).
% 7.19/2.72  tff(c_3927, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_98, c_96, c_837, c_3925])).
% 7.19/2.72  tff(c_3928, plain, (k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_92])).
% 7.19/2.72  tff(c_3986, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitLeft, [status(thm)], [c_3928])).
% 7.19/2.72  tff(c_7063, plain, (![A_718, B_719, C_720, D_721]: (k3_mcart_1(k5_mcart_1(A_718, B_719, C_720, D_721), k6_mcart_1(A_718, B_719, C_720, D_721), k7_mcart_1(A_718, B_719, C_720, D_721))=D_721 | ~m1_subset_1(D_721, k3_zfmisc_1(A_718, B_719, C_720)) | k1_xboole_0=C_720 | k1_xboole_0=B_719 | k1_xboole_0=A_718)), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.19/2.72  tff(c_7132, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9')='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_3986, c_7063])).
% 7.19/2.72  tff(c_7140, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_7132])).
% 7.19/2.72  tff(c_7142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_98, c_96, c_4097, c_7140])).
% 7.19/2.72  tff(c_7143, plain, (k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_3928])).
% 7.19/2.72  tff(c_8965, plain, (![A_925, B_926, C_927, D_928]: (k7_mcart_1(A_925, B_926, C_927, D_928)=k2_mcart_1(D_928) | ~m1_subset_1(D_928, k3_zfmisc_1(A_925, B_926, C_927)) | k1_xboole_0=C_927 | k1_xboole_0=B_926 | k1_xboole_0=A_925)), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.19/2.72  tff(c_8971, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_94, c_8965])).
% 7.19/2.72  tff(c_8974, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_100, c_98, c_96, c_8971])).
% 7.19/2.72  tff(c_11228, plain, (![A_1059, B_1060, C_1061, D_1062]: (k3_mcart_1(k5_mcart_1(A_1059, B_1060, C_1061, D_1062), k6_mcart_1(A_1059, B_1060, C_1061, D_1062), k7_mcart_1(A_1059, B_1060, C_1061, D_1062))=D_1062 | ~m1_subset_1(D_1062, k3_zfmisc_1(A_1059, B_1060, C_1061)) | k1_xboole_0=C_1061 | k1_xboole_0=B_1060 | k1_xboole_0=A_1059)), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.19/2.72  tff(c_11297, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k2_mcart_1('#skF_9'))='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_8974, c_11228])).
% 7.19/2.72  tff(c_11308, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9', k2_mcart_1('#skF_9'))='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_7143, c_11297])).
% 7.19/2.72  tff(c_11310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_98, c_96, c_7674, c_11308])).
% 7.19/2.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.19/2.72  
% 7.19/2.72  Inference rules
% 7.19/2.72  ----------------------
% 7.19/2.72  #Ref     : 18
% 7.19/2.72  #Sup     : 2545
% 7.19/2.72  #Fact    : 6
% 7.19/2.72  #Define  : 0
% 7.19/2.72  #Split   : 2
% 7.19/2.72  #Chain   : 0
% 7.19/2.72  #Close   : 0
% 7.19/2.72  
% 7.19/2.72  Ordering : KBO
% 7.19/2.72  
% 7.19/2.72  Simplification rules
% 7.19/2.72  ----------------------
% 7.19/2.72  #Subsume      : 435
% 7.19/2.72  #Demod        : 972
% 7.19/2.72  #Tautology    : 783
% 7.19/2.72  #SimpNegUnit  : 376
% 7.19/2.72  #BackRed      : 13
% 7.19/2.72  
% 7.19/2.72  #Partial instantiations: 0
% 7.19/2.72  #Strategies tried      : 1
% 7.19/2.72  
% 7.19/2.72  Timing (in seconds)
% 7.19/2.72  ----------------------
% 7.19/2.72  Preprocessing        : 0.35
% 7.19/2.73  Parsing              : 0.17
% 7.19/2.73  CNF conversion       : 0.03
% 7.19/2.73  Main loop            : 1.53
% 7.19/2.73  Inferencing          : 0.49
% 7.19/2.73  Reduction            : 0.52
% 7.19/2.73  Demodulation         : 0.35
% 7.19/2.73  BG Simplification    : 0.07
% 7.19/2.73  Subsumption          : 0.34
% 7.19/2.73  Abstraction          : 0.10
% 7.19/2.73  MUC search           : 0.00
% 7.19/2.73  Cooper               : 0.00
% 7.19/2.73  Total                : 1.93
% 7.19/2.73  Index Insertion      : 0.00
% 7.19/2.73  Index Deletion       : 0.00
% 7.19/2.73  Index Matching       : 0.00
% 7.19/2.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
