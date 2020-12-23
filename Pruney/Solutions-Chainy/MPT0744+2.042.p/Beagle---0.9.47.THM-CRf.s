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
% DateTime   : Thu Dec  3 10:06:20 EST 2020

% Result     : Theorem 25.58s
% Output     : CNFRefutation 25.58s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 208 expanded)
%              Number of leaves         :   47 (  87 expanded)
%              Depth                    :   12
%              Number of atoms          :  160 ( 381 expanded)
%              Number of equality atoms :   38 (  65 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_5 > #skF_1 > #skF_3 > #skF_7 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_93,axiom,(
    ! [A,B,C,D,E,F,G,H,I] :
      ( I = k6_enumset1(A,B,C,D,E,F,G,H)
    <=> ! [J] :
          ( r2_hidden(J,I)
        <=> ~ ( J != A
              & J != B
              & J != C
              & J != D
              & J != E
              & J != F
              & J != G
              & J != H ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

tff(f_101,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_149,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_99,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_125,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_108,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(c_28,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    ! [A_12,B_13] : k1_enumset1(A_12,A_12,B_13) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_32,plain,(
    ! [A_14,B_15,C_16] : k2_enumset1(A_14,A_14,B_15,C_16) = k1_enumset1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    ! [A_17,B_18,C_19,D_20] : k3_enumset1(A_17,A_17,B_18,C_19,D_20) = k2_enumset1(A_17,B_18,C_19,D_20) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_36,plain,(
    ! [A_21,B_22,D_24,C_23,E_25] : k4_enumset1(A_21,A_21,B_22,C_23,D_24,E_25) = k3_enumset1(A_21,B_22,C_23,D_24,E_25) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    ! [B_27,D_29,A_26,E_30,F_31,C_28] : k5_enumset1(A_26,A_26,B_27,C_28,D_29,E_30,F_31) = k4_enumset1(A_26,B_27,C_28,D_29,E_30,F_31) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2128,plain,(
    ! [E_370,F_372,A_374,B_371,G_376,C_373,D_375] : k6_enumset1(A_374,A_374,B_371,C_373,D_375,E_370,F_372,G_376) = k5_enumset1(A_374,B_371,C_373,D_375,E_370,F_372,G_376) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_54,plain,(
    ! [G_49,H_50,F_48,D_46,C_45,A_43,J_54,B_44] : r2_hidden(J_54,k6_enumset1(A_43,B_44,C_45,D_46,J_54,F_48,G_49,H_50)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2185,plain,(
    ! [C_382,B_383,D_379,E_378,G_380,F_381,A_377] : r2_hidden(D_379,k5_enumset1(A_377,B_383,C_382,D_379,E_378,F_381,G_380)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2128,c_54])).

tff(c_2270,plain,(
    ! [A_386,F_387,B_385,E_389,D_384,C_388] : r2_hidden(C_388,k4_enumset1(A_386,B_385,C_388,D_384,E_389,F_387)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2185])).

tff(c_2355,plain,(
    ! [D_391,B_393,A_390,E_394,C_392] : r2_hidden(B_393,k3_enumset1(A_390,B_393,C_392,D_391,E_394)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2270])).

tff(c_2589,plain,(
    ! [A_398,B_399,C_400,D_401] : r2_hidden(A_398,k2_enumset1(A_398,B_399,C_400,D_401)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2355])).

tff(c_2674,plain,(
    ! [A_402,B_403,C_404] : r2_hidden(A_402,k1_enumset1(A_402,B_403,C_404)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2589])).

tff(c_2759,plain,(
    ! [A_405,B_406] : r2_hidden(A_405,k2_tarski(A_405,B_406)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2674])).

tff(c_2864,plain,(
    ! [A_407] : r2_hidden(A_407,k1_tarski(A_407)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2759])).

tff(c_104,plain,(
    ! [A_56] : k2_xboole_0(A_56,k1_tarski(A_56)) = k1_ordinal1(A_56) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_289,plain,(
    ! [D_105,B_106,A_107] :
      ( ~ r2_hidden(D_105,B_106)
      | r2_hidden(D_105,k2_xboole_0(A_107,B_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_298,plain,(
    ! [D_105,A_56] :
      ( ~ r2_hidden(D_105,k1_tarski(A_56))
      | r2_hidden(D_105,k1_ordinal1(A_56)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_289])).

tff(c_2994,plain,(
    ! [A_407] : r2_hidden(A_407,k1_ordinal1(A_407)) ),
    inference(resolution,[status(thm)],[c_2864,c_298])).

tff(c_124,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_122,plain,(
    v3_ordinal1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_126,plain,
    ( ~ r1_ordinal1('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_161,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_132,plain,
    ( r2_hidden('#skF_6',k1_ordinal1('#skF_7'))
    | r1_ordinal1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_189,plain,(
    r1_ordinal1('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_132])).

tff(c_114,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(A_61,B_62)
      | ~ r1_ordinal1(A_61,B_62)
      | ~ v3_ordinal1(B_62)
      | ~ v3_ordinal1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_134,plain,(
    ! [A_73] :
      ( v1_ordinal1(A_73)
      | ~ v3_ordinal1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_142,plain,(
    v1_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_124,c_134])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( r2_xboole_0(A_7,B_8)
      | B_8 = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_564,plain,(
    ! [A_147,B_148] :
      ( r2_hidden(A_147,B_148)
      | ~ r2_xboole_0(A_147,B_148)
      | ~ v3_ordinal1(B_148)
      | ~ v1_ordinal1(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_39426,plain,(
    ! [A_138244,B_138245] :
      ( r2_hidden(A_138244,B_138245)
      | ~ v3_ordinal1(B_138245)
      | ~ v1_ordinal1(A_138244)
      | B_138245 = A_138244
      | ~ r1_tarski(A_138244,B_138245) ) ),
    inference(resolution,[status(thm)],[c_20,c_564])).

tff(c_250,plain,(
    ! [D_96,A_97,B_98] :
      ( ~ r2_hidden(D_96,A_97)
      | r2_hidden(D_96,k2_xboole_0(A_97,B_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_261,plain,(
    ! [D_99,A_100] :
      ( ~ r2_hidden(D_99,A_100)
      | r2_hidden(D_99,k1_ordinal1(A_100)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_250])).

tff(c_269,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_261,c_161])).

tff(c_40034,plain,
    ( ~ v3_ordinal1('#skF_7')
    | ~ v1_ordinal1('#skF_6')
    | '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_39426,c_269])).

tff(c_40211,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_122,c_40034])).

tff(c_40217,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_40211])).

tff(c_40220,plain,
    ( ~ r1_ordinal1('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_114,c_40217])).

tff(c_40224,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_122,c_189,c_40220])).

tff(c_40225,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_40211])).

tff(c_40231,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40225,c_161])).

tff(c_40237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2994,c_40231])).

tff(c_40238,plain,(
    ~ r1_ordinal1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_141,plain,(
    v1_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_122,c_134])).

tff(c_40240,plain,(
    r1_ordinal1('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_40241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40238,c_40240])).

tff(c_40242,plain,(
    r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_40755,plain,(
    ! [D_139379,B_139380,A_139381] :
      ( r2_hidden(D_139379,B_139380)
      | r2_hidden(D_139379,A_139381)
      | ~ r2_hidden(D_139379,k2_xboole_0(A_139381,B_139380)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_41444,plain,(
    ! [D_139503,A_139504] :
      ( r2_hidden(D_139503,k1_tarski(A_139504))
      | r2_hidden(D_139503,A_139504)
      | ~ r2_hidden(D_139503,k1_ordinal1(A_139504)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_40755])).

tff(c_26,plain,(
    ! [A_9] : k2_xboole_0(A_9,A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_40291,plain,(
    ! [A_139299,B_139300] : k3_tarski(k2_tarski(A_139299,B_139300)) = k2_xboole_0(A_139299,B_139300) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_40303,plain,(
    ! [A_11] : k3_tarski(k1_tarski(A_11)) = k2_xboole_0(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_40291])).

tff(c_40318,plain,(
    ! [A_139304] : k3_tarski(k1_tarski(A_139304)) = A_139304 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_40303])).

tff(c_42,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,k3_tarski(B_40))
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_40324,plain,(
    ! [A_39,A_139304] :
      ( r1_tarski(A_39,A_139304)
      | ~ r2_hidden(A_39,k1_tarski(A_139304)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40318,c_42])).

tff(c_41556,plain,(
    ! [D_139505,A_139506] :
      ( r1_tarski(D_139505,A_139506)
      | r2_hidden(D_139505,A_139506)
      | ~ r2_hidden(D_139505,k1_ordinal1(A_139506)) ) ),
    inference(resolution,[status(thm)],[c_41444,c_40324])).

tff(c_41578,plain,
    ( r1_tarski('#skF_6','#skF_7')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_40242,c_41556])).

tff(c_41579,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_41578])).

tff(c_106,plain,(
    ! [B_60,A_57] :
      ( r1_tarski(B_60,A_57)
      | ~ r2_hidden(B_60,A_57)
      | ~ v1_ordinal1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_41582,plain,
    ( r1_tarski('#skF_6','#skF_7')
    | ~ v1_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_41579,c_106])).

tff(c_41588,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_41582])).

tff(c_112,plain,(
    ! [A_61,B_62] :
      ( r1_ordinal1(A_61,B_62)
      | ~ r1_tarski(A_61,B_62)
      | ~ v3_ordinal1(B_62)
      | ~ v3_ordinal1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_41618,plain,
    ( r1_ordinal1('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_41588,c_112])).

tff(c_41621,plain,(
    r1_ordinal1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_122,c_41618])).

tff(c_41623,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40238,c_41621])).

tff(c_41624,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_41578])).

tff(c_41628,plain,
    ( r1_ordinal1('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_41624,c_112])).

tff(c_41631,plain,(
    r1_ordinal1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_122,c_41628])).

tff(c_41633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40238,c_41631])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:41:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 25.58/16.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.58/16.09  
% 25.58/16.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.58/16.10  %$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_5 > #skF_1 > #skF_3 > #skF_7 > #skF_6 > #skF_2 > #skF_4
% 25.58/16.10  
% 25.58/16.10  %Foreground sorts:
% 25.58/16.10  
% 25.58/16.10  
% 25.58/16.10  %Background operators:
% 25.58/16.10  
% 25.58/16.10  
% 25.58/16.10  %Foreground operators:
% 25.58/16.10  tff('#skF_5', type, '#skF_5': $i > $i).
% 25.58/16.10  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 25.58/16.10  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 25.58/16.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 25.58/16.10  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 25.58/16.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 25.58/16.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 25.58/16.10  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 25.58/16.10  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 25.58/16.10  tff('#skF_7', type, '#skF_7': $i).
% 25.58/16.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 25.58/16.10  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 25.58/16.10  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 25.58/16.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 25.58/16.10  tff('#skF_6', type, '#skF_6': $i).
% 25.58/16.10  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 25.58/16.10  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 25.58/16.10  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 25.58/16.10  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 25.58/16.10  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 25.58/16.10  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 25.58/16.10  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 25.58/16.10  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 25.58/16.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 25.58/16.10  tff(k3_tarski, type, k3_tarski: $i > $i).
% 25.58/16.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 25.58/16.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 25.58/16.10  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 25.58/16.10  
% 25.58/16.11  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 25.58/16.11  tff(f_47, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 25.58/16.11  tff(f_49, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 25.58/16.11  tff(f_51, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 25.58/16.11  tff(f_53, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 25.58/16.11  tff(f_55, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 25.58/16.11  tff(f_57, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 25.58/16.11  tff(f_93, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 25.58/16.11  tff(f_101, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 25.58/16.11  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 25.58/16.11  tff(f_149, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 25.58/16.11  tff(f_116, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 25.58/16.11  tff(f_99, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 25.58/16.11  tff(f_41, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 25.58/16.11  tff(f_125, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_ordinal1)).
% 25.58/16.11  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 25.58/16.11  tff(f_63, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 25.58/16.11  tff(f_61, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 25.58/16.11  tff(f_108, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 25.58/16.11  tff(c_28, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 25.58/16.11  tff(c_30, plain, (![A_12, B_13]: (k1_enumset1(A_12, A_12, B_13)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 25.58/16.11  tff(c_32, plain, (![A_14, B_15, C_16]: (k2_enumset1(A_14, A_14, B_15, C_16)=k1_enumset1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 25.58/16.11  tff(c_34, plain, (![A_17, B_18, C_19, D_20]: (k3_enumset1(A_17, A_17, B_18, C_19, D_20)=k2_enumset1(A_17, B_18, C_19, D_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 25.58/16.11  tff(c_36, plain, (![A_21, B_22, D_24, C_23, E_25]: (k4_enumset1(A_21, A_21, B_22, C_23, D_24, E_25)=k3_enumset1(A_21, B_22, C_23, D_24, E_25))), inference(cnfTransformation, [status(thm)], [f_53])).
% 25.58/16.11  tff(c_38, plain, (![B_27, D_29, A_26, E_30, F_31, C_28]: (k5_enumset1(A_26, A_26, B_27, C_28, D_29, E_30, F_31)=k4_enumset1(A_26, B_27, C_28, D_29, E_30, F_31))), inference(cnfTransformation, [status(thm)], [f_55])).
% 25.58/16.11  tff(c_2128, plain, (![E_370, F_372, A_374, B_371, G_376, C_373, D_375]: (k6_enumset1(A_374, A_374, B_371, C_373, D_375, E_370, F_372, G_376)=k5_enumset1(A_374, B_371, C_373, D_375, E_370, F_372, G_376))), inference(cnfTransformation, [status(thm)], [f_57])).
% 25.58/16.11  tff(c_54, plain, (![G_49, H_50, F_48, D_46, C_45, A_43, J_54, B_44]: (r2_hidden(J_54, k6_enumset1(A_43, B_44, C_45, D_46, J_54, F_48, G_49, H_50)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 25.58/16.11  tff(c_2185, plain, (![C_382, B_383, D_379, E_378, G_380, F_381, A_377]: (r2_hidden(D_379, k5_enumset1(A_377, B_383, C_382, D_379, E_378, F_381, G_380)))), inference(superposition, [status(thm), theory('equality')], [c_2128, c_54])).
% 25.58/16.11  tff(c_2270, plain, (![A_386, F_387, B_385, E_389, D_384, C_388]: (r2_hidden(C_388, k4_enumset1(A_386, B_385, C_388, D_384, E_389, F_387)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_2185])).
% 25.58/16.11  tff(c_2355, plain, (![D_391, B_393, A_390, E_394, C_392]: (r2_hidden(B_393, k3_enumset1(A_390, B_393, C_392, D_391, E_394)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2270])).
% 25.58/16.11  tff(c_2589, plain, (![A_398, B_399, C_400, D_401]: (r2_hidden(A_398, k2_enumset1(A_398, B_399, C_400, D_401)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2355])).
% 25.58/16.11  tff(c_2674, plain, (![A_402, B_403, C_404]: (r2_hidden(A_402, k1_enumset1(A_402, B_403, C_404)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2589])).
% 25.58/16.11  tff(c_2759, plain, (![A_405, B_406]: (r2_hidden(A_405, k2_tarski(A_405, B_406)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2674])).
% 25.58/16.11  tff(c_2864, plain, (![A_407]: (r2_hidden(A_407, k1_tarski(A_407)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2759])).
% 25.58/16.11  tff(c_104, plain, (![A_56]: (k2_xboole_0(A_56, k1_tarski(A_56))=k1_ordinal1(A_56))), inference(cnfTransformation, [status(thm)], [f_101])).
% 25.58/16.11  tff(c_289, plain, (![D_105, B_106, A_107]: (~r2_hidden(D_105, B_106) | r2_hidden(D_105, k2_xboole_0(A_107, B_106)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 25.58/16.11  tff(c_298, plain, (![D_105, A_56]: (~r2_hidden(D_105, k1_tarski(A_56)) | r2_hidden(D_105, k1_ordinal1(A_56)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_289])).
% 25.58/16.11  tff(c_2994, plain, (![A_407]: (r2_hidden(A_407, k1_ordinal1(A_407)))), inference(resolution, [status(thm)], [c_2864, c_298])).
% 25.58/16.11  tff(c_124, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_149])).
% 25.58/16.11  tff(c_122, plain, (v3_ordinal1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_149])).
% 25.58/16.11  tff(c_126, plain, (~r1_ordinal1('#skF_6', '#skF_7') | ~r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 25.58/16.11  tff(c_161, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(splitLeft, [status(thm)], [c_126])).
% 25.58/16.11  tff(c_132, plain, (r2_hidden('#skF_6', k1_ordinal1('#skF_7')) | r1_ordinal1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_149])).
% 25.58/16.11  tff(c_189, plain, (r1_ordinal1('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_161, c_132])).
% 25.58/16.11  tff(c_114, plain, (![A_61, B_62]: (r1_tarski(A_61, B_62) | ~r1_ordinal1(A_61, B_62) | ~v3_ordinal1(B_62) | ~v3_ordinal1(A_61))), inference(cnfTransformation, [status(thm)], [f_116])).
% 25.58/16.11  tff(c_134, plain, (![A_73]: (v1_ordinal1(A_73) | ~v3_ordinal1(A_73))), inference(cnfTransformation, [status(thm)], [f_99])).
% 25.58/16.11  tff(c_142, plain, (v1_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_124, c_134])).
% 25.58/16.11  tff(c_20, plain, (![A_7, B_8]: (r2_xboole_0(A_7, B_8) | B_8=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 25.58/16.11  tff(c_564, plain, (![A_147, B_148]: (r2_hidden(A_147, B_148) | ~r2_xboole_0(A_147, B_148) | ~v3_ordinal1(B_148) | ~v1_ordinal1(A_147))), inference(cnfTransformation, [status(thm)], [f_125])).
% 25.58/16.11  tff(c_39426, plain, (![A_138244, B_138245]: (r2_hidden(A_138244, B_138245) | ~v3_ordinal1(B_138245) | ~v1_ordinal1(A_138244) | B_138245=A_138244 | ~r1_tarski(A_138244, B_138245))), inference(resolution, [status(thm)], [c_20, c_564])).
% 25.58/16.11  tff(c_250, plain, (![D_96, A_97, B_98]: (~r2_hidden(D_96, A_97) | r2_hidden(D_96, k2_xboole_0(A_97, B_98)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 25.58/16.11  tff(c_261, plain, (![D_99, A_100]: (~r2_hidden(D_99, A_100) | r2_hidden(D_99, k1_ordinal1(A_100)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_250])).
% 25.58/16.11  tff(c_269, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_261, c_161])).
% 25.58/16.11  tff(c_40034, plain, (~v3_ordinal1('#skF_7') | ~v1_ordinal1('#skF_6') | '#skF_7'='#skF_6' | ~r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_39426, c_269])).
% 25.58/16.11  tff(c_40211, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_122, c_40034])).
% 25.58/16.11  tff(c_40217, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_40211])).
% 25.58/16.11  tff(c_40220, plain, (~r1_ordinal1('#skF_6', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_114, c_40217])).
% 25.58/16.11  tff(c_40224, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_122, c_189, c_40220])).
% 25.58/16.11  tff(c_40225, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_40211])).
% 25.58/16.11  tff(c_40231, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_40225, c_161])).
% 25.58/16.11  tff(c_40237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2994, c_40231])).
% 25.58/16.11  tff(c_40238, plain, (~r1_ordinal1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_126])).
% 25.58/16.11  tff(c_141, plain, (v1_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_122, c_134])).
% 25.58/16.11  tff(c_40240, plain, (r1_ordinal1('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_132])).
% 25.58/16.11  tff(c_40241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40238, c_40240])).
% 25.58/16.11  tff(c_40242, plain, (r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(splitRight, [status(thm)], [c_132])).
% 25.58/16.11  tff(c_40755, plain, (![D_139379, B_139380, A_139381]: (r2_hidden(D_139379, B_139380) | r2_hidden(D_139379, A_139381) | ~r2_hidden(D_139379, k2_xboole_0(A_139381, B_139380)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 25.58/16.11  tff(c_41444, plain, (![D_139503, A_139504]: (r2_hidden(D_139503, k1_tarski(A_139504)) | r2_hidden(D_139503, A_139504) | ~r2_hidden(D_139503, k1_ordinal1(A_139504)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_40755])).
% 25.58/16.11  tff(c_26, plain, (![A_9]: (k2_xboole_0(A_9, A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_43])).
% 25.58/16.11  tff(c_40291, plain, (![A_139299, B_139300]: (k3_tarski(k2_tarski(A_139299, B_139300))=k2_xboole_0(A_139299, B_139300))), inference(cnfTransformation, [status(thm)], [f_63])).
% 25.58/16.11  tff(c_40303, plain, (![A_11]: (k3_tarski(k1_tarski(A_11))=k2_xboole_0(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_28, c_40291])).
% 25.58/16.11  tff(c_40318, plain, (![A_139304]: (k3_tarski(k1_tarski(A_139304))=A_139304)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_40303])).
% 25.58/16.11  tff(c_42, plain, (![A_39, B_40]: (r1_tarski(A_39, k3_tarski(B_40)) | ~r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_61])).
% 25.58/16.11  tff(c_40324, plain, (![A_39, A_139304]: (r1_tarski(A_39, A_139304) | ~r2_hidden(A_39, k1_tarski(A_139304)))), inference(superposition, [status(thm), theory('equality')], [c_40318, c_42])).
% 25.58/16.11  tff(c_41556, plain, (![D_139505, A_139506]: (r1_tarski(D_139505, A_139506) | r2_hidden(D_139505, A_139506) | ~r2_hidden(D_139505, k1_ordinal1(A_139506)))), inference(resolution, [status(thm)], [c_41444, c_40324])).
% 25.58/16.11  tff(c_41578, plain, (r1_tarski('#skF_6', '#skF_7') | r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_40242, c_41556])).
% 25.58/16.11  tff(c_41579, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_41578])).
% 25.58/16.11  tff(c_106, plain, (![B_60, A_57]: (r1_tarski(B_60, A_57) | ~r2_hidden(B_60, A_57) | ~v1_ordinal1(A_57))), inference(cnfTransformation, [status(thm)], [f_108])).
% 25.58/16.11  tff(c_41582, plain, (r1_tarski('#skF_6', '#skF_7') | ~v1_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_41579, c_106])).
% 25.58/16.11  tff(c_41588, plain, (r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_41582])).
% 25.58/16.11  tff(c_112, plain, (![A_61, B_62]: (r1_ordinal1(A_61, B_62) | ~r1_tarski(A_61, B_62) | ~v3_ordinal1(B_62) | ~v3_ordinal1(A_61))), inference(cnfTransformation, [status(thm)], [f_116])).
% 25.58/16.11  tff(c_41618, plain, (r1_ordinal1('#skF_6', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_41588, c_112])).
% 25.58/16.11  tff(c_41621, plain, (r1_ordinal1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_122, c_41618])).
% 25.58/16.11  tff(c_41623, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40238, c_41621])).
% 25.58/16.11  tff(c_41624, plain, (r1_tarski('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_41578])).
% 25.58/16.11  tff(c_41628, plain, (r1_ordinal1('#skF_6', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_41624, c_112])).
% 25.58/16.11  tff(c_41631, plain, (r1_ordinal1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_122, c_41628])).
% 25.58/16.11  tff(c_41633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40238, c_41631])).
% 25.58/16.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.58/16.11  
% 25.58/16.11  Inference rules
% 25.58/16.11  ----------------------
% 25.58/16.11  #Ref     : 0
% 25.58/16.11  #Sup     : 7653
% 25.58/16.11  #Fact    : 454
% 25.58/16.11  #Define  : 0
% 25.58/16.11  #Split   : 7
% 25.58/16.11  #Chain   : 0
% 25.58/16.11  #Close   : 0
% 25.58/16.11  
% 25.58/16.11  Ordering : KBO
% 25.58/16.11  
% 25.58/16.11  Simplification rules
% 25.58/16.11  ----------------------
% 25.58/16.11  #Subsume      : 4312
% 25.58/16.11  #Demod        : 140
% 25.58/16.12  #Tautology    : 663
% 25.58/16.12  #SimpNegUnit  : 24
% 25.58/16.12  #BackRed      : 8
% 25.58/16.12  
% 25.58/16.12  #Partial instantiations: 38304
% 25.58/16.12  #Strategies tried      : 1
% 25.58/16.12  
% 25.58/16.12  Timing (in seconds)
% 25.58/16.12  ----------------------
% 25.58/16.12  Preprocessing        : 0.38
% 25.58/16.12  Parsing              : 0.18
% 25.58/16.12  CNF conversion       : 0.03
% 25.58/16.12  Main loop            : 14.96
% 25.58/16.12  Inferencing          : 5.37
% 25.58/16.12  Reduction            : 1.84
% 25.58/16.12  Demodulation         : 1.39
% 25.58/16.12  BG Simplification    : 0.32
% 25.58/16.12  Subsumption          : 7.17
% 25.58/16.12  Abstraction          : 1.17
% 25.58/16.12  MUC search           : 0.00
% 25.58/16.12  Cooper               : 0.00
% 25.58/16.12  Total                : 15.39
% 25.58/16.12  Index Insertion      : 0.00
% 25.58/16.12  Index Deletion       : 0.00
% 25.58/16.12  Index Matching       : 0.00
% 25.58/16.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
