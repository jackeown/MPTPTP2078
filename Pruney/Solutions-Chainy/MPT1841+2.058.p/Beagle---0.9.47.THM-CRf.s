%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:35 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 4.15s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 177 expanded)
%              Number of leaves         :   46 (  77 expanded)
%              Depth                    :   12
%              Number of atoms          :  139 ( 315 expanded)
%              Number of equality atoms :   32 (  44 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_1 > #skF_7 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_161,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_95,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_135,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_128,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_48,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_88,axiom,(
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

tff(f_149,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_93,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(c_112,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_90,plain,(
    ! [A_54] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_54)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_268,plain,(
    ! [C_116,B_117,A_118] :
      ( ~ v1_xboole_0(C_116)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(C_116))
      | ~ r2_hidden(A_118,B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_274,plain,(
    ! [A_54,A_118] :
      ( ~ v1_xboole_0(A_54)
      | ~ r2_hidden(A_118,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_90,c_268])).

tff(c_276,plain,(
    ! [A_119] : ~ r2_hidden(A_119,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_274])).

tff(c_286,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_276])).

tff(c_110,plain,(
    m1_subset_1('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_336,plain,(
    ! [A_126,B_127] :
      ( k6_domain_1(A_126,B_127) = k1_tarski(B_127)
      | ~ m1_subset_1(B_127,A_126)
      | v1_xboole_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_342,plain,
    ( k6_domain_1('#skF_6','#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_110,c_336])).

tff(c_346,plain,(
    k6_domain_1('#skF_6','#skF_7') = k1_tarski('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_342])).

tff(c_539,plain,(
    ! [A_202,B_203] :
      ( m1_subset_1(k6_domain_1(A_202,B_203),k1_zfmisc_1(A_202))
      | ~ m1_subset_1(B_203,A_202)
      | v1_xboole_0(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_555,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1('#skF_7','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_539])).

tff(c_563,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1('#skF_6'))
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_555])).

tff(c_564,plain,(
    m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_563])).

tff(c_94,plain,(
    ! [A_58,C_60,B_59] :
      ( m1_subset_1(A_58,C_60)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(C_60))
      | ~ r2_hidden(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_581,plain,(
    ! [A_204] :
      ( m1_subset_1(A_204,'#skF_6')
      | ~ r2_hidden(A_204,k1_tarski('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_564,c_94])).

tff(c_596,plain,
    ( m1_subset_1('#skF_1'(k1_tarski('#skF_7')),'#skF_6')
    | v1_xboole_0(k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_4,c_581])).

tff(c_597,plain,(
    v1_xboole_0(k1_tarski('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_596])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_293,plain,(
    ! [B_120] : r1_tarski(k1_xboole_0,B_120) ),
    inference(resolution,[status(thm)],[c_10,c_276])).

tff(c_148,plain,(
    ! [A_87,B_88] :
      ( r2_hidden('#skF_2'(A_87,B_88),A_87)
      | r1_tarski(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_156,plain,(
    ! [A_87,B_88] :
      ( ~ v1_xboole_0(A_87)
      | r1_tarski(A_87,B_88) ) ),
    inference(resolution,[status(thm)],[c_148,c_2])).

tff(c_170,plain,(
    ! [B_93,A_94] :
      ( B_93 = A_94
      | ~ r1_tarski(B_93,A_94)
      | ~ r1_tarski(A_94,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_175,plain,(
    ! [B_88,A_87] :
      ( B_88 = A_87
      | ~ r1_tarski(B_88,A_87)
      | ~ v1_xboole_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_156,c_170])).

tff(c_309,plain,(
    ! [B_120] :
      ( k1_xboole_0 = B_120
      | ~ v1_xboole_0(B_120) ) ),
    inference(resolution,[status(thm)],[c_293,c_175])).

tff(c_603,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_597,c_309])).

tff(c_18,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20,plain,(
    ! [A_13,B_14] : k1_enumset1(A_13,A_13,B_14) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_15,B_16,C_17] : k2_enumset1(A_15,A_15,B_16,C_17) = k1_enumset1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    ! [A_18,B_19,C_20,D_21] : k3_enumset1(A_18,A_18,B_19,C_20,D_21) = k2_enumset1(A_18,B_19,C_20,D_21) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    ! [E_26,A_22,B_23,D_25,C_24] : k4_enumset1(A_22,A_22,B_23,C_24,D_25,E_26) = k3_enumset1(A_22,B_23,C_24,D_25,E_26) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] : k5_enumset1(A_27,A_27,B_28,C_29,D_30,E_31,F_32) = k4_enumset1(A_27,B_28,C_29,D_30,E_31,F_32) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_795,plain,(
    ! [F_308,E_306,C_307,B_311,D_309,G_310,A_305] : k6_enumset1(A_305,A_305,B_311,C_307,D_309,E_306,F_308,G_310) = k5_enumset1(A_305,B_311,C_307,D_309,E_306,F_308,G_310) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_372,plain,(
    ! [G_129,E_130,C_133,D_131,B_136,F_132,J_135,H_134] : r2_hidden(J_135,k6_enumset1(J_135,B_136,C_133,D_131,E_130,F_132,G_129,H_134)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_383,plain,(
    ! [G_129,E_130,C_133,D_131,B_136,F_132,J_135,H_134] : ~ v1_xboole_0(k6_enumset1(J_135,B_136,C_133,D_131,E_130,F_132,G_129,H_134)) ),
    inference(resolution,[status(thm)],[c_372,c_2])).

tff(c_854,plain,(
    ! [A_315,E_317,D_316,F_312,B_318,G_313,C_314] : ~ v1_xboole_0(k5_enumset1(A_315,B_318,C_314,D_316,E_317,F_312,G_313)) ),
    inference(superposition,[status(thm),theory(equality)],[c_795,c_383])).

tff(c_857,plain,(
    ! [D_321,C_320,F_319,B_323,E_322,A_324] : ~ v1_xboole_0(k4_enumset1(A_324,B_323,C_320,D_321,E_322,F_319)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_854])).

tff(c_860,plain,(
    ! [D_328,A_325,C_326,B_329,E_327] : ~ v1_xboole_0(k3_enumset1(A_325,B_329,C_326,D_328,E_327)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_857])).

tff(c_863,plain,(
    ! [A_330,B_331,C_332,D_333] : ~ v1_xboole_0(k2_enumset1(A_330,B_331,C_332,D_333)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_860])).

tff(c_866,plain,(
    ! [A_334,B_335,C_336] : ~ v1_xboole_0(k1_enumset1(A_334,B_335,C_336)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_863])).

tff(c_935,plain,(
    ! [A_346,B_347] : ~ v1_xboole_0(k2_tarski(A_346,B_347)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_866])).

tff(c_938,plain,(
    ! [A_348] : ~ v1_xboole_0(k1_tarski(A_348)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_935])).

tff(c_940,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_938])).

tff(c_943,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_940])).

tff(c_945,plain,(
    ~ v1_xboole_0(k1_tarski('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_596])).

tff(c_106,plain,(
    v1_zfmisc_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_108,plain,(
    v1_subset_1(k6_domain_1('#skF_6','#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_347,plain,(
    v1_subset_1(k1_tarski('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_108])).

tff(c_1572,plain,(
    ! [B_473,A_474] :
      ( ~ v1_subset_1(B_473,A_474)
      | v1_xboole_0(B_473)
      | ~ m1_subset_1(B_473,k1_zfmisc_1(A_474))
      | ~ v1_zfmisc_1(A_474)
      | v1_xboole_0(A_474) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1581,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_7'),'#skF_6')
    | v1_xboole_0(k1_tarski('#skF_7'))
    | ~ v1_zfmisc_1('#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_564,c_1572])).

tff(c_1597,plain,
    ( v1_xboole_0(k1_tarski('#skF_7'))
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_347,c_1581])).

tff(c_1599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_945,c_1597])).

tff(c_1600,plain,(
    ! [A_54] : ~ v1_xboole_0(A_54) ),
    inference(splitRight,[status(thm)],[c_274])).

tff(c_86,plain,(
    ! [A_52] : v1_xboole_0('#skF_5'(A_52)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1604,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1600,c_86])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:13:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.75/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.64  
% 4.15/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.64  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_1 > #skF_7 > #skF_6 > #skF_4 > #skF_2
% 4.15/1.64  
% 4.15/1.64  %Foreground sorts:
% 4.15/1.64  
% 4.15/1.64  
% 4.15/1.64  %Background operators:
% 4.15/1.64  
% 4.15/1.64  
% 4.15/1.64  %Foreground operators:
% 4.15/1.64  tff('#skF_5', type, '#skF_5': $i > $i).
% 4.15/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.15/1.64  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.15/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.15/1.64  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.15/1.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.15/1.64  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.15/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.15/1.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.15/1.64  tff('#skF_7', type, '#skF_7': $i).
% 4.15/1.64  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.15/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.15/1.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.15/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.15/1.64  tff('#skF_6', type, '#skF_6': $i).
% 4.15/1.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.15/1.64  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.15/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.15/1.64  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.15/1.64  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.15/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.15/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.15/1.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.15/1.64  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.15/1.64  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.15/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.15/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.15/1.64  
% 4.15/1.66  tff(f_161, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 4.15/1.66  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.15/1.66  tff(f_95, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.15/1.66  tff(f_116, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.15/1.66  tff(f_135, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.15/1.66  tff(f_128, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 4.15/1.66  tff(f_109, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.15/1.66  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.15/1.66  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.15/1.66  tff(f_46, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.15/1.66  tff(f_48, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.15/1.66  tff(f_50, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 4.15/1.66  tff(f_52, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 4.15/1.66  tff(f_54, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 4.15/1.66  tff(f_56, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 4.15/1.66  tff(f_58, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 4.15/1.66  tff(f_88, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 4.15/1.66  tff(f_149, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 4.15/1.66  tff(f_93, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 4.15/1.66  tff(c_112, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.15/1.66  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.15/1.66  tff(c_90, plain, (![A_54]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.15/1.66  tff(c_268, plain, (![C_116, B_117, A_118]: (~v1_xboole_0(C_116) | ~m1_subset_1(B_117, k1_zfmisc_1(C_116)) | ~r2_hidden(A_118, B_117))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.15/1.66  tff(c_274, plain, (![A_54, A_118]: (~v1_xboole_0(A_54) | ~r2_hidden(A_118, k1_xboole_0))), inference(resolution, [status(thm)], [c_90, c_268])).
% 4.15/1.66  tff(c_276, plain, (![A_119]: (~r2_hidden(A_119, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_274])).
% 4.15/1.66  tff(c_286, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_276])).
% 4.15/1.66  tff(c_110, plain, (m1_subset_1('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.15/1.66  tff(c_336, plain, (![A_126, B_127]: (k6_domain_1(A_126, B_127)=k1_tarski(B_127) | ~m1_subset_1(B_127, A_126) | v1_xboole_0(A_126))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.15/1.66  tff(c_342, plain, (k6_domain_1('#skF_6', '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_110, c_336])).
% 4.15/1.66  tff(c_346, plain, (k6_domain_1('#skF_6', '#skF_7')=k1_tarski('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_112, c_342])).
% 4.15/1.66  tff(c_539, plain, (![A_202, B_203]: (m1_subset_1(k6_domain_1(A_202, B_203), k1_zfmisc_1(A_202)) | ~m1_subset_1(B_203, A_202) | v1_xboole_0(A_202))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.15/1.66  tff(c_555, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_7', '#skF_6') | v1_xboole_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_346, c_539])).
% 4.15/1.66  tff(c_563, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1('#skF_6')) | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_555])).
% 4.15/1.66  tff(c_564, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_112, c_563])).
% 4.15/1.66  tff(c_94, plain, (![A_58, C_60, B_59]: (m1_subset_1(A_58, C_60) | ~m1_subset_1(B_59, k1_zfmisc_1(C_60)) | ~r2_hidden(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.15/1.66  tff(c_581, plain, (![A_204]: (m1_subset_1(A_204, '#skF_6') | ~r2_hidden(A_204, k1_tarski('#skF_7')))), inference(resolution, [status(thm)], [c_564, c_94])).
% 4.15/1.66  tff(c_596, plain, (m1_subset_1('#skF_1'(k1_tarski('#skF_7')), '#skF_6') | v1_xboole_0(k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_4, c_581])).
% 4.15/1.66  tff(c_597, plain, (v1_xboole_0(k1_tarski('#skF_7'))), inference(splitLeft, [status(thm)], [c_596])).
% 4.15/1.66  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.15/1.66  tff(c_293, plain, (![B_120]: (r1_tarski(k1_xboole_0, B_120))), inference(resolution, [status(thm)], [c_10, c_276])).
% 4.15/1.66  tff(c_148, plain, (![A_87, B_88]: (r2_hidden('#skF_2'(A_87, B_88), A_87) | r1_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.15/1.66  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.15/1.66  tff(c_156, plain, (![A_87, B_88]: (~v1_xboole_0(A_87) | r1_tarski(A_87, B_88))), inference(resolution, [status(thm)], [c_148, c_2])).
% 4.15/1.66  tff(c_170, plain, (![B_93, A_94]: (B_93=A_94 | ~r1_tarski(B_93, A_94) | ~r1_tarski(A_94, B_93))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.15/1.66  tff(c_175, plain, (![B_88, A_87]: (B_88=A_87 | ~r1_tarski(B_88, A_87) | ~v1_xboole_0(A_87))), inference(resolution, [status(thm)], [c_156, c_170])).
% 4.15/1.66  tff(c_309, plain, (![B_120]: (k1_xboole_0=B_120 | ~v1_xboole_0(B_120))), inference(resolution, [status(thm)], [c_293, c_175])).
% 4.15/1.66  tff(c_603, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_597, c_309])).
% 4.15/1.66  tff(c_18, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.15/1.66  tff(c_20, plain, (![A_13, B_14]: (k1_enumset1(A_13, A_13, B_14)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.15/1.66  tff(c_22, plain, (![A_15, B_16, C_17]: (k2_enumset1(A_15, A_15, B_16, C_17)=k1_enumset1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.15/1.66  tff(c_24, plain, (![A_18, B_19, C_20, D_21]: (k3_enumset1(A_18, A_18, B_19, C_20, D_21)=k2_enumset1(A_18, B_19, C_20, D_21))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.15/1.66  tff(c_26, plain, (![E_26, A_22, B_23, D_25, C_24]: (k4_enumset1(A_22, A_22, B_23, C_24, D_25, E_26)=k3_enumset1(A_22, B_23, C_24, D_25, E_26))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.15/1.66  tff(c_28, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (k5_enumset1(A_27, A_27, B_28, C_29, D_30, E_31, F_32)=k4_enumset1(A_27, B_28, C_29, D_30, E_31, F_32))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.15/1.66  tff(c_795, plain, (![F_308, E_306, C_307, B_311, D_309, G_310, A_305]: (k6_enumset1(A_305, A_305, B_311, C_307, D_309, E_306, F_308, G_310)=k5_enumset1(A_305, B_311, C_307, D_309, E_306, F_308, G_310))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.15/1.66  tff(c_372, plain, (![G_129, E_130, C_133, D_131, B_136, F_132, J_135, H_134]: (r2_hidden(J_135, k6_enumset1(J_135, B_136, C_133, D_131, E_130, F_132, G_129, H_134)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.15/1.66  tff(c_383, plain, (![G_129, E_130, C_133, D_131, B_136, F_132, J_135, H_134]: (~v1_xboole_0(k6_enumset1(J_135, B_136, C_133, D_131, E_130, F_132, G_129, H_134)))), inference(resolution, [status(thm)], [c_372, c_2])).
% 4.15/1.66  tff(c_854, plain, (![A_315, E_317, D_316, F_312, B_318, G_313, C_314]: (~v1_xboole_0(k5_enumset1(A_315, B_318, C_314, D_316, E_317, F_312, G_313)))), inference(superposition, [status(thm), theory('equality')], [c_795, c_383])).
% 4.15/1.66  tff(c_857, plain, (![D_321, C_320, F_319, B_323, E_322, A_324]: (~v1_xboole_0(k4_enumset1(A_324, B_323, C_320, D_321, E_322, F_319)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_854])).
% 4.15/1.66  tff(c_860, plain, (![D_328, A_325, C_326, B_329, E_327]: (~v1_xboole_0(k3_enumset1(A_325, B_329, C_326, D_328, E_327)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_857])).
% 4.15/1.66  tff(c_863, plain, (![A_330, B_331, C_332, D_333]: (~v1_xboole_0(k2_enumset1(A_330, B_331, C_332, D_333)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_860])).
% 4.15/1.66  tff(c_866, plain, (![A_334, B_335, C_336]: (~v1_xboole_0(k1_enumset1(A_334, B_335, C_336)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_863])).
% 4.15/1.66  tff(c_935, plain, (![A_346, B_347]: (~v1_xboole_0(k2_tarski(A_346, B_347)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_866])).
% 4.15/1.66  tff(c_938, plain, (![A_348]: (~v1_xboole_0(k1_tarski(A_348)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_935])).
% 4.15/1.66  tff(c_940, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_603, c_938])).
% 4.15/1.66  tff(c_943, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_286, c_940])).
% 4.15/1.66  tff(c_945, plain, (~v1_xboole_0(k1_tarski('#skF_7'))), inference(splitRight, [status(thm)], [c_596])).
% 4.15/1.66  tff(c_106, plain, (v1_zfmisc_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.15/1.66  tff(c_108, plain, (v1_subset_1(k6_domain_1('#skF_6', '#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.15/1.66  tff(c_347, plain, (v1_subset_1(k1_tarski('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_346, c_108])).
% 4.15/1.66  tff(c_1572, plain, (![B_473, A_474]: (~v1_subset_1(B_473, A_474) | v1_xboole_0(B_473) | ~m1_subset_1(B_473, k1_zfmisc_1(A_474)) | ~v1_zfmisc_1(A_474) | v1_xboole_0(A_474))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.15/1.66  tff(c_1581, plain, (~v1_subset_1(k1_tarski('#skF_7'), '#skF_6') | v1_xboole_0(k1_tarski('#skF_7')) | ~v1_zfmisc_1('#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_564, c_1572])).
% 4.15/1.66  tff(c_1597, plain, (v1_xboole_0(k1_tarski('#skF_7')) | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_347, c_1581])).
% 4.15/1.66  tff(c_1599, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_945, c_1597])).
% 4.15/1.66  tff(c_1600, plain, (![A_54]: (~v1_xboole_0(A_54))), inference(splitRight, [status(thm)], [c_274])).
% 4.15/1.66  tff(c_86, plain, (![A_52]: (v1_xboole_0('#skF_5'(A_52)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.15/1.66  tff(c_1604, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1600, c_86])).
% 4.15/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.66  
% 4.15/1.66  Inference rules
% 4.15/1.66  ----------------------
% 4.15/1.66  #Ref     : 0
% 4.15/1.66  #Sup     : 331
% 4.15/1.66  #Fact    : 0
% 4.15/1.66  #Define  : 0
% 4.15/1.66  #Split   : 4
% 4.15/1.66  #Chain   : 0
% 4.15/1.66  #Close   : 0
% 4.15/1.66  
% 4.15/1.66  Ordering : KBO
% 4.15/1.66  
% 4.15/1.66  Simplification rules
% 4.15/1.66  ----------------------
% 4.15/1.66  #Subsume      : 82
% 4.15/1.66  #Demod        : 98
% 4.15/1.66  #Tautology    : 124
% 4.15/1.66  #SimpNegUnit  : 30
% 4.15/1.66  #BackRed      : 20
% 4.15/1.66  
% 4.15/1.66  #Partial instantiations: 0
% 4.15/1.66  #Strategies tried      : 1
% 4.15/1.66  
% 4.15/1.66  Timing (in seconds)
% 4.15/1.66  ----------------------
% 4.15/1.66  Preprocessing        : 0.37
% 4.15/1.66  Parsing              : 0.17
% 4.15/1.66  CNF conversion       : 0.03
% 4.15/1.66  Main loop            : 0.50
% 4.15/1.66  Inferencing          : 0.16
% 4.15/1.66  Reduction            : 0.15
% 4.15/1.66  Demodulation         : 0.10
% 4.15/1.66  BG Simplification    : 0.03
% 4.15/1.66  Subsumption          : 0.13
% 4.15/1.66  Abstraction          : 0.04
% 4.15/1.66  MUC search           : 0.00
% 4.15/1.66  Cooper               : 0.00
% 4.15/1.66  Total                : 0.91
% 4.15/1.66  Index Insertion      : 0.00
% 4.15/1.66  Index Deletion       : 0.00
% 4.15/1.66  Index Matching       : 0.00
% 4.15/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
