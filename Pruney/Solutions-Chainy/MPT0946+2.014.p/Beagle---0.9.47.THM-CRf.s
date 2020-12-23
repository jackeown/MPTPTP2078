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
% DateTime   : Thu Dec  3 10:10:33 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 371 expanded)
%              Number of leaves         :   33 ( 144 expanded)
%              Depth                    :   12
%              Number of atoms          :  236 ( 999 expanded)
%              Number of equality atoms :   17 ( 120 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_wellord1 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_103,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_120,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_101,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_112,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
           => A = k1_wellord1(k1_wellord2(B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r4_wellord1(A,k2_wellord1(A,k1_wellord1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

tff(f_48,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_116,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v2_wellord1(B)
       => k3_relat_1(k2_wellord1(B,k1_wellord1(B,A))) = k1_wellord1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_wellord1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k3_relat_1(k2_wellord1(C,B)))
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_wellord1)).

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_52,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_56,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_58,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ r1_ordinal1(A_3,B_4)
      | ~ v3_ordinal1(B_4)
      | ~ v3_ordinal1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_44,plain,(
    ! [A_29] : v1_relat_1(k1_wellord2(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_54,plain,(
    r4_wellord1(k1_wellord2('#skF_3'),k1_wellord2('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_95,plain,(
    ! [B_47,A_48] :
      ( r4_wellord1(B_47,A_48)
      | ~ r4_wellord1(A_48,B_47)
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_97,plain,
    ( r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_3'))
    | ~ v1_relat_1(k1_wellord2('#skF_4'))
    | ~ v1_relat_1(k1_wellord2('#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_95])).

tff(c_100,plain,(
    r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_97])).

tff(c_50,plain,(
    ! [B_35,A_34] :
      ( k2_wellord1(k1_wellord2(B_35),A_34) = k1_wellord2(A_34)
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_38,plain,(
    ! [A_21] :
      ( k3_relat_1(k1_wellord2(A_21)) = A_21
      | ~ v1_relat_1(k1_wellord2(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_64,plain,(
    ! [A_21] : k3_relat_1(k1_wellord2(A_21)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38])).

tff(c_46,plain,(
    ! [B_32,A_30] :
      ( k1_wellord1(k1_wellord2(B_32),A_30) = A_30
      | ~ r2_hidden(A_30,B_32)
      | ~ v3_ordinal1(B_32)
      | ~ v3_ordinal1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_318,plain,(
    ! [A_80,B_81] :
      ( ~ r4_wellord1(A_80,k2_wellord1(A_80,k1_wellord1(A_80,B_81)))
      | ~ r2_hidden(B_81,k3_relat_1(A_80))
      | ~ v2_wellord1(A_80)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_321,plain,(
    ! [B_32,A_30] :
      ( ~ r4_wellord1(k1_wellord2(B_32),k2_wellord1(k1_wellord2(B_32),A_30))
      | ~ r2_hidden(A_30,k3_relat_1(k1_wellord2(B_32)))
      | ~ v2_wellord1(k1_wellord2(B_32))
      | ~ v1_relat_1(k1_wellord2(B_32))
      | ~ r2_hidden(A_30,B_32)
      | ~ v3_ordinal1(B_32)
      | ~ v3_ordinal1(A_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_318])).

tff(c_568,plain,(
    ! [B_110,A_111] :
      ( ~ r4_wellord1(k1_wellord2(B_110),k2_wellord1(k1_wellord2(B_110),A_111))
      | ~ v2_wellord1(k1_wellord2(B_110))
      | ~ r2_hidden(A_111,B_110)
      | ~ v3_ordinal1(B_110)
      | ~ v3_ordinal1(A_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_64,c_321])).

tff(c_695,plain,(
    ! [B_124,A_125] :
      ( ~ r4_wellord1(k1_wellord2(B_124),k1_wellord2(A_125))
      | ~ v2_wellord1(k1_wellord2(B_124))
      | ~ r2_hidden(A_125,B_124)
      | ~ v3_ordinal1(B_124)
      | ~ v3_ordinal1(A_125)
      | ~ r1_tarski(A_125,B_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_568])).

tff(c_698,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_695])).

tff(c_704,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_698])).

tff(c_708,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_704])).

tff(c_871,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_708])).

tff(c_874,plain,(
    ~ r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_871])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( r2_hidden(B_7,A_5)
      | r1_ordinal1(A_5,B_7)
      | ~ v3_ordinal1(B_7)
      | ~ v3_ordinal1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_48,plain,(
    ! [A_33] :
      ( v2_wellord1(k1_wellord2(A_33))
      | ~ v3_ordinal1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_701,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_695])).

tff(c_707,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_701])).

tff(c_709,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_707])).

tff(c_718,plain,
    ( ~ r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_709])).

tff(c_721,plain,(
    ~ r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_718])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_175,plain,(
    ! [B_71,A_72] :
      ( k3_relat_1(k2_wellord1(B_71,k1_wellord1(B_71,A_72))) = k1_wellord1(B_71,A_72)
      | ~ v2_wellord1(B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [A_10,C_12,B_11] :
      ( r2_hidden(A_10,k3_relat_1(C_12))
      | ~ r2_hidden(A_10,k3_relat_1(k2_wellord1(C_12,B_11)))
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_347,plain,(
    ! [A_88,B_89,A_90] :
      ( r2_hidden(A_88,k3_relat_1(B_89))
      | ~ r2_hidden(A_88,k1_wellord1(B_89,A_90))
      | ~ v1_relat_1(B_89)
      | ~ v2_wellord1(B_89)
      | ~ v1_relat_1(B_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_18])).

tff(c_350,plain,(
    ! [A_88,B_32,A_30] :
      ( r2_hidden(A_88,k3_relat_1(k1_wellord2(B_32)))
      | ~ r2_hidden(A_88,A_30)
      | ~ v1_relat_1(k1_wellord2(B_32))
      | ~ v2_wellord1(k1_wellord2(B_32))
      | ~ v1_relat_1(k1_wellord2(B_32))
      | ~ r2_hidden(A_30,B_32)
      | ~ v3_ordinal1(B_32)
      | ~ v3_ordinal1(A_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_347])).

tff(c_427,plain,(
    ! [A_100,B_101,A_102] :
      ( r2_hidden(A_100,B_101)
      | ~ r2_hidden(A_100,A_102)
      | ~ v2_wellord1(k1_wellord2(B_101))
      | ~ r2_hidden(A_102,B_101)
      | ~ v3_ordinal1(B_101)
      | ~ v3_ordinal1(A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_64,c_350])).

tff(c_722,plain,(
    ! [B_126,B_127,A_128] :
      ( r2_hidden(B_126,B_127)
      | ~ v2_wellord1(k1_wellord2(B_127))
      | ~ r2_hidden(A_128,B_127)
      | ~ v3_ordinal1(B_127)
      | r1_ordinal1(A_128,B_126)
      | ~ v3_ordinal1(B_126)
      | ~ v3_ordinal1(A_128) ) ),
    inference(resolution,[status(thm)],[c_12,c_427])).

tff(c_746,plain,(
    ! [B_132,A_133,A_134] :
      ( r2_hidden(B_132,A_133)
      | ~ r2_hidden(A_134,A_133)
      | r1_ordinal1(A_134,B_132)
      | ~ v3_ordinal1(B_132)
      | ~ v3_ordinal1(A_134)
      | ~ v3_ordinal1(A_133) ) ),
    inference(resolution,[status(thm)],[c_48,c_722])).

tff(c_770,plain,(
    ! [B_135,A_136,B_137] :
      ( r2_hidden(B_135,A_136)
      | r1_ordinal1(B_137,B_135)
      | ~ v3_ordinal1(B_135)
      | r1_ordinal1(A_136,B_137)
      | ~ v3_ordinal1(B_137)
      | ~ v3_ordinal1(A_136) ) ),
    inference(resolution,[status(thm)],[c_12,c_746])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( ~ r1_tarski(B_9,A_8)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_824,plain,(
    ! [A_138,B_139,B_140] :
      ( ~ r1_tarski(A_138,B_139)
      | r1_ordinal1(B_140,B_139)
      | ~ v3_ordinal1(B_139)
      | r1_ordinal1(A_138,B_140)
      | ~ v3_ordinal1(B_140)
      | ~ v3_ordinal1(A_138) ) ),
    inference(resolution,[status(thm)],[c_770,c_14])).

tff(c_845,plain,(
    ! [B_141,B_142] :
      ( r1_ordinal1(B_141,B_142)
      | r1_ordinal1(B_142,B_141)
      | ~ v3_ordinal1(B_141)
      | ~ v3_ordinal1(B_142) ) ),
    inference(resolution,[status(thm)],[c_6,c_824])).

tff(c_712,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_708])).

tff(c_715,plain,(
    ~ r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_712])).

tff(c_849,plain,
    ( r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_845,c_715])).

tff(c_864,plain,(
    r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_849])).

tff(c_866,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_721,c_864])).

tff(c_867,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ v2_wellord1(k1_wellord2('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_707])).

tff(c_928,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_867])).

tff(c_931,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_928])).

tff(c_935,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_931])).

tff(c_936,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_867])).

tff(c_940,plain,
    ( r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_936])).

tff(c_943,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_940])).

tff(c_945,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_874,c_943])).

tff(c_947,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_704])).

tff(c_112,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,B_53)
      | ~ r1_ordinal1(A_52,B_53)
      | ~ v3_ordinal1(B_53)
      | ~ v3_ordinal1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_119,plain,(
    ! [B_53,A_52] :
      ( B_53 = A_52
      | ~ r1_tarski(B_53,A_52)
      | ~ r1_ordinal1(A_52,B_53)
      | ~ v3_ordinal1(B_53)
      | ~ v3_ordinal1(A_52) ) ),
    inference(resolution,[status(thm)],[c_112,c_2])).

tff(c_952,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_947,c_119])).

tff(c_963,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_952])).

tff(c_964,plain,(
    ~ r1_ordinal1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_963])).

tff(c_946,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_704])).

tff(c_988,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_946])).

tff(c_1011,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_988])).

tff(c_1015,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1011])).

tff(c_1016,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_946])).

tff(c_1020,plain,
    ( r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_1016])).

tff(c_1023,plain,(
    r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_1020])).

tff(c_1025,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_964,c_1023])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:01:44 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.62  
% 3.60/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.63  %$ r4_wellord1 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.60/1.63  
% 3.60/1.63  %Foreground sorts:
% 3.60/1.63  
% 3.60/1.63  
% 3.60/1.63  %Background operators:
% 3.60/1.63  
% 3.60/1.63  
% 3.60/1.63  %Foreground operators:
% 3.60/1.63  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 3.60/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.60/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.60/1.63  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.60/1.63  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.60/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.60/1.63  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 3.60/1.63  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 3.60/1.63  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 3.60/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.60/1.63  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.60/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.60/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.60/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.60/1.63  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 3.60/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.60/1.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.60/1.63  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 3.60/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.60/1.63  
% 3.60/1.65  tff(f_130, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r4_wellord1(k1_wellord2(A), k1_wellord2(B)) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_wellord2)).
% 3.60/1.65  tff(f_39, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 3.60/1.65  tff(f_103, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 3.60/1.65  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_wellord1)).
% 3.60/1.65  tff(f_120, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord2)).
% 3.60/1.65  tff(f_101, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 3.60/1.65  tff(f_112, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) => (A = k1_wellord1(k1_wellord2(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_wellord2)).
% 3.60/1.65  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~(r2_hidden(B, k3_relat_1(A)) & r4_wellord1(A, k2_wellord1(A, k1_wellord1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_wellord1)).
% 3.60/1.65  tff(f_48, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 3.60/1.65  tff(f_116, axiom, (![A]: (v3_ordinal1(A) => v2_wellord1(k1_wellord2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_wellord2)).
% 3.60/1.65  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.60/1.65  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (v2_wellord1(B) => (k3_relat_1(k2_wellord1(B, k1_wellord1(B, A))) = k1_wellord1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_wellord1)).
% 3.60/1.65  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k3_relat_1(k2_wellord1(C, B))) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_wellord1)).
% 3.60/1.65  tff(f_53, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.60/1.65  tff(c_52, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.60/1.65  tff(c_56, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.60/1.65  tff(c_58, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.60/1.65  tff(c_10, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~r1_ordinal1(A_3, B_4) | ~v3_ordinal1(B_4) | ~v3_ordinal1(A_3))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.60/1.65  tff(c_44, plain, (![A_29]: (v1_relat_1(k1_wellord2(A_29)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.60/1.65  tff(c_54, plain, (r4_wellord1(k1_wellord2('#skF_3'), k1_wellord2('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.60/1.65  tff(c_95, plain, (![B_47, A_48]: (r4_wellord1(B_47, A_48) | ~r4_wellord1(A_48, B_47) | ~v1_relat_1(B_47) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.60/1.65  tff(c_97, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_3')) | ~v1_relat_1(k1_wellord2('#skF_4')) | ~v1_relat_1(k1_wellord2('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_95])).
% 3.60/1.65  tff(c_100, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_97])).
% 3.60/1.65  tff(c_50, plain, (![B_35, A_34]: (k2_wellord1(k1_wellord2(B_35), A_34)=k1_wellord2(A_34) | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.60/1.65  tff(c_38, plain, (![A_21]: (k3_relat_1(k1_wellord2(A_21))=A_21 | ~v1_relat_1(k1_wellord2(A_21)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.60/1.65  tff(c_64, plain, (![A_21]: (k3_relat_1(k1_wellord2(A_21))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38])).
% 3.60/1.65  tff(c_46, plain, (![B_32, A_30]: (k1_wellord1(k1_wellord2(B_32), A_30)=A_30 | ~r2_hidden(A_30, B_32) | ~v3_ordinal1(B_32) | ~v3_ordinal1(A_30))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.60/1.65  tff(c_318, plain, (![A_80, B_81]: (~r4_wellord1(A_80, k2_wellord1(A_80, k1_wellord1(A_80, B_81))) | ~r2_hidden(B_81, k3_relat_1(A_80)) | ~v2_wellord1(A_80) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.60/1.65  tff(c_321, plain, (![B_32, A_30]: (~r4_wellord1(k1_wellord2(B_32), k2_wellord1(k1_wellord2(B_32), A_30)) | ~r2_hidden(A_30, k3_relat_1(k1_wellord2(B_32))) | ~v2_wellord1(k1_wellord2(B_32)) | ~v1_relat_1(k1_wellord2(B_32)) | ~r2_hidden(A_30, B_32) | ~v3_ordinal1(B_32) | ~v3_ordinal1(A_30))), inference(superposition, [status(thm), theory('equality')], [c_46, c_318])).
% 3.60/1.65  tff(c_568, plain, (![B_110, A_111]: (~r4_wellord1(k1_wellord2(B_110), k2_wellord1(k1_wellord2(B_110), A_111)) | ~v2_wellord1(k1_wellord2(B_110)) | ~r2_hidden(A_111, B_110) | ~v3_ordinal1(B_110) | ~v3_ordinal1(A_111))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_64, c_321])).
% 3.60/1.65  tff(c_695, plain, (![B_124, A_125]: (~r4_wellord1(k1_wellord2(B_124), k1_wellord2(A_125)) | ~v2_wellord1(k1_wellord2(B_124)) | ~r2_hidden(A_125, B_124) | ~v3_ordinal1(B_124) | ~v3_ordinal1(A_125) | ~r1_tarski(A_125, B_124))), inference(superposition, [status(thm), theory('equality')], [c_50, c_568])).
% 3.60/1.65  tff(c_698, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3') | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_100, c_695])).
% 3.60/1.65  tff(c_704, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_3', '#skF_4') | ~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_698])).
% 3.60/1.65  tff(c_708, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_704])).
% 3.60/1.65  tff(c_871, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_708])).
% 3.60/1.65  tff(c_874, plain, (~r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_871])).
% 3.60/1.65  tff(c_12, plain, (![B_7, A_5]: (r2_hidden(B_7, A_5) | r1_ordinal1(A_5, B_7) | ~v3_ordinal1(B_7) | ~v3_ordinal1(A_5))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.60/1.65  tff(c_48, plain, (![A_33]: (v2_wellord1(k1_wellord2(A_33)) | ~v3_ordinal1(A_33))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.60/1.65  tff(c_701, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_695])).
% 3.60/1.65  tff(c_707, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_4', '#skF_3') | ~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_701])).
% 3.60/1.65  tff(c_709, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_707])).
% 3.60/1.65  tff(c_718, plain, (~r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_709])).
% 3.60/1.65  tff(c_721, plain, (~r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_718])).
% 3.60/1.65  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.60/1.65  tff(c_175, plain, (![B_71, A_72]: (k3_relat_1(k2_wellord1(B_71, k1_wellord1(B_71, A_72)))=k1_wellord1(B_71, A_72) | ~v2_wellord1(B_71) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.60/1.65  tff(c_18, plain, (![A_10, C_12, B_11]: (r2_hidden(A_10, k3_relat_1(C_12)) | ~r2_hidden(A_10, k3_relat_1(k2_wellord1(C_12, B_11))) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.60/1.65  tff(c_347, plain, (![A_88, B_89, A_90]: (r2_hidden(A_88, k3_relat_1(B_89)) | ~r2_hidden(A_88, k1_wellord1(B_89, A_90)) | ~v1_relat_1(B_89) | ~v2_wellord1(B_89) | ~v1_relat_1(B_89))), inference(superposition, [status(thm), theory('equality')], [c_175, c_18])).
% 3.60/1.65  tff(c_350, plain, (![A_88, B_32, A_30]: (r2_hidden(A_88, k3_relat_1(k1_wellord2(B_32))) | ~r2_hidden(A_88, A_30) | ~v1_relat_1(k1_wellord2(B_32)) | ~v2_wellord1(k1_wellord2(B_32)) | ~v1_relat_1(k1_wellord2(B_32)) | ~r2_hidden(A_30, B_32) | ~v3_ordinal1(B_32) | ~v3_ordinal1(A_30))), inference(superposition, [status(thm), theory('equality')], [c_46, c_347])).
% 3.60/1.65  tff(c_427, plain, (![A_100, B_101, A_102]: (r2_hidden(A_100, B_101) | ~r2_hidden(A_100, A_102) | ~v2_wellord1(k1_wellord2(B_101)) | ~r2_hidden(A_102, B_101) | ~v3_ordinal1(B_101) | ~v3_ordinal1(A_102))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_64, c_350])).
% 3.60/1.65  tff(c_722, plain, (![B_126, B_127, A_128]: (r2_hidden(B_126, B_127) | ~v2_wellord1(k1_wellord2(B_127)) | ~r2_hidden(A_128, B_127) | ~v3_ordinal1(B_127) | r1_ordinal1(A_128, B_126) | ~v3_ordinal1(B_126) | ~v3_ordinal1(A_128))), inference(resolution, [status(thm)], [c_12, c_427])).
% 3.60/1.65  tff(c_746, plain, (![B_132, A_133, A_134]: (r2_hidden(B_132, A_133) | ~r2_hidden(A_134, A_133) | r1_ordinal1(A_134, B_132) | ~v3_ordinal1(B_132) | ~v3_ordinal1(A_134) | ~v3_ordinal1(A_133))), inference(resolution, [status(thm)], [c_48, c_722])).
% 3.60/1.65  tff(c_770, plain, (![B_135, A_136, B_137]: (r2_hidden(B_135, A_136) | r1_ordinal1(B_137, B_135) | ~v3_ordinal1(B_135) | r1_ordinal1(A_136, B_137) | ~v3_ordinal1(B_137) | ~v3_ordinal1(A_136))), inference(resolution, [status(thm)], [c_12, c_746])).
% 3.60/1.65  tff(c_14, plain, (![B_9, A_8]: (~r1_tarski(B_9, A_8) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.60/1.65  tff(c_824, plain, (![A_138, B_139, B_140]: (~r1_tarski(A_138, B_139) | r1_ordinal1(B_140, B_139) | ~v3_ordinal1(B_139) | r1_ordinal1(A_138, B_140) | ~v3_ordinal1(B_140) | ~v3_ordinal1(A_138))), inference(resolution, [status(thm)], [c_770, c_14])).
% 3.60/1.65  tff(c_845, plain, (![B_141, B_142]: (r1_ordinal1(B_141, B_142) | r1_ordinal1(B_142, B_141) | ~v3_ordinal1(B_141) | ~v3_ordinal1(B_142))), inference(resolution, [status(thm)], [c_6, c_824])).
% 3.60/1.65  tff(c_712, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_708])).
% 3.60/1.65  tff(c_715, plain, (~r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_712])).
% 3.60/1.65  tff(c_849, plain, (r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_845, c_715])).
% 3.60/1.65  tff(c_864, plain, (r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_849])).
% 3.60/1.65  tff(c_866, plain, $false, inference(negUnitSimplification, [status(thm)], [c_721, c_864])).
% 3.60/1.65  tff(c_867, plain, (~r2_hidden('#skF_4', '#skF_3') | ~v2_wellord1(k1_wellord2('#skF_3'))), inference(splitRight, [status(thm)], [c_707])).
% 3.60/1.65  tff(c_928, plain, (~v2_wellord1(k1_wellord2('#skF_3'))), inference(splitLeft, [status(thm)], [c_867])).
% 3.60/1.65  tff(c_931, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_928])).
% 3.60/1.65  tff(c_935, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_931])).
% 3.60/1.65  tff(c_936, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_867])).
% 3.60/1.65  tff(c_940, plain, (r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_936])).
% 3.60/1.65  tff(c_943, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_940])).
% 3.60/1.65  tff(c_945, plain, $false, inference(negUnitSimplification, [status(thm)], [c_874, c_943])).
% 3.60/1.65  tff(c_947, plain, (r1_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_704])).
% 3.60/1.65  tff(c_112, plain, (![A_52, B_53]: (r1_tarski(A_52, B_53) | ~r1_ordinal1(A_52, B_53) | ~v3_ordinal1(B_53) | ~v3_ordinal1(A_52))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.60/1.65  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.60/1.65  tff(c_119, plain, (![B_53, A_52]: (B_53=A_52 | ~r1_tarski(B_53, A_52) | ~r1_ordinal1(A_52, B_53) | ~v3_ordinal1(B_53) | ~v3_ordinal1(A_52))), inference(resolution, [status(thm)], [c_112, c_2])).
% 3.60/1.65  tff(c_952, plain, ('#skF_3'='#skF_4' | ~r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_947, c_119])).
% 3.60/1.65  tff(c_963, plain, ('#skF_3'='#skF_4' | ~r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_952])).
% 3.60/1.65  tff(c_964, plain, (~r1_ordinal1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_963])).
% 3.60/1.65  tff(c_946, plain, (~r2_hidden('#skF_3', '#skF_4') | ~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitRight, [status(thm)], [c_704])).
% 3.60/1.65  tff(c_988, plain, (~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitLeft, [status(thm)], [c_946])).
% 3.60/1.65  tff(c_1011, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_988])).
% 3.60/1.65  tff(c_1015, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_1011])).
% 3.60/1.65  tff(c_1016, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_946])).
% 3.60/1.65  tff(c_1020, plain, (r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_1016])).
% 3.60/1.65  tff(c_1023, plain, (r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_1020])).
% 3.60/1.65  tff(c_1025, plain, $false, inference(negUnitSimplification, [status(thm)], [c_964, c_1023])).
% 3.60/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.65  
% 3.60/1.65  Inference rules
% 3.60/1.65  ----------------------
% 3.60/1.65  #Ref     : 0
% 3.60/1.65  #Sup     : 211
% 3.60/1.65  #Fact    : 2
% 3.60/1.65  #Define  : 0
% 3.60/1.65  #Split   : 4
% 3.60/1.65  #Chain   : 0
% 3.60/1.65  #Close   : 0
% 3.60/1.65  
% 3.60/1.65  Ordering : KBO
% 3.60/1.65  
% 3.60/1.65  Simplification rules
% 3.60/1.65  ----------------------
% 3.60/1.65  #Subsume      : 21
% 3.60/1.65  #Demod        : 157
% 3.60/1.65  #Tautology    : 41
% 3.60/1.65  #SimpNegUnit  : 9
% 3.60/1.65  #BackRed      : 0
% 3.60/1.65  
% 3.60/1.65  #Partial instantiations: 0
% 3.60/1.65  #Strategies tried      : 1
% 3.60/1.65  
% 3.60/1.65  Timing (in seconds)
% 3.60/1.65  ----------------------
% 3.60/1.65  Preprocessing        : 0.32
% 3.60/1.65  Parsing              : 0.17
% 3.60/1.65  CNF conversion       : 0.02
% 3.60/1.65  Main loop            : 0.52
% 3.60/1.65  Inferencing          : 0.19
% 3.60/1.65  Reduction            : 0.15
% 3.60/1.65  Demodulation         : 0.11
% 3.60/1.65  BG Simplification    : 0.03
% 3.60/1.65  Subsumption          : 0.12
% 3.60/1.65  Abstraction          : 0.03
% 3.60/1.65  MUC search           : 0.00
% 3.60/1.65  Cooper               : 0.00
% 3.60/1.65  Total                : 0.89
% 3.60/1.65  Index Insertion      : 0.00
% 3.60/1.65  Index Deletion       : 0.00
% 3.60/1.65  Index Matching       : 0.00
% 3.60/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
