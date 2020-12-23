%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:22 EST 2020

% Result     : Theorem 11.49s
% Output     : CNFRefutation 11.54s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 251 expanded)
%              Number of leaves         :   26 (  98 expanded)
%              Depth                    :   11
%              Number of atoms          :  156 ( 678 expanded)
%              Number of equality atoms :   29 ( 156 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_215,plain,(
    ! [A_78,B_79,C_80] :
      ( ~ r2_hidden('#skF_1'(A_78,B_79,C_80),C_80)
      | r2_hidden('#skF_2'(A_78,B_79,C_80),C_80)
      | k3_xboole_0(A_78,B_79) = C_80 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_229,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2,B_2),B_2)
      | k3_xboole_0(A_1,B_2) = B_2 ) ),
    inference(resolution,[status(thm)],[c_16,c_215])).

tff(c_151,plain,(
    ! [A_66,B_67,C_68] :
      ( r2_hidden('#skF_1'(A_66,B_67,C_68),B_67)
      | r2_hidden('#skF_2'(A_66,B_67,C_68),C_68)
      | k3_xboole_0(A_66,B_67) = C_68 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_545,plain,(
    ! [A_117,B_118,A_119,B_120] :
      ( r2_hidden('#skF_2'(A_117,B_118,k3_xboole_0(A_119,B_120)),B_120)
      | r2_hidden('#skF_1'(A_117,B_118,k3_xboole_0(A_119,B_120)),B_118)
      | k3_xboole_0(A_119,B_120) = k3_xboole_0(A_117,B_118) ) ),
    inference(resolution,[status(thm)],[c_151,c_4])).

tff(c_10,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_579,plain,(
    ! [B_120,B_118,A_119] :
      ( ~ r2_hidden('#skF_2'(B_120,B_118,k3_xboole_0(A_119,B_120)),B_118)
      | r2_hidden('#skF_1'(B_120,B_118,k3_xboole_0(A_119,B_120)),B_118)
      | k3_xboole_0(B_120,B_118) = k3_xboole_0(A_119,B_120) ) ),
    inference(resolution,[status(thm)],[c_545,c_10])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_584,plain,(
    ! [A_119,B_2,A_1,A_117,B_120] :
      ( r2_hidden('#skF_1'(A_117,k3_xboole_0(A_1,B_2),k3_xboole_0(A_119,B_120)),A_1)
      | r2_hidden('#skF_2'(A_117,k3_xboole_0(A_1,B_2),k3_xboole_0(A_119,B_120)),B_120)
      | k3_xboole_0(A_119,B_120) = k3_xboole_0(A_117,k3_xboole_0(A_1,B_2)) ) ),
    inference(resolution,[status(thm)],[c_545,c_6])).

tff(c_194,plain,(
    ! [A_75,B_76,C_77] :
      ( r2_hidden('#skF_1'(A_75,B_76,C_77),A_75)
      | r2_hidden('#skF_2'(A_75,B_76,C_77),C_77)
      | k3_xboole_0(A_75,B_76) = C_77 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_214,plain,(
    ! [A_75,B_76,A_1,B_2] :
      ( r2_hidden('#skF_2'(A_75,B_76,k3_xboole_0(A_1,B_2)),B_2)
      | r2_hidden('#skF_1'(A_75,B_76,k3_xboole_0(A_1,B_2)),A_75)
      | k3_xboole_0(A_75,B_76) = k3_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_194,c_4])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k3_xboole_0(A_1,B_2))
      | ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1142,plain,(
    ! [A_185,B_186,A_187,B_188] :
      ( r2_hidden('#skF_2'(A_185,B_186,k3_xboole_0(A_187,B_188)),k3_xboole_0(A_187,B_188))
      | k3_xboole_0(A_187,B_188) = k3_xboole_0(A_185,B_186)
      | ~ r2_hidden('#skF_1'(A_185,B_186,k3_xboole_0(A_187,B_188)),B_188)
      | ~ r2_hidden('#skF_1'(A_185,B_186,k3_xboole_0(A_187,B_188)),A_187) ) ),
    inference(resolution,[status(thm)],[c_2,c_215])).

tff(c_6904,plain,(
    ! [A_566,B_567,A_568,B_569] :
      ( r2_hidden('#skF_2'(A_566,B_567,k3_xboole_0(A_568,B_569)),B_569)
      | k3_xboole_0(A_568,B_569) = k3_xboole_0(A_566,B_567)
      | ~ r2_hidden('#skF_1'(A_566,B_567,k3_xboole_0(A_568,B_569)),B_569)
      | ~ r2_hidden('#skF_1'(A_566,B_567,k3_xboole_0(A_568,B_569)),A_568) ) ),
    inference(resolution,[status(thm)],[c_1142,c_4])).

tff(c_7357,plain,(
    ! [A_582,B_583,A_584] :
      ( ~ r2_hidden('#skF_1'(A_582,B_583,k3_xboole_0(A_584,A_582)),A_584)
      | r2_hidden('#skF_2'(A_582,B_583,k3_xboole_0(A_584,A_582)),A_582)
      | k3_xboole_0(A_584,A_582) = k3_xboole_0(A_582,B_583) ) ),
    inference(resolution,[status(thm)],[c_214,c_6904])).

tff(c_7483,plain,(
    ! [B_120,A_1,B_2] :
      ( r2_hidden('#skF_2'(B_120,k3_xboole_0(A_1,B_2),k3_xboole_0(A_1,B_120)),B_120)
      | k3_xboole_0(B_120,k3_xboole_0(A_1,B_2)) = k3_xboole_0(A_1,B_120) ) ),
    inference(resolution,[status(thm)],[c_584,c_7357])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_253,plain,(
    ! [A_85,B_86,C_87] :
      ( r2_hidden('#skF_1'(A_85,B_86,C_87),A_85)
      | ~ r2_hidden('#skF_2'(A_85,B_86,C_87),B_86)
      | ~ r2_hidden('#skF_2'(A_85,B_86,C_87),A_85)
      | k3_xboole_0(A_85,B_86) = C_87 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_268,plain,(
    ! [A_1,C_3] :
      ( ~ r2_hidden('#skF_2'(A_1,C_3,C_3),A_1)
      | r2_hidden('#skF_1'(A_1,C_3,C_3),A_1)
      | k3_xboole_0(A_1,C_3) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_253])).

tff(c_312,plain,(
    ! [A_96,B_97,C_98] :
      ( ~ r2_hidden('#skF_1'(A_96,B_97,C_98),C_98)
      | ~ r2_hidden('#skF_2'(A_96,B_97,C_98),B_97)
      | ~ r2_hidden('#skF_2'(A_96,B_97,C_98),A_96)
      | k3_xboole_0(A_96,B_97) = C_98 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_329,plain,(
    ! [A_99] :
      ( ~ r2_hidden('#skF_2'(A_99,A_99,A_99),A_99)
      | k3_xboole_0(A_99,A_99) = A_99 ) ),
    inference(resolution,[status(thm)],[c_268,c_312])).

tff(c_346,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_229,c_329])).

tff(c_230,plain,(
    ! [A_78,B_79,A_1,B_2] :
      ( r2_hidden('#skF_2'(A_78,B_79,k3_xboole_0(A_1,B_2)),k3_xboole_0(A_1,B_2))
      | k3_xboole_0(A_78,B_79) = k3_xboole_0(A_1,B_2)
      | ~ r2_hidden('#skF_1'(A_78,B_79,k3_xboole_0(A_1,B_2)),B_2)
      | ~ r2_hidden('#skF_1'(A_78,B_79,k3_xboole_0(A_1,B_2)),A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_215])).

tff(c_2196,plain,(
    ! [A_263,B_264,A_265,B_266] :
      ( ~ r2_hidden('#skF_2'(A_263,B_264,k3_xboole_0(A_265,B_266)),B_264)
      | ~ r2_hidden('#skF_2'(A_263,B_264,k3_xboole_0(A_265,B_266)),A_263)
      | k3_xboole_0(A_265,B_266) = k3_xboole_0(A_263,B_264)
      | ~ r2_hidden('#skF_1'(A_263,B_264,k3_xboole_0(A_265,B_266)),B_266)
      | ~ r2_hidden('#skF_1'(A_263,B_264,k3_xboole_0(A_265,B_266)),A_265) ) ),
    inference(resolution,[status(thm)],[c_2,c_312])).

tff(c_9363,plain,(
    ! [A_693,A_694,B_695] :
      ( ~ r2_hidden('#skF_2'(A_693,k3_xboole_0(A_694,B_695),k3_xboole_0(A_694,B_695)),A_693)
      | k3_xboole_0(A_693,k3_xboole_0(A_694,B_695)) = k3_xboole_0(A_694,B_695)
      | ~ r2_hidden('#skF_1'(A_693,k3_xboole_0(A_694,B_695),k3_xboole_0(A_694,B_695)),B_695)
      | ~ r2_hidden('#skF_1'(A_693,k3_xboole_0(A_694,B_695),k3_xboole_0(A_694,B_695)),A_694) ) ),
    inference(resolution,[status(thm)],[c_230,c_2196])).

tff(c_9472,plain,(
    ! [A_693,B_2] :
      ( ~ r2_hidden('#skF_2'(A_693,B_2,k3_xboole_0(B_2,B_2)),A_693)
      | k3_xboole_0(A_693,k3_xboole_0(B_2,B_2)) = k3_xboole_0(B_2,B_2)
      | ~ r2_hidden('#skF_1'(A_693,k3_xboole_0(B_2,B_2),k3_xboole_0(B_2,B_2)),B_2)
      | ~ r2_hidden('#skF_1'(A_693,k3_xboole_0(B_2,B_2),k3_xboole_0(B_2,B_2)),B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_9363])).

tff(c_9588,plain,(
    ! [A_700,B_701] :
      ( ~ r2_hidden('#skF_2'(A_700,B_701,B_701),A_700)
      | k3_xboole_0(A_700,B_701) = B_701
      | ~ r2_hidden('#skF_1'(A_700,B_701,B_701),B_701)
      | ~ r2_hidden('#skF_1'(A_700,B_701,B_701),B_701) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_346,c_346,c_346,c_346,c_346,c_346,c_9472])).

tff(c_9763,plain,(
    ! [B_702,A_703] :
      ( ~ r2_hidden('#skF_1'(B_702,k3_xboole_0(A_703,B_702),k3_xboole_0(A_703,B_702)),k3_xboole_0(A_703,B_702))
      | k3_xboole_0(B_702,k3_xboole_0(A_703,B_702)) = k3_xboole_0(A_703,B_702) ) ),
    inference(resolution,[status(thm)],[c_7483,c_9588])).

tff(c_9960,plain,(
    ! [B_710,A_711] :
      ( ~ r2_hidden('#skF_2'(B_710,k3_xboole_0(A_711,B_710),k3_xboole_0(A_711,B_710)),k3_xboole_0(A_711,B_710))
      | k3_xboole_0(B_710,k3_xboole_0(A_711,B_710)) = k3_xboole_0(A_711,B_710) ) ),
    inference(resolution,[status(thm)],[c_579,c_9763])).

tff(c_10059,plain,(
    ! [A_712,A_713] : k3_xboole_0(A_712,k3_xboole_0(A_713,A_712)) = k3_xboole_0(A_713,A_712) ),
    inference(resolution,[status(thm)],[c_229,c_9960])).

tff(c_20,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11439,plain,(
    ! [A_713,A_712] : r1_tarski(k3_xboole_0(A_713,A_712),A_712) ),
    inference(superposition,[status(thm),theory(equality)],[c_10059,c_20])).

tff(c_44,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_70,plain,(
    ! [B_38,A_39] :
      ( v1_relat_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_75,plain,(
    ! [A_40,B_41] :
      ( v1_relat_1(A_40)
      | ~ v1_relat_1(B_41)
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(resolution,[status(thm)],[c_32,c_70])).

tff(c_79,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k3_xboole_0(A_7,B_8))
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_20,c_75])).

tff(c_42,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    ! [A_24,B_26] :
      ( r1_tarski(k2_relat_1(A_24),k2_relat_1(B_26))
      | ~ r1_tarski(A_24,B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_101,plain,(
    ! [A_56,B_57,C_58] :
      ( r1_tarski(A_56,k3_xboole_0(B_57,C_58))
      | ~ r1_tarski(A_56,C_58)
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_40,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k2_relat_1('#skF_3'),k2_relat_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_108,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_4'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_101,c_40])).

tff(c_124,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_127,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_124])).

tff(c_130,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_20,c_127])).

tff(c_133,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_130])).

tff(c_137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_133])).

tff(c_138,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_142,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_138])).

tff(c_145,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_142])).

tff(c_172,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_175,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_172])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_175])).

tff(c_180,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_11886,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11439,c_180])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 21:04:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.49/3.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.54/3.82  
% 11.54/3.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.54/3.82  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 11.54/3.82  
% 11.54/3.82  %Foreground sorts:
% 11.54/3.82  
% 11.54/3.82  
% 11.54/3.82  %Background operators:
% 11.54/3.82  
% 11.54/3.82  
% 11.54/3.82  %Foreground operators:
% 11.54/3.82  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.54/3.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.54/3.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.54/3.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.54/3.82  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.54/3.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.54/3.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.54/3.82  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.54/3.82  tff('#skF_3', type, '#skF_3': $i).
% 11.54/3.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.54/3.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.54/3.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.54/3.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.54/3.82  tff('#skF_4', type, '#skF_4': $i).
% 11.54/3.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.54/3.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.54/3.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.54/3.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.54/3.82  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.54/3.82  
% 11.54/3.84  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 11.54/3.84  tff(f_36, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 11.54/3.84  tff(f_78, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_relat_1)).
% 11.54/3.84  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.54/3.84  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 11.54/3.84  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 11.54/3.84  tff(f_42, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 11.54/3.84  tff(c_16, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.54/3.84  tff(c_215, plain, (![A_78, B_79, C_80]: (~r2_hidden('#skF_1'(A_78, B_79, C_80), C_80) | r2_hidden('#skF_2'(A_78, B_79, C_80), C_80) | k3_xboole_0(A_78, B_79)=C_80)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.54/3.84  tff(c_229, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2, B_2), B_2) | k3_xboole_0(A_1, B_2)=B_2)), inference(resolution, [status(thm)], [c_16, c_215])).
% 11.54/3.84  tff(c_151, plain, (![A_66, B_67, C_68]: (r2_hidden('#skF_1'(A_66, B_67, C_68), B_67) | r2_hidden('#skF_2'(A_66, B_67, C_68), C_68) | k3_xboole_0(A_66, B_67)=C_68)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.54/3.84  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.54/3.84  tff(c_545, plain, (![A_117, B_118, A_119, B_120]: (r2_hidden('#skF_2'(A_117, B_118, k3_xboole_0(A_119, B_120)), B_120) | r2_hidden('#skF_1'(A_117, B_118, k3_xboole_0(A_119, B_120)), B_118) | k3_xboole_0(A_119, B_120)=k3_xboole_0(A_117, B_118))), inference(resolution, [status(thm)], [c_151, c_4])).
% 11.54/3.84  tff(c_10, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.54/3.84  tff(c_579, plain, (![B_120, B_118, A_119]: (~r2_hidden('#skF_2'(B_120, B_118, k3_xboole_0(A_119, B_120)), B_118) | r2_hidden('#skF_1'(B_120, B_118, k3_xboole_0(A_119, B_120)), B_118) | k3_xboole_0(B_120, B_118)=k3_xboole_0(A_119, B_120))), inference(resolution, [status(thm)], [c_545, c_10])).
% 11.54/3.84  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.54/3.84  tff(c_584, plain, (![A_119, B_2, A_1, A_117, B_120]: (r2_hidden('#skF_1'(A_117, k3_xboole_0(A_1, B_2), k3_xboole_0(A_119, B_120)), A_1) | r2_hidden('#skF_2'(A_117, k3_xboole_0(A_1, B_2), k3_xboole_0(A_119, B_120)), B_120) | k3_xboole_0(A_119, B_120)=k3_xboole_0(A_117, k3_xboole_0(A_1, B_2)))), inference(resolution, [status(thm)], [c_545, c_6])).
% 11.54/3.84  tff(c_194, plain, (![A_75, B_76, C_77]: (r2_hidden('#skF_1'(A_75, B_76, C_77), A_75) | r2_hidden('#skF_2'(A_75, B_76, C_77), C_77) | k3_xboole_0(A_75, B_76)=C_77)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.54/3.84  tff(c_214, plain, (![A_75, B_76, A_1, B_2]: (r2_hidden('#skF_2'(A_75, B_76, k3_xboole_0(A_1, B_2)), B_2) | r2_hidden('#skF_1'(A_75, B_76, k3_xboole_0(A_1, B_2)), A_75) | k3_xboole_0(A_75, B_76)=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_194, c_4])).
% 11.54/3.84  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k3_xboole_0(A_1, B_2)) | ~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.54/3.84  tff(c_1142, plain, (![A_185, B_186, A_187, B_188]: (r2_hidden('#skF_2'(A_185, B_186, k3_xboole_0(A_187, B_188)), k3_xboole_0(A_187, B_188)) | k3_xboole_0(A_187, B_188)=k3_xboole_0(A_185, B_186) | ~r2_hidden('#skF_1'(A_185, B_186, k3_xboole_0(A_187, B_188)), B_188) | ~r2_hidden('#skF_1'(A_185, B_186, k3_xboole_0(A_187, B_188)), A_187))), inference(resolution, [status(thm)], [c_2, c_215])).
% 11.54/3.84  tff(c_6904, plain, (![A_566, B_567, A_568, B_569]: (r2_hidden('#skF_2'(A_566, B_567, k3_xboole_0(A_568, B_569)), B_569) | k3_xboole_0(A_568, B_569)=k3_xboole_0(A_566, B_567) | ~r2_hidden('#skF_1'(A_566, B_567, k3_xboole_0(A_568, B_569)), B_569) | ~r2_hidden('#skF_1'(A_566, B_567, k3_xboole_0(A_568, B_569)), A_568))), inference(resolution, [status(thm)], [c_1142, c_4])).
% 11.54/3.84  tff(c_7357, plain, (![A_582, B_583, A_584]: (~r2_hidden('#skF_1'(A_582, B_583, k3_xboole_0(A_584, A_582)), A_584) | r2_hidden('#skF_2'(A_582, B_583, k3_xboole_0(A_584, A_582)), A_582) | k3_xboole_0(A_584, A_582)=k3_xboole_0(A_582, B_583))), inference(resolution, [status(thm)], [c_214, c_6904])).
% 11.54/3.84  tff(c_7483, plain, (![B_120, A_1, B_2]: (r2_hidden('#skF_2'(B_120, k3_xboole_0(A_1, B_2), k3_xboole_0(A_1, B_120)), B_120) | k3_xboole_0(B_120, k3_xboole_0(A_1, B_2))=k3_xboole_0(A_1, B_120))), inference(resolution, [status(thm)], [c_584, c_7357])).
% 11.54/3.84  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.54/3.84  tff(c_253, plain, (![A_85, B_86, C_87]: (r2_hidden('#skF_1'(A_85, B_86, C_87), A_85) | ~r2_hidden('#skF_2'(A_85, B_86, C_87), B_86) | ~r2_hidden('#skF_2'(A_85, B_86, C_87), A_85) | k3_xboole_0(A_85, B_86)=C_87)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.54/3.84  tff(c_268, plain, (![A_1, C_3]: (~r2_hidden('#skF_2'(A_1, C_3, C_3), A_1) | r2_hidden('#skF_1'(A_1, C_3, C_3), A_1) | k3_xboole_0(A_1, C_3)=C_3)), inference(resolution, [status(thm)], [c_18, c_253])).
% 11.54/3.84  tff(c_312, plain, (![A_96, B_97, C_98]: (~r2_hidden('#skF_1'(A_96, B_97, C_98), C_98) | ~r2_hidden('#skF_2'(A_96, B_97, C_98), B_97) | ~r2_hidden('#skF_2'(A_96, B_97, C_98), A_96) | k3_xboole_0(A_96, B_97)=C_98)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.54/3.84  tff(c_329, plain, (![A_99]: (~r2_hidden('#skF_2'(A_99, A_99, A_99), A_99) | k3_xboole_0(A_99, A_99)=A_99)), inference(resolution, [status(thm)], [c_268, c_312])).
% 11.54/3.84  tff(c_346, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_229, c_329])).
% 11.54/3.84  tff(c_230, plain, (![A_78, B_79, A_1, B_2]: (r2_hidden('#skF_2'(A_78, B_79, k3_xboole_0(A_1, B_2)), k3_xboole_0(A_1, B_2)) | k3_xboole_0(A_78, B_79)=k3_xboole_0(A_1, B_2) | ~r2_hidden('#skF_1'(A_78, B_79, k3_xboole_0(A_1, B_2)), B_2) | ~r2_hidden('#skF_1'(A_78, B_79, k3_xboole_0(A_1, B_2)), A_1))), inference(resolution, [status(thm)], [c_2, c_215])).
% 11.54/3.84  tff(c_2196, plain, (![A_263, B_264, A_265, B_266]: (~r2_hidden('#skF_2'(A_263, B_264, k3_xboole_0(A_265, B_266)), B_264) | ~r2_hidden('#skF_2'(A_263, B_264, k3_xboole_0(A_265, B_266)), A_263) | k3_xboole_0(A_265, B_266)=k3_xboole_0(A_263, B_264) | ~r2_hidden('#skF_1'(A_263, B_264, k3_xboole_0(A_265, B_266)), B_266) | ~r2_hidden('#skF_1'(A_263, B_264, k3_xboole_0(A_265, B_266)), A_265))), inference(resolution, [status(thm)], [c_2, c_312])).
% 11.54/3.84  tff(c_9363, plain, (![A_693, A_694, B_695]: (~r2_hidden('#skF_2'(A_693, k3_xboole_0(A_694, B_695), k3_xboole_0(A_694, B_695)), A_693) | k3_xboole_0(A_693, k3_xboole_0(A_694, B_695))=k3_xboole_0(A_694, B_695) | ~r2_hidden('#skF_1'(A_693, k3_xboole_0(A_694, B_695), k3_xboole_0(A_694, B_695)), B_695) | ~r2_hidden('#skF_1'(A_693, k3_xboole_0(A_694, B_695), k3_xboole_0(A_694, B_695)), A_694))), inference(resolution, [status(thm)], [c_230, c_2196])).
% 11.54/3.84  tff(c_9472, plain, (![A_693, B_2]: (~r2_hidden('#skF_2'(A_693, B_2, k3_xboole_0(B_2, B_2)), A_693) | k3_xboole_0(A_693, k3_xboole_0(B_2, B_2))=k3_xboole_0(B_2, B_2) | ~r2_hidden('#skF_1'(A_693, k3_xboole_0(B_2, B_2), k3_xboole_0(B_2, B_2)), B_2) | ~r2_hidden('#skF_1'(A_693, k3_xboole_0(B_2, B_2), k3_xboole_0(B_2, B_2)), B_2))), inference(superposition, [status(thm), theory('equality')], [c_346, c_9363])).
% 11.54/3.84  tff(c_9588, plain, (![A_700, B_701]: (~r2_hidden('#skF_2'(A_700, B_701, B_701), A_700) | k3_xboole_0(A_700, B_701)=B_701 | ~r2_hidden('#skF_1'(A_700, B_701, B_701), B_701) | ~r2_hidden('#skF_1'(A_700, B_701, B_701), B_701))), inference(demodulation, [status(thm), theory('equality')], [c_346, c_346, c_346, c_346, c_346, c_346, c_346, c_9472])).
% 11.54/3.84  tff(c_9763, plain, (![B_702, A_703]: (~r2_hidden('#skF_1'(B_702, k3_xboole_0(A_703, B_702), k3_xboole_0(A_703, B_702)), k3_xboole_0(A_703, B_702)) | k3_xboole_0(B_702, k3_xboole_0(A_703, B_702))=k3_xboole_0(A_703, B_702))), inference(resolution, [status(thm)], [c_7483, c_9588])).
% 11.54/3.84  tff(c_9960, plain, (![B_710, A_711]: (~r2_hidden('#skF_2'(B_710, k3_xboole_0(A_711, B_710), k3_xboole_0(A_711, B_710)), k3_xboole_0(A_711, B_710)) | k3_xboole_0(B_710, k3_xboole_0(A_711, B_710))=k3_xboole_0(A_711, B_710))), inference(resolution, [status(thm)], [c_579, c_9763])).
% 11.54/3.84  tff(c_10059, plain, (![A_712, A_713]: (k3_xboole_0(A_712, k3_xboole_0(A_713, A_712))=k3_xboole_0(A_713, A_712))), inference(resolution, [status(thm)], [c_229, c_9960])).
% 11.54/3.84  tff(c_20, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.54/3.84  tff(c_11439, plain, (![A_713, A_712]: (r1_tarski(k3_xboole_0(A_713, A_712), A_712))), inference(superposition, [status(thm), theory('equality')], [c_10059, c_20])).
% 11.54/3.84  tff(c_44, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.54/3.84  tff(c_32, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.54/3.84  tff(c_70, plain, (![B_38, A_39]: (v1_relat_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.54/3.84  tff(c_75, plain, (![A_40, B_41]: (v1_relat_1(A_40) | ~v1_relat_1(B_41) | ~r1_tarski(A_40, B_41))), inference(resolution, [status(thm)], [c_32, c_70])).
% 11.54/3.84  tff(c_79, plain, (![A_7, B_8]: (v1_relat_1(k3_xboole_0(A_7, B_8)) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_20, c_75])).
% 11.54/3.84  tff(c_42, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.54/3.84  tff(c_36, plain, (![A_24, B_26]: (r1_tarski(k2_relat_1(A_24), k2_relat_1(B_26)) | ~r1_tarski(A_24, B_26) | ~v1_relat_1(B_26) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.54/3.84  tff(c_101, plain, (![A_56, B_57, C_58]: (r1_tarski(A_56, k3_xboole_0(B_57, C_58)) | ~r1_tarski(A_56, C_58) | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.54/3.84  tff(c_40, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k2_relat_1('#skF_3'), k2_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.54/3.84  tff(c_108, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_4')) | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_101, c_40])).
% 11.54/3.84  tff(c_124, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_108])).
% 11.54/3.84  tff(c_127, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_124])).
% 11.54/3.84  tff(c_130, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_20, c_127])).
% 11.54/3.84  tff(c_133, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_79, c_130])).
% 11.54/3.84  tff(c_137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_133])).
% 11.54/3.84  tff(c_138, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_108])).
% 11.54/3.84  tff(c_142, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_138])).
% 11.54/3.84  tff(c_145, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_142])).
% 11.54/3.84  tff(c_172, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_145])).
% 11.54/3.84  tff(c_175, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_79, c_172])).
% 11.54/3.84  tff(c_179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_175])).
% 11.54/3.84  tff(c_180, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_145])).
% 11.54/3.84  tff(c_11886, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11439, c_180])).
% 11.54/3.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.54/3.84  
% 11.54/3.84  Inference rules
% 11.54/3.84  ----------------------
% 11.54/3.84  #Ref     : 0
% 11.54/3.84  #Sup     : 2510
% 11.54/3.84  #Fact    : 0
% 11.54/3.84  #Define  : 0
% 11.54/3.84  #Split   : 3
% 11.54/3.84  #Chain   : 0
% 11.54/3.84  #Close   : 0
% 11.54/3.84  
% 11.54/3.84  Ordering : KBO
% 11.54/3.84  
% 11.54/3.84  Simplification rules
% 11.54/3.84  ----------------------
% 11.54/3.84  #Subsume      : 1258
% 11.54/3.84  #Demod        : 2885
% 11.54/3.84  #Tautology    : 279
% 11.54/3.84  #SimpNegUnit  : 0
% 11.54/3.84  #BackRed      : 3
% 11.54/3.84  
% 11.54/3.84  #Partial instantiations: 0
% 11.54/3.84  #Strategies tried      : 1
% 11.54/3.84  
% 11.54/3.84  Timing (in seconds)
% 11.54/3.84  ----------------------
% 11.54/3.84  Preprocessing        : 0.32
% 11.54/3.84  Parsing              : 0.16
% 11.54/3.84  CNF conversion       : 0.02
% 11.54/3.84  Main loop            : 2.76
% 11.54/3.85  Inferencing          : 0.96
% 11.54/3.85  Reduction            : 0.59
% 11.54/3.85  Demodulation         : 0.42
% 11.54/3.85  BG Simplification    : 0.09
% 11.54/3.85  Subsumption          : 0.97
% 11.54/3.85  Abstraction          : 0.20
% 11.54/3.85  MUC search           : 0.00
% 11.54/3.85  Cooper               : 0.00
% 11.54/3.85  Total                : 3.12
% 11.54/3.85  Index Insertion      : 0.00
% 11.54/3.85  Index Deletion       : 0.00
% 11.54/3.85  Index Matching       : 0.00
% 11.54/3.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
