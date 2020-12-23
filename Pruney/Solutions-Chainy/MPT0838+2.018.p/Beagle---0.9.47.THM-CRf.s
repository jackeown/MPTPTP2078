%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:11 EST 2020

% Result     : Theorem 5.31s
% Output     : CNFRefutation 5.43s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 316 expanded)
%              Number of leaves         :   38 ( 118 expanded)
%              Depth                    :   17
%              Number of atoms          :  236 ( 694 expanded)
%              Number of equality atoms :   28 (  75 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(c_16,plain,(
    ! [A_8] : m1_subset_1('#skF_1'(A_8),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    ! [A_18] :
      ( v1_xboole_0(k1_relat_1(A_18))
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_59,plain,(
    ! [A_58] :
      ( v1_xboole_0(k1_relat_1(A_58))
      | ~ v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_64,plain,(
    ! [A_59] :
      ( k1_relat_1(A_59) = k1_xboole_0
      | ~ v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_59,c_2])).

tff(c_71,plain,(
    ! [A_63] :
      ( k1_relat_1(k1_relat_1(A_63)) = k1_xboole_0
      | ~ v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_24,c_64])).

tff(c_80,plain,(
    ! [A_63] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k1_relat_1(A_63))
      | ~ v1_xboole_0(A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_24])).

tff(c_90,plain,(
    ! [A_64] :
      ( ~ v1_xboole_0(k1_relat_1(A_64))
      | ~ v1_xboole_0(A_64) ) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_97,plain,(
    ! [A_18] : ~ v1_xboole_0(A_18) ),
    inference(resolution,[status(thm)],[c_24,c_90])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( r2_hidden(A_16,B_17)
      | v1_xboole_0(B_17)
      | ~ m1_subset_1(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_127,plain,(
    ! [A_16,B_17] :
      ( r2_hidden(A_16,B_17)
      | ~ m1_subset_1(A_16,B_17) ) ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_22])).

tff(c_149,plain,(
    ! [C_81,A_82,B_83] :
      ( r2_hidden(C_81,A_82)
      | ~ r2_hidden(C_81,B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_221,plain,(
    ! [A_108,A_109,B_110] :
      ( r2_hidden(A_108,A_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_109))
      | ~ m1_subset_1(A_108,B_110) ) ),
    inference(resolution,[status(thm)],[c_127,c_149])).

tff(c_247,plain,(
    ! [A_112,A_113] :
      ( r2_hidden(A_112,A_113)
      | ~ m1_subset_1(A_112,'#skF_1'(k1_zfmisc_1(A_113))) ) ),
    inference(resolution,[status(thm)],[c_16,c_221])).

tff(c_253,plain,(
    ! [A_114] : r2_hidden('#skF_1'('#skF_1'(k1_zfmisc_1(A_114))),A_114) ),
    inference(resolution,[status(thm)],[c_16,c_247])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_159,plain,(
    ! [A_88,B_89,C_90] :
      ( k2_relset_1(A_88,B_89,C_90) = k2_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_167,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_159])).

tff(c_46,plain,(
    ! [D_54] :
      ( ~ r2_hidden(D_54,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_54,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_171,plain,(
    ! [D_54] :
      ( ~ r2_hidden(D_54,k2_relat_1('#skF_5'))
      | ~ m1_subset_1(D_54,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_46])).

tff(c_263,plain,(
    ~ m1_subset_1('#skF_1'('#skF_1'(k1_zfmisc_1(k2_relat_1('#skF_5')))),'#skF_4') ),
    inference(resolution,[status(thm)],[c_253,c_171])).

tff(c_252,plain,(
    ! [A_113] : r2_hidden('#skF_1'('#skF_1'(k1_zfmisc_1(A_113))),A_113) ),
    inference(resolution,[status(thm)],[c_16,c_247])).

tff(c_107,plain,(
    ! [C_68,A_69,B_70] :
      ( v1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_115,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_107])).

tff(c_34,plain,(
    ! [A_25] :
      ( k9_relat_1(A_25,k1_relat_1(A_25)) = k2_relat_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_441,plain,(
    ! [A_136,B_137,C_138] :
      ( r2_hidden(k4_tarski('#skF_2'(A_136,B_137,C_138),A_136),C_138)
      | ~ r2_hidden(A_136,k9_relat_1(C_138,B_137))
      | ~ v1_relat_1(C_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,B_15)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1962,plain,(
    ! [A_229,B_230,C_231] :
      ( m1_subset_1(k4_tarski('#skF_2'(A_229,B_230,C_231),A_229),C_231)
      | ~ r2_hidden(A_229,k9_relat_1(C_231,B_230))
      | ~ v1_relat_1(C_231) ) ),
    inference(resolution,[status(thm)],[c_441,c_20])).

tff(c_229,plain,(
    ! [A_111] :
      ( r2_hidden(A_111,k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ m1_subset_1(A_111,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_221])).

tff(c_12,plain,(
    ! [B_5,D_7,A_4,C_6] :
      ( r2_hidden(B_5,D_7)
      | ~ r2_hidden(k4_tarski(A_4,B_5),k2_zfmisc_1(C_6,D_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_245,plain,(
    ! [B_5,A_4] :
      ( r2_hidden(B_5,'#skF_4')
      | ~ m1_subset_1(k4_tarski(A_4,B_5),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_229,c_12])).

tff(c_1999,plain,(
    ! [A_229,B_230] :
      ( r2_hidden(A_229,'#skF_4')
      | ~ r2_hidden(A_229,k9_relat_1('#skF_5',B_230))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1962,c_245])).

tff(c_2062,plain,(
    ! [A_232,B_233] :
      ( r2_hidden(A_232,'#skF_4')
      | ~ r2_hidden(A_232,k9_relat_1('#skF_5',B_233)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_1999])).

tff(c_2138,plain,(
    ! [A_232] :
      ( r2_hidden(A_232,'#skF_4')
      | ~ r2_hidden(A_232,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2062])).

tff(c_2159,plain,(
    ! [A_234] :
      ( r2_hidden(A_234,'#skF_4')
      | ~ r2_hidden(A_234,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_2138])).

tff(c_2248,plain,(
    r2_hidden('#skF_1'('#skF_1'(k1_zfmisc_1(k2_relat_1('#skF_5')))),'#skF_4') ),
    inference(resolution,[status(thm)],[c_252,c_2159])).

tff(c_2256,plain,(
    m1_subset_1('#skF_1'('#skF_1'(k1_zfmisc_1(k2_relat_1('#skF_5')))),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2248,c_20])).

tff(c_2262,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_263,c_2256])).

tff(c_2263,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4061,plain,(
    ! [A_472,B_473,C_474] :
      ( k1_relset_1(A_472,B_473,C_474) = k1_relat_1(C_474)
      | ~ m1_subset_1(C_474,k1_zfmisc_1(k2_zfmisc_1(A_472,B_473))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_4074,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_4061])).

tff(c_48,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_4095,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4074,c_48])).

tff(c_3996,plain,(
    ! [C_459,A_460,B_461] :
      ( r2_hidden(C_459,A_460)
      | ~ r2_hidden(C_459,B_461)
      | ~ m1_subset_1(B_461,k1_zfmisc_1(A_460)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4220,plain,(
    ! [A_498,A_499,B_500] :
      ( r2_hidden(A_498,A_499)
      | ~ m1_subset_1(B_500,k1_zfmisc_1(A_499))
      | v1_xboole_0(B_500)
      | ~ m1_subset_1(A_498,B_500) ) ),
    inference(resolution,[status(thm)],[c_22,c_3996])).

tff(c_4230,plain,(
    ! [A_498] :
      ( r2_hidden(A_498,k2_zfmisc_1('#skF_3','#skF_4'))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(A_498,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_4220])).

tff(c_4232,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4230])).

tff(c_63,plain,(
    ! [A_58] :
      ( k1_relat_1(A_58) = k1_xboole_0
      | ~ v1_xboole_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_59,c_2])).

tff(c_4239,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4232,c_63])).

tff(c_4248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4095,c_4239])).

tff(c_4250,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_4230])).

tff(c_2556,plain,(
    ! [A_298,B_299,C_300] :
      ( k2_relset_1(A_298,B_299,C_300) = k2_relat_1(C_300)
      | ~ m1_subset_1(C_300,k1_zfmisc_1(k2_zfmisc_1(A_298,B_299))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2568,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_2556])).

tff(c_2415,plain,(
    ! [A_267,B_268] :
      ( r2_hidden(A_267,B_268)
      | v1_xboole_0(B_268)
      | ~ m1_subset_1(A_267,B_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2424,plain,(
    ! [A_267] :
      ( ~ m1_subset_1(A_267,'#skF_4')
      | v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(A_267,k2_relset_1('#skF_3','#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2415,c_46])).

tff(c_2432,plain,(
    ! [A_269] :
      ( ~ m1_subset_1(A_269,'#skF_4')
      | ~ m1_subset_1(A_269,k2_relset_1('#skF_3','#skF_4','#skF_5')) ) ),
    inference(splitLeft,[status(thm)],[c_2424])).

tff(c_2437,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_2432])).

tff(c_2570,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2568,c_2437])).

tff(c_2501,plain,(
    ! [A_290,B_291,C_292] :
      ( k1_relset_1(A_290,B_291,C_292) = k1_relat_1(C_292)
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(A_290,B_291))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2514,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_2501])).

tff(c_2516,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2514,c_48])).

tff(c_2443,plain,(
    ! [C_274,A_275,B_276] :
      ( r2_hidden(C_274,A_275)
      | ~ r2_hidden(C_274,B_276)
      | ~ m1_subset_1(B_276,k1_zfmisc_1(A_275)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2688,plain,(
    ! [A_317,A_318,B_319] :
      ( r2_hidden(A_317,A_318)
      | ~ m1_subset_1(B_319,k1_zfmisc_1(A_318))
      | v1_xboole_0(B_319)
      | ~ m1_subset_1(A_317,B_319) ) ),
    inference(resolution,[status(thm)],[c_22,c_2443])).

tff(c_2698,plain,(
    ! [A_317] :
      ( r2_hidden(A_317,k2_zfmisc_1('#skF_3','#skF_4'))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(A_317,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_2688])).

tff(c_2700,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2698])).

tff(c_2707,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2700,c_63])).

tff(c_2716,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2516,c_2707])).

tff(c_2718,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_2698])).

tff(c_3055,plain,(
    ! [D_362,C_363,B_364,A_365] :
      ( m1_subset_1(D_362,k1_zfmisc_1(k2_zfmisc_1(C_363,B_364)))
      | ~ r1_tarski(k2_relat_1(D_362),B_364)
      | ~ m1_subset_1(D_362,k1_zfmisc_1(k2_zfmisc_1(C_363,A_365))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3094,plain,(
    ! [B_369] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_369)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_369) ) ),
    inference(resolution,[status(thm)],[c_50,c_3055])).

tff(c_38,plain,(
    ! [C_32,B_30,A_29] :
      ( v1_xboole_0(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(B_30,A_29)))
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3107,plain,(
    ! [B_369] :
      ( v1_xboole_0('#skF_5')
      | ~ v1_xboole_0(B_369)
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_369) ) ),
    inference(resolution,[status(thm)],[c_3094,c_38])).

tff(c_3122,plain,(
    ! [B_370] :
      ( ~ v1_xboole_0(B_370)
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_370) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2718,c_3107])).

tff(c_3127,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_8,c_3122])).

tff(c_2294,plain,(
    ! [C_237,A_238,B_239] :
      ( v1_relat_1(C_237)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_238,B_239))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2302,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_2294])).

tff(c_2968,plain,(
    ! [A_356,B_357,C_358] :
      ( r2_hidden(k4_tarski('#skF_2'(A_356,B_357,C_358),A_356),C_358)
      | ~ r2_hidden(A_356,k9_relat_1(C_358,B_357))
      | ~ v1_relat_1(C_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3764,plain,(
    ! [A_441,B_442,C_443] :
      ( m1_subset_1(k4_tarski('#skF_2'(A_441,B_442,C_443),A_441),C_443)
      | ~ r2_hidden(A_441,k9_relat_1(C_443,B_442))
      | ~ v1_relat_1(C_443) ) ),
    inference(resolution,[status(thm)],[c_2968,c_20])).

tff(c_2719,plain,(
    ! [A_320] :
      ( r2_hidden(A_320,k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ m1_subset_1(A_320,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_2698])).

tff(c_2733,plain,(
    ! [B_5,A_4] :
      ( r2_hidden(B_5,'#skF_4')
      | ~ m1_subset_1(k4_tarski(A_4,B_5),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2719,c_12])).

tff(c_3790,plain,(
    ! [A_441,B_442] :
      ( r2_hidden(A_441,'#skF_4')
      | ~ r2_hidden(A_441,k9_relat_1('#skF_5',B_442))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3764,c_2733])).

tff(c_3833,plain,(
    ! [A_444,B_445] :
      ( r2_hidden(A_444,'#skF_4')
      | ~ r2_hidden(A_444,k9_relat_1('#skF_5',B_445)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2302,c_3790])).

tff(c_3857,plain,(
    ! [A_444] :
      ( r2_hidden(A_444,'#skF_4')
      | ~ r2_hidden(A_444,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_3833])).

tff(c_3865,plain,(
    ! [A_446] :
      ( r2_hidden(A_446,'#skF_4')
      | ~ r2_hidden(A_446,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2302,c_3857])).

tff(c_3885,plain,(
    ! [A_16] :
      ( r2_hidden(A_16,'#skF_4')
      | v1_xboole_0(k2_relat_1('#skF_5'))
      | ~ m1_subset_1(A_16,k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_22,c_3865])).

tff(c_3914,plain,(
    ! [A_448] :
      ( r2_hidden(A_448,'#skF_4')
      | ~ m1_subset_1(A_448,k2_relat_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3127,c_3885])).

tff(c_3934,plain,(
    r2_hidden('#skF_1'(k2_relat_1('#skF_5')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_3914])).

tff(c_3941,plain,(
    m1_subset_1('#skF_1'(k2_relat_1('#skF_5')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_3934,c_20])).

tff(c_3947,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2570,c_3941])).

tff(c_3948,plain,(
    v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2424])).

tff(c_3956,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3948,c_2])).

tff(c_4076,plain,(
    ! [A_475,B_476,C_477] :
      ( k2_relset_1(A_475,B_476,C_477) = k2_relat_1(C_477)
      | ~ m1_subset_1(C_477,k1_zfmisc_1(k2_zfmisc_1(A_475,B_476))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4082,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_4076])).

tff(c_4089,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3956,c_4082])).

tff(c_4547,plain,(
    ! [D_533,C_534,B_535,A_536] :
      ( m1_subset_1(D_533,k1_zfmisc_1(k2_zfmisc_1(C_534,B_535)))
      | ~ r1_tarski(k2_relat_1(D_533),B_535)
      | ~ m1_subset_1(D_533,k1_zfmisc_1(k2_zfmisc_1(C_534,A_536))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_4554,plain,(
    ! [B_535] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_535)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_535) ) ),
    inference(resolution,[status(thm)],[c_50,c_4547])).

tff(c_4563,plain,(
    ! [B_537] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_537)))
      | ~ r1_tarski(k1_xboole_0,B_537) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4089,c_4554])).

tff(c_4576,plain,(
    ! [B_537] :
      ( v1_xboole_0('#skF_5')
      | ~ v1_xboole_0(B_537)
      | ~ r1_tarski(k1_xboole_0,B_537) ) ),
    inference(resolution,[status(thm)],[c_4563,c_38])).

tff(c_4593,plain,(
    ! [B_538] :
      ( ~ v1_xboole_0(B_538)
      | ~ r1_tarski(k1_xboole_0,B_538) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4250,c_4576])).

tff(c_4597,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_4593])).

tff(c_4601,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2263,c_4597])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:12:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.31/2.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.43/2.07  
% 5.43/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.43/2.07  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 5.43/2.07  
% 5.43/2.07  %Foreground sorts:
% 5.43/2.07  
% 5.43/2.07  
% 5.43/2.07  %Background operators:
% 5.43/2.07  
% 5.43/2.07  
% 5.43/2.07  %Foreground operators:
% 5.43/2.07  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.43/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.43/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.43/2.07  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.43/2.07  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.43/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.43/2.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.43/2.07  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.43/2.07  tff('#skF_5', type, '#skF_5': $i).
% 5.43/2.07  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.43/2.07  tff('#skF_3', type, '#skF_3': $i).
% 5.43/2.07  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.43/2.07  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.43/2.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.43/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.43/2.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.43/2.07  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.43/2.07  tff('#skF_4', type, '#skF_4': $i).
% 5.43/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.43/2.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.43/2.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.43/2.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.43/2.07  
% 5.43/2.09  tff(f_44, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 5.43/2.09  tff(f_65, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 5.43/2.09  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.43/2.09  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.43/2.09  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 5.43/2.09  tff(f_126, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 5.43/2.09  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.43/2.09  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.43/2.09  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 5.43/2.09  tff(f_76, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 5.43/2.09  tff(f_55, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 5.43/2.09  tff(f_41, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 5.43/2.09  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.43/2.09  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.43/2.09  tff(f_105, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 5.43/2.09  tff(f_91, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 5.43/2.09  tff(c_16, plain, (![A_8]: (m1_subset_1('#skF_1'(A_8), A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.43/2.09  tff(c_24, plain, (![A_18]: (v1_xboole_0(k1_relat_1(A_18)) | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.43/2.09  tff(c_59, plain, (![A_58]: (v1_xboole_0(k1_relat_1(A_58)) | ~v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.43/2.09  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.43/2.09  tff(c_64, plain, (![A_59]: (k1_relat_1(A_59)=k1_xboole_0 | ~v1_xboole_0(A_59))), inference(resolution, [status(thm)], [c_59, c_2])).
% 5.43/2.09  tff(c_71, plain, (![A_63]: (k1_relat_1(k1_relat_1(A_63))=k1_xboole_0 | ~v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_24, c_64])).
% 5.43/2.09  tff(c_80, plain, (![A_63]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_relat_1(A_63)) | ~v1_xboole_0(A_63))), inference(superposition, [status(thm), theory('equality')], [c_71, c_24])).
% 5.43/2.09  tff(c_90, plain, (![A_64]: (~v1_xboole_0(k1_relat_1(A_64)) | ~v1_xboole_0(A_64))), inference(splitLeft, [status(thm)], [c_80])).
% 5.43/2.09  tff(c_97, plain, (![A_18]: (~v1_xboole_0(A_18))), inference(resolution, [status(thm)], [c_24, c_90])).
% 5.43/2.09  tff(c_22, plain, (![A_16, B_17]: (r2_hidden(A_16, B_17) | v1_xboole_0(B_17) | ~m1_subset_1(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.43/2.09  tff(c_127, plain, (![A_16, B_17]: (r2_hidden(A_16, B_17) | ~m1_subset_1(A_16, B_17))), inference(negUnitSimplification, [status(thm)], [c_97, c_22])).
% 5.43/2.09  tff(c_149, plain, (![C_81, A_82, B_83]: (r2_hidden(C_81, A_82) | ~r2_hidden(C_81, B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(A_82)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.43/2.09  tff(c_221, plain, (![A_108, A_109, B_110]: (r2_hidden(A_108, A_109) | ~m1_subset_1(B_110, k1_zfmisc_1(A_109)) | ~m1_subset_1(A_108, B_110))), inference(resolution, [status(thm)], [c_127, c_149])).
% 5.43/2.09  tff(c_247, plain, (![A_112, A_113]: (r2_hidden(A_112, A_113) | ~m1_subset_1(A_112, '#skF_1'(k1_zfmisc_1(A_113))))), inference(resolution, [status(thm)], [c_16, c_221])).
% 5.43/2.09  tff(c_253, plain, (![A_114]: (r2_hidden('#skF_1'('#skF_1'(k1_zfmisc_1(A_114))), A_114))), inference(resolution, [status(thm)], [c_16, c_247])).
% 5.43/2.09  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.43/2.09  tff(c_159, plain, (![A_88, B_89, C_90]: (k2_relset_1(A_88, B_89, C_90)=k2_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.43/2.09  tff(c_167, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_159])).
% 5.43/2.09  tff(c_46, plain, (![D_54]: (~r2_hidden(D_54, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_54, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.43/2.09  tff(c_171, plain, (![D_54]: (~r2_hidden(D_54, k2_relat_1('#skF_5')) | ~m1_subset_1(D_54, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_46])).
% 5.43/2.09  tff(c_263, plain, (~m1_subset_1('#skF_1'('#skF_1'(k1_zfmisc_1(k2_relat_1('#skF_5')))), '#skF_4')), inference(resolution, [status(thm)], [c_253, c_171])).
% 5.43/2.09  tff(c_252, plain, (![A_113]: (r2_hidden('#skF_1'('#skF_1'(k1_zfmisc_1(A_113))), A_113))), inference(resolution, [status(thm)], [c_16, c_247])).
% 5.43/2.09  tff(c_107, plain, (![C_68, A_69, B_70]: (v1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.43/2.09  tff(c_115, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_107])).
% 5.43/2.09  tff(c_34, plain, (![A_25]: (k9_relat_1(A_25, k1_relat_1(A_25))=k2_relat_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.43/2.09  tff(c_441, plain, (![A_136, B_137, C_138]: (r2_hidden(k4_tarski('#skF_2'(A_136, B_137, C_138), A_136), C_138) | ~r2_hidden(A_136, k9_relat_1(C_138, B_137)) | ~v1_relat_1(C_138))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.43/2.09  tff(c_20, plain, (![A_14, B_15]: (m1_subset_1(A_14, B_15) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.43/2.09  tff(c_1962, plain, (![A_229, B_230, C_231]: (m1_subset_1(k4_tarski('#skF_2'(A_229, B_230, C_231), A_229), C_231) | ~r2_hidden(A_229, k9_relat_1(C_231, B_230)) | ~v1_relat_1(C_231))), inference(resolution, [status(thm)], [c_441, c_20])).
% 5.43/2.09  tff(c_229, plain, (![A_111]: (r2_hidden(A_111, k2_zfmisc_1('#skF_3', '#skF_4')) | ~m1_subset_1(A_111, '#skF_5'))), inference(resolution, [status(thm)], [c_50, c_221])).
% 5.43/2.09  tff(c_12, plain, (![B_5, D_7, A_4, C_6]: (r2_hidden(B_5, D_7) | ~r2_hidden(k4_tarski(A_4, B_5), k2_zfmisc_1(C_6, D_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.43/2.09  tff(c_245, plain, (![B_5, A_4]: (r2_hidden(B_5, '#skF_4') | ~m1_subset_1(k4_tarski(A_4, B_5), '#skF_5'))), inference(resolution, [status(thm)], [c_229, c_12])).
% 5.43/2.09  tff(c_1999, plain, (![A_229, B_230]: (r2_hidden(A_229, '#skF_4') | ~r2_hidden(A_229, k9_relat_1('#skF_5', B_230)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1962, c_245])).
% 5.43/2.09  tff(c_2062, plain, (![A_232, B_233]: (r2_hidden(A_232, '#skF_4') | ~r2_hidden(A_232, k9_relat_1('#skF_5', B_233)))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_1999])).
% 5.43/2.09  tff(c_2138, plain, (![A_232]: (r2_hidden(A_232, '#skF_4') | ~r2_hidden(A_232, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2062])).
% 5.43/2.09  tff(c_2159, plain, (![A_234]: (r2_hidden(A_234, '#skF_4') | ~r2_hidden(A_234, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_2138])).
% 5.43/2.09  tff(c_2248, plain, (r2_hidden('#skF_1'('#skF_1'(k1_zfmisc_1(k2_relat_1('#skF_5')))), '#skF_4')), inference(resolution, [status(thm)], [c_252, c_2159])).
% 5.43/2.09  tff(c_2256, plain, (m1_subset_1('#skF_1'('#skF_1'(k1_zfmisc_1(k2_relat_1('#skF_5')))), '#skF_4')), inference(resolution, [status(thm)], [c_2248, c_20])).
% 5.43/2.09  tff(c_2262, plain, $false, inference(negUnitSimplification, [status(thm)], [c_263, c_2256])).
% 5.43/2.09  tff(c_2263, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_80])).
% 5.43/2.09  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.43/2.09  tff(c_4061, plain, (![A_472, B_473, C_474]: (k1_relset_1(A_472, B_473, C_474)=k1_relat_1(C_474) | ~m1_subset_1(C_474, k1_zfmisc_1(k2_zfmisc_1(A_472, B_473))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.43/2.09  tff(c_4074, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_4061])).
% 5.43/2.09  tff(c_48, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.43/2.09  tff(c_4095, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4074, c_48])).
% 5.43/2.09  tff(c_3996, plain, (![C_459, A_460, B_461]: (r2_hidden(C_459, A_460) | ~r2_hidden(C_459, B_461) | ~m1_subset_1(B_461, k1_zfmisc_1(A_460)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.43/2.09  tff(c_4220, plain, (![A_498, A_499, B_500]: (r2_hidden(A_498, A_499) | ~m1_subset_1(B_500, k1_zfmisc_1(A_499)) | v1_xboole_0(B_500) | ~m1_subset_1(A_498, B_500))), inference(resolution, [status(thm)], [c_22, c_3996])).
% 5.43/2.09  tff(c_4230, plain, (![A_498]: (r2_hidden(A_498, k2_zfmisc_1('#skF_3', '#skF_4')) | v1_xboole_0('#skF_5') | ~m1_subset_1(A_498, '#skF_5'))), inference(resolution, [status(thm)], [c_50, c_4220])).
% 5.43/2.09  tff(c_4232, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_4230])).
% 5.43/2.09  tff(c_63, plain, (![A_58]: (k1_relat_1(A_58)=k1_xboole_0 | ~v1_xboole_0(A_58))), inference(resolution, [status(thm)], [c_59, c_2])).
% 5.43/2.09  tff(c_4239, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_4232, c_63])).
% 5.43/2.09  tff(c_4248, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4095, c_4239])).
% 5.43/2.09  tff(c_4250, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_4230])).
% 5.43/2.09  tff(c_2556, plain, (![A_298, B_299, C_300]: (k2_relset_1(A_298, B_299, C_300)=k2_relat_1(C_300) | ~m1_subset_1(C_300, k1_zfmisc_1(k2_zfmisc_1(A_298, B_299))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.43/2.09  tff(c_2568, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_2556])).
% 5.43/2.09  tff(c_2415, plain, (![A_267, B_268]: (r2_hidden(A_267, B_268) | v1_xboole_0(B_268) | ~m1_subset_1(A_267, B_268))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.43/2.09  tff(c_2424, plain, (![A_267]: (~m1_subset_1(A_267, '#skF_4') | v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(A_267, k2_relset_1('#skF_3', '#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_2415, c_46])).
% 5.43/2.09  tff(c_2432, plain, (![A_269]: (~m1_subset_1(A_269, '#skF_4') | ~m1_subset_1(A_269, k2_relset_1('#skF_3', '#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_2424])).
% 5.43/2.09  tff(c_2437, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(resolution, [status(thm)], [c_16, c_2432])).
% 5.43/2.09  tff(c_2570, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2568, c_2437])).
% 5.43/2.09  tff(c_2501, plain, (![A_290, B_291, C_292]: (k1_relset_1(A_290, B_291, C_292)=k1_relat_1(C_292) | ~m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(A_290, B_291))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.43/2.09  tff(c_2514, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_2501])).
% 5.43/2.09  tff(c_2516, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2514, c_48])).
% 5.43/2.09  tff(c_2443, plain, (![C_274, A_275, B_276]: (r2_hidden(C_274, A_275) | ~r2_hidden(C_274, B_276) | ~m1_subset_1(B_276, k1_zfmisc_1(A_275)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.43/2.09  tff(c_2688, plain, (![A_317, A_318, B_319]: (r2_hidden(A_317, A_318) | ~m1_subset_1(B_319, k1_zfmisc_1(A_318)) | v1_xboole_0(B_319) | ~m1_subset_1(A_317, B_319))), inference(resolution, [status(thm)], [c_22, c_2443])).
% 5.43/2.09  tff(c_2698, plain, (![A_317]: (r2_hidden(A_317, k2_zfmisc_1('#skF_3', '#skF_4')) | v1_xboole_0('#skF_5') | ~m1_subset_1(A_317, '#skF_5'))), inference(resolution, [status(thm)], [c_50, c_2688])).
% 5.43/2.09  tff(c_2700, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_2698])).
% 5.43/2.09  tff(c_2707, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_2700, c_63])).
% 5.43/2.09  tff(c_2716, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2516, c_2707])).
% 5.43/2.09  tff(c_2718, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_2698])).
% 5.43/2.09  tff(c_3055, plain, (![D_362, C_363, B_364, A_365]: (m1_subset_1(D_362, k1_zfmisc_1(k2_zfmisc_1(C_363, B_364))) | ~r1_tarski(k2_relat_1(D_362), B_364) | ~m1_subset_1(D_362, k1_zfmisc_1(k2_zfmisc_1(C_363, A_365))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.43/2.09  tff(c_3094, plain, (![B_369]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_369))) | ~r1_tarski(k2_relat_1('#skF_5'), B_369))), inference(resolution, [status(thm)], [c_50, c_3055])).
% 5.43/2.09  tff(c_38, plain, (![C_32, B_30, A_29]: (v1_xboole_0(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(B_30, A_29))) | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.43/2.09  tff(c_3107, plain, (![B_369]: (v1_xboole_0('#skF_5') | ~v1_xboole_0(B_369) | ~r1_tarski(k2_relat_1('#skF_5'), B_369))), inference(resolution, [status(thm)], [c_3094, c_38])).
% 5.43/2.09  tff(c_3122, plain, (![B_370]: (~v1_xboole_0(B_370) | ~r1_tarski(k2_relat_1('#skF_5'), B_370))), inference(negUnitSimplification, [status(thm)], [c_2718, c_3107])).
% 5.43/2.09  tff(c_3127, plain, (~v1_xboole_0(k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_8, c_3122])).
% 5.43/2.09  tff(c_2294, plain, (![C_237, A_238, B_239]: (v1_relat_1(C_237) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_238, B_239))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.43/2.09  tff(c_2302, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_2294])).
% 5.43/2.09  tff(c_2968, plain, (![A_356, B_357, C_358]: (r2_hidden(k4_tarski('#skF_2'(A_356, B_357, C_358), A_356), C_358) | ~r2_hidden(A_356, k9_relat_1(C_358, B_357)) | ~v1_relat_1(C_358))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.43/2.09  tff(c_3764, plain, (![A_441, B_442, C_443]: (m1_subset_1(k4_tarski('#skF_2'(A_441, B_442, C_443), A_441), C_443) | ~r2_hidden(A_441, k9_relat_1(C_443, B_442)) | ~v1_relat_1(C_443))), inference(resolution, [status(thm)], [c_2968, c_20])).
% 5.43/2.09  tff(c_2719, plain, (![A_320]: (r2_hidden(A_320, k2_zfmisc_1('#skF_3', '#skF_4')) | ~m1_subset_1(A_320, '#skF_5'))), inference(splitRight, [status(thm)], [c_2698])).
% 5.43/2.09  tff(c_2733, plain, (![B_5, A_4]: (r2_hidden(B_5, '#skF_4') | ~m1_subset_1(k4_tarski(A_4, B_5), '#skF_5'))), inference(resolution, [status(thm)], [c_2719, c_12])).
% 5.43/2.09  tff(c_3790, plain, (![A_441, B_442]: (r2_hidden(A_441, '#skF_4') | ~r2_hidden(A_441, k9_relat_1('#skF_5', B_442)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_3764, c_2733])).
% 5.43/2.09  tff(c_3833, plain, (![A_444, B_445]: (r2_hidden(A_444, '#skF_4') | ~r2_hidden(A_444, k9_relat_1('#skF_5', B_445)))), inference(demodulation, [status(thm), theory('equality')], [c_2302, c_3790])).
% 5.43/2.09  tff(c_3857, plain, (![A_444]: (r2_hidden(A_444, '#skF_4') | ~r2_hidden(A_444, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_3833])).
% 5.43/2.09  tff(c_3865, plain, (![A_446]: (r2_hidden(A_446, '#skF_4') | ~r2_hidden(A_446, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_2302, c_3857])).
% 5.43/2.09  tff(c_3885, plain, (![A_16]: (r2_hidden(A_16, '#skF_4') | v1_xboole_0(k2_relat_1('#skF_5')) | ~m1_subset_1(A_16, k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_22, c_3865])).
% 5.43/2.09  tff(c_3914, plain, (![A_448]: (r2_hidden(A_448, '#skF_4') | ~m1_subset_1(A_448, k2_relat_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_3127, c_3885])).
% 5.43/2.09  tff(c_3934, plain, (r2_hidden('#skF_1'(k2_relat_1('#skF_5')), '#skF_4')), inference(resolution, [status(thm)], [c_16, c_3914])).
% 5.43/2.09  tff(c_3941, plain, (m1_subset_1('#skF_1'(k2_relat_1('#skF_5')), '#skF_4')), inference(resolution, [status(thm)], [c_3934, c_20])).
% 5.43/2.09  tff(c_3947, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2570, c_3941])).
% 5.43/2.09  tff(c_3948, plain, (v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_2424])).
% 5.43/2.09  tff(c_3956, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_3948, c_2])).
% 5.43/2.09  tff(c_4076, plain, (![A_475, B_476, C_477]: (k2_relset_1(A_475, B_476, C_477)=k2_relat_1(C_477) | ~m1_subset_1(C_477, k1_zfmisc_1(k2_zfmisc_1(A_475, B_476))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.43/2.09  tff(c_4082, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_4076])).
% 5.43/2.09  tff(c_4089, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3956, c_4082])).
% 5.43/2.09  tff(c_4547, plain, (![D_533, C_534, B_535, A_536]: (m1_subset_1(D_533, k1_zfmisc_1(k2_zfmisc_1(C_534, B_535))) | ~r1_tarski(k2_relat_1(D_533), B_535) | ~m1_subset_1(D_533, k1_zfmisc_1(k2_zfmisc_1(C_534, A_536))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.43/2.09  tff(c_4554, plain, (![B_535]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_535))) | ~r1_tarski(k2_relat_1('#skF_5'), B_535))), inference(resolution, [status(thm)], [c_50, c_4547])).
% 5.43/2.09  tff(c_4563, plain, (![B_537]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_537))) | ~r1_tarski(k1_xboole_0, B_537))), inference(demodulation, [status(thm), theory('equality')], [c_4089, c_4554])).
% 5.43/2.09  tff(c_4576, plain, (![B_537]: (v1_xboole_0('#skF_5') | ~v1_xboole_0(B_537) | ~r1_tarski(k1_xboole_0, B_537))), inference(resolution, [status(thm)], [c_4563, c_38])).
% 5.43/2.09  tff(c_4593, plain, (![B_538]: (~v1_xboole_0(B_538) | ~r1_tarski(k1_xboole_0, B_538))), inference(negUnitSimplification, [status(thm)], [c_4250, c_4576])).
% 5.43/2.09  tff(c_4597, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_4593])).
% 5.43/2.09  tff(c_4601, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2263, c_4597])).
% 5.43/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.43/2.09  
% 5.43/2.09  Inference rules
% 5.43/2.09  ----------------------
% 5.43/2.09  #Ref     : 0
% 5.43/2.09  #Sup     : 989
% 5.43/2.09  #Fact    : 0
% 5.43/2.09  #Define  : 0
% 5.43/2.09  #Split   : 14
% 5.43/2.09  #Chain   : 0
% 5.43/2.09  #Close   : 0
% 5.43/2.09  
% 5.43/2.09  Ordering : KBO
% 5.43/2.09  
% 5.43/2.09  Simplification rules
% 5.43/2.09  ----------------------
% 5.43/2.09  #Subsume      : 123
% 5.43/2.09  #Demod        : 207
% 5.43/2.09  #Tautology    : 207
% 5.43/2.09  #SimpNegUnit  : 27
% 5.43/2.09  #BackRed      : 27
% 5.43/2.09  
% 5.43/2.09  #Partial instantiations: 0
% 5.43/2.09  #Strategies tried      : 1
% 5.43/2.09  
% 5.43/2.09  Timing (in seconds)
% 5.43/2.09  ----------------------
% 5.43/2.10  Preprocessing        : 0.33
% 5.43/2.10  Parsing              : 0.18
% 5.43/2.10  CNF conversion       : 0.02
% 5.43/2.10  Main loop            : 0.93
% 5.43/2.10  Inferencing          : 0.32
% 5.43/2.10  Reduction            : 0.28
% 5.43/2.10  Demodulation         : 0.20
% 5.43/2.10  BG Simplification    : 0.04
% 5.43/2.10  Subsumption          : 0.20
% 5.43/2.10  Abstraction          : 0.05
% 5.43/2.10  MUC search           : 0.00
% 5.43/2.10  Cooper               : 0.00
% 5.43/2.10  Total                : 1.31
% 5.43/2.10  Index Insertion      : 0.00
% 5.43/2.10  Index Deletion       : 0.00
% 5.43/2.10  Index Matching       : 0.00
% 5.43/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
