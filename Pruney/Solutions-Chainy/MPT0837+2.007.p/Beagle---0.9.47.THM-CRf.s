%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:06 EST 2020

% Result     : Theorem 4.68s
% Output     : CNFRefutation 4.68s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 289 expanded)
%              Number of leaves         :   40 ( 112 expanded)
%              Depth                    :   10
%              Number of atoms          :  178 ( 632 expanded)
%              Number of equality atoms :   15 (  57 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ! [D] :
                    ( r2_hidden(D,k2_relset_1(B,A,C))
                  <=> ? [E] :
                        ( m1_subset_1(E,B)
                        & r2_hidden(k4_tarski(E,D),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2435,plain,(
    ! [A_474,B_475,C_476] :
      ( k2_relset_1(A_474,B_475,C_476) = k2_relat_1(C_476)
      | ~ m1_subset_1(C_476,k1_zfmisc_1(k2_zfmisc_1(A_474,B_475))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2448,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_2435])).

tff(c_536,plain,(
    ! [A_198,B_199,C_200] :
      ( k2_relset_1(A_198,B_199,C_200) = k2_relat_1(C_200)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_549,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_536])).

tff(c_58,plain,
    ( m1_subset_1('#skF_6','#skF_3')
    | r2_hidden('#skF_7',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_81,plain,(
    r2_hidden('#skF_7',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_554,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_81])).

tff(c_91,plain,(
    ! [C_89,A_90,B_91] :
      ( v1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_104,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_91])).

tff(c_158,plain,(
    ! [C_109,A_110,B_111] :
      ( v4_relat_1(C_109,A_110)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_171,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_158])).

tff(c_30,plain,(
    ! [B_24,A_23] :
      ( k7_relat_1(B_24,A_23) = B_24
      | ~ v4_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_176,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_171,c_30])).

tff(c_179,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_176])).

tff(c_28,plain,(
    ! [B_22,A_21] :
      ( k2_relat_1(k7_relat_1(B_22,A_21)) = k9_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_183,plain,
    ( k9_relat_1('#skF_4','#skF_3') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_28])).

tff(c_187,plain,(
    k9_relat_1('#skF_4','#skF_3') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_183])).

tff(c_1526,plain,(
    ! [A_344,B_345,C_346] :
      ( r2_hidden(k4_tarski('#skF_1'(A_344,B_345,C_346),A_344),C_346)
      | ~ r2_hidden(A_344,k9_relat_1(C_346,B_345))
      | ~ v1_relat_1(C_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_48,plain,(
    ! [E_79] :
      ( ~ r2_hidden('#skF_5',k2_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ r2_hidden(k4_tarski(E_79,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(E_79,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_738,plain,(
    ! [E_79] :
      ( ~ r2_hidden('#skF_5',k2_relat_1('#skF_4'))
      | ~ r2_hidden(k4_tarski(E_79,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(E_79,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_48])).

tff(c_739,plain,(
    ~ r2_hidden('#skF_5',k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_738])).

tff(c_8,plain,(
    ! [A_5] : k2_subset_1(A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_6] : m1_subset_1(k2_subset_1(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_59,plain,(
    ! [A_6] : m1_subset_1(A_6,k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_71,plain,(
    ! [A_84,B_85] :
      ( r1_tarski(A_84,B_85)
      | ~ m1_subset_1(A_84,k1_zfmisc_1(B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_79,plain,(
    ! [A_6] : r1_tarski(A_6,A_6) ),
    inference(resolution,[status(thm)],[c_59,c_71])).

tff(c_1157,plain,(
    ! [D_300,C_301,B_302,A_303] :
      ( m1_subset_1(D_300,k1_zfmisc_1(k2_zfmisc_1(C_301,B_302)))
      | ~ r1_tarski(k2_relat_1(D_300),B_302)
      | ~ m1_subset_1(D_300,k1_zfmisc_1(k2_zfmisc_1(C_301,A_303))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1173,plain,(
    ! [B_304] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_304)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_304) ) ),
    inference(resolution,[status(thm)],[c_42,c_1157])).

tff(c_625,plain,(
    ! [A_213,B_214,C_215] :
      ( r2_hidden('#skF_1'(A_213,B_214,C_215),B_214)
      | ~ r2_hidden(A_213,k9_relat_1(C_215,B_214))
      | ~ v1_relat_1(C_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_635,plain,(
    ! [A_220,B_221,C_222] :
      ( m1_subset_1('#skF_1'(A_220,B_221,C_222),B_221)
      | ~ r2_hidden(A_220,k9_relat_1(C_222,B_221))
      | ~ v1_relat_1(C_222) ) ),
    inference(resolution,[status(thm)],[c_625,c_14])).

tff(c_642,plain,(
    ! [A_220] :
      ( m1_subset_1('#skF_1'(A_220,'#skF_3','#skF_4'),'#skF_3')
      | ~ r2_hidden(A_220,k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_635])).

tff(c_648,plain,(
    ! [A_223] :
      ( m1_subset_1('#skF_1'(A_223,'#skF_3','#skF_4'),'#skF_3')
      | ~ r2_hidden(A_223,k2_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_642])).

tff(c_657,plain,(
    m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_554,c_648])).

tff(c_667,plain,(
    ! [A_230,B_231,C_232] :
      ( r2_hidden(k4_tarski('#skF_1'(A_230,B_231,C_232),A_230),C_232)
      | ~ r2_hidden(A_230,k9_relat_1(C_232,B_231))
      | ~ v1_relat_1(C_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_50,plain,(
    ! [E_79] :
      ( r2_hidden(k4_tarski('#skF_6','#skF_5'),'#skF_4')
      | ~ r2_hidden(k4_tarski(E_79,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(E_79,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_567,plain,(
    ! [E_79] :
      ( ~ r2_hidden(k4_tarski(E_79,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(E_79,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_678,plain,(
    ! [B_231] :
      ( ~ m1_subset_1('#skF_1'('#skF_7',B_231,'#skF_4'),'#skF_3')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_4',B_231))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_667,c_567])).

tff(c_730,plain,(
    ! [B_240] :
      ( ~ m1_subset_1('#skF_1'('#skF_7',B_240,'#skF_4'),'#skF_3')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_4',B_240)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_678])).

tff(c_733,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),'#skF_3')
    | ~ r2_hidden('#skF_7',k2_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_730])).

tff(c_736,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_554,c_657,c_733])).

tff(c_737,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_12,plain,(
    ! [C_10,A_7,B_8] :
      ( r2_hidden(C_10,A_7)
      | ~ r2_hidden(C_10,B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_782,plain,(
    ! [A_247] :
      ( r2_hidden(k4_tarski('#skF_6','#skF_5'),A_247)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_247)) ) ),
    inference(resolution,[status(thm)],[c_737,c_12])).

tff(c_4,plain,(
    ! [B_2,D_4,A_1,C_3] :
      ( r2_hidden(B_2,D_4)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_797,plain,(
    ! [D_4,C_3] :
      ( r2_hidden('#skF_5',D_4)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(C_3,D_4))) ) ),
    inference(resolution,[status(thm)],[c_782,c_4])).

tff(c_1223,plain,(
    ! [B_306] :
      ( r2_hidden('#skF_5',B_306)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_306) ) ),
    inference(resolution,[status(thm)],[c_1173,c_797])).

tff(c_1227,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_79,c_1223])).

tff(c_1231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_739,c_1227])).

tff(c_1232,plain,(
    ! [E_79] :
      ( ~ r2_hidden(k4_tarski(E_79,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(E_79,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_738])).

tff(c_1530,plain,(
    ! [B_345] :
      ( ~ m1_subset_1('#skF_1'('#skF_7',B_345,'#skF_4'),'#skF_3')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_4',B_345))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1526,c_1232])).

tff(c_1934,plain,(
    ! [B_398] :
      ( ~ m1_subset_1('#skF_1'('#skF_7',B_398,'#skF_4'),'#skF_3')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_4',B_398)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1530])).

tff(c_1937,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),'#skF_3')
    | ~ r2_hidden('#skF_7',k2_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_1934])).

tff(c_1939,plain,(
    ~ m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_554,c_1937])).

tff(c_1255,plain,(
    ! [A_308,B_309,C_310] :
      ( r2_hidden('#skF_1'(A_308,B_309,C_310),B_309)
      | ~ r2_hidden(A_308,k9_relat_1(C_310,B_309))
      | ~ v1_relat_1(C_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2117,plain,(
    ! [A_417,B_418,C_419] :
      ( m1_subset_1('#skF_1'(A_417,B_418,C_419),B_418)
      | ~ r2_hidden(A_417,k9_relat_1(C_419,B_418))
      | ~ v1_relat_1(C_419) ) ),
    inference(resolution,[status(thm)],[c_1255,c_14])).

tff(c_2142,plain,(
    ! [A_417] :
      ( m1_subset_1('#skF_1'(A_417,'#skF_3','#skF_4'),'#skF_3')
      | ~ r2_hidden(A_417,k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_2117])).

tff(c_2154,plain,(
    ! [A_420] :
      ( m1_subset_1('#skF_1'(A_420,'#skF_3','#skF_4'),'#skF_3')
      | ~ r2_hidden(A_420,k2_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_2142])).

tff(c_2188,plain,(
    m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_554,c_2154])).

tff(c_2200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1939,c_2188])).

tff(c_2202,plain,(
    ~ r2_hidden('#skF_7',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_54,plain,
    ( ~ r2_hidden('#skF_5',k2_relset_1('#skF_3','#skF_2','#skF_4'))
    | r2_hidden('#skF_7',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2333,plain,(
    ~ r2_hidden('#skF_5',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_2202,c_54])).

tff(c_2451,plain,(
    ~ r2_hidden('#skF_5',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2448,c_2333])).

tff(c_2859,plain,(
    ! [D_545,C_546,B_547,A_548] :
      ( m1_subset_1(D_545,k1_zfmisc_1(k2_zfmisc_1(C_546,B_547)))
      | ~ r1_tarski(k2_relat_1(D_545),B_547)
      | ~ m1_subset_1(D_545,k1_zfmisc_1(k2_zfmisc_1(C_546,A_548))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2875,plain,(
    ! [B_549] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_549)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_549) ) ),
    inference(resolution,[status(thm)],[c_42,c_2859])).

tff(c_56,plain,
    ( r2_hidden(k4_tarski('#skF_6','#skF_5'),'#skF_4')
    | r2_hidden('#skF_7',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2203,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_2202,c_56])).

tff(c_2358,plain,(
    ! [C_459,A_460,B_461] :
      ( r2_hidden(C_459,A_460)
      | ~ r2_hidden(C_459,B_461)
      | ~ m1_subset_1(B_461,k1_zfmisc_1(A_460)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2362,plain,(
    ! [A_462] :
      ( r2_hidden(k4_tarski('#skF_6','#skF_5'),A_462)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_462)) ) ),
    inference(resolution,[status(thm)],[c_2203,c_2358])).

tff(c_2373,plain,(
    ! [D_4,C_3] :
      ( r2_hidden('#skF_5',D_4)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(C_3,D_4))) ) ),
    inference(resolution,[status(thm)],[c_2362,c_4])).

tff(c_2929,plain,(
    ! [B_551] :
      ( r2_hidden('#skF_5',B_551)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_551) ) ),
    inference(resolution,[status(thm)],[c_2875,c_2373])).

tff(c_2933,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_79,c_2929])).

tff(c_2937,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2451,c_2933])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:01:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.68/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.88  
% 4.68/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.89  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 4.68/1.89  
% 4.68/1.89  %Foreground sorts:
% 4.68/1.89  
% 4.68/1.89  
% 4.68/1.89  %Background operators:
% 4.68/1.89  
% 4.68/1.89  
% 4.68/1.89  %Foreground operators:
% 4.68/1.89  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.68/1.89  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.68/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.68/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.68/1.89  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.68/1.89  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.68/1.89  tff('#skF_7', type, '#skF_7': $i).
% 4.68/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.68/1.89  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.68/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.68/1.89  tff('#skF_6', type, '#skF_6': $i).
% 4.68/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.68/1.89  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.68/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.68/1.89  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.68/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.68/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.68/1.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.68/1.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.68/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.68/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.68/1.89  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.68/1.89  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.68/1.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.68/1.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.68/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.68/1.89  
% 4.68/1.91  tff(f_110, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (![D]: (r2_hidden(D, k2_relset_1(B, A, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(E, D), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relset_1)).
% 4.68/1.91  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.68/1.91  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.68/1.91  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.68/1.91  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 4.68/1.91  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 4.68/1.91  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 4.68/1.91  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.68/1.91  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.68/1.91  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.68/1.91  tff(f_91, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 4.68/1.91  tff(f_46, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.68/1.91  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.68/1.91  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 4.68/1.91  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.68/1.91  tff(c_2435, plain, (![A_474, B_475, C_476]: (k2_relset_1(A_474, B_475, C_476)=k2_relat_1(C_476) | ~m1_subset_1(C_476, k1_zfmisc_1(k2_zfmisc_1(A_474, B_475))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.68/1.91  tff(c_2448, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_2435])).
% 4.68/1.91  tff(c_536, plain, (![A_198, B_199, C_200]: (k2_relset_1(A_198, B_199, C_200)=k2_relat_1(C_200) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.68/1.91  tff(c_549, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_536])).
% 4.68/1.91  tff(c_58, plain, (m1_subset_1('#skF_6', '#skF_3') | r2_hidden('#skF_7', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.68/1.91  tff(c_81, plain, (r2_hidden('#skF_7', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_58])).
% 4.68/1.91  tff(c_554, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_549, c_81])).
% 4.68/1.91  tff(c_91, plain, (![C_89, A_90, B_91]: (v1_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.68/1.91  tff(c_104, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_91])).
% 4.68/1.91  tff(c_158, plain, (![C_109, A_110, B_111]: (v4_relat_1(C_109, A_110) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.68/1.91  tff(c_171, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_158])).
% 4.68/1.91  tff(c_30, plain, (![B_24, A_23]: (k7_relat_1(B_24, A_23)=B_24 | ~v4_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.68/1.91  tff(c_176, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_171, c_30])).
% 4.68/1.91  tff(c_179, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_176])).
% 4.68/1.91  tff(c_28, plain, (![B_22, A_21]: (k2_relat_1(k7_relat_1(B_22, A_21))=k9_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.68/1.91  tff(c_183, plain, (k9_relat_1('#skF_4', '#skF_3')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_179, c_28])).
% 4.68/1.91  tff(c_187, plain, (k9_relat_1('#skF_4', '#skF_3')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_183])).
% 4.68/1.91  tff(c_1526, plain, (![A_344, B_345, C_346]: (r2_hidden(k4_tarski('#skF_1'(A_344, B_345, C_346), A_344), C_346) | ~r2_hidden(A_344, k9_relat_1(C_346, B_345)) | ~v1_relat_1(C_346))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.68/1.91  tff(c_48, plain, (![E_79]: (~r2_hidden('#skF_5', k2_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~r2_hidden(k4_tarski(E_79, '#skF_7'), '#skF_4') | ~m1_subset_1(E_79, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.68/1.91  tff(c_738, plain, (![E_79]: (~r2_hidden('#skF_5', k2_relat_1('#skF_4')) | ~r2_hidden(k4_tarski(E_79, '#skF_7'), '#skF_4') | ~m1_subset_1(E_79, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_549, c_48])).
% 4.68/1.91  tff(c_739, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_738])).
% 4.68/1.91  tff(c_8, plain, (![A_5]: (k2_subset_1(A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.68/1.91  tff(c_10, plain, (![A_6]: (m1_subset_1(k2_subset_1(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.68/1.91  tff(c_59, plain, (![A_6]: (m1_subset_1(A_6, k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 4.68/1.91  tff(c_71, plain, (![A_84, B_85]: (r1_tarski(A_84, B_85) | ~m1_subset_1(A_84, k1_zfmisc_1(B_85)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.68/1.91  tff(c_79, plain, (![A_6]: (r1_tarski(A_6, A_6))), inference(resolution, [status(thm)], [c_59, c_71])).
% 4.68/1.91  tff(c_1157, plain, (![D_300, C_301, B_302, A_303]: (m1_subset_1(D_300, k1_zfmisc_1(k2_zfmisc_1(C_301, B_302))) | ~r1_tarski(k2_relat_1(D_300), B_302) | ~m1_subset_1(D_300, k1_zfmisc_1(k2_zfmisc_1(C_301, A_303))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.68/1.91  tff(c_1173, plain, (![B_304]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_304))) | ~r1_tarski(k2_relat_1('#skF_4'), B_304))), inference(resolution, [status(thm)], [c_42, c_1157])).
% 4.68/1.91  tff(c_625, plain, (![A_213, B_214, C_215]: (r2_hidden('#skF_1'(A_213, B_214, C_215), B_214) | ~r2_hidden(A_213, k9_relat_1(C_215, B_214)) | ~v1_relat_1(C_215))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.68/1.91  tff(c_14, plain, (![A_11, B_12]: (m1_subset_1(A_11, B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.68/1.91  tff(c_635, plain, (![A_220, B_221, C_222]: (m1_subset_1('#skF_1'(A_220, B_221, C_222), B_221) | ~r2_hidden(A_220, k9_relat_1(C_222, B_221)) | ~v1_relat_1(C_222))), inference(resolution, [status(thm)], [c_625, c_14])).
% 4.68/1.91  tff(c_642, plain, (![A_220]: (m1_subset_1('#skF_1'(A_220, '#skF_3', '#skF_4'), '#skF_3') | ~r2_hidden(A_220, k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_187, c_635])).
% 4.68/1.91  tff(c_648, plain, (![A_223]: (m1_subset_1('#skF_1'(A_223, '#skF_3', '#skF_4'), '#skF_3') | ~r2_hidden(A_223, k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_642])).
% 4.68/1.91  tff(c_657, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_554, c_648])).
% 4.68/1.91  tff(c_667, plain, (![A_230, B_231, C_232]: (r2_hidden(k4_tarski('#skF_1'(A_230, B_231, C_232), A_230), C_232) | ~r2_hidden(A_230, k9_relat_1(C_232, B_231)) | ~v1_relat_1(C_232))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.68/1.91  tff(c_50, plain, (![E_79]: (r2_hidden(k4_tarski('#skF_6', '#skF_5'), '#skF_4') | ~r2_hidden(k4_tarski(E_79, '#skF_7'), '#skF_4') | ~m1_subset_1(E_79, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.68/1.91  tff(c_567, plain, (![E_79]: (~r2_hidden(k4_tarski(E_79, '#skF_7'), '#skF_4') | ~m1_subset_1(E_79, '#skF_3'))), inference(splitLeft, [status(thm)], [c_50])).
% 4.68/1.91  tff(c_678, plain, (![B_231]: (~m1_subset_1('#skF_1'('#skF_7', B_231, '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k9_relat_1('#skF_4', B_231)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_667, c_567])).
% 4.68/1.91  tff(c_730, plain, (![B_240]: (~m1_subset_1('#skF_1'('#skF_7', B_240, '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k9_relat_1('#skF_4', B_240)))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_678])).
% 4.68/1.91  tff(c_733, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k2_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_187, c_730])).
% 4.68/1.91  tff(c_736, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_554, c_657, c_733])).
% 4.68/1.91  tff(c_737, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 4.68/1.91  tff(c_12, plain, (![C_10, A_7, B_8]: (r2_hidden(C_10, A_7) | ~r2_hidden(C_10, B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.68/1.91  tff(c_782, plain, (![A_247]: (r2_hidden(k4_tarski('#skF_6', '#skF_5'), A_247) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_247)))), inference(resolution, [status(thm)], [c_737, c_12])).
% 4.68/1.91  tff(c_4, plain, (![B_2, D_4, A_1, C_3]: (r2_hidden(B_2, D_4) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.68/1.91  tff(c_797, plain, (![D_4, C_3]: (r2_hidden('#skF_5', D_4) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(C_3, D_4))))), inference(resolution, [status(thm)], [c_782, c_4])).
% 4.68/1.91  tff(c_1223, plain, (![B_306]: (r2_hidden('#skF_5', B_306) | ~r1_tarski(k2_relat_1('#skF_4'), B_306))), inference(resolution, [status(thm)], [c_1173, c_797])).
% 4.68/1.91  tff(c_1227, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_79, c_1223])).
% 4.68/1.91  tff(c_1231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_739, c_1227])).
% 4.68/1.91  tff(c_1232, plain, (![E_79]: (~r2_hidden(k4_tarski(E_79, '#skF_7'), '#skF_4') | ~m1_subset_1(E_79, '#skF_3'))), inference(splitRight, [status(thm)], [c_738])).
% 4.68/1.91  tff(c_1530, plain, (![B_345]: (~m1_subset_1('#skF_1'('#skF_7', B_345, '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k9_relat_1('#skF_4', B_345)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1526, c_1232])).
% 4.68/1.91  tff(c_1934, plain, (![B_398]: (~m1_subset_1('#skF_1'('#skF_7', B_398, '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k9_relat_1('#skF_4', B_398)))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_1530])).
% 4.68/1.91  tff(c_1937, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k2_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_187, c_1934])).
% 4.68/1.91  tff(c_1939, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_554, c_1937])).
% 4.68/1.91  tff(c_1255, plain, (![A_308, B_309, C_310]: (r2_hidden('#skF_1'(A_308, B_309, C_310), B_309) | ~r2_hidden(A_308, k9_relat_1(C_310, B_309)) | ~v1_relat_1(C_310))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.68/1.91  tff(c_2117, plain, (![A_417, B_418, C_419]: (m1_subset_1('#skF_1'(A_417, B_418, C_419), B_418) | ~r2_hidden(A_417, k9_relat_1(C_419, B_418)) | ~v1_relat_1(C_419))), inference(resolution, [status(thm)], [c_1255, c_14])).
% 4.68/1.91  tff(c_2142, plain, (![A_417]: (m1_subset_1('#skF_1'(A_417, '#skF_3', '#skF_4'), '#skF_3') | ~r2_hidden(A_417, k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_187, c_2117])).
% 4.68/1.91  tff(c_2154, plain, (![A_420]: (m1_subset_1('#skF_1'(A_420, '#skF_3', '#skF_4'), '#skF_3') | ~r2_hidden(A_420, k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_2142])).
% 4.68/1.91  tff(c_2188, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_554, c_2154])).
% 4.68/1.91  tff(c_2200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1939, c_2188])).
% 4.68/1.91  tff(c_2202, plain, (~r2_hidden('#skF_7', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_58])).
% 4.68/1.91  tff(c_54, plain, (~r2_hidden('#skF_5', k2_relset_1('#skF_3', '#skF_2', '#skF_4')) | r2_hidden('#skF_7', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.68/1.91  tff(c_2333, plain, (~r2_hidden('#skF_5', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_2202, c_54])).
% 4.68/1.91  tff(c_2451, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2448, c_2333])).
% 4.68/1.91  tff(c_2859, plain, (![D_545, C_546, B_547, A_548]: (m1_subset_1(D_545, k1_zfmisc_1(k2_zfmisc_1(C_546, B_547))) | ~r1_tarski(k2_relat_1(D_545), B_547) | ~m1_subset_1(D_545, k1_zfmisc_1(k2_zfmisc_1(C_546, A_548))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.68/1.91  tff(c_2875, plain, (![B_549]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_549))) | ~r1_tarski(k2_relat_1('#skF_4'), B_549))), inference(resolution, [status(thm)], [c_42, c_2859])).
% 4.68/1.91  tff(c_56, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_5'), '#skF_4') | r2_hidden('#skF_7', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.68/1.91  tff(c_2203, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_2202, c_56])).
% 4.68/1.91  tff(c_2358, plain, (![C_459, A_460, B_461]: (r2_hidden(C_459, A_460) | ~r2_hidden(C_459, B_461) | ~m1_subset_1(B_461, k1_zfmisc_1(A_460)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.68/1.91  tff(c_2362, plain, (![A_462]: (r2_hidden(k4_tarski('#skF_6', '#skF_5'), A_462) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_462)))), inference(resolution, [status(thm)], [c_2203, c_2358])).
% 4.68/1.91  tff(c_2373, plain, (![D_4, C_3]: (r2_hidden('#skF_5', D_4) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(C_3, D_4))))), inference(resolution, [status(thm)], [c_2362, c_4])).
% 4.68/1.91  tff(c_2929, plain, (![B_551]: (r2_hidden('#skF_5', B_551) | ~r1_tarski(k2_relat_1('#skF_4'), B_551))), inference(resolution, [status(thm)], [c_2875, c_2373])).
% 4.68/1.91  tff(c_2933, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_79, c_2929])).
% 4.68/1.91  tff(c_2937, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2451, c_2933])).
% 4.68/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.91  
% 4.68/1.91  Inference rules
% 4.68/1.91  ----------------------
% 4.68/1.91  #Ref     : 0
% 4.68/1.91  #Sup     : 592
% 4.68/1.91  #Fact    : 0
% 4.68/1.91  #Define  : 0
% 4.68/1.91  #Split   : 14
% 4.68/1.91  #Chain   : 0
% 4.68/1.91  #Close   : 0
% 4.68/1.91  
% 4.68/1.91  Ordering : KBO
% 4.68/1.91  
% 4.68/1.91  Simplification rules
% 4.68/1.91  ----------------------
% 4.68/1.91  #Subsume      : 60
% 4.68/1.91  #Demod        : 165
% 4.68/1.91  #Tautology    : 157
% 4.68/1.91  #SimpNegUnit  : 5
% 4.68/1.91  #BackRed      : 11
% 4.68/1.91  
% 4.68/1.91  #Partial instantiations: 0
% 4.68/1.91  #Strategies tried      : 1
% 4.68/1.91  
% 4.68/1.91  Timing (in seconds)
% 4.68/1.91  ----------------------
% 4.68/1.91  Preprocessing        : 0.33
% 4.68/1.91  Parsing              : 0.17
% 4.68/1.91  CNF conversion       : 0.03
% 4.68/1.91  Main loop            : 0.80
% 4.68/1.91  Inferencing          : 0.30
% 4.68/1.91  Reduction            : 0.25
% 5.02/1.91  Demodulation         : 0.17
% 5.02/1.91  BG Simplification    : 0.03
% 5.02/1.91  Subsumption          : 0.15
% 5.02/1.91  Abstraction          : 0.03
% 5.02/1.91  MUC search           : 0.00
% 5.02/1.91  Cooper               : 0.00
% 5.02/1.91  Total                : 1.18
% 5.02/1.91  Index Insertion      : 0.00
% 5.02/1.91  Index Deletion       : 0.00
% 5.02/1.91  Index Matching       : 0.00
% 5.02/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
