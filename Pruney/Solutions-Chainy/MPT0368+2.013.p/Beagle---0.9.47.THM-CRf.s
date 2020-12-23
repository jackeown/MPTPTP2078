%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:49 EST 2020

% Result     : Theorem 5.34s
% Output     : CNFRefutation 5.34s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 256 expanded)
%              Number of leaves         :   22 (  93 expanded)
%              Depth                    :   15
%              Number of atoms          :  217 ( 627 expanded)
%              Number of equality atoms :   15 (  48 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( ! [C] :
              ( m1_subset_1(C,A)
             => r2_hidden(C,B) )
         => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                <=> r2_hidden(D,C) ) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_3293,plain,(
    ! [B_343,A_344] :
      ( m1_subset_1(B_343,A_344)
      | ~ v1_xboole_0(B_343)
      | ~ v1_xboole_0(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_144,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_2'(A_52,B_53),A_52)
      | r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_159,plain,(
    ! [A_52] : r1_tarski(A_52,A_52) ),
    inference(resolution,[status(thm)],[c_144,c_8])).

tff(c_14,plain,(
    ! [C_14,A_10] :
      ( r2_hidden(C_14,k1_zfmisc_1(A_10))
      | ~ r1_tarski(C_14,A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [C_14,A_10] :
      ( r1_tarski(C_14,A_10)
      | ~ r2_hidden(C_14,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_600,plain,(
    ! [A_103,B_104] :
      ( r1_tarski('#skF_2'(k1_zfmisc_1(A_103),B_104),A_103)
      | r1_tarski(k1_zfmisc_1(A_103),B_104) ) ),
    inference(resolution,[status(thm)],[c_144,c_12])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_171,plain,(
    ! [C_59,B_60,A_61] :
      ( r2_hidden(C_59,B_60)
      | ~ r2_hidden(C_59,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_187,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_1'(A_62),B_63)
      | ~ r1_tarski(A_62,B_63)
      | v1_xboole_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_4,c_171])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_203,plain,(
    ! [B_63,A_62] :
      ( ~ v1_xboole_0(B_63)
      | ~ r1_tarski(A_62,B_63)
      | v1_xboole_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_187,c_2])).

tff(c_1111,plain,(
    ! [A_164,B_165] :
      ( ~ v1_xboole_0(A_164)
      | v1_xboole_0('#skF_2'(k1_zfmisc_1(A_164),B_165))
      | r1_tarski(k1_zfmisc_1(A_164),B_165) ) ),
    inference(resolution,[status(thm)],[c_600,c_203])).

tff(c_162,plain,(
    ! [A_52,B_53] :
      ( ~ v1_xboole_0(A_52)
      | r1_tarski(A_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_144,c_2])).

tff(c_109,plain,(
    ! [A_47,B_48] :
      ( ~ r2_hidden('#skF_2'(A_47,B_48),B_48)
      | r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_614,plain,(
    ! [A_108,A_109] :
      ( r1_tarski(A_108,k1_zfmisc_1(A_109))
      | ~ r1_tarski('#skF_2'(A_108,k1_zfmisc_1(A_109)),A_109) ) ),
    inference(resolution,[status(thm)],[c_14,c_109])).

tff(c_625,plain,(
    ! [A_108,B_53] :
      ( r1_tarski(A_108,k1_zfmisc_1(B_53))
      | ~ v1_xboole_0('#skF_2'(A_108,k1_zfmisc_1(B_53))) ) ),
    inference(resolution,[status(thm)],[c_162,c_614])).

tff(c_1122,plain,(
    ! [A_167,B_168] :
      ( ~ v1_xboole_0(A_167)
      | r1_tarski(k1_zfmisc_1(A_167),k1_zfmisc_1(B_168)) ) ),
    inference(resolution,[status(thm)],[c_1111,c_625])).

tff(c_1135,plain,(
    ! [B_168,A_167] :
      ( ~ v1_xboole_0(k1_zfmisc_1(B_168))
      | v1_xboole_0(k1_zfmisc_1(A_167))
      | ~ v1_xboole_0(A_167) ) ),
    inference(resolution,[status(thm)],[c_1122,c_203])).

tff(c_1136,plain,(
    ! [B_168] : ~ v1_xboole_0(k1_zfmisc_1(B_168)) ),
    inference(splitLeft,[status(thm)],[c_1135])).

tff(c_89,plain,(
    ! [B_44,A_45] :
      ( m1_subset_1(B_44,A_45)
      | ~ r2_hidden(B_44,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_99,plain,(
    ! [C_14,A_10] :
      ( m1_subset_1(C_14,k1_zfmisc_1(A_10))
      | v1_xboole_0(k1_zfmisc_1(A_10))
      | ~ r1_tarski(C_14,A_10) ) ),
    inference(resolution,[status(thm)],[c_14,c_89])).

tff(c_1138,plain,(
    ! [C_14,A_10] :
      ( m1_subset_1(C_14,k1_zfmisc_1(A_10))
      | ~ r1_tarski(C_14,A_10) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1136,c_99])).

tff(c_44,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_34,plain,(
    ! [A_21,B_22,C_26] :
      ( m1_subset_1('#skF_5'(A_21,B_22,C_26),A_21)
      | C_26 = B_22
      | ~ m1_subset_1(C_26,k1_zfmisc_1(A_21))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_46,plain,(
    ! [C_29] :
      ( r2_hidden(C_29,'#skF_7')
      | ~ m1_subset_1(C_29,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_204,plain,(
    ! [C_64,A_65,B_66] :
      ( r2_hidden(C_64,A_65)
      | ~ r2_hidden(C_64,B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_341,plain,(
    ! [C_80,A_81] :
      ( r2_hidden(C_80,A_81)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_81))
      | ~ m1_subset_1(C_80,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_204])).

tff(c_348,plain,(
    ! [C_80] :
      ( r2_hidden(C_80,'#skF_6')
      | ~ m1_subset_1(C_80,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_341])).

tff(c_1449,plain,(
    ! [A_191,B_192,C_193] :
      ( ~ r2_hidden('#skF_5'(A_191,B_192,C_193),C_193)
      | ~ r2_hidden('#skF_5'(A_191,B_192,C_193),B_192)
      | C_193 = B_192
      | ~ m1_subset_1(C_193,k1_zfmisc_1(A_191))
      | ~ m1_subset_1(B_192,k1_zfmisc_1(A_191)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1529,plain,(
    ! [A_198,B_199] :
      ( ~ r2_hidden('#skF_5'(A_198,B_199,'#skF_7'),B_199)
      | B_199 = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_198))
      | ~ m1_subset_1(B_199,k1_zfmisc_1(A_198))
      | ~ m1_subset_1('#skF_5'(A_198,B_199,'#skF_7'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_1449])).

tff(c_1555,plain,(
    ! [A_198] :
      ( '#skF_7' = '#skF_6'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_198))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_198))
      | ~ m1_subset_1('#skF_5'(A_198,'#skF_6','#skF_7'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_348,c_1529])).

tff(c_1725,plain,(
    ! [A_217] :
      ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_217))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_217))
      | ~ m1_subset_1('#skF_5'(A_217,'#skF_6','#skF_7'),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1555])).

tff(c_1729,plain,
    ( '#skF_7' = '#skF_6'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_1725])).

tff(c_1735,plain,
    ( '#skF_7' = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1729])).

tff(c_1736,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1735])).

tff(c_1743,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_1138,c_1736])).

tff(c_1751,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_1743])).

tff(c_1753,plain,(
    ! [A_218] :
      ( v1_xboole_0(k1_zfmisc_1(A_218))
      | ~ v1_xboole_0(A_218) ) ),
    inference(splitRight,[status(thm)],[c_1135])).

tff(c_79,plain,(
    ! [C_40,A_41] :
      ( r2_hidden(C_40,k1_zfmisc_1(A_41))
      | ~ r1_tarski(C_40,A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_87,plain,(
    ! [A_41,C_40] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_41))
      | ~ r1_tarski(C_40,A_41) ) ),
    inference(resolution,[status(thm)],[c_79,c_2])).

tff(c_1761,plain,(
    ! [C_219,A_220] :
      ( ~ r1_tarski(C_219,A_220)
      | ~ v1_xboole_0(A_220) ) ),
    inference(resolution,[status(thm)],[c_1753,c_87])).

tff(c_1805,plain,(
    ! [A_52] : ~ v1_xboole_0(A_52) ),
    inference(resolution,[status(thm)],[c_159,c_1761])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( m1_subset_1(B_16,A_15)
      | ~ r2_hidden(B_16,A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1901,plain,(
    ! [B_230,A_231] :
      ( m1_subset_1(B_230,A_231)
      | ~ r2_hidden(B_230,A_231) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1805,c_24])).

tff(c_1949,plain,(
    ! [C_14,A_10] :
      ( m1_subset_1(C_14,k1_zfmisc_1(A_10))
      | ~ r1_tarski(C_14,A_10) ) ),
    inference(resolution,[status(thm)],[c_14,c_1901])).

tff(c_50,plain,(
    ! [C_32] :
      ( r2_hidden(C_32,'#skF_7')
      | ~ m1_subset_1(C_32,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_54,plain,(
    ! [C_32] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ m1_subset_1(C_32,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_50,c_2])).

tff(c_55,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_98,plain,(
    ! [C_29] :
      ( m1_subset_1(C_29,'#skF_7')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(C_29,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_89])).

tff(c_103,plain,(
    ! [C_29] :
      ( m1_subset_1(C_29,'#skF_7')
      | ~ m1_subset_1(C_29,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_98])).

tff(c_61,plain,(
    ! [B_34,A_35] :
      ( v1_xboole_0(B_34)
      | ~ m1_subset_1(B_34,A_35)
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_64,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_48,c_61])).

tff(c_67,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_64])).

tff(c_125,plain,(
    ! [B_50,A_51] :
      ( r2_hidden(B_50,A_51)
      | ~ m1_subset_1(B_50,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_324,plain,(
    ! [B_78,A_79] :
      ( r1_tarski(B_78,A_79)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_79))
      | v1_xboole_0(k1_zfmisc_1(A_79)) ) ),
    inference(resolution,[status(thm)],[c_125,c_12])).

tff(c_335,plain,
    ( r1_tarski('#skF_7','#skF_6')
    | v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_48,c_324])).

tff(c_340,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_335])).

tff(c_26,plain,(
    ! [B_16,A_15] :
      ( r2_hidden(B_16,A_15)
      | ~ m1_subset_1(B_16,A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_651,plain,(
    ! [B_120,B_121,A_122] :
      ( r2_hidden(B_120,B_121)
      | ~ r1_tarski(A_122,B_121)
      | ~ m1_subset_1(B_120,A_122)
      | v1_xboole_0(A_122) ) ),
    inference(resolution,[status(thm)],[c_26,c_171])).

tff(c_661,plain,(
    ! [B_120] :
      ( r2_hidden(B_120,'#skF_6')
      | ~ m1_subset_1(B_120,'#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_340,c_651])).

tff(c_675,plain,(
    ! [B_120] :
      ( r2_hidden(B_120,'#skF_6')
      | ~ m1_subset_1(B_120,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_661])).

tff(c_2072,plain,(
    ! [A_246,B_247,C_248] :
      ( ~ r2_hidden('#skF_5'(A_246,B_247,C_248),C_248)
      | ~ r2_hidden('#skF_5'(A_246,B_247,C_248),B_247)
      | C_248 = B_247
      | ~ m1_subset_1(C_248,k1_zfmisc_1(A_246))
      | ~ m1_subset_1(B_247,k1_zfmisc_1(A_246)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2139,plain,(
    ! [A_251,B_252] :
      ( ~ r2_hidden('#skF_5'(A_251,B_252,'#skF_7'),B_252)
      | B_252 = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_251))
      | ~ m1_subset_1(B_252,k1_zfmisc_1(A_251))
      | ~ m1_subset_1('#skF_5'(A_251,B_252,'#skF_7'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_2072])).

tff(c_2157,plain,(
    ! [A_251] :
      ( '#skF_7' = '#skF_6'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_251))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_251))
      | ~ m1_subset_1('#skF_5'(A_251,'#skF_6','#skF_7'),'#skF_6')
      | ~ m1_subset_1('#skF_5'(A_251,'#skF_6','#skF_7'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_675,c_2139])).

tff(c_2264,plain,(
    ! [A_264] :
      ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_264))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_264))
      | ~ m1_subset_1('#skF_5'(A_264,'#skF_6','#skF_7'),'#skF_6')
      | ~ m1_subset_1('#skF_5'(A_264,'#skF_6','#skF_7'),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2157])).

tff(c_3264,plain,(
    ! [A_338] :
      ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_338))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_338))
      | ~ m1_subset_1('#skF_5'(A_338,'#skF_6','#skF_7'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_103,c_2264])).

tff(c_3268,plain,
    ( '#skF_7' = '#skF_6'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_3264])).

tff(c_3271,plain,
    ( '#skF_7' = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3268])).

tff(c_3272,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_3271])).

tff(c_3275,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_1949,c_3272])).

tff(c_3279,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_3275])).

tff(c_3280,plain,(
    ! [C_32] : ~ m1_subset_1(C_32,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_3298,plain,(
    ! [B_343] :
      ( ~ v1_xboole_0(B_343)
      | ~ v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_3293,c_3280])).

tff(c_3299,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_3298])).

tff(c_3344,plain,(
    ! [B_358,A_359] :
      ( m1_subset_1(B_358,A_359)
      | ~ r2_hidden(B_358,A_359)
      | v1_xboole_0(A_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3357,plain,(
    ! [A_360] :
      ( m1_subset_1('#skF_1'(A_360),A_360)
      | v1_xboole_0(A_360) ) ),
    inference(resolution,[status(thm)],[c_4,c_3344])).

tff(c_3364,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_3357,c_3280])).

tff(c_3369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3299,c_3364])).

tff(c_3370,plain,(
    ! [B_343] : ~ v1_xboole_0(B_343) ),
    inference(splitRight,[status(thm)],[c_3298])).

tff(c_3281,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_3374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3370,c_3281])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.34/2.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.34/2.03  
% 5.34/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.34/2.04  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4
% 5.34/2.04  
% 5.34/2.04  %Foreground sorts:
% 5.34/2.04  
% 5.34/2.04  
% 5.34/2.04  %Background operators:
% 5.34/2.04  
% 5.34/2.04  
% 5.34/2.04  %Foreground operators:
% 5.34/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.34/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.34/2.04  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.34/2.04  tff('#skF_7', type, '#skF_7': $i).
% 5.34/2.04  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.34/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.34/2.04  tff('#skF_6', type, '#skF_6': $i).
% 5.34/2.04  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.34/2.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.34/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.34/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.34/2.04  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.34/2.04  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.34/2.04  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.34/2.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.34/2.04  
% 5.34/2.06  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 5.34/2.06  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.34/2.06  tff(f_45, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 5.34/2.06  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.34/2.06  tff(f_89, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 5.34/2.06  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_subset_1)).
% 5.34/2.06  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 5.34/2.06  tff(c_3293, plain, (![B_343, A_344]: (m1_subset_1(B_343, A_344) | ~v1_xboole_0(B_343) | ~v1_xboole_0(A_344))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.34/2.06  tff(c_144, plain, (![A_52, B_53]: (r2_hidden('#skF_2'(A_52, B_53), A_52) | r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.34/2.06  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.34/2.06  tff(c_159, plain, (![A_52]: (r1_tarski(A_52, A_52))), inference(resolution, [status(thm)], [c_144, c_8])).
% 5.34/2.06  tff(c_14, plain, (![C_14, A_10]: (r2_hidden(C_14, k1_zfmisc_1(A_10)) | ~r1_tarski(C_14, A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.34/2.06  tff(c_12, plain, (![C_14, A_10]: (r1_tarski(C_14, A_10) | ~r2_hidden(C_14, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.34/2.06  tff(c_600, plain, (![A_103, B_104]: (r1_tarski('#skF_2'(k1_zfmisc_1(A_103), B_104), A_103) | r1_tarski(k1_zfmisc_1(A_103), B_104))), inference(resolution, [status(thm)], [c_144, c_12])).
% 5.34/2.06  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.34/2.06  tff(c_171, plain, (![C_59, B_60, A_61]: (r2_hidden(C_59, B_60) | ~r2_hidden(C_59, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.34/2.06  tff(c_187, plain, (![A_62, B_63]: (r2_hidden('#skF_1'(A_62), B_63) | ~r1_tarski(A_62, B_63) | v1_xboole_0(A_62))), inference(resolution, [status(thm)], [c_4, c_171])).
% 5.34/2.06  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.34/2.06  tff(c_203, plain, (![B_63, A_62]: (~v1_xboole_0(B_63) | ~r1_tarski(A_62, B_63) | v1_xboole_0(A_62))), inference(resolution, [status(thm)], [c_187, c_2])).
% 5.34/2.06  tff(c_1111, plain, (![A_164, B_165]: (~v1_xboole_0(A_164) | v1_xboole_0('#skF_2'(k1_zfmisc_1(A_164), B_165)) | r1_tarski(k1_zfmisc_1(A_164), B_165))), inference(resolution, [status(thm)], [c_600, c_203])).
% 5.34/2.06  tff(c_162, plain, (![A_52, B_53]: (~v1_xboole_0(A_52) | r1_tarski(A_52, B_53))), inference(resolution, [status(thm)], [c_144, c_2])).
% 5.34/2.06  tff(c_109, plain, (![A_47, B_48]: (~r2_hidden('#skF_2'(A_47, B_48), B_48) | r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.34/2.06  tff(c_614, plain, (![A_108, A_109]: (r1_tarski(A_108, k1_zfmisc_1(A_109)) | ~r1_tarski('#skF_2'(A_108, k1_zfmisc_1(A_109)), A_109))), inference(resolution, [status(thm)], [c_14, c_109])).
% 5.34/2.06  tff(c_625, plain, (![A_108, B_53]: (r1_tarski(A_108, k1_zfmisc_1(B_53)) | ~v1_xboole_0('#skF_2'(A_108, k1_zfmisc_1(B_53))))), inference(resolution, [status(thm)], [c_162, c_614])).
% 5.34/2.06  tff(c_1122, plain, (![A_167, B_168]: (~v1_xboole_0(A_167) | r1_tarski(k1_zfmisc_1(A_167), k1_zfmisc_1(B_168)))), inference(resolution, [status(thm)], [c_1111, c_625])).
% 5.34/2.06  tff(c_1135, plain, (![B_168, A_167]: (~v1_xboole_0(k1_zfmisc_1(B_168)) | v1_xboole_0(k1_zfmisc_1(A_167)) | ~v1_xboole_0(A_167))), inference(resolution, [status(thm)], [c_1122, c_203])).
% 5.34/2.06  tff(c_1136, plain, (![B_168]: (~v1_xboole_0(k1_zfmisc_1(B_168)))), inference(splitLeft, [status(thm)], [c_1135])).
% 5.34/2.06  tff(c_89, plain, (![B_44, A_45]: (m1_subset_1(B_44, A_45) | ~r2_hidden(B_44, A_45) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.34/2.06  tff(c_99, plain, (![C_14, A_10]: (m1_subset_1(C_14, k1_zfmisc_1(A_10)) | v1_xboole_0(k1_zfmisc_1(A_10)) | ~r1_tarski(C_14, A_10))), inference(resolution, [status(thm)], [c_14, c_89])).
% 5.34/2.06  tff(c_1138, plain, (![C_14, A_10]: (m1_subset_1(C_14, k1_zfmisc_1(A_10)) | ~r1_tarski(C_14, A_10))), inference(negUnitSimplification, [status(thm)], [c_1136, c_99])).
% 5.34/2.06  tff(c_44, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.34/2.06  tff(c_48, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.34/2.06  tff(c_34, plain, (![A_21, B_22, C_26]: (m1_subset_1('#skF_5'(A_21, B_22, C_26), A_21) | C_26=B_22 | ~m1_subset_1(C_26, k1_zfmisc_1(A_21)) | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.34/2.06  tff(c_46, plain, (![C_29]: (r2_hidden(C_29, '#skF_7') | ~m1_subset_1(C_29, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.34/2.06  tff(c_204, plain, (![C_64, A_65, B_66]: (r2_hidden(C_64, A_65) | ~r2_hidden(C_64, B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.34/2.06  tff(c_341, plain, (![C_80, A_81]: (r2_hidden(C_80, A_81) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_81)) | ~m1_subset_1(C_80, '#skF_6'))), inference(resolution, [status(thm)], [c_46, c_204])).
% 5.34/2.06  tff(c_348, plain, (![C_80]: (r2_hidden(C_80, '#skF_6') | ~m1_subset_1(C_80, '#skF_6'))), inference(resolution, [status(thm)], [c_48, c_341])).
% 5.34/2.06  tff(c_1449, plain, (![A_191, B_192, C_193]: (~r2_hidden('#skF_5'(A_191, B_192, C_193), C_193) | ~r2_hidden('#skF_5'(A_191, B_192, C_193), B_192) | C_193=B_192 | ~m1_subset_1(C_193, k1_zfmisc_1(A_191)) | ~m1_subset_1(B_192, k1_zfmisc_1(A_191)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.34/2.06  tff(c_1529, plain, (![A_198, B_199]: (~r2_hidden('#skF_5'(A_198, B_199, '#skF_7'), B_199) | B_199='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_198)) | ~m1_subset_1(B_199, k1_zfmisc_1(A_198)) | ~m1_subset_1('#skF_5'(A_198, B_199, '#skF_7'), '#skF_6'))), inference(resolution, [status(thm)], [c_46, c_1449])).
% 5.34/2.06  tff(c_1555, plain, (![A_198]: ('#skF_7'='#skF_6' | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_198)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_198)) | ~m1_subset_1('#skF_5'(A_198, '#skF_6', '#skF_7'), '#skF_6'))), inference(resolution, [status(thm)], [c_348, c_1529])).
% 5.34/2.06  tff(c_1725, plain, (![A_217]: (~m1_subset_1('#skF_7', k1_zfmisc_1(A_217)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_217)) | ~m1_subset_1('#skF_5'(A_217, '#skF_6', '#skF_7'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_44, c_1555])).
% 5.34/2.06  tff(c_1729, plain, ('#skF_7'='#skF_6' | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_34, c_1725])).
% 5.34/2.06  tff(c_1735, plain, ('#skF_7'='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1729])).
% 5.34/2.06  tff(c_1736, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_44, c_1735])).
% 5.34/2.06  tff(c_1743, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_1138, c_1736])).
% 5.34/2.06  tff(c_1751, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_159, c_1743])).
% 5.34/2.06  tff(c_1753, plain, (![A_218]: (v1_xboole_0(k1_zfmisc_1(A_218)) | ~v1_xboole_0(A_218))), inference(splitRight, [status(thm)], [c_1135])).
% 5.34/2.06  tff(c_79, plain, (![C_40, A_41]: (r2_hidden(C_40, k1_zfmisc_1(A_41)) | ~r1_tarski(C_40, A_41))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.34/2.06  tff(c_87, plain, (![A_41, C_40]: (~v1_xboole_0(k1_zfmisc_1(A_41)) | ~r1_tarski(C_40, A_41))), inference(resolution, [status(thm)], [c_79, c_2])).
% 5.34/2.06  tff(c_1761, plain, (![C_219, A_220]: (~r1_tarski(C_219, A_220) | ~v1_xboole_0(A_220))), inference(resolution, [status(thm)], [c_1753, c_87])).
% 5.34/2.06  tff(c_1805, plain, (![A_52]: (~v1_xboole_0(A_52))), inference(resolution, [status(thm)], [c_159, c_1761])).
% 5.34/2.06  tff(c_24, plain, (![B_16, A_15]: (m1_subset_1(B_16, A_15) | ~r2_hidden(B_16, A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.34/2.06  tff(c_1901, plain, (![B_230, A_231]: (m1_subset_1(B_230, A_231) | ~r2_hidden(B_230, A_231))), inference(negUnitSimplification, [status(thm)], [c_1805, c_24])).
% 5.34/2.06  tff(c_1949, plain, (![C_14, A_10]: (m1_subset_1(C_14, k1_zfmisc_1(A_10)) | ~r1_tarski(C_14, A_10))), inference(resolution, [status(thm)], [c_14, c_1901])).
% 5.34/2.06  tff(c_50, plain, (![C_32]: (r2_hidden(C_32, '#skF_7') | ~m1_subset_1(C_32, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.34/2.06  tff(c_54, plain, (![C_32]: (~v1_xboole_0('#skF_7') | ~m1_subset_1(C_32, '#skF_6'))), inference(resolution, [status(thm)], [c_50, c_2])).
% 5.34/2.06  tff(c_55, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_54])).
% 5.34/2.06  tff(c_98, plain, (![C_29]: (m1_subset_1(C_29, '#skF_7') | v1_xboole_0('#skF_7') | ~m1_subset_1(C_29, '#skF_6'))), inference(resolution, [status(thm)], [c_46, c_89])).
% 5.34/2.06  tff(c_103, plain, (![C_29]: (m1_subset_1(C_29, '#skF_7') | ~m1_subset_1(C_29, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_55, c_98])).
% 5.34/2.06  tff(c_61, plain, (![B_34, A_35]: (v1_xboole_0(B_34) | ~m1_subset_1(B_34, A_35) | ~v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.34/2.06  tff(c_64, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_61])).
% 5.34/2.06  tff(c_67, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_55, c_64])).
% 5.34/2.06  tff(c_125, plain, (![B_50, A_51]: (r2_hidden(B_50, A_51) | ~m1_subset_1(B_50, A_51) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.34/2.06  tff(c_324, plain, (![B_78, A_79]: (r1_tarski(B_78, A_79) | ~m1_subset_1(B_78, k1_zfmisc_1(A_79)) | v1_xboole_0(k1_zfmisc_1(A_79)))), inference(resolution, [status(thm)], [c_125, c_12])).
% 5.34/2.06  tff(c_335, plain, (r1_tarski('#skF_7', '#skF_6') | v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_324])).
% 5.34/2.06  tff(c_340, plain, (r1_tarski('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_67, c_335])).
% 5.34/2.06  tff(c_26, plain, (![B_16, A_15]: (r2_hidden(B_16, A_15) | ~m1_subset_1(B_16, A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.34/2.06  tff(c_651, plain, (![B_120, B_121, A_122]: (r2_hidden(B_120, B_121) | ~r1_tarski(A_122, B_121) | ~m1_subset_1(B_120, A_122) | v1_xboole_0(A_122))), inference(resolution, [status(thm)], [c_26, c_171])).
% 5.34/2.06  tff(c_661, plain, (![B_120]: (r2_hidden(B_120, '#skF_6') | ~m1_subset_1(B_120, '#skF_7') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_340, c_651])).
% 5.34/2.06  tff(c_675, plain, (![B_120]: (r2_hidden(B_120, '#skF_6') | ~m1_subset_1(B_120, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_55, c_661])).
% 5.34/2.06  tff(c_2072, plain, (![A_246, B_247, C_248]: (~r2_hidden('#skF_5'(A_246, B_247, C_248), C_248) | ~r2_hidden('#skF_5'(A_246, B_247, C_248), B_247) | C_248=B_247 | ~m1_subset_1(C_248, k1_zfmisc_1(A_246)) | ~m1_subset_1(B_247, k1_zfmisc_1(A_246)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.34/2.06  tff(c_2139, plain, (![A_251, B_252]: (~r2_hidden('#skF_5'(A_251, B_252, '#skF_7'), B_252) | B_252='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_251)) | ~m1_subset_1(B_252, k1_zfmisc_1(A_251)) | ~m1_subset_1('#skF_5'(A_251, B_252, '#skF_7'), '#skF_6'))), inference(resolution, [status(thm)], [c_46, c_2072])).
% 5.34/2.06  tff(c_2157, plain, (![A_251]: ('#skF_7'='#skF_6' | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_251)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_251)) | ~m1_subset_1('#skF_5'(A_251, '#skF_6', '#skF_7'), '#skF_6') | ~m1_subset_1('#skF_5'(A_251, '#skF_6', '#skF_7'), '#skF_7'))), inference(resolution, [status(thm)], [c_675, c_2139])).
% 5.34/2.06  tff(c_2264, plain, (![A_264]: (~m1_subset_1('#skF_7', k1_zfmisc_1(A_264)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_264)) | ~m1_subset_1('#skF_5'(A_264, '#skF_6', '#skF_7'), '#skF_6') | ~m1_subset_1('#skF_5'(A_264, '#skF_6', '#skF_7'), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_44, c_2157])).
% 5.34/2.06  tff(c_3264, plain, (![A_338]: (~m1_subset_1('#skF_7', k1_zfmisc_1(A_338)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_338)) | ~m1_subset_1('#skF_5'(A_338, '#skF_6', '#skF_7'), '#skF_6'))), inference(resolution, [status(thm)], [c_103, c_2264])).
% 5.34/2.06  tff(c_3268, plain, ('#skF_7'='#skF_6' | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_34, c_3264])).
% 5.34/2.06  tff(c_3271, plain, ('#skF_7'='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3268])).
% 5.34/2.06  tff(c_3272, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_44, c_3271])).
% 5.34/2.06  tff(c_3275, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_1949, c_3272])).
% 5.34/2.06  tff(c_3279, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_159, c_3275])).
% 5.34/2.06  tff(c_3280, plain, (![C_32]: (~m1_subset_1(C_32, '#skF_6'))), inference(splitRight, [status(thm)], [c_54])).
% 5.34/2.06  tff(c_3298, plain, (![B_343]: (~v1_xboole_0(B_343) | ~v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_3293, c_3280])).
% 5.34/2.06  tff(c_3299, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_3298])).
% 5.34/2.06  tff(c_3344, plain, (![B_358, A_359]: (m1_subset_1(B_358, A_359) | ~r2_hidden(B_358, A_359) | v1_xboole_0(A_359))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.34/2.06  tff(c_3357, plain, (![A_360]: (m1_subset_1('#skF_1'(A_360), A_360) | v1_xboole_0(A_360))), inference(resolution, [status(thm)], [c_4, c_3344])).
% 5.34/2.06  tff(c_3364, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_3357, c_3280])).
% 5.34/2.06  tff(c_3369, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3299, c_3364])).
% 5.34/2.06  tff(c_3370, plain, (![B_343]: (~v1_xboole_0(B_343))), inference(splitRight, [status(thm)], [c_3298])).
% 5.34/2.06  tff(c_3281, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_54])).
% 5.34/2.06  tff(c_3374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3370, c_3281])).
% 5.34/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.34/2.06  
% 5.34/2.06  Inference rules
% 5.34/2.06  ----------------------
% 5.34/2.06  #Ref     : 0
% 5.34/2.06  #Sup     : 711
% 5.34/2.06  #Fact    : 4
% 5.34/2.06  #Define  : 0
% 5.34/2.06  #Split   : 8
% 5.34/2.06  #Chain   : 0
% 5.34/2.06  #Close   : 0
% 5.34/2.06  
% 5.34/2.06  Ordering : KBO
% 5.34/2.06  
% 5.34/2.06  Simplification rules
% 5.34/2.06  ----------------------
% 5.34/2.06  #Subsume      : 244
% 5.34/2.06  #Demod        : 47
% 5.34/2.06  #Tautology    : 76
% 5.34/2.06  #SimpNegUnit  : 84
% 5.34/2.06  #BackRed      : 31
% 5.34/2.06  
% 5.34/2.06  #Partial instantiations: 0
% 5.34/2.06  #Strategies tried      : 1
% 5.34/2.06  
% 5.34/2.06  Timing (in seconds)
% 5.34/2.06  ----------------------
% 5.34/2.06  Preprocessing        : 0.38
% 5.34/2.06  Parsing              : 0.16
% 5.34/2.06  CNF conversion       : 0.04
% 5.34/2.06  Main loop            : 0.91
% 5.34/2.06  Inferencing          : 0.32
% 5.34/2.06  Reduction            : 0.22
% 5.34/2.06  Demodulation         : 0.13
% 5.34/2.06  BG Simplification    : 0.05
% 5.34/2.06  Subsumption          : 0.26
% 5.34/2.06  Abstraction          : 0.04
% 5.34/2.06  MUC search           : 0.00
% 5.34/2.06  Cooper               : 0.00
% 5.34/2.06  Total                : 1.33
% 5.34/2.06  Index Insertion      : 0.00
% 5.34/2.06  Index Deletion       : 0.00
% 5.34/2.06  Index Matching       : 0.00
% 5.34/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
