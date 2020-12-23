%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:08 EST 2020

% Result     : Theorem 5.75s
% Output     : CNFRefutation 5.75s
% Verified   : 
% Statistics : Number of formulae       :  176 (1069 expanded)
%              Number of leaves         :   37 ( 359 expanded)
%              Depth                    :   13
%              Number of atoms          :  345 (3391 expanded)
%              Number of equality atoms :   78 (1018 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(k2_relset_1(A,B,D),C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_51,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1992,plain,(
    ! [C_285,A_286,B_287] :
      ( v1_relat_1(C_285)
      | ~ m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(A_286,B_287))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1996,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_1992])).

tff(c_2011,plain,(
    ! [C_292,A_293,B_294] :
      ( v4_relat_1(C_292,A_293)
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(A_293,B_294))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2015,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_2011])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2133,plain,(
    ! [A_323,B_324,C_325] :
      ( k2_relset_1(A_323,B_324,C_325) = k2_relat_1(C_325)
      | ~ m1_subset_1(C_325,k1_zfmisc_1(k2_zfmisc_1(A_323,B_324))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2137,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_2133])).

tff(c_52,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2140,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2137,c_52])).

tff(c_2287,plain,(
    ! [C_361,A_362,B_363] :
      ( m1_subset_1(C_361,k1_zfmisc_1(k2_zfmisc_1(A_362,B_363)))
      | ~ r1_tarski(k2_relat_1(C_361),B_363)
      | ~ r1_tarski(k1_relat_1(C_361),A_362)
      | ~ v1_relat_1(C_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_60,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_48])).

tff(c_66,plain,(
    ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_67,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_71,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_67])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_50,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_56,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_230,plain,(
    ! [A_78,B_79,C_80] :
      ( k1_relset_1(A_78,B_79,C_80) = k1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_234,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_230])).

tff(c_518,plain,(
    ! [B_141,A_142,C_143] :
      ( k1_xboole_0 = B_141
      | k1_relset_1(A_142,B_141,C_143) = A_142
      | ~ v1_funct_2(C_143,A_142,B_141)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_142,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_524,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_518])).

tff(c_528,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_234,c_524])).

tff(c_529,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_528])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_240,plain,(
    ! [A_82,B_83,C_84] :
      ( k2_relset_1(A_82,B_83,C_84) = k2_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_244,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_240])).

tff(c_246,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_52])).

tff(c_422,plain,(
    ! [C_128,A_129,B_130] :
      ( m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130)))
      | ~ r1_tarski(k2_relat_1(C_128),B_130)
      | ~ r1_tarski(k1_relat_1(C_128),A_129)
      | ~ v1_relat_1(C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    ! [A_19,B_20,C_21] :
      ( k1_relset_1(A_19,B_20,C_21) = k1_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_802,plain,(
    ! [A_165,B_166,C_167] :
      ( k1_relset_1(A_165,B_166,C_167) = k1_relat_1(C_167)
      | ~ r1_tarski(k2_relat_1(C_167),B_166)
      | ~ r1_tarski(k1_relat_1(C_167),A_165)
      | ~ v1_relat_1(C_167) ) ),
    inference(resolution,[status(thm)],[c_422,c_28])).

tff(c_804,plain,(
    ! [A_165] :
      ( k1_relset_1(A_165,'#skF_4','#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_165)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_246,c_802])).

tff(c_812,plain,(
    ! [A_168] :
      ( k1_relset_1(A_168,'#skF_4','#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_2',A_168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_529,c_529,c_804])).

tff(c_817,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_12,c_812])).

tff(c_32,plain,(
    ! [C_27,A_25,B_26] :
      ( m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ r1_tarski(k2_relat_1(C_27),B_26)
      | ~ r1_tarski(k1_relat_1(C_27),A_25)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_463,plain,(
    ! [B_131,C_132,A_133] :
      ( k1_xboole_0 = B_131
      | v1_funct_2(C_132,A_133,B_131)
      | k1_relset_1(A_133,B_131,C_132) != A_133
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_133,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1437,plain,(
    ! [B_229,C_230,A_231] :
      ( k1_xboole_0 = B_229
      | v1_funct_2(C_230,A_231,B_229)
      | k1_relset_1(A_231,B_229,C_230) != A_231
      | ~ r1_tarski(k2_relat_1(C_230),B_229)
      | ~ r1_tarski(k1_relat_1(C_230),A_231)
      | ~ v1_relat_1(C_230) ) ),
    inference(resolution,[status(thm)],[c_32,c_463])).

tff(c_1439,plain,(
    ! [A_231] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2('#skF_5',A_231,'#skF_4')
      | k1_relset_1(A_231,'#skF_4','#skF_5') != A_231
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_231)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_246,c_1437])).

tff(c_1445,plain,(
    ! [A_231] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2('#skF_5',A_231,'#skF_4')
      | k1_relset_1(A_231,'#skF_4','#skF_5') != A_231
      | ~ r1_tarski('#skF_2',A_231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_529,c_1439])).

tff(c_1473,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1445])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_663,plain,(
    ! [D_146,C_147,A_148,B_149] :
      ( r2_hidden(k1_funct_1(D_146,C_147),k2_relset_1(A_148,B_149,D_146))
      | k1_xboole_0 = B_149
      | ~ r2_hidden(C_147,A_148)
      | ~ m1_subset_1(D_146,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149)))
      | ~ v1_funct_2(D_146,A_148,B_149)
      | ~ v1_funct_1(D_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_671,plain,(
    ! [C_147] :
      ( r2_hidden(k1_funct_1('#skF_5',C_147),k2_relat_1('#skF_5'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_147,'#skF_2')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_663])).

tff(c_675,plain,(
    ! [C_147] :
      ( r2_hidden(k1_funct_1('#skF_5',C_147),k2_relat_1('#skF_5'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_147,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_671])).

tff(c_701,plain,(
    ! [C_152] :
      ( r2_hidden(k1_funct_1('#skF_5',C_152),k2_relat_1('#skF_5'))
      | ~ r2_hidden(C_152,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_675])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_710,plain,(
    ! [C_154,B_155] :
      ( r2_hidden(k1_funct_1('#skF_5',C_154),B_155)
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_155)
      | ~ r2_hidden(C_154,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_701,c_2])).

tff(c_20,plain,(
    ! [B_12,A_11] :
      ( ~ r1_tarski(B_12,A_11)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_743,plain,(
    ! [B_160,C_161] :
      ( ~ r1_tarski(B_160,k1_funct_1('#skF_5',C_161))
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_160)
      | ~ r2_hidden(C_161,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_710,c_20])).

tff(c_759,plain,(
    ! [C_161] :
      ( ~ r1_tarski(k2_relat_1('#skF_5'),k1_xboole_0)
      | ~ r2_hidden(C_161,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_743])).

tff(c_760,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_759])).

tff(c_1484,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1473,c_760])).

tff(c_1510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_1484])).

tff(c_1517,plain,(
    ! [A_236] :
      ( v1_funct_2('#skF_5',A_236,'#skF_4')
      | k1_relset_1(A_236,'#skF_4','#skF_5') != A_236
      | ~ r1_tarski('#skF_2',A_236) ) ),
    inference(splitRight,[status(thm)],[c_1445])).

tff(c_1520,plain,
    ( k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_1517,c_66])).

tff(c_1524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_817,c_1520])).

tff(c_1537,plain,(
    ! [C_240] : ~ r2_hidden(C_240,'#skF_2') ),
    inference(splitRight,[status(thm)],[c_759])).

tff(c_1552,plain,(
    ! [B_2] : r1_tarski('#skF_2',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_1537])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( v4_relat_1(B_10,A_9)
      | ~ r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_556,plain,(
    ! [A_9] :
      ( v4_relat_1('#skF_5',A_9)
      | ~ r1_tarski('#skF_2',A_9)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_529,c_16])).

tff(c_579,plain,(
    ! [A_9] :
      ( v4_relat_1('#skF_5',A_9)
      | ~ r1_tarski('#skF_2',A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_556])).

tff(c_142,plain,(
    ! [C_60,B_61,A_62] :
      ( r2_hidden(C_60,B_61)
      | ~ r2_hidden(C_60,A_62)
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_157,plain,(
    ! [A_66,B_67,B_68] :
      ( r2_hidden('#skF_1'(A_66,B_67),B_68)
      | ~ r1_tarski(A_66,B_68)
      | r1_tarski(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_6,c_142])).

tff(c_171,plain,(
    ! [B_69,A_70,B_71] :
      ( ~ r1_tarski(B_69,'#skF_1'(A_70,B_71))
      | ~ r1_tarski(A_70,B_69)
      | r1_tarski(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_157,c_20])).

tff(c_187,plain,(
    ! [A_72,B_73] :
      ( ~ r1_tarski(A_72,k1_xboole_0)
      | r1_tarski(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_14,c_171])).

tff(c_197,plain,(
    ! [B_10,B_73] :
      ( r1_tarski(k1_relat_1(B_10),B_73)
      | ~ v4_relat_1(B_10,k1_xboole_0)
      | ~ v1_relat_1(B_10) ) ),
    inference(resolution,[status(thm)],[c_18,c_187])).

tff(c_550,plain,(
    ! [B_73] :
      ( r1_tarski('#skF_2',B_73)
      | ~ v4_relat_1('#skF_5',k1_xboole_0)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_529,c_197])).

tff(c_575,plain,(
    ! [B_73] :
      ( r1_tarski('#skF_2',B_73)
      | ~ v4_relat_1('#skF_5',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_550])).

tff(c_658,plain,(
    ~ v4_relat_1('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_575])).

tff(c_662,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_579,c_658])).

tff(c_1561,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1552,c_662])).

tff(c_1562,plain,(
    ! [B_73] : r1_tarski('#skF_2',B_73) ),
    inference(splitRight,[status(thm)],[c_575])).

tff(c_1788,plain,(
    ! [A_259,B_260,C_261] :
      ( k1_relset_1(A_259,B_260,C_261) = k1_relat_1(C_261)
      | ~ r1_tarski(k2_relat_1(C_261),B_260)
      | ~ r1_tarski(k1_relat_1(C_261),A_259)
      | ~ v1_relat_1(C_261) ) ),
    inference(resolution,[status(thm)],[c_422,c_28])).

tff(c_1790,plain,(
    ! [A_259] :
      ( k1_relset_1(A_259,'#skF_4','#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_259)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_246,c_1788])).

tff(c_1796,plain,(
    ! [A_259] : k1_relset_1(A_259,'#skF_4','#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_1562,c_529,c_529,c_1790])).

tff(c_1567,plain,(
    ! [B_241] : r1_tarski('#skF_2',B_241) ),
    inference(splitRight,[status(thm)],[c_575])).

tff(c_72,plain,(
    ! [B_42,A_43] :
      ( B_42 = A_43
      | ~ r1_tarski(B_42,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_84,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_72])).

tff(c_1618,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1567,c_84])).

tff(c_38,plain,(
    ! [C_30,B_29] :
      ( v1_funct_2(C_30,k1_xboole_0,B_29)
      | k1_relset_1(k1_xboole_0,B_29,C_30) != k1_xboole_0
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_454,plain,(
    ! [C_128,B_130] :
      ( v1_funct_2(C_128,k1_xboole_0,B_130)
      | k1_relset_1(k1_xboole_0,B_130,C_128) != k1_xboole_0
      | ~ r1_tarski(k2_relat_1(C_128),B_130)
      | ~ r1_tarski(k1_relat_1(C_128),k1_xboole_0)
      | ~ v1_relat_1(C_128) ) ),
    inference(resolution,[status(thm)],[c_422,c_38])).

tff(c_1945,plain,(
    ! [C_278,B_279] :
      ( v1_funct_2(C_278,'#skF_2',B_279)
      | k1_relset_1('#skF_2',B_279,C_278) != '#skF_2'
      | ~ r1_tarski(k2_relat_1(C_278),B_279)
      | ~ r1_tarski(k1_relat_1(C_278),'#skF_2')
      | ~ v1_relat_1(C_278) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1618,c_1618,c_1618,c_1618,c_454])).

tff(c_1948,plain,
    ( v1_funct_2('#skF_5','#skF_2','#skF_4')
    | k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2'
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_246,c_1945])).

tff(c_1955,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_12,c_529,c_1796,c_1948])).

tff(c_1957,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1955])).

tff(c_1958,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_2321,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2287,c_1958])).

tff(c_2333,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1996,c_2140,c_2321])).

tff(c_2339,plain,
    ( ~ v4_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_2333])).

tff(c_2346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1996,c_2015,c_2339])).

tff(c_2348,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2347,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2354,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2348,c_2347])).

tff(c_2367,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2354,c_54])).

tff(c_3444,plain,(
    ! [C_537,A_538,B_539] :
      ( v1_relat_1(C_537)
      | ~ m1_subset_1(C_537,k1_zfmisc_1(k2_zfmisc_1(A_538,B_539))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3448,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2367,c_3444])).

tff(c_2349,plain,(
    ! [A_8] : r1_tarski('#skF_2',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2347,c_14])).

tff(c_2365,plain,(
    ! [A_8] : r1_tarski('#skF_3',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2354,c_2349])).

tff(c_3492,plain,(
    ! [C_554,A_555,B_556] :
      ( v4_relat_1(C_554,A_555)
      | ~ m1_subset_1(C_554,k1_zfmisc_1(k2_zfmisc_1(A_555,B_556))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3496,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_2367,c_3492])).

tff(c_3457,plain,(
    ! [B_542,A_543] :
      ( r1_tarski(k1_relat_1(B_542),A_543)
      | ~ v4_relat_1(B_542,A_543)
      | ~ v1_relat_1(B_542) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2374,plain,(
    ! [B_369,A_370] :
      ( B_369 = A_370
      | ~ r1_tarski(B_369,A_370)
      | ~ r1_tarski(A_370,B_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2382,plain,(
    ! [A_8] :
      ( A_8 = '#skF_3'
      | ~ r1_tarski(A_8,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2365,c_2374])).

tff(c_3469,plain,(
    ! [B_542] :
      ( k1_relat_1(B_542) = '#skF_3'
      | ~ v4_relat_1(B_542,'#skF_3')
      | ~ v1_relat_1(B_542) ) ),
    inference(resolution,[status(thm)],[c_3457,c_2382])).

tff(c_3499,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3496,c_3469])).

tff(c_3502,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3448,c_3499])).

tff(c_3626,plain,(
    ! [A_574,B_575,C_576] :
      ( k2_relset_1(A_574,B_575,C_576) = k2_relat_1(C_576)
      | ~ m1_subset_1(C_576,k1_zfmisc_1(k2_zfmisc_1(A_574,B_575))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3630,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2367,c_3626])).

tff(c_2359,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2354,c_52])).

tff(c_3632,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3630,c_2359])).

tff(c_3884,plain,(
    ! [C_617,A_618,B_619] :
      ( m1_subset_1(C_617,k1_zfmisc_1(k2_zfmisc_1(A_618,B_619)))
      | ~ r1_tarski(k2_relat_1(C_617),B_619)
      | ~ r1_tarski(k1_relat_1(C_617),A_618)
      | ~ v1_relat_1(C_617) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2400,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2354,c_2354,c_60])).

tff(c_2401,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2400])).

tff(c_2402,plain,(
    ! [C_372,A_373,B_374] :
      ( v1_relat_1(C_372)
      | ~ m1_subset_1(C_372,k1_zfmisc_1(k2_zfmisc_1(A_373,B_374))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2406,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2367,c_2402])).

tff(c_2430,plain,(
    ! [C_385,A_386,B_387] :
      ( v4_relat_1(C_385,A_386)
      | ~ m1_subset_1(C_385,k1_zfmisc_1(k2_zfmisc_1(A_386,B_387))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2434,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_2367,c_2430])).

tff(c_2435,plain,(
    ! [B_388,A_389] :
      ( r1_tarski(k1_relat_1(B_388),A_389)
      | ~ v4_relat_1(B_388,A_389)
      | ~ v1_relat_1(B_388) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2449,plain,(
    ! [B_390] :
      ( k1_relat_1(B_390) = '#skF_3'
      | ~ v4_relat_1(B_390,'#skF_3')
      | ~ v1_relat_1(B_390) ) ),
    inference(resolution,[status(thm)],[c_2435,c_2382])).

tff(c_2452,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2434,c_2449])).

tff(c_2455,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2406,c_2452])).

tff(c_2584,plain,(
    ! [A_409,B_410,C_411] :
      ( k2_relset_1(A_409,B_410,C_411) = k2_relat_1(C_411)
      | ~ m1_subset_1(C_411,k1_zfmisc_1(k2_zfmisc_1(A_409,B_410))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2588,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2367,c_2584])).

tff(c_2590,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2588,c_2359])).

tff(c_2795,plain,(
    ! [C_444,A_445,B_446] :
      ( m1_subset_1(C_444,k1_zfmisc_1(k2_zfmisc_1(A_445,B_446)))
      | ~ r1_tarski(k2_relat_1(C_444),B_446)
      | ~ r1_tarski(k1_relat_1(C_444),A_445)
      | ~ v1_relat_1(C_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3109,plain,(
    ! [A_488,B_489,C_490] :
      ( k1_relset_1(A_488,B_489,C_490) = k1_relat_1(C_490)
      | ~ r1_tarski(k2_relat_1(C_490),B_489)
      | ~ r1_tarski(k1_relat_1(C_490),A_488)
      | ~ v1_relat_1(C_490) ) ),
    inference(resolution,[status(thm)],[c_2795,c_28])).

tff(c_3111,plain,(
    ! [A_488] :
      ( k1_relset_1(A_488,'#skF_4','#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_488)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2590,c_3109])).

tff(c_3117,plain,(
    ! [A_488] : k1_relset_1(A_488,'#skF_4','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2406,c_2365,c_2455,c_2455,c_3111])).

tff(c_2787,plain,(
    ! [C_30,B_29] :
      ( v1_funct_2(C_30,'#skF_3',B_29)
      | k1_relset_1('#skF_3',B_29,C_30) != '#skF_3'
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_29))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2348,c_2348,c_2348,c_2348,c_38])).

tff(c_3422,plain,(
    ! [C_533,B_534] :
      ( v1_funct_2(C_533,'#skF_3',B_534)
      | k1_relset_1('#skF_3',B_534,C_533) != '#skF_3'
      | ~ r1_tarski(k2_relat_1(C_533),B_534)
      | ~ r1_tarski(k1_relat_1(C_533),'#skF_3')
      | ~ v1_relat_1(C_533) ) ),
    inference(resolution,[status(thm)],[c_2795,c_2787])).

tff(c_3425,plain,
    ( v1_funct_2('#skF_5','#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_3'
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2590,c_3422])).

tff(c_3432,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2406,c_12,c_2455,c_3117,c_3425])).

tff(c_3434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2401,c_3432])).

tff(c_3435,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_2400])).

tff(c_3918,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3884,c_3435])).

tff(c_3931,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3448,c_2365,c_3502,c_3632,c_3918])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:47:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.75/2.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.18  
% 5.75/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.18  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.75/2.18  
% 5.75/2.18  %Foreground sorts:
% 5.75/2.18  
% 5.75/2.18  
% 5.75/2.18  %Background operators:
% 5.75/2.18  
% 5.75/2.18  
% 5.75/2.18  %Foreground operators:
% 5.75/2.18  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.75/2.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.75/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.75/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.75/2.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.75/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.75/2.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.75/2.18  tff('#skF_5', type, '#skF_5': $i).
% 5.75/2.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.75/2.18  tff('#skF_2', type, '#skF_2': $i).
% 5.75/2.18  tff('#skF_3', type, '#skF_3': $i).
% 5.75/2.18  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.75/2.18  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.75/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.75/2.18  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.75/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.75/2.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.75/2.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.75/2.18  tff('#skF_4', type, '#skF_4': $i).
% 5.75/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.75/2.18  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.75/2.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.75/2.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.75/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.75/2.18  
% 5.75/2.21  tff(f_127, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 5.75/2.21  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.75/2.21  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.75/2.21  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.75/2.21  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.75/2.21  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 5.75/2.21  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.75/2.21  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.75/2.21  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.75/2.21  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.75/2.21  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.75/2.21  tff(f_107, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 5.75/2.21  tff(f_51, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.75/2.21  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.75/2.21  tff(c_1992, plain, (![C_285, A_286, B_287]: (v1_relat_1(C_285) | ~m1_subset_1(C_285, k1_zfmisc_1(k2_zfmisc_1(A_286, B_287))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.75/2.21  tff(c_1996, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_1992])).
% 5.75/2.21  tff(c_2011, plain, (![C_292, A_293, B_294]: (v4_relat_1(C_292, A_293) | ~m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(A_293, B_294))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.75/2.21  tff(c_2015, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_2011])).
% 5.75/2.21  tff(c_18, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(B_10), A_9) | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.75/2.21  tff(c_2133, plain, (![A_323, B_324, C_325]: (k2_relset_1(A_323, B_324, C_325)=k2_relat_1(C_325) | ~m1_subset_1(C_325, k1_zfmisc_1(k2_zfmisc_1(A_323, B_324))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.75/2.21  tff(c_2137, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_2133])).
% 5.75/2.21  tff(c_52, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.75/2.21  tff(c_2140, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2137, c_52])).
% 5.75/2.21  tff(c_2287, plain, (![C_361, A_362, B_363]: (m1_subset_1(C_361, k1_zfmisc_1(k2_zfmisc_1(A_362, B_363))) | ~r1_tarski(k2_relat_1(C_361), B_363) | ~r1_tarski(k1_relat_1(C_361), A_362) | ~v1_relat_1(C_361))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.75/2.21  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.75/2.21  tff(c_48, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.75/2.21  tff(c_60, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_48])).
% 5.75/2.21  tff(c_66, plain, (~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_60])).
% 5.75/2.21  tff(c_67, plain, (![C_39, A_40, B_41]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.75/2.21  tff(c_71, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_67])).
% 5.75/2.21  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.75/2.21  tff(c_50, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.75/2.21  tff(c_64, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_50])).
% 5.75/2.21  tff(c_56, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.75/2.21  tff(c_230, plain, (![A_78, B_79, C_80]: (k1_relset_1(A_78, B_79, C_80)=k1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.75/2.21  tff(c_234, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_230])).
% 5.75/2.21  tff(c_518, plain, (![B_141, A_142, C_143]: (k1_xboole_0=B_141 | k1_relset_1(A_142, B_141, C_143)=A_142 | ~v1_funct_2(C_143, A_142, B_141) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_142, B_141))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.75/2.21  tff(c_524, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_518])).
% 5.75/2.21  tff(c_528, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_234, c_524])).
% 5.75/2.21  tff(c_529, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_64, c_528])).
% 5.75/2.21  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.75/2.21  tff(c_240, plain, (![A_82, B_83, C_84]: (k2_relset_1(A_82, B_83, C_84)=k2_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.75/2.21  tff(c_244, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_240])).
% 5.75/2.21  tff(c_246, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_244, c_52])).
% 5.75/2.21  tff(c_422, plain, (![C_128, A_129, B_130]: (m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))) | ~r1_tarski(k2_relat_1(C_128), B_130) | ~r1_tarski(k1_relat_1(C_128), A_129) | ~v1_relat_1(C_128))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.75/2.21  tff(c_28, plain, (![A_19, B_20, C_21]: (k1_relset_1(A_19, B_20, C_21)=k1_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.75/2.21  tff(c_802, plain, (![A_165, B_166, C_167]: (k1_relset_1(A_165, B_166, C_167)=k1_relat_1(C_167) | ~r1_tarski(k2_relat_1(C_167), B_166) | ~r1_tarski(k1_relat_1(C_167), A_165) | ~v1_relat_1(C_167))), inference(resolution, [status(thm)], [c_422, c_28])).
% 5.75/2.21  tff(c_804, plain, (![A_165]: (k1_relset_1(A_165, '#skF_4', '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski(k1_relat_1('#skF_5'), A_165) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_246, c_802])).
% 5.75/2.21  tff(c_812, plain, (![A_168]: (k1_relset_1(A_168, '#skF_4', '#skF_5')='#skF_2' | ~r1_tarski('#skF_2', A_168))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_529, c_529, c_804])).
% 5.75/2.21  tff(c_817, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_12, c_812])).
% 5.75/2.21  tff(c_32, plain, (![C_27, A_25, B_26]: (m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~r1_tarski(k2_relat_1(C_27), B_26) | ~r1_tarski(k1_relat_1(C_27), A_25) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.75/2.21  tff(c_463, plain, (![B_131, C_132, A_133]: (k1_xboole_0=B_131 | v1_funct_2(C_132, A_133, B_131) | k1_relset_1(A_133, B_131, C_132)!=A_133 | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_133, B_131))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.75/2.21  tff(c_1437, plain, (![B_229, C_230, A_231]: (k1_xboole_0=B_229 | v1_funct_2(C_230, A_231, B_229) | k1_relset_1(A_231, B_229, C_230)!=A_231 | ~r1_tarski(k2_relat_1(C_230), B_229) | ~r1_tarski(k1_relat_1(C_230), A_231) | ~v1_relat_1(C_230))), inference(resolution, [status(thm)], [c_32, c_463])).
% 5.75/2.21  tff(c_1439, plain, (![A_231]: (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', A_231, '#skF_4') | k1_relset_1(A_231, '#skF_4', '#skF_5')!=A_231 | ~r1_tarski(k1_relat_1('#skF_5'), A_231) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_246, c_1437])).
% 5.75/2.21  tff(c_1445, plain, (![A_231]: (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', A_231, '#skF_4') | k1_relset_1(A_231, '#skF_4', '#skF_5')!=A_231 | ~r1_tarski('#skF_2', A_231))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_529, c_1439])).
% 5.75/2.21  tff(c_1473, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1445])).
% 5.75/2.21  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.75/2.21  tff(c_663, plain, (![D_146, C_147, A_148, B_149]: (r2_hidden(k1_funct_1(D_146, C_147), k2_relset_1(A_148, B_149, D_146)) | k1_xboole_0=B_149 | ~r2_hidden(C_147, A_148) | ~m1_subset_1(D_146, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))) | ~v1_funct_2(D_146, A_148, B_149) | ~v1_funct_1(D_146))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.75/2.21  tff(c_671, plain, (![C_147]: (r2_hidden(k1_funct_1('#skF_5', C_147), k2_relat_1('#skF_5')) | k1_xboole_0='#skF_3' | ~r2_hidden(C_147, '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_244, c_663])).
% 5.75/2.21  tff(c_675, plain, (![C_147]: (r2_hidden(k1_funct_1('#skF_5', C_147), k2_relat_1('#skF_5')) | k1_xboole_0='#skF_3' | ~r2_hidden(C_147, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_671])).
% 5.75/2.21  tff(c_701, plain, (![C_152]: (r2_hidden(k1_funct_1('#skF_5', C_152), k2_relat_1('#skF_5')) | ~r2_hidden(C_152, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_64, c_675])).
% 5.75/2.21  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.75/2.21  tff(c_710, plain, (![C_154, B_155]: (r2_hidden(k1_funct_1('#skF_5', C_154), B_155) | ~r1_tarski(k2_relat_1('#skF_5'), B_155) | ~r2_hidden(C_154, '#skF_2'))), inference(resolution, [status(thm)], [c_701, c_2])).
% 5.75/2.21  tff(c_20, plain, (![B_12, A_11]: (~r1_tarski(B_12, A_11) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.75/2.21  tff(c_743, plain, (![B_160, C_161]: (~r1_tarski(B_160, k1_funct_1('#skF_5', C_161)) | ~r1_tarski(k2_relat_1('#skF_5'), B_160) | ~r2_hidden(C_161, '#skF_2'))), inference(resolution, [status(thm)], [c_710, c_20])).
% 5.75/2.21  tff(c_759, plain, (![C_161]: (~r1_tarski(k2_relat_1('#skF_5'), k1_xboole_0) | ~r2_hidden(C_161, '#skF_2'))), inference(resolution, [status(thm)], [c_14, c_743])).
% 5.75/2.21  tff(c_760, plain, (~r1_tarski(k2_relat_1('#skF_5'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_759])).
% 5.75/2.21  tff(c_1484, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1473, c_760])).
% 5.75/2.21  tff(c_1510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_246, c_1484])).
% 5.75/2.21  tff(c_1517, plain, (![A_236]: (v1_funct_2('#skF_5', A_236, '#skF_4') | k1_relset_1(A_236, '#skF_4', '#skF_5')!=A_236 | ~r1_tarski('#skF_2', A_236))), inference(splitRight, [status(thm)], [c_1445])).
% 5.75/2.21  tff(c_1520, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_1517, c_66])).
% 5.75/2.21  tff(c_1524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_817, c_1520])).
% 5.75/2.21  tff(c_1537, plain, (![C_240]: (~r2_hidden(C_240, '#skF_2'))), inference(splitRight, [status(thm)], [c_759])).
% 5.75/2.21  tff(c_1552, plain, (![B_2]: (r1_tarski('#skF_2', B_2))), inference(resolution, [status(thm)], [c_6, c_1537])).
% 5.75/2.21  tff(c_16, plain, (![B_10, A_9]: (v4_relat_1(B_10, A_9) | ~r1_tarski(k1_relat_1(B_10), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.75/2.21  tff(c_556, plain, (![A_9]: (v4_relat_1('#skF_5', A_9) | ~r1_tarski('#skF_2', A_9) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_529, c_16])).
% 5.75/2.21  tff(c_579, plain, (![A_9]: (v4_relat_1('#skF_5', A_9) | ~r1_tarski('#skF_2', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_556])).
% 5.75/2.21  tff(c_142, plain, (![C_60, B_61, A_62]: (r2_hidden(C_60, B_61) | ~r2_hidden(C_60, A_62) | ~r1_tarski(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.75/2.21  tff(c_157, plain, (![A_66, B_67, B_68]: (r2_hidden('#skF_1'(A_66, B_67), B_68) | ~r1_tarski(A_66, B_68) | r1_tarski(A_66, B_67))), inference(resolution, [status(thm)], [c_6, c_142])).
% 5.75/2.21  tff(c_171, plain, (![B_69, A_70, B_71]: (~r1_tarski(B_69, '#skF_1'(A_70, B_71)) | ~r1_tarski(A_70, B_69) | r1_tarski(A_70, B_71))), inference(resolution, [status(thm)], [c_157, c_20])).
% 5.75/2.21  tff(c_187, plain, (![A_72, B_73]: (~r1_tarski(A_72, k1_xboole_0) | r1_tarski(A_72, B_73))), inference(resolution, [status(thm)], [c_14, c_171])).
% 5.75/2.21  tff(c_197, plain, (![B_10, B_73]: (r1_tarski(k1_relat_1(B_10), B_73) | ~v4_relat_1(B_10, k1_xboole_0) | ~v1_relat_1(B_10))), inference(resolution, [status(thm)], [c_18, c_187])).
% 5.75/2.21  tff(c_550, plain, (![B_73]: (r1_tarski('#skF_2', B_73) | ~v4_relat_1('#skF_5', k1_xboole_0) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_529, c_197])).
% 5.75/2.21  tff(c_575, plain, (![B_73]: (r1_tarski('#skF_2', B_73) | ~v4_relat_1('#skF_5', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_550])).
% 5.75/2.21  tff(c_658, plain, (~v4_relat_1('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_575])).
% 5.75/2.21  tff(c_662, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_579, c_658])).
% 5.75/2.21  tff(c_1561, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1552, c_662])).
% 5.75/2.21  tff(c_1562, plain, (![B_73]: (r1_tarski('#skF_2', B_73))), inference(splitRight, [status(thm)], [c_575])).
% 5.75/2.21  tff(c_1788, plain, (![A_259, B_260, C_261]: (k1_relset_1(A_259, B_260, C_261)=k1_relat_1(C_261) | ~r1_tarski(k2_relat_1(C_261), B_260) | ~r1_tarski(k1_relat_1(C_261), A_259) | ~v1_relat_1(C_261))), inference(resolution, [status(thm)], [c_422, c_28])).
% 5.75/2.21  tff(c_1790, plain, (![A_259]: (k1_relset_1(A_259, '#skF_4', '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski(k1_relat_1('#skF_5'), A_259) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_246, c_1788])).
% 5.75/2.21  tff(c_1796, plain, (![A_259]: (k1_relset_1(A_259, '#skF_4', '#skF_5')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_1562, c_529, c_529, c_1790])).
% 5.75/2.21  tff(c_1567, plain, (![B_241]: (r1_tarski('#skF_2', B_241))), inference(splitRight, [status(thm)], [c_575])).
% 5.75/2.21  tff(c_72, plain, (![B_42, A_43]: (B_42=A_43 | ~r1_tarski(B_42, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.75/2.21  tff(c_84, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_72])).
% 5.75/2.21  tff(c_1618, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1567, c_84])).
% 5.75/2.21  tff(c_38, plain, (![C_30, B_29]: (v1_funct_2(C_30, k1_xboole_0, B_29) | k1_relset_1(k1_xboole_0, B_29, C_30)!=k1_xboole_0 | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_29))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.75/2.21  tff(c_454, plain, (![C_128, B_130]: (v1_funct_2(C_128, k1_xboole_0, B_130) | k1_relset_1(k1_xboole_0, B_130, C_128)!=k1_xboole_0 | ~r1_tarski(k2_relat_1(C_128), B_130) | ~r1_tarski(k1_relat_1(C_128), k1_xboole_0) | ~v1_relat_1(C_128))), inference(resolution, [status(thm)], [c_422, c_38])).
% 5.75/2.21  tff(c_1945, plain, (![C_278, B_279]: (v1_funct_2(C_278, '#skF_2', B_279) | k1_relset_1('#skF_2', B_279, C_278)!='#skF_2' | ~r1_tarski(k2_relat_1(C_278), B_279) | ~r1_tarski(k1_relat_1(C_278), '#skF_2') | ~v1_relat_1(C_278))), inference(demodulation, [status(thm), theory('equality')], [c_1618, c_1618, c_1618, c_1618, c_454])).
% 5.75/2.21  tff(c_1948, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_4') | k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2' | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_246, c_1945])).
% 5.75/2.21  tff(c_1955, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_12, c_529, c_1796, c_1948])).
% 5.75/2.21  tff(c_1957, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1955])).
% 5.75/2.21  tff(c_1958, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(splitRight, [status(thm)], [c_60])).
% 5.75/2.21  tff(c_2321, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2287, c_1958])).
% 5.75/2.21  tff(c_2333, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1996, c_2140, c_2321])).
% 5.75/2.21  tff(c_2339, plain, (~v4_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_2333])).
% 5.75/2.21  tff(c_2346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1996, c_2015, c_2339])).
% 5.75/2.21  tff(c_2348, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_50])).
% 5.75/2.21  tff(c_2347, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_50])).
% 5.75/2.21  tff(c_2354, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2348, c_2347])).
% 5.75/2.21  tff(c_2367, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2354, c_54])).
% 5.75/2.21  tff(c_3444, plain, (![C_537, A_538, B_539]: (v1_relat_1(C_537) | ~m1_subset_1(C_537, k1_zfmisc_1(k2_zfmisc_1(A_538, B_539))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.75/2.21  tff(c_3448, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2367, c_3444])).
% 5.75/2.21  tff(c_2349, plain, (![A_8]: (r1_tarski('#skF_2', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_2347, c_14])).
% 5.75/2.21  tff(c_2365, plain, (![A_8]: (r1_tarski('#skF_3', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_2354, c_2349])).
% 5.75/2.21  tff(c_3492, plain, (![C_554, A_555, B_556]: (v4_relat_1(C_554, A_555) | ~m1_subset_1(C_554, k1_zfmisc_1(k2_zfmisc_1(A_555, B_556))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.75/2.21  tff(c_3496, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_2367, c_3492])).
% 5.75/2.21  tff(c_3457, plain, (![B_542, A_543]: (r1_tarski(k1_relat_1(B_542), A_543) | ~v4_relat_1(B_542, A_543) | ~v1_relat_1(B_542))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.75/2.21  tff(c_2374, plain, (![B_369, A_370]: (B_369=A_370 | ~r1_tarski(B_369, A_370) | ~r1_tarski(A_370, B_369))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.75/2.21  tff(c_2382, plain, (![A_8]: (A_8='#skF_3' | ~r1_tarski(A_8, '#skF_3'))), inference(resolution, [status(thm)], [c_2365, c_2374])).
% 5.75/2.21  tff(c_3469, plain, (![B_542]: (k1_relat_1(B_542)='#skF_3' | ~v4_relat_1(B_542, '#skF_3') | ~v1_relat_1(B_542))), inference(resolution, [status(thm)], [c_3457, c_2382])).
% 5.75/2.21  tff(c_3499, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_3496, c_3469])).
% 5.75/2.21  tff(c_3502, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3448, c_3499])).
% 5.75/2.21  tff(c_3626, plain, (![A_574, B_575, C_576]: (k2_relset_1(A_574, B_575, C_576)=k2_relat_1(C_576) | ~m1_subset_1(C_576, k1_zfmisc_1(k2_zfmisc_1(A_574, B_575))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.75/2.21  tff(c_3630, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2367, c_3626])).
% 5.75/2.21  tff(c_2359, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2354, c_52])).
% 5.75/2.21  tff(c_3632, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3630, c_2359])).
% 5.75/2.21  tff(c_3884, plain, (![C_617, A_618, B_619]: (m1_subset_1(C_617, k1_zfmisc_1(k2_zfmisc_1(A_618, B_619))) | ~r1_tarski(k2_relat_1(C_617), B_619) | ~r1_tarski(k1_relat_1(C_617), A_618) | ~v1_relat_1(C_617))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.75/2.21  tff(c_2400, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2354, c_2354, c_60])).
% 5.75/2.21  tff(c_2401, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_2400])).
% 5.75/2.21  tff(c_2402, plain, (![C_372, A_373, B_374]: (v1_relat_1(C_372) | ~m1_subset_1(C_372, k1_zfmisc_1(k2_zfmisc_1(A_373, B_374))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.75/2.21  tff(c_2406, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2367, c_2402])).
% 5.75/2.21  tff(c_2430, plain, (![C_385, A_386, B_387]: (v4_relat_1(C_385, A_386) | ~m1_subset_1(C_385, k1_zfmisc_1(k2_zfmisc_1(A_386, B_387))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.75/2.21  tff(c_2434, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_2367, c_2430])).
% 5.75/2.21  tff(c_2435, plain, (![B_388, A_389]: (r1_tarski(k1_relat_1(B_388), A_389) | ~v4_relat_1(B_388, A_389) | ~v1_relat_1(B_388))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.75/2.21  tff(c_2449, plain, (![B_390]: (k1_relat_1(B_390)='#skF_3' | ~v4_relat_1(B_390, '#skF_3') | ~v1_relat_1(B_390))), inference(resolution, [status(thm)], [c_2435, c_2382])).
% 5.75/2.21  tff(c_2452, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2434, c_2449])).
% 5.75/2.21  tff(c_2455, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2406, c_2452])).
% 5.75/2.21  tff(c_2584, plain, (![A_409, B_410, C_411]: (k2_relset_1(A_409, B_410, C_411)=k2_relat_1(C_411) | ~m1_subset_1(C_411, k1_zfmisc_1(k2_zfmisc_1(A_409, B_410))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.75/2.21  tff(c_2588, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2367, c_2584])).
% 5.75/2.21  tff(c_2590, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2588, c_2359])).
% 5.75/2.21  tff(c_2795, plain, (![C_444, A_445, B_446]: (m1_subset_1(C_444, k1_zfmisc_1(k2_zfmisc_1(A_445, B_446))) | ~r1_tarski(k2_relat_1(C_444), B_446) | ~r1_tarski(k1_relat_1(C_444), A_445) | ~v1_relat_1(C_444))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.75/2.21  tff(c_3109, plain, (![A_488, B_489, C_490]: (k1_relset_1(A_488, B_489, C_490)=k1_relat_1(C_490) | ~r1_tarski(k2_relat_1(C_490), B_489) | ~r1_tarski(k1_relat_1(C_490), A_488) | ~v1_relat_1(C_490))), inference(resolution, [status(thm)], [c_2795, c_28])).
% 5.75/2.21  tff(c_3111, plain, (![A_488]: (k1_relset_1(A_488, '#skF_4', '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski(k1_relat_1('#skF_5'), A_488) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_2590, c_3109])).
% 5.75/2.21  tff(c_3117, plain, (![A_488]: (k1_relset_1(A_488, '#skF_4', '#skF_5')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2406, c_2365, c_2455, c_2455, c_3111])).
% 5.75/2.21  tff(c_2787, plain, (![C_30, B_29]: (v1_funct_2(C_30, '#skF_3', B_29) | k1_relset_1('#skF_3', B_29, C_30)!='#skF_3' | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_29))))), inference(demodulation, [status(thm), theory('equality')], [c_2348, c_2348, c_2348, c_2348, c_38])).
% 5.75/2.21  tff(c_3422, plain, (![C_533, B_534]: (v1_funct_2(C_533, '#skF_3', B_534) | k1_relset_1('#skF_3', B_534, C_533)!='#skF_3' | ~r1_tarski(k2_relat_1(C_533), B_534) | ~r1_tarski(k1_relat_1(C_533), '#skF_3') | ~v1_relat_1(C_533))), inference(resolution, [status(thm)], [c_2795, c_2787])).
% 5.75/2.21  tff(c_3425, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_3' | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2590, c_3422])).
% 5.75/2.21  tff(c_3432, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2406, c_12, c_2455, c_3117, c_3425])).
% 5.75/2.21  tff(c_3434, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2401, c_3432])).
% 5.75/2.21  tff(c_3435, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_2400])).
% 5.75/2.21  tff(c_3918, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_3884, c_3435])).
% 5.75/2.21  tff(c_3931, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3448, c_2365, c_3502, c_3632, c_3918])).
% 5.75/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.21  
% 5.75/2.21  Inference rules
% 5.75/2.21  ----------------------
% 5.75/2.21  #Ref     : 0
% 5.75/2.21  #Sup     : 777
% 5.75/2.21  #Fact    : 0
% 5.75/2.21  #Define  : 0
% 5.75/2.21  #Split   : 22
% 5.75/2.21  #Chain   : 0
% 6.05/2.21  #Close   : 0
% 6.05/2.21  
% 6.05/2.21  Ordering : KBO
% 6.05/2.21  
% 6.05/2.21  Simplification rules
% 6.05/2.21  ----------------------
% 6.05/2.21  #Subsume      : 198
% 6.05/2.21  #Demod        : 629
% 6.05/2.21  #Tautology    : 266
% 6.05/2.21  #SimpNegUnit  : 6
% 6.05/2.21  #BackRed      : 72
% 6.05/2.21  
% 6.05/2.21  #Partial instantiations: 0
% 6.05/2.21  #Strategies tried      : 1
% 6.05/2.21  
% 6.05/2.21  Timing (in seconds)
% 6.05/2.21  ----------------------
% 6.05/2.21  Preprocessing        : 0.37
% 6.05/2.21  Parsing              : 0.19
% 6.05/2.21  CNF conversion       : 0.03
% 6.05/2.21  Main loop            : 1.00
% 6.05/2.21  Inferencing          : 0.34
% 6.05/2.21  Reduction            : 0.29
% 6.05/2.21  Demodulation         : 0.20
% 6.05/2.21  BG Simplification    : 0.05
% 6.05/2.21  Subsumption          : 0.24
% 6.05/2.21  Abstraction          : 0.04
% 6.05/2.21  MUC search           : 0.00
% 6.05/2.21  Cooper               : 0.00
% 6.05/2.21  Total                : 1.42
% 6.05/2.21  Index Insertion      : 0.00
% 6.05/2.21  Index Deletion       : 0.00
% 6.05/2.21  Index Matching       : 0.00
% 6.05/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
