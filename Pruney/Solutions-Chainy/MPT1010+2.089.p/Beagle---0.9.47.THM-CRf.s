%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:17 EST 2020

% Result     : Theorem 49.15s
% Output     : CNFRefutation 49.15s
% Verified   : 
% Statistics : Number of formulae       :  169 (2524 expanded)
%              Number of leaves         :   43 ( 848 expanded)
%              Depth                    :   38
%              Number of atoms          :  319 (6224 expanded)
%              Number of equality atoms :   75 ( 976 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_129,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_77,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_118,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_90,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_82,plain,(
    k1_funct_1('#skF_9','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_199,plain,(
    ! [A_87,B_88] :
      ( r2_hidden('#skF_1'(A_87,B_88),A_87)
      | r1_tarski(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_211,plain,(
    ! [A_87] : r1_tarski(A_87,A_87) ),
    inference(resolution,[status(thm)],[c_199,c_4])).

tff(c_84,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_258,plain,(
    ! [C_106,B_107,A_108] :
      ( r2_hidden(C_106,B_107)
      | ~ r2_hidden(C_106,A_108)
      | ~ r1_tarski(A_108,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_282,plain,(
    ! [B_107] :
      ( r2_hidden('#skF_8',B_107)
      | ~ r1_tarski('#skF_6',B_107) ) ),
    inference(resolution,[status(thm)],[c_84,c_258])).

tff(c_58,plain,(
    ! [A_30,B_31] : v1_relat_1(k2_zfmisc_1(A_30,B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_86,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_188,plain,(
    ! [B_82,A_83] :
      ( v1_relat_1(B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_83))
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_191,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_86,c_188])).

tff(c_194,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_191])).

tff(c_90,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_88,plain,(
    v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_935,plain,(
    ! [A_184,B_185,C_186] :
      ( k1_relset_1(A_184,B_185,C_186) = k1_relat_1(C_186)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_939,plain,(
    k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_86,c_935])).

tff(c_1534,plain,(
    ! [B_250,A_251,C_252] :
      ( k1_xboole_0 = B_250
      | k1_relset_1(A_251,B_250,C_252) = A_251
      | ~ v1_funct_2(C_252,A_251,B_250)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_251,B_250))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1537,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_86,c_1534])).

tff(c_1540,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_939,c_1537])).

tff(c_1541,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1540])).

tff(c_60,plain,(
    ! [B_33,A_32] :
      ( r2_hidden(k1_funct_1(B_33,A_32),k2_relat_1(B_33))
      | ~ r2_hidden(A_32,k1_relat_1(B_33))
      | ~ v1_funct_1(B_33)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_34,plain,(
    ! [C_18,A_14] :
      ( C_18 = A_14
      | ~ r2_hidden(C_18,k1_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_213,plain,(
    ! [A_14,B_88] :
      ( '#skF_1'(k1_tarski(A_14),B_88) = A_14
      | r1_tarski(k1_tarski(A_14),B_88) ) ),
    inference(resolution,[status(thm)],[c_199,c_34])).

tff(c_36,plain,(
    ! [C_18] : r2_hidden(C_18,k1_tarski(C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_112,plain,(
    ! [B_61,A_62] :
      ( ~ r1_tarski(B_61,A_62)
      | ~ r2_hidden(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_131,plain,(
    ! [C_18] : ~ r1_tarski(k1_tarski(C_18),C_18) ),
    inference(resolution,[status(thm)],[c_36,c_112])).

tff(c_358,plain,(
    ! [A_128,B_129] :
      ( '#skF_1'(k1_tarski(A_128),B_129) = A_128
      | r1_tarski(k1_tarski(A_128),B_129) ) ),
    inference(resolution,[status(thm)],[c_199,c_34])).

tff(c_379,plain,(
    ! [B_129] : '#skF_1'(k1_tarski(B_129),B_129) = B_129 ),
    inference(resolution,[status(thm)],[c_358,c_131])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_253,plain,(
    ! [C_103,B_104,A_105] :
      ( v5_relat_1(C_103,B_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_105,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_257,plain,(
    v5_relat_1('#skF_9',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_86,c_253])).

tff(c_56,plain,(
    ! [B_29,A_28] :
      ( r1_tarski(k2_relat_1(B_29),A_28)
      | ~ v5_relat_1(B_29,A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_493,plain,(
    ! [A_151,B_152,B_153] :
      ( r2_hidden('#skF_1'(A_151,B_152),B_153)
      | ~ r1_tarski(A_151,B_153)
      | r1_tarski(A_151,B_152) ) ),
    inference(resolution,[status(thm)],[c_6,c_258])).

tff(c_950,plain,(
    ! [A_187,A_188,B_189] :
      ( A_187 = '#skF_1'(A_188,B_189)
      | ~ r1_tarski(A_188,k1_tarski(A_187))
      | r1_tarski(A_188,B_189) ) ),
    inference(resolution,[status(thm)],[c_493,c_34])).

tff(c_13055,plain,(
    ! [A_17641,B_17642,B_17643] :
      ( A_17641 = '#skF_1'(k2_relat_1(B_17642),B_17643)
      | r1_tarski(k2_relat_1(B_17642),B_17643)
      | ~ v5_relat_1(B_17642,k1_tarski(A_17641))
      | ~ v1_relat_1(B_17642) ) ),
    inference(resolution,[status(thm)],[c_56,c_950])).

tff(c_13127,plain,(
    ! [B_17643] :
      ( '#skF_1'(k2_relat_1('#skF_9'),B_17643) = '#skF_7'
      | r1_tarski(k2_relat_1('#skF_9'),B_17643)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_257,c_13055])).

tff(c_13131,plain,(
    ! [B_17780] :
      ( '#skF_1'(k2_relat_1('#skF_9'),B_17780) = '#skF_7'
      | r1_tarski(k2_relat_1('#skF_9'),B_17780) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_13127])).

tff(c_526,plain,(
    ! [A_14,A_151,B_152] :
      ( A_14 = '#skF_1'(A_151,B_152)
      | ~ r1_tarski(A_151,k1_tarski(A_14))
      | r1_tarski(A_151,B_152) ) ),
    inference(resolution,[status(thm)],[c_493,c_34])).

tff(c_31984,plain,(
    ! [A_60336,B_60337] :
      ( A_60336 = '#skF_1'(k2_relat_1('#skF_9'),B_60337)
      | r1_tarski(k2_relat_1('#skF_9'),B_60337)
      | '#skF_1'(k2_relat_1('#skF_9'),k1_tarski(A_60336)) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_13131,c_526])).

tff(c_54,plain,(
    ! [B_29,A_28] :
      ( v5_relat_1(B_29,A_28)
      | ~ r1_tarski(k2_relat_1(B_29),A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_35107,plain,(
    ! [B_60337,A_60336] :
      ( v5_relat_1('#skF_9',B_60337)
      | ~ v1_relat_1('#skF_9')
      | A_60336 = '#skF_1'(k2_relat_1('#skF_9'),B_60337)
      | '#skF_1'(k2_relat_1('#skF_9'),k1_tarski(A_60336)) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_31984,c_54])).

tff(c_35668,plain,(
    ! [B_60337,A_60336] :
      ( v5_relat_1('#skF_9',B_60337)
      | A_60336 = '#skF_1'(k2_relat_1('#skF_9'),B_60337)
      | '#skF_1'(k2_relat_1('#skF_9'),k1_tarski(A_60336)) = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_35107])).

tff(c_41175,plain,(
    ! [A_75576] :
      ( v5_relat_1('#skF_9',k1_tarski(A_75576))
      | '#skF_1'(k2_relat_1('#skF_9'),k1_tarski(A_75576)) = A_75576
      | A_75576 != '#skF_7' ) ),
    inference(factorization,[status(thm),theory(equality)],[c_35668])).

tff(c_41244,plain,(
    ! [A_75576] :
      ( ~ r2_hidden(A_75576,k1_tarski(A_75576))
      | r1_tarski(k2_relat_1('#skF_9'),k1_tarski(A_75576))
      | v5_relat_1('#skF_9',k1_tarski(A_75576))
      | A_75576 != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41175,c_4])).

tff(c_41648,plain,(
    ! [A_75951] :
      ( r1_tarski(k2_relat_1('#skF_9'),k1_tarski(A_75951))
      | v5_relat_1('#skF_9',k1_tarski(A_75951))
      | A_75951 != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_41244])).

tff(c_41670,plain,(
    ! [A_75951] :
      ( ~ v1_relat_1('#skF_9')
      | v5_relat_1('#skF_9',k1_tarski(A_75951))
      | A_75951 != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_41648,c_54])).

tff(c_41783,plain,(
    ! [A_76326] :
      ( v5_relat_1('#skF_9',k1_tarski(A_76326))
      | A_76326 != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_41670])).

tff(c_62,plain,(
    ! [B_35,A_34] :
      ( ~ r1_tarski(B_35,A_34)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_561,plain,(
    ! [B_159,A_160,B_161] :
      ( ~ r1_tarski(B_159,'#skF_1'(A_160,B_161))
      | ~ r1_tarski(A_160,B_159)
      | r1_tarski(A_160,B_161) ) ),
    inference(resolution,[status(thm)],[c_493,c_62])).

tff(c_589,plain,(
    ! [A_162,B_163] :
      ( ~ r1_tarski(A_162,k1_xboole_0)
      | r1_tarski(A_162,B_163) ) ),
    inference(resolution,[status(thm)],[c_8,c_561])).

tff(c_603,plain,(
    ! [B_29,B_163] :
      ( r1_tarski(k2_relat_1(B_29),B_163)
      | ~ v5_relat_1(B_29,k1_xboole_0)
      | ~ v1_relat_1(B_29) ) ),
    inference(resolution,[status(thm)],[c_56,c_589])).

tff(c_1127,plain,(
    ! [B_208,A_209] :
      ( r2_hidden(k1_funct_1(B_208,A_209),k2_relat_1(B_208))
      | ~ r2_hidden(A_209,k1_relat_1(B_208))
      | ~ v1_funct_1(B_208)
      | ~ v1_relat_1(B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1162,plain,(
    ! [B_214,A_215] :
      ( ~ r1_tarski(k2_relat_1(B_214),k1_funct_1(B_214,A_215))
      | ~ r2_hidden(A_215,k1_relat_1(B_214))
      | ~ v1_funct_1(B_214)
      | ~ v1_relat_1(B_214) ) ),
    inference(resolution,[status(thm)],[c_1127,c_62])).

tff(c_1173,plain,(
    ! [A_216,B_217] :
      ( ~ r2_hidden(A_216,k1_relat_1(B_217))
      | ~ v1_funct_1(B_217)
      | ~ v5_relat_1(B_217,k1_xboole_0)
      | ~ v1_relat_1(B_217) ) ),
    inference(resolution,[status(thm)],[c_603,c_1162])).

tff(c_1197,plain,(
    ! [B_217] :
      ( ~ v1_funct_1(B_217)
      | ~ v5_relat_1(B_217,k1_xboole_0)
      | ~ v1_relat_1(B_217)
      | ~ r1_tarski('#skF_6',k1_relat_1(B_217)) ) ),
    inference(resolution,[status(thm)],[c_282,c_1173])).

tff(c_1549,plain,
    ( ~ v1_funct_1('#skF_9')
    | ~ v5_relat_1('#skF_9',k1_xboole_0)
    | ~ v1_relat_1('#skF_9')
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1541,c_1197])).

tff(c_1558,plain,(
    ~ v5_relat_1('#skF_9',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_194,c_90,c_1549])).

tff(c_588,plain,(
    ! [A_160,B_161] :
      ( ~ r1_tarski(A_160,k1_xboole_0)
      | r1_tarski(A_160,B_161) ) ),
    inference(resolution,[status(thm)],[c_8,c_561])).

tff(c_13251,plain,(
    ! [B_161] :
      ( r1_tarski(k2_relat_1('#skF_9'),B_161)
      | '#skF_1'(k2_relat_1('#skF_9'),k1_xboole_0) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_13131,c_588])).

tff(c_14236,plain,(
    '#skF_1'(k2_relat_1('#skF_9'),k1_xboole_0) = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_13251])).

tff(c_14261,plain,
    ( r2_hidden('#skF_7',k2_relat_1('#skF_9'))
    | r1_tarski(k2_relat_1('#skF_9'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14236,c_6])).

tff(c_15357,plain,(
    r1_tarski(k2_relat_1('#skF_9'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_14261])).

tff(c_15368,plain,
    ( v5_relat_1('#skF_9',k1_xboole_0)
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_15357,c_54])).

tff(c_15378,plain,(
    v5_relat_1('#skF_9',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_15368])).

tff(c_15380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1558,c_15378])).

tff(c_15381,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_14261])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16440,plain,(
    ! [B_24352] :
      ( r2_hidden('#skF_7',B_24352)
      | ~ r1_tarski(k2_relat_1('#skF_9'),B_24352) ) ),
    inference(resolution,[status(thm)],[c_15381,c_2])).

tff(c_16451,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_7',A_28)
      | ~ v5_relat_1('#skF_9',A_28)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_56,c_16440])).

tff(c_16462,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_7',A_28)
      | ~ v5_relat_1('#skF_9',A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_16451])).

tff(c_41880,plain,(
    ! [A_76701] :
      ( r2_hidden('#skF_7',k1_tarski(A_76701))
      | A_76701 != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_41783,c_16462])).

tff(c_43909,plain,(
    ! [B_85037,A_85038] :
      ( r2_hidden('#skF_7',B_85037)
      | ~ r1_tarski(k1_tarski(A_85038),B_85037)
      | A_85038 != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_41880,c_2])).

tff(c_45889,plain,(
    ! [B_95382,A_95383] :
      ( r2_hidden('#skF_7',B_95382)
      | A_95383 != '#skF_7'
      | '#skF_1'(k1_tarski(A_95383),B_95382) = A_95383 ) ),
    inference(resolution,[status(thm)],[c_213,c_43909])).

tff(c_49011,plain,(
    ! [A_106751,B_106752] :
      ( ~ r2_hidden(A_106751,B_106752)
      | r1_tarski(k1_tarski(A_106751),B_106752)
      | r2_hidden('#skF_7',B_106752)
      | A_106751 != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45889,c_4])).

tff(c_41972,plain,(
    ! [B_2,A_76701] :
      ( r2_hidden('#skF_7',B_2)
      | ~ r1_tarski(k1_tarski(A_76701),B_2)
      | A_76701 != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_41880,c_2])).

tff(c_49205,plain,(
    ! [A_107229,B_107230] :
      ( ~ r2_hidden(A_107229,B_107230)
      | r2_hidden('#skF_7',B_107230)
      | A_107229 != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_49011,c_41972])).

tff(c_50960,plain,(
    ! [A_112969,B_112970] :
      ( r2_hidden('#skF_7',A_112969)
      | '#skF_1'(A_112969,B_112970) != '#skF_7'
      | r1_tarski(A_112969,B_112970) ) ),
    inference(resolution,[status(thm)],[c_6,c_49205])).

tff(c_283,plain,(
    ! [B_109] :
      ( r2_hidden('#skF_8',B_109)
      | ~ r1_tarski('#skF_6',B_109) ) ),
    inference(resolution,[status(thm)],[c_84,c_258])).

tff(c_295,plain,(
    ! [A_14] :
      ( A_14 = '#skF_8'
      | ~ r1_tarski('#skF_6',k1_tarski(A_14)) ) ),
    inference(resolution,[status(thm)],[c_283,c_34])).

tff(c_51266,plain,(
    ! [A_14] :
      ( A_14 = '#skF_8'
      | r2_hidden('#skF_7','#skF_6')
      | '#skF_1'('#skF_6',k1_tarski(A_14)) != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_50960,c_295])).

tff(c_51377,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_51266])).

tff(c_36603,plain,(
    ! [B_68536,A_68537] :
      ( v5_relat_1('#skF_9',B_68536)
      | A_68537 = '#skF_1'(k2_relat_1('#skF_9'),B_68536)
      | '#skF_1'(k2_relat_1('#skF_9'),k1_tarski(A_68537)) = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_35107])).

tff(c_215242,plain,(
    ! [A_413664,B_413665] :
      ( ~ r2_hidden(A_413664,B_413665)
      | r1_tarski(k2_relat_1('#skF_9'),B_413665)
      | v5_relat_1('#skF_9',B_413665)
      | '#skF_1'(k2_relat_1('#skF_9'),k1_tarski(A_413664)) = '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36603,c_4])).

tff(c_215665,plain,
    ( r1_tarski(k2_relat_1('#skF_9'),'#skF_6')
    | v5_relat_1('#skF_9','#skF_6')
    | '#skF_1'(k2_relat_1('#skF_9'),k1_tarski('#skF_7')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_51377,c_215242])).

tff(c_215702,plain,(
    '#skF_1'(k2_relat_1('#skF_9'),k1_tarski('#skF_7')) = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_215665])).

tff(c_216662,plain,
    ( ~ r2_hidden('#skF_7',k1_tarski('#skF_7'))
    | r1_tarski(k2_relat_1('#skF_9'),k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_215702,c_4])).

tff(c_217100,plain,(
    r1_tarski(k2_relat_1('#skF_9'),k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_216662])).

tff(c_523,plain,(
    ! [A_151,B_152,B_2,B_153] :
      ( r2_hidden('#skF_1'(A_151,B_152),B_2)
      | ~ r1_tarski(B_153,B_2)
      | ~ r1_tarski(A_151,B_153)
      | r1_tarski(A_151,B_152) ) ),
    inference(resolution,[status(thm)],[c_493,c_2])).

tff(c_217267,plain,(
    ! [A_416252,B_416253] :
      ( r2_hidden('#skF_1'(A_416252,B_416253),k1_tarski('#skF_7'))
      | ~ r1_tarski(A_416252,k2_relat_1('#skF_9'))
      | r1_tarski(A_416252,B_416253) ) ),
    inference(resolution,[status(thm)],[c_217100,c_523])).

tff(c_218467,plain,(
    ! [B_129] :
      ( r2_hidden(B_129,k1_tarski('#skF_7'))
      | ~ r1_tarski(k1_tarski(B_129),k2_relat_1('#skF_9'))
      | r1_tarski(k1_tarski(B_129),B_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_217267])).

tff(c_218899,plain,(
    ! [B_417547] :
      ( r2_hidden(B_417547,k1_tarski('#skF_7'))
      | ~ r1_tarski(k1_tarski(B_417547),k2_relat_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_218467])).

tff(c_220262,plain,(
    ! [A_418844] :
      ( r2_hidden(A_418844,k1_tarski('#skF_7'))
      | '#skF_1'(k1_tarski(A_418844),k2_relat_1('#skF_9')) = A_418844 ) ),
    inference(resolution,[status(thm)],[c_213,c_218899])).

tff(c_226775,plain,(
    ! [A_428555] :
      ( ~ r2_hidden(A_428555,k2_relat_1('#skF_9'))
      | r1_tarski(k1_tarski(A_428555),k2_relat_1('#skF_9'))
      | r2_hidden(A_428555,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_220262,c_4])).

tff(c_218739,plain,(
    ! [B_129] :
      ( r2_hidden(B_129,k1_tarski('#skF_7'))
      | ~ r1_tarski(k1_tarski(B_129),k2_relat_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_218467])).

tff(c_227543,plain,(
    ! [A_429852] :
      ( ~ r2_hidden(A_429852,k2_relat_1('#skF_9'))
      | r2_hidden(A_429852,k1_tarski('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_226775,c_218739])).

tff(c_227623,plain,(
    ! [A_32] :
      ( r2_hidden(k1_funct_1('#skF_9',A_32),k1_tarski('#skF_7'))
      | ~ r2_hidden(A_32,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_60,c_227543])).

tff(c_227668,plain,(
    ! [A_430499] :
      ( r2_hidden(k1_funct_1('#skF_9',A_430499),k1_tarski('#skF_7'))
      | ~ r2_hidden(A_430499,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_90,c_1541,c_227623])).

tff(c_227804,plain,(
    ! [A_431146] :
      ( k1_funct_1('#skF_9',A_431146) = '#skF_7'
      | ~ r2_hidden(A_431146,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_227668,c_34])).

tff(c_227901,plain,
    ( k1_funct_1('#skF_9','#skF_8') = '#skF_7'
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_282,c_227804])).

tff(c_227937,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_227901])).

tff(c_227939,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_227937])).

tff(c_227941,plain,(
    '#skF_1'(k2_relat_1('#skF_9'),k1_tarski('#skF_7')) != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_215665])).

tff(c_13130,plain,(
    ! [B_17643] :
      ( '#skF_1'(k2_relat_1('#skF_9'),B_17643) = '#skF_7'
      | r1_tarski(k2_relat_1('#skF_9'),B_17643) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_13127])).

tff(c_13250,plain,(
    ! [A_14,B_152] :
      ( A_14 = '#skF_1'(k2_relat_1('#skF_9'),B_152)
      | r1_tarski(k2_relat_1('#skF_9'),B_152)
      | '#skF_1'(k2_relat_1('#skF_9'),k1_tarski(A_14)) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_13131,c_526])).

tff(c_228830,plain,(
    ! [A_14] :
      ( A_14 != '#skF_7'
      | r1_tarski(k2_relat_1('#skF_9'),k1_tarski('#skF_7'))
      | '#skF_1'(k2_relat_1('#skF_9'),k1_tarski(A_14)) = '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13250,c_227941])).

tff(c_238584,plain,(
    r1_tarski(k2_relat_1('#skF_9'),k1_tarski('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_228830])).

tff(c_238720,plain,(
    ! [A_448627,B_448628] :
      ( r2_hidden('#skF_1'(A_448627,B_448628),k1_tarski('#skF_7'))
      | ~ r1_tarski(A_448627,k2_relat_1('#skF_9'))
      | r1_tarski(A_448627,B_448628) ) ),
    inference(resolution,[status(thm)],[c_238584,c_523])).

tff(c_239927,plain,(
    ! [B_129] :
      ( r2_hidden(B_129,k1_tarski('#skF_7'))
      | ~ r1_tarski(k1_tarski(B_129),k2_relat_1('#skF_9'))
      | r1_tarski(k1_tarski(B_129),B_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_238720])).

tff(c_240363,plain,(
    ! [B_449922] :
      ( r2_hidden(B_449922,k1_tarski('#skF_7'))
      | ~ r1_tarski(k1_tarski(B_449922),k2_relat_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_239927])).

tff(c_241016,plain,(
    ! [A_451219] :
      ( r2_hidden(A_451219,k1_tarski('#skF_7'))
      | '#skF_1'(k1_tarski(A_451219),k2_relat_1('#skF_9')) = A_451219 ) ),
    inference(resolution,[status(thm)],[c_213,c_240363])).

tff(c_271127,plain,(
    ! [A_501068] :
      ( ~ r2_hidden(A_501068,k2_relat_1('#skF_9'))
      | r1_tarski(k1_tarski(A_501068),k2_relat_1('#skF_9'))
      | r2_hidden(A_501068,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_241016,c_4])).

tff(c_240203,plain,(
    ! [B_129] :
      ( r2_hidden(B_129,k1_tarski('#skF_7'))
      | ~ r1_tarski(k1_tarski(B_129),k2_relat_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_239927])).

tff(c_271386,plain,(
    ! [A_501715] :
      ( ~ r2_hidden(A_501715,k2_relat_1('#skF_9'))
      | r2_hidden(A_501715,k1_tarski('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_271127,c_240203])).

tff(c_271470,plain,(
    ! [A_32] :
      ( r2_hidden(k1_funct_1('#skF_9',A_32),k1_tarski('#skF_7'))
      | ~ r2_hidden(A_32,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_60,c_271386])).

tff(c_272062,plain,(
    ! [A_503012] :
      ( r2_hidden(k1_funct_1('#skF_9',A_503012),k1_tarski('#skF_7'))
      | ~ r2_hidden(A_503012,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_90,c_1541,c_271470])).

tff(c_272237,plain,(
    ! [A_503659] :
      ( k1_funct_1('#skF_9',A_503659) = '#skF_7'
      | ~ r2_hidden(A_503659,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_272062,c_34])).

tff(c_272362,plain,
    ( k1_funct_1('#skF_9','#skF_8') = '#skF_7'
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_282,c_272237])).

tff(c_272409,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_272362])).

tff(c_272411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_272409])).

tff(c_272413,plain,(
    ~ r1_tarski(k2_relat_1('#skF_9'),k1_tarski('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_228830])).

tff(c_272445,plain,(
    '#skF_1'(k2_relat_1('#skF_9'),k1_tarski('#skF_7')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_13130,c_272413])).

tff(c_272473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_227941,c_272445])).

tff(c_272474,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1540])).

tff(c_272544,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_272474,c_131])).

tff(c_272572,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_272544])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:49:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 49.15/37.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 49.15/37.15  
% 49.15/37.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 49.15/37.15  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 49.15/37.15  
% 49.15/37.15  %Foreground sorts:
% 49.15/37.15  
% 49.15/37.15  
% 49.15/37.15  %Background operators:
% 49.15/37.15  
% 49.15/37.15  
% 49.15/37.15  %Foreground operators:
% 49.15/37.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 49.15/37.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 49.15/37.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 49.15/37.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 49.15/37.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 49.15/37.15  tff('#skF_7', type, '#skF_7': $i).
% 49.15/37.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 49.15/37.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 49.15/37.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 49.15/37.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 49.15/37.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 49.15/37.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 49.15/37.15  tff('#skF_6', type, '#skF_6': $i).
% 49.15/37.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 49.15/37.15  tff('#skF_9', type, '#skF_9': $i).
% 49.15/37.15  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 49.15/37.15  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 49.15/37.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 49.15/37.15  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 49.15/37.15  tff('#skF_8', type, '#skF_8': $i).
% 49.15/37.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 49.15/37.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 49.15/37.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 49.15/37.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 49.15/37.15  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 49.15/37.15  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 49.15/37.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 49.15/37.15  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 49.15/37.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 49.15/37.15  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 49.15/37.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 49.15/37.15  
% 49.15/37.18  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 49.15/37.18  tff(f_129, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 49.15/37.18  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 49.15/37.18  tff(f_77, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 49.15/37.18  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 49.15/37.18  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 49.15/37.18  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 49.15/37.18  tff(f_85, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 49.15/37.18  tff(f_56, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 49.15/37.18  tff(f_90, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 49.15/37.18  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 49.15/37.18  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 49.15/37.18  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 49.15/37.18  tff(c_82, plain, (k1_funct_1('#skF_9', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_129])).
% 49.15/37.18  tff(c_199, plain, (![A_87, B_88]: (r2_hidden('#skF_1'(A_87, B_88), A_87) | r1_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_32])).
% 49.15/37.18  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 49.15/37.18  tff(c_211, plain, (![A_87]: (r1_tarski(A_87, A_87))), inference(resolution, [status(thm)], [c_199, c_4])).
% 49.15/37.18  tff(c_84, plain, (r2_hidden('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_129])).
% 49.15/37.18  tff(c_258, plain, (![C_106, B_107, A_108]: (r2_hidden(C_106, B_107) | ~r2_hidden(C_106, A_108) | ~r1_tarski(A_108, B_107))), inference(cnfTransformation, [status(thm)], [f_32])).
% 49.15/37.18  tff(c_282, plain, (![B_107]: (r2_hidden('#skF_8', B_107) | ~r1_tarski('#skF_6', B_107))), inference(resolution, [status(thm)], [c_84, c_258])).
% 49.15/37.18  tff(c_58, plain, (![A_30, B_31]: (v1_relat_1(k2_zfmisc_1(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 49.15/37.18  tff(c_86, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 49.15/37.18  tff(c_188, plain, (![B_82, A_83]: (v1_relat_1(B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(A_83)) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_69])).
% 49.15/37.18  tff(c_191, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7')))), inference(resolution, [status(thm)], [c_86, c_188])).
% 49.15/37.18  tff(c_194, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_191])).
% 49.15/37.18  tff(c_90, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_129])).
% 49.15/37.18  tff(c_88, plain, (v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 49.15/37.18  tff(c_935, plain, (![A_184, B_185, C_186]: (k1_relset_1(A_184, B_185, C_186)=k1_relat_1(C_186) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 49.15/37.18  tff(c_939, plain, (k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_86, c_935])).
% 49.15/37.18  tff(c_1534, plain, (![B_250, A_251, C_252]: (k1_xboole_0=B_250 | k1_relset_1(A_251, B_250, C_252)=A_251 | ~v1_funct_2(C_252, A_251, B_250) | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(A_251, B_250))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 49.15/37.18  tff(c_1537, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_86, c_1534])).
% 49.15/37.18  tff(c_1540, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_939, c_1537])).
% 49.15/37.18  tff(c_1541, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_1540])).
% 49.15/37.18  tff(c_60, plain, (![B_33, A_32]: (r2_hidden(k1_funct_1(B_33, A_32), k2_relat_1(B_33)) | ~r2_hidden(A_32, k1_relat_1(B_33)) | ~v1_funct_1(B_33) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_85])).
% 49.15/37.18  tff(c_34, plain, (![C_18, A_14]: (C_18=A_14 | ~r2_hidden(C_18, k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 49.15/37.18  tff(c_213, plain, (![A_14, B_88]: ('#skF_1'(k1_tarski(A_14), B_88)=A_14 | r1_tarski(k1_tarski(A_14), B_88))), inference(resolution, [status(thm)], [c_199, c_34])).
% 49.15/37.18  tff(c_36, plain, (![C_18]: (r2_hidden(C_18, k1_tarski(C_18)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 49.15/37.18  tff(c_112, plain, (![B_61, A_62]: (~r1_tarski(B_61, A_62) | ~r2_hidden(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_90])).
% 49.15/37.18  tff(c_131, plain, (![C_18]: (~r1_tarski(k1_tarski(C_18), C_18))), inference(resolution, [status(thm)], [c_36, c_112])).
% 49.15/37.18  tff(c_358, plain, (![A_128, B_129]: ('#skF_1'(k1_tarski(A_128), B_129)=A_128 | r1_tarski(k1_tarski(A_128), B_129))), inference(resolution, [status(thm)], [c_199, c_34])).
% 49.15/37.18  tff(c_379, plain, (![B_129]: ('#skF_1'(k1_tarski(B_129), B_129)=B_129)), inference(resolution, [status(thm)], [c_358, c_131])).
% 49.15/37.18  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 49.15/37.18  tff(c_253, plain, (![C_103, B_104, A_105]: (v5_relat_1(C_103, B_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_105, B_104))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 49.15/37.18  tff(c_257, plain, (v5_relat_1('#skF_9', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_86, c_253])).
% 49.15/37.18  tff(c_56, plain, (![B_29, A_28]: (r1_tarski(k2_relat_1(B_29), A_28) | ~v5_relat_1(B_29, A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_75])).
% 49.15/37.18  tff(c_493, plain, (![A_151, B_152, B_153]: (r2_hidden('#skF_1'(A_151, B_152), B_153) | ~r1_tarski(A_151, B_153) | r1_tarski(A_151, B_152))), inference(resolution, [status(thm)], [c_6, c_258])).
% 49.15/37.18  tff(c_950, plain, (![A_187, A_188, B_189]: (A_187='#skF_1'(A_188, B_189) | ~r1_tarski(A_188, k1_tarski(A_187)) | r1_tarski(A_188, B_189))), inference(resolution, [status(thm)], [c_493, c_34])).
% 49.15/37.18  tff(c_13055, plain, (![A_17641, B_17642, B_17643]: (A_17641='#skF_1'(k2_relat_1(B_17642), B_17643) | r1_tarski(k2_relat_1(B_17642), B_17643) | ~v5_relat_1(B_17642, k1_tarski(A_17641)) | ~v1_relat_1(B_17642))), inference(resolution, [status(thm)], [c_56, c_950])).
% 49.15/37.18  tff(c_13127, plain, (![B_17643]: ('#skF_1'(k2_relat_1('#skF_9'), B_17643)='#skF_7' | r1_tarski(k2_relat_1('#skF_9'), B_17643) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_257, c_13055])).
% 49.15/37.18  tff(c_13131, plain, (![B_17780]: ('#skF_1'(k2_relat_1('#skF_9'), B_17780)='#skF_7' | r1_tarski(k2_relat_1('#skF_9'), B_17780))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_13127])).
% 49.15/37.18  tff(c_526, plain, (![A_14, A_151, B_152]: (A_14='#skF_1'(A_151, B_152) | ~r1_tarski(A_151, k1_tarski(A_14)) | r1_tarski(A_151, B_152))), inference(resolution, [status(thm)], [c_493, c_34])).
% 49.15/37.18  tff(c_31984, plain, (![A_60336, B_60337]: (A_60336='#skF_1'(k2_relat_1('#skF_9'), B_60337) | r1_tarski(k2_relat_1('#skF_9'), B_60337) | '#skF_1'(k2_relat_1('#skF_9'), k1_tarski(A_60336))='#skF_7')), inference(resolution, [status(thm)], [c_13131, c_526])).
% 49.15/37.18  tff(c_54, plain, (![B_29, A_28]: (v5_relat_1(B_29, A_28) | ~r1_tarski(k2_relat_1(B_29), A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_75])).
% 49.15/37.18  tff(c_35107, plain, (![B_60337, A_60336]: (v5_relat_1('#skF_9', B_60337) | ~v1_relat_1('#skF_9') | A_60336='#skF_1'(k2_relat_1('#skF_9'), B_60337) | '#skF_1'(k2_relat_1('#skF_9'), k1_tarski(A_60336))='#skF_7')), inference(resolution, [status(thm)], [c_31984, c_54])).
% 49.15/37.18  tff(c_35668, plain, (![B_60337, A_60336]: (v5_relat_1('#skF_9', B_60337) | A_60336='#skF_1'(k2_relat_1('#skF_9'), B_60337) | '#skF_1'(k2_relat_1('#skF_9'), k1_tarski(A_60336))='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_35107])).
% 49.15/37.18  tff(c_41175, plain, (![A_75576]: (v5_relat_1('#skF_9', k1_tarski(A_75576)) | '#skF_1'(k2_relat_1('#skF_9'), k1_tarski(A_75576))=A_75576 | A_75576!='#skF_7')), inference(factorization, [status(thm), theory('equality')], [c_35668])).
% 49.15/37.18  tff(c_41244, plain, (![A_75576]: (~r2_hidden(A_75576, k1_tarski(A_75576)) | r1_tarski(k2_relat_1('#skF_9'), k1_tarski(A_75576)) | v5_relat_1('#skF_9', k1_tarski(A_75576)) | A_75576!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_41175, c_4])).
% 49.15/37.18  tff(c_41648, plain, (![A_75951]: (r1_tarski(k2_relat_1('#skF_9'), k1_tarski(A_75951)) | v5_relat_1('#skF_9', k1_tarski(A_75951)) | A_75951!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_41244])).
% 49.15/37.18  tff(c_41670, plain, (![A_75951]: (~v1_relat_1('#skF_9') | v5_relat_1('#skF_9', k1_tarski(A_75951)) | A_75951!='#skF_7')), inference(resolution, [status(thm)], [c_41648, c_54])).
% 49.15/37.18  tff(c_41783, plain, (![A_76326]: (v5_relat_1('#skF_9', k1_tarski(A_76326)) | A_76326!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_41670])).
% 49.15/37.18  tff(c_62, plain, (![B_35, A_34]: (~r1_tarski(B_35, A_34) | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_90])).
% 49.15/37.18  tff(c_561, plain, (![B_159, A_160, B_161]: (~r1_tarski(B_159, '#skF_1'(A_160, B_161)) | ~r1_tarski(A_160, B_159) | r1_tarski(A_160, B_161))), inference(resolution, [status(thm)], [c_493, c_62])).
% 49.15/37.18  tff(c_589, plain, (![A_162, B_163]: (~r1_tarski(A_162, k1_xboole_0) | r1_tarski(A_162, B_163))), inference(resolution, [status(thm)], [c_8, c_561])).
% 49.15/37.18  tff(c_603, plain, (![B_29, B_163]: (r1_tarski(k2_relat_1(B_29), B_163) | ~v5_relat_1(B_29, k1_xboole_0) | ~v1_relat_1(B_29))), inference(resolution, [status(thm)], [c_56, c_589])).
% 49.15/37.18  tff(c_1127, plain, (![B_208, A_209]: (r2_hidden(k1_funct_1(B_208, A_209), k2_relat_1(B_208)) | ~r2_hidden(A_209, k1_relat_1(B_208)) | ~v1_funct_1(B_208) | ~v1_relat_1(B_208))), inference(cnfTransformation, [status(thm)], [f_85])).
% 49.15/37.18  tff(c_1162, plain, (![B_214, A_215]: (~r1_tarski(k2_relat_1(B_214), k1_funct_1(B_214, A_215)) | ~r2_hidden(A_215, k1_relat_1(B_214)) | ~v1_funct_1(B_214) | ~v1_relat_1(B_214))), inference(resolution, [status(thm)], [c_1127, c_62])).
% 49.15/37.18  tff(c_1173, plain, (![A_216, B_217]: (~r2_hidden(A_216, k1_relat_1(B_217)) | ~v1_funct_1(B_217) | ~v5_relat_1(B_217, k1_xboole_0) | ~v1_relat_1(B_217))), inference(resolution, [status(thm)], [c_603, c_1162])).
% 49.15/37.18  tff(c_1197, plain, (![B_217]: (~v1_funct_1(B_217) | ~v5_relat_1(B_217, k1_xboole_0) | ~v1_relat_1(B_217) | ~r1_tarski('#skF_6', k1_relat_1(B_217)))), inference(resolution, [status(thm)], [c_282, c_1173])).
% 49.15/37.18  tff(c_1549, plain, (~v1_funct_1('#skF_9') | ~v5_relat_1('#skF_9', k1_xboole_0) | ~v1_relat_1('#skF_9') | ~r1_tarski('#skF_6', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1541, c_1197])).
% 49.15/37.18  tff(c_1558, plain, (~v5_relat_1('#skF_9', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_211, c_194, c_90, c_1549])).
% 49.15/37.18  tff(c_588, plain, (![A_160, B_161]: (~r1_tarski(A_160, k1_xboole_0) | r1_tarski(A_160, B_161))), inference(resolution, [status(thm)], [c_8, c_561])).
% 49.15/37.18  tff(c_13251, plain, (![B_161]: (r1_tarski(k2_relat_1('#skF_9'), B_161) | '#skF_1'(k2_relat_1('#skF_9'), k1_xboole_0)='#skF_7')), inference(resolution, [status(thm)], [c_13131, c_588])).
% 49.15/37.18  tff(c_14236, plain, ('#skF_1'(k2_relat_1('#skF_9'), k1_xboole_0)='#skF_7'), inference(splitLeft, [status(thm)], [c_13251])).
% 49.15/37.18  tff(c_14261, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_9')) | r1_tarski(k2_relat_1('#skF_9'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14236, c_6])).
% 49.15/37.18  tff(c_15357, plain, (r1_tarski(k2_relat_1('#skF_9'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_14261])).
% 49.15/37.18  tff(c_15368, plain, (v5_relat_1('#skF_9', k1_xboole_0) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_15357, c_54])).
% 49.15/37.18  tff(c_15378, plain, (v5_relat_1('#skF_9', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_194, c_15368])).
% 49.15/37.18  tff(c_15380, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1558, c_15378])).
% 49.15/37.18  tff(c_15381, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_14261])).
% 49.15/37.18  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 49.15/37.18  tff(c_16440, plain, (![B_24352]: (r2_hidden('#skF_7', B_24352) | ~r1_tarski(k2_relat_1('#skF_9'), B_24352))), inference(resolution, [status(thm)], [c_15381, c_2])).
% 49.15/37.18  tff(c_16451, plain, (![A_28]: (r2_hidden('#skF_7', A_28) | ~v5_relat_1('#skF_9', A_28) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_56, c_16440])).
% 49.15/37.18  tff(c_16462, plain, (![A_28]: (r2_hidden('#skF_7', A_28) | ~v5_relat_1('#skF_9', A_28))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_16451])).
% 49.15/37.18  tff(c_41880, plain, (![A_76701]: (r2_hidden('#skF_7', k1_tarski(A_76701)) | A_76701!='#skF_7')), inference(resolution, [status(thm)], [c_41783, c_16462])).
% 49.15/37.18  tff(c_43909, plain, (![B_85037, A_85038]: (r2_hidden('#skF_7', B_85037) | ~r1_tarski(k1_tarski(A_85038), B_85037) | A_85038!='#skF_7')), inference(resolution, [status(thm)], [c_41880, c_2])).
% 49.15/37.18  tff(c_45889, plain, (![B_95382, A_95383]: (r2_hidden('#skF_7', B_95382) | A_95383!='#skF_7' | '#skF_1'(k1_tarski(A_95383), B_95382)=A_95383)), inference(resolution, [status(thm)], [c_213, c_43909])).
% 49.15/37.18  tff(c_49011, plain, (![A_106751, B_106752]: (~r2_hidden(A_106751, B_106752) | r1_tarski(k1_tarski(A_106751), B_106752) | r2_hidden('#skF_7', B_106752) | A_106751!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_45889, c_4])).
% 49.15/37.18  tff(c_41972, plain, (![B_2, A_76701]: (r2_hidden('#skF_7', B_2) | ~r1_tarski(k1_tarski(A_76701), B_2) | A_76701!='#skF_7')), inference(resolution, [status(thm)], [c_41880, c_2])).
% 49.15/37.18  tff(c_49205, plain, (![A_107229, B_107230]: (~r2_hidden(A_107229, B_107230) | r2_hidden('#skF_7', B_107230) | A_107229!='#skF_7')), inference(resolution, [status(thm)], [c_49011, c_41972])).
% 49.15/37.18  tff(c_50960, plain, (![A_112969, B_112970]: (r2_hidden('#skF_7', A_112969) | '#skF_1'(A_112969, B_112970)!='#skF_7' | r1_tarski(A_112969, B_112970))), inference(resolution, [status(thm)], [c_6, c_49205])).
% 49.15/37.18  tff(c_283, plain, (![B_109]: (r2_hidden('#skF_8', B_109) | ~r1_tarski('#skF_6', B_109))), inference(resolution, [status(thm)], [c_84, c_258])).
% 49.15/37.18  tff(c_295, plain, (![A_14]: (A_14='#skF_8' | ~r1_tarski('#skF_6', k1_tarski(A_14)))), inference(resolution, [status(thm)], [c_283, c_34])).
% 49.15/37.18  tff(c_51266, plain, (![A_14]: (A_14='#skF_8' | r2_hidden('#skF_7', '#skF_6') | '#skF_1'('#skF_6', k1_tarski(A_14))!='#skF_7')), inference(resolution, [status(thm)], [c_50960, c_295])).
% 49.15/37.18  tff(c_51377, plain, (r2_hidden('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_51266])).
% 49.15/37.18  tff(c_36603, plain, (![B_68536, A_68537]: (v5_relat_1('#skF_9', B_68536) | A_68537='#skF_1'(k2_relat_1('#skF_9'), B_68536) | '#skF_1'(k2_relat_1('#skF_9'), k1_tarski(A_68537))='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_35107])).
% 49.15/37.18  tff(c_215242, plain, (![A_413664, B_413665]: (~r2_hidden(A_413664, B_413665) | r1_tarski(k2_relat_1('#skF_9'), B_413665) | v5_relat_1('#skF_9', B_413665) | '#skF_1'(k2_relat_1('#skF_9'), k1_tarski(A_413664))='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_36603, c_4])).
% 49.15/37.18  tff(c_215665, plain, (r1_tarski(k2_relat_1('#skF_9'), '#skF_6') | v5_relat_1('#skF_9', '#skF_6') | '#skF_1'(k2_relat_1('#skF_9'), k1_tarski('#skF_7'))='#skF_7'), inference(resolution, [status(thm)], [c_51377, c_215242])).
% 49.15/37.18  tff(c_215702, plain, ('#skF_1'(k2_relat_1('#skF_9'), k1_tarski('#skF_7'))='#skF_7'), inference(splitLeft, [status(thm)], [c_215665])).
% 49.15/37.18  tff(c_216662, plain, (~r2_hidden('#skF_7', k1_tarski('#skF_7')) | r1_tarski(k2_relat_1('#skF_9'), k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_215702, c_4])).
% 49.15/37.18  tff(c_217100, plain, (r1_tarski(k2_relat_1('#skF_9'), k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_216662])).
% 49.15/37.18  tff(c_523, plain, (![A_151, B_152, B_2, B_153]: (r2_hidden('#skF_1'(A_151, B_152), B_2) | ~r1_tarski(B_153, B_2) | ~r1_tarski(A_151, B_153) | r1_tarski(A_151, B_152))), inference(resolution, [status(thm)], [c_493, c_2])).
% 49.15/37.18  tff(c_217267, plain, (![A_416252, B_416253]: (r2_hidden('#skF_1'(A_416252, B_416253), k1_tarski('#skF_7')) | ~r1_tarski(A_416252, k2_relat_1('#skF_9')) | r1_tarski(A_416252, B_416253))), inference(resolution, [status(thm)], [c_217100, c_523])).
% 49.15/37.18  tff(c_218467, plain, (![B_129]: (r2_hidden(B_129, k1_tarski('#skF_7')) | ~r1_tarski(k1_tarski(B_129), k2_relat_1('#skF_9')) | r1_tarski(k1_tarski(B_129), B_129))), inference(superposition, [status(thm), theory('equality')], [c_379, c_217267])).
% 49.15/37.18  tff(c_218899, plain, (![B_417547]: (r2_hidden(B_417547, k1_tarski('#skF_7')) | ~r1_tarski(k1_tarski(B_417547), k2_relat_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_131, c_218467])).
% 49.15/37.18  tff(c_220262, plain, (![A_418844]: (r2_hidden(A_418844, k1_tarski('#skF_7')) | '#skF_1'(k1_tarski(A_418844), k2_relat_1('#skF_9'))=A_418844)), inference(resolution, [status(thm)], [c_213, c_218899])).
% 49.15/37.18  tff(c_226775, plain, (![A_428555]: (~r2_hidden(A_428555, k2_relat_1('#skF_9')) | r1_tarski(k1_tarski(A_428555), k2_relat_1('#skF_9')) | r2_hidden(A_428555, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_220262, c_4])).
% 49.15/37.18  tff(c_218739, plain, (![B_129]: (r2_hidden(B_129, k1_tarski('#skF_7')) | ~r1_tarski(k1_tarski(B_129), k2_relat_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_131, c_218467])).
% 49.15/37.18  tff(c_227543, plain, (![A_429852]: (~r2_hidden(A_429852, k2_relat_1('#skF_9')) | r2_hidden(A_429852, k1_tarski('#skF_7')))), inference(resolution, [status(thm)], [c_226775, c_218739])).
% 49.15/37.18  tff(c_227623, plain, (![A_32]: (r2_hidden(k1_funct_1('#skF_9', A_32), k1_tarski('#skF_7')) | ~r2_hidden(A_32, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_60, c_227543])).
% 49.15/37.18  tff(c_227668, plain, (![A_430499]: (r2_hidden(k1_funct_1('#skF_9', A_430499), k1_tarski('#skF_7')) | ~r2_hidden(A_430499, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_90, c_1541, c_227623])).
% 49.15/37.18  tff(c_227804, plain, (![A_431146]: (k1_funct_1('#skF_9', A_431146)='#skF_7' | ~r2_hidden(A_431146, '#skF_6'))), inference(resolution, [status(thm)], [c_227668, c_34])).
% 49.15/37.18  tff(c_227901, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7' | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_282, c_227804])).
% 49.15/37.18  tff(c_227937, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_211, c_227901])).
% 49.15/37.18  tff(c_227939, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_227937])).
% 49.15/37.18  tff(c_227941, plain, ('#skF_1'(k2_relat_1('#skF_9'), k1_tarski('#skF_7'))!='#skF_7'), inference(splitRight, [status(thm)], [c_215665])).
% 49.15/37.18  tff(c_13130, plain, (![B_17643]: ('#skF_1'(k2_relat_1('#skF_9'), B_17643)='#skF_7' | r1_tarski(k2_relat_1('#skF_9'), B_17643))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_13127])).
% 49.15/37.18  tff(c_13250, plain, (![A_14, B_152]: (A_14='#skF_1'(k2_relat_1('#skF_9'), B_152) | r1_tarski(k2_relat_1('#skF_9'), B_152) | '#skF_1'(k2_relat_1('#skF_9'), k1_tarski(A_14))='#skF_7')), inference(resolution, [status(thm)], [c_13131, c_526])).
% 49.15/37.18  tff(c_228830, plain, (![A_14]: (A_14!='#skF_7' | r1_tarski(k2_relat_1('#skF_9'), k1_tarski('#skF_7')) | '#skF_1'(k2_relat_1('#skF_9'), k1_tarski(A_14))='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_13250, c_227941])).
% 49.15/37.18  tff(c_238584, plain, (r1_tarski(k2_relat_1('#skF_9'), k1_tarski('#skF_7'))), inference(splitLeft, [status(thm)], [c_228830])).
% 49.15/37.18  tff(c_238720, plain, (![A_448627, B_448628]: (r2_hidden('#skF_1'(A_448627, B_448628), k1_tarski('#skF_7')) | ~r1_tarski(A_448627, k2_relat_1('#skF_9')) | r1_tarski(A_448627, B_448628))), inference(resolution, [status(thm)], [c_238584, c_523])).
% 49.15/37.18  tff(c_239927, plain, (![B_129]: (r2_hidden(B_129, k1_tarski('#skF_7')) | ~r1_tarski(k1_tarski(B_129), k2_relat_1('#skF_9')) | r1_tarski(k1_tarski(B_129), B_129))), inference(superposition, [status(thm), theory('equality')], [c_379, c_238720])).
% 49.15/37.18  tff(c_240363, plain, (![B_449922]: (r2_hidden(B_449922, k1_tarski('#skF_7')) | ~r1_tarski(k1_tarski(B_449922), k2_relat_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_131, c_239927])).
% 49.15/37.18  tff(c_241016, plain, (![A_451219]: (r2_hidden(A_451219, k1_tarski('#skF_7')) | '#skF_1'(k1_tarski(A_451219), k2_relat_1('#skF_9'))=A_451219)), inference(resolution, [status(thm)], [c_213, c_240363])).
% 49.15/37.18  tff(c_271127, plain, (![A_501068]: (~r2_hidden(A_501068, k2_relat_1('#skF_9')) | r1_tarski(k1_tarski(A_501068), k2_relat_1('#skF_9')) | r2_hidden(A_501068, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_241016, c_4])).
% 49.15/37.18  tff(c_240203, plain, (![B_129]: (r2_hidden(B_129, k1_tarski('#skF_7')) | ~r1_tarski(k1_tarski(B_129), k2_relat_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_131, c_239927])).
% 49.15/37.18  tff(c_271386, plain, (![A_501715]: (~r2_hidden(A_501715, k2_relat_1('#skF_9')) | r2_hidden(A_501715, k1_tarski('#skF_7')))), inference(resolution, [status(thm)], [c_271127, c_240203])).
% 49.15/37.18  tff(c_271470, plain, (![A_32]: (r2_hidden(k1_funct_1('#skF_9', A_32), k1_tarski('#skF_7')) | ~r2_hidden(A_32, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_60, c_271386])).
% 49.15/37.18  tff(c_272062, plain, (![A_503012]: (r2_hidden(k1_funct_1('#skF_9', A_503012), k1_tarski('#skF_7')) | ~r2_hidden(A_503012, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_90, c_1541, c_271470])).
% 49.15/37.18  tff(c_272237, plain, (![A_503659]: (k1_funct_1('#skF_9', A_503659)='#skF_7' | ~r2_hidden(A_503659, '#skF_6'))), inference(resolution, [status(thm)], [c_272062, c_34])).
% 49.15/37.18  tff(c_272362, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7' | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_282, c_272237])).
% 49.15/37.18  tff(c_272409, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_211, c_272362])).
% 49.15/37.18  tff(c_272411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_272409])).
% 49.15/37.18  tff(c_272413, plain, (~r1_tarski(k2_relat_1('#skF_9'), k1_tarski('#skF_7'))), inference(splitRight, [status(thm)], [c_228830])).
% 49.15/37.18  tff(c_272445, plain, ('#skF_1'(k2_relat_1('#skF_9'), k1_tarski('#skF_7'))='#skF_7'), inference(resolution, [status(thm)], [c_13130, c_272413])).
% 49.15/37.18  tff(c_272473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_227941, c_272445])).
% 49.15/37.18  tff(c_272474, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1540])).
% 49.15/37.18  tff(c_272544, plain, (~r1_tarski(k1_xboole_0, '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_272474, c_131])).
% 49.15/37.18  tff(c_272572, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_272544])).
% 49.15/37.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 49.15/37.18  
% 49.15/37.18  Inference rules
% 49.15/37.18  ----------------------
% 49.15/37.18  #Ref     : 1
% 49.15/37.18  #Sup     : 44597
% 49.15/37.18  #Fact    : 326
% 49.15/37.18  #Define  : 0
% 49.15/37.18  #Split   : 81
% 49.15/37.18  #Chain   : 0
% 49.15/37.18  #Close   : 0
% 49.15/37.18  
% 49.15/37.18  Ordering : KBO
% 49.15/37.18  
% 49.15/37.18  Simplification rules
% 49.15/37.18  ----------------------
% 49.15/37.18  #Subsume      : 17192
% 49.15/37.18  #Demod        : 5669
% 49.15/37.18  #Tautology    : 7095
% 49.15/37.18  #SimpNegUnit  : 1303
% 49.15/37.18  #BackRed      : 145
% 49.15/37.18  
% 49.15/37.18  #Partial instantiations: 296220
% 49.15/37.18  #Strategies tried      : 1
% 49.15/37.18  
% 49.15/37.18  Timing (in seconds)
% 49.15/37.18  ----------------------
% 49.15/37.18  Preprocessing        : 0.34
% 49.15/37.18  Parsing              : 0.17
% 49.15/37.18  CNF conversion       : 0.03
% 49.15/37.18  Main loop            : 36.05
% 49.15/37.18  Inferencing          : 8.26
% 49.15/37.18  Reduction            : 9.00
% 49.15/37.18  Demodulation         : 5.77
% 49.15/37.18  BG Simplification    : 0.66
% 49.15/37.18  Subsumption          : 15.96
% 49.15/37.18  Abstraction          : 1.04
% 49.15/37.18  MUC search           : 0.00
% 49.15/37.18  Cooper               : 0.00
% 49.15/37.18  Total                : 36.44
% 49.15/37.18  Index Insertion      : 0.00
% 49.15/37.18  Index Deletion       : 0.00
% 49.15/37.18  Index Matching       : 0.00
% 49.15/37.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
