%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:26 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 379 expanded)
%              Number of leaves         :   44 ( 142 expanded)
%              Depth                    :   16
%              Number of atoms          :  184 ( 799 expanded)
%              Number of equality atoms :   74 ( 344 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_70,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_127,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_101,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_112,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_120,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_112])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_40,plain,(
    ! [A_23] :
      ( k1_relat_1(A_23) != k1_xboole_0
      | k1_xboole_0 = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_129,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_120,c_40])).

tff(c_145,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_412,plain,(
    ! [B_105,A_106] :
      ( k1_tarski(k1_funct_1(B_105,A_106)) = k2_relat_1(B_105)
      | k1_tarski(A_106) != k1_relat_1(B_105)
      | ~ v1_funct_1(B_105)
      | ~ v1_relat_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_338,plain,(
    ! [A_98,B_99,C_100] :
      ( k2_relset_1(A_98,B_99,C_100) = k2_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_346,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_338])).

tff(c_60,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_374,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_60])).

tff(c_418,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_374])).

tff(c_428,plain,(
    k1_tarski('#skF_2') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_68,c_418])).

tff(c_241,plain,(
    ! [C_80,A_81,B_82] :
      ( v4_relat_1(C_80,A_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_249,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_241])).

tff(c_30,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k1_relat_1(B_20),A_19)
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_199,plain,(
    ! [B_75,A_76] :
      ( k1_tarski(B_75) = A_76
      | k1_xboole_0 = A_76
      | ~ r1_tarski(A_76,k1_tarski(B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_572,plain,(
    ! [B_123,B_124] :
      ( k1_tarski(B_123) = k1_relat_1(B_124)
      | k1_relat_1(B_124) = k1_xboole_0
      | ~ v4_relat_1(B_124,k1_tarski(B_123))
      | ~ v1_relat_1(B_124) ) ),
    inference(resolution,[status(thm)],[c_30,c_199])).

tff(c_582,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_249,c_572])).

tff(c_590,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_582])).

tff(c_592,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_428,c_590])).

tff(c_593,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_602,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_593,c_34])).

tff(c_38,plain,(
    ! [A_23] :
      ( k2_relat_1(A_23) != k1_xboole_0
      | k1_xboole_0 = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_128,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_120,c_38])).

tff(c_144,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_595,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_144])).

tff(c_629,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_595])).

tff(c_630,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_639,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_630,c_36])).

tff(c_631,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_662,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_631])).

tff(c_925,plain,(
    ! [B_174,A_175] :
      ( k1_tarski(k1_funct_1(B_174,A_175)) = k2_relat_1(B_174)
      | k1_tarski(A_175) != k1_relat_1(B_174)
      | ~ v1_funct_1(B_174)
      | ~ v1_relat_1(B_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_24,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_635,plain,(
    ! [A_15] : m1_subset_1('#skF_4',k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_24])).

tff(c_877,plain,(
    ! [A_168,B_169,C_170] :
      ( k2_relset_1(A_168,B_169,C_170) = k2_relat_1(C_170)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_881,plain,(
    ! [A_168,B_169] : k2_relset_1(A_168,B_169,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_635,c_877])).

tff(c_883,plain,(
    ! [A_168,B_169] : k2_relset_1(A_168,B_169,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_881])).

tff(c_884,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_883,c_60])).

tff(c_931,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_925,c_884])).

tff(c_940,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_68,c_639,c_662,c_931])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_637,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_10])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_641,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_62])).

tff(c_66,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    ! [D_43,C_42,A_40,B_41] :
      ( r2_hidden(k1_funct_1(D_43,C_42),k2_relset_1(A_40,B_41,D_43))
      | k1_xboole_0 = B_41
      | ~ r2_hidden(C_42,A_40)
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | ~ v1_funct_2(D_43,A_40,B_41)
      | ~ v1_funct_1(D_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1032,plain,(
    ! [D_184,C_185,A_186,B_187] :
      ( r2_hidden(k1_funct_1(D_184,C_185),k2_relset_1(A_186,B_187,D_184))
      | B_187 = '#skF_4'
      | ~ r2_hidden(C_185,A_186)
      | ~ m1_subset_1(D_184,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187)))
      | ~ v1_funct_2(D_184,A_186,B_187)
      | ~ v1_funct_1(D_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_58])).

tff(c_1040,plain,(
    ! [C_185,B_169,A_168] :
      ( r2_hidden(k1_funct_1('#skF_4',C_185),'#skF_4')
      | B_169 = '#skF_4'
      | ~ r2_hidden(C_185,A_168)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_168,B_169)))
      | ~ v1_funct_2('#skF_4',A_168,B_169)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_883,c_1032])).

tff(c_1395,plain,(
    ! [C_217,B_218,A_219] :
      ( r2_hidden(k1_funct_1('#skF_4',C_217),'#skF_4')
      | B_218 = '#skF_4'
      | ~ r2_hidden(C_217,A_219)
      | ~ v1_funct_2('#skF_4',A_219,B_218) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_635,c_1040])).

tff(c_1811,plain,(
    ! [A_234,B_235,B_236] :
      ( r2_hidden(k1_funct_1('#skF_4','#skF_1'(A_234,B_235)),'#skF_4')
      | B_236 = '#skF_4'
      | ~ v1_funct_2('#skF_4',A_234,B_236)
      | r1_tarski(A_234,B_235) ) ),
    inference(resolution,[status(thm)],[c_6,c_1395])).

tff(c_1813,plain,(
    ! [B_235] :
      ( r2_hidden(k1_funct_1('#skF_4','#skF_1'(k1_tarski('#skF_2'),B_235)),'#skF_4')
      | '#skF_3' = '#skF_4'
      | r1_tarski(k1_tarski('#skF_2'),B_235) ) ),
    inference(resolution,[status(thm)],[c_66,c_1811])).

tff(c_1817,plain,(
    ! [B_237] :
      ( r2_hidden(k1_funct_1('#skF_4','#skF_1'(k1_tarski('#skF_2'),B_237)),'#skF_4')
      | r1_tarski(k1_tarski('#skF_2'),B_237) ) ),
    inference(negUnitSimplification,[status(thm)],[c_641,c_1813])).

tff(c_48,plain,(
    ! [B_30,A_29] :
      ( ~ r1_tarski(B_30,A_29)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1826,plain,(
    ! [B_237] :
      ( ~ r1_tarski('#skF_4',k1_funct_1('#skF_4','#skF_1'(k1_tarski('#skF_2'),B_237)))
      | r1_tarski(k1_tarski('#skF_2'),B_237) ) ),
    inference(resolution,[status(thm)],[c_1817,c_48])).

tff(c_1836,plain,(
    ! [B_238] : r1_tarski(k1_tarski('#skF_2'),B_238) ),
    inference(demodulation,[status(thm),theory(equality)],[c_637,c_1826])).

tff(c_724,plain,(
    ! [C_140,A_141,B_142] :
      ( v4_relat_1(C_140,A_141)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_729,plain,(
    ! [A_141] : v4_relat_1('#skF_4',A_141) ),
    inference(resolution,[status(thm)],[c_635,c_724])).

tff(c_735,plain,(
    ! [B_147,A_148] :
      ( k7_relat_1(B_147,A_148) = B_147
      | ~ v4_relat_1(B_147,A_148)
      | ~ v1_relat_1(B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_738,plain,(
    ! [A_141] :
      ( k7_relat_1('#skF_4',A_141) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_729,c_735])).

tff(c_741,plain,(
    ! [A_141] : k7_relat_1('#skF_4',A_141) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_738])).

tff(c_838,plain,(
    ! [B_165,A_166] :
      ( k1_relat_1(k7_relat_1(B_165,A_166)) = A_166
      | ~ r1_tarski(A_166,k1_relat_1(B_165))
      | ~ v1_relat_1(B_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_849,plain,(
    ! [A_166] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_166)) = A_166
      | ~ r1_tarski(A_166,'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_639,c_838])).

tff(c_857,plain,(
    ! [A_166] :
      ( A_166 = '#skF_4'
      | ~ r1_tarski(A_166,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_639,c_741,c_849])).

tff(c_1855,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1836,c_857])).

tff(c_1879,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_940,c_1855])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n012.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 12:51:52 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.66/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.57  
% 3.66/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.57  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.66/1.57  
% 3.66/1.57  %Foreground sorts:
% 3.66/1.57  
% 3.66/1.57  
% 3.66/1.57  %Background operators:
% 3.66/1.57  
% 3.66/1.57  
% 3.66/1.57  %Foreground operators:
% 3.66/1.57  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.66/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.66/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.66/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.66/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.66/1.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.66/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.66/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.66/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.66/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.66/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.66/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.66/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.66/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.66/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.66/1.57  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.66/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.66/1.57  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.66/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.66/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.66/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.66/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.66/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.66/1.57  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.66/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.66/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.66/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.66/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.66/1.57  
% 3.66/1.59  tff(f_139, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 3.66/1.59  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.66/1.59  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.66/1.59  tff(f_96, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.66/1.59  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.66/1.59  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.66/1.59  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.66/1.59  tff(f_47, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.66/1.59  tff(f_70, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.66/1.59  tff(f_49, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.66/1.59  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.66/1.59  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.66/1.59  tff(f_127, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 3.66/1.59  tff(f_101, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.66/1.59  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.66/1.59  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 3.66/1.59  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.66/1.59  tff(c_112, plain, (![C_57, A_58, B_59]: (v1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.66/1.59  tff(c_120, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_112])).
% 3.66/1.59  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.66/1.59  tff(c_40, plain, (![A_23]: (k1_relat_1(A_23)!=k1_xboole_0 | k1_xboole_0=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.66/1.59  tff(c_129, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_120, c_40])).
% 3.66/1.59  tff(c_145, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_129])).
% 3.66/1.59  tff(c_412, plain, (![B_105, A_106]: (k1_tarski(k1_funct_1(B_105, A_106))=k2_relat_1(B_105) | k1_tarski(A_106)!=k1_relat_1(B_105) | ~v1_funct_1(B_105) | ~v1_relat_1(B_105))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.66/1.59  tff(c_338, plain, (![A_98, B_99, C_100]: (k2_relset_1(A_98, B_99, C_100)=k2_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.66/1.59  tff(c_346, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_338])).
% 3.66/1.59  tff(c_60, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.66/1.59  tff(c_374, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_346, c_60])).
% 3.66/1.59  tff(c_418, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_412, c_374])).
% 3.66/1.59  tff(c_428, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_68, c_418])).
% 3.66/1.59  tff(c_241, plain, (![C_80, A_81, B_82]: (v4_relat_1(C_80, A_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.66/1.59  tff(c_249, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_64, c_241])).
% 3.66/1.59  tff(c_30, plain, (![B_20, A_19]: (r1_tarski(k1_relat_1(B_20), A_19) | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.66/1.59  tff(c_199, plain, (![B_75, A_76]: (k1_tarski(B_75)=A_76 | k1_xboole_0=A_76 | ~r1_tarski(A_76, k1_tarski(B_75)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.66/1.59  tff(c_572, plain, (![B_123, B_124]: (k1_tarski(B_123)=k1_relat_1(B_124) | k1_relat_1(B_124)=k1_xboole_0 | ~v4_relat_1(B_124, k1_tarski(B_123)) | ~v1_relat_1(B_124))), inference(resolution, [status(thm)], [c_30, c_199])).
% 3.66/1.59  tff(c_582, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_249, c_572])).
% 3.66/1.59  tff(c_590, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_120, c_582])).
% 3.66/1.59  tff(c_592, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145, c_428, c_590])).
% 3.66/1.59  tff(c_593, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_129])).
% 3.66/1.59  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.66/1.59  tff(c_602, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_593, c_593, c_34])).
% 3.66/1.59  tff(c_38, plain, (![A_23]: (k2_relat_1(A_23)!=k1_xboole_0 | k1_xboole_0=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.66/1.59  tff(c_128, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_120, c_38])).
% 3.66/1.59  tff(c_144, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_128])).
% 3.66/1.59  tff(c_595, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_593, c_144])).
% 3.66/1.59  tff(c_629, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_602, c_595])).
% 3.66/1.59  tff(c_630, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_128])).
% 3.66/1.59  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.66/1.59  tff(c_639, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_630, c_630, c_36])).
% 3.66/1.59  tff(c_631, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_128])).
% 3.66/1.59  tff(c_662, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_630, c_631])).
% 3.66/1.59  tff(c_925, plain, (![B_174, A_175]: (k1_tarski(k1_funct_1(B_174, A_175))=k2_relat_1(B_174) | k1_tarski(A_175)!=k1_relat_1(B_174) | ~v1_funct_1(B_174) | ~v1_relat_1(B_174))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.66/1.59  tff(c_24, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.66/1.59  tff(c_635, plain, (![A_15]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_630, c_24])).
% 3.66/1.59  tff(c_877, plain, (![A_168, B_169, C_170]: (k2_relset_1(A_168, B_169, C_170)=k2_relat_1(C_170) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.66/1.59  tff(c_881, plain, (![A_168, B_169]: (k2_relset_1(A_168, B_169, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_635, c_877])).
% 3.66/1.59  tff(c_883, plain, (![A_168, B_169]: (k2_relset_1(A_168, B_169, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_662, c_881])).
% 3.66/1.59  tff(c_884, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_883, c_60])).
% 3.66/1.59  tff(c_931, plain, (k2_relat_1('#skF_4')!='#skF_4' | k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_925, c_884])).
% 3.66/1.59  tff(c_940, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_120, c_68, c_639, c_662, c_931])).
% 3.66/1.59  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.66/1.59  tff(c_637, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_630, c_10])).
% 3.66/1.59  tff(c_62, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.66/1.59  tff(c_641, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_630, c_62])).
% 3.66/1.59  tff(c_66, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.66/1.59  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.66/1.59  tff(c_58, plain, (![D_43, C_42, A_40, B_41]: (r2_hidden(k1_funct_1(D_43, C_42), k2_relset_1(A_40, B_41, D_43)) | k1_xboole_0=B_41 | ~r2_hidden(C_42, A_40) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))) | ~v1_funct_2(D_43, A_40, B_41) | ~v1_funct_1(D_43))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.66/1.59  tff(c_1032, plain, (![D_184, C_185, A_186, B_187]: (r2_hidden(k1_funct_1(D_184, C_185), k2_relset_1(A_186, B_187, D_184)) | B_187='#skF_4' | ~r2_hidden(C_185, A_186) | ~m1_subset_1(D_184, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))) | ~v1_funct_2(D_184, A_186, B_187) | ~v1_funct_1(D_184))), inference(demodulation, [status(thm), theory('equality')], [c_630, c_58])).
% 3.66/1.59  tff(c_1040, plain, (![C_185, B_169, A_168]: (r2_hidden(k1_funct_1('#skF_4', C_185), '#skF_4') | B_169='#skF_4' | ~r2_hidden(C_185, A_168) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))) | ~v1_funct_2('#skF_4', A_168, B_169) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_883, c_1032])).
% 3.66/1.59  tff(c_1395, plain, (![C_217, B_218, A_219]: (r2_hidden(k1_funct_1('#skF_4', C_217), '#skF_4') | B_218='#skF_4' | ~r2_hidden(C_217, A_219) | ~v1_funct_2('#skF_4', A_219, B_218))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_635, c_1040])).
% 3.66/1.59  tff(c_1811, plain, (![A_234, B_235, B_236]: (r2_hidden(k1_funct_1('#skF_4', '#skF_1'(A_234, B_235)), '#skF_4') | B_236='#skF_4' | ~v1_funct_2('#skF_4', A_234, B_236) | r1_tarski(A_234, B_235))), inference(resolution, [status(thm)], [c_6, c_1395])).
% 3.66/1.59  tff(c_1813, plain, (![B_235]: (r2_hidden(k1_funct_1('#skF_4', '#skF_1'(k1_tarski('#skF_2'), B_235)), '#skF_4') | '#skF_3'='#skF_4' | r1_tarski(k1_tarski('#skF_2'), B_235))), inference(resolution, [status(thm)], [c_66, c_1811])).
% 3.66/1.59  tff(c_1817, plain, (![B_237]: (r2_hidden(k1_funct_1('#skF_4', '#skF_1'(k1_tarski('#skF_2'), B_237)), '#skF_4') | r1_tarski(k1_tarski('#skF_2'), B_237))), inference(negUnitSimplification, [status(thm)], [c_641, c_1813])).
% 3.66/1.59  tff(c_48, plain, (![B_30, A_29]: (~r1_tarski(B_30, A_29) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.66/1.59  tff(c_1826, plain, (![B_237]: (~r1_tarski('#skF_4', k1_funct_1('#skF_4', '#skF_1'(k1_tarski('#skF_2'), B_237))) | r1_tarski(k1_tarski('#skF_2'), B_237))), inference(resolution, [status(thm)], [c_1817, c_48])).
% 3.66/1.59  tff(c_1836, plain, (![B_238]: (r1_tarski(k1_tarski('#skF_2'), B_238))), inference(demodulation, [status(thm), theory('equality')], [c_637, c_1826])).
% 3.66/1.59  tff(c_724, plain, (![C_140, A_141, B_142]: (v4_relat_1(C_140, A_141) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.66/1.59  tff(c_729, plain, (![A_141]: (v4_relat_1('#skF_4', A_141))), inference(resolution, [status(thm)], [c_635, c_724])).
% 3.66/1.59  tff(c_735, plain, (![B_147, A_148]: (k7_relat_1(B_147, A_148)=B_147 | ~v4_relat_1(B_147, A_148) | ~v1_relat_1(B_147))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.66/1.59  tff(c_738, plain, (![A_141]: (k7_relat_1('#skF_4', A_141)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_729, c_735])).
% 3.66/1.59  tff(c_741, plain, (![A_141]: (k7_relat_1('#skF_4', A_141)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_738])).
% 3.66/1.59  tff(c_838, plain, (![B_165, A_166]: (k1_relat_1(k7_relat_1(B_165, A_166))=A_166 | ~r1_tarski(A_166, k1_relat_1(B_165)) | ~v1_relat_1(B_165))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.66/1.59  tff(c_849, plain, (![A_166]: (k1_relat_1(k7_relat_1('#skF_4', A_166))=A_166 | ~r1_tarski(A_166, '#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_639, c_838])).
% 3.66/1.59  tff(c_857, plain, (![A_166]: (A_166='#skF_4' | ~r1_tarski(A_166, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_639, c_741, c_849])).
% 3.66/1.59  tff(c_1855, plain, (k1_tarski('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_1836, c_857])).
% 3.66/1.59  tff(c_1879, plain, $false, inference(negUnitSimplification, [status(thm)], [c_940, c_1855])).
% 3.66/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.59  
% 3.66/1.59  Inference rules
% 3.66/1.59  ----------------------
% 3.66/1.59  #Ref     : 0
% 3.66/1.59  #Sup     : 408
% 3.66/1.59  #Fact    : 0
% 3.66/1.59  #Define  : 0
% 3.66/1.59  #Split   : 2
% 3.66/1.59  #Chain   : 0
% 3.66/1.59  #Close   : 0
% 3.66/1.59  
% 3.66/1.59  Ordering : KBO
% 3.66/1.59  
% 3.66/1.59  Simplification rules
% 3.66/1.59  ----------------------
% 3.66/1.59  #Subsume      : 65
% 3.66/1.59  #Demod        : 250
% 3.66/1.59  #Tautology    : 161
% 3.66/1.59  #SimpNegUnit  : 4
% 3.66/1.59  #BackRed      : 23
% 3.66/1.59  
% 3.66/1.59  #Partial instantiations: 0
% 3.66/1.59  #Strategies tried      : 1
% 3.66/1.59  
% 3.66/1.59  Timing (in seconds)
% 3.66/1.59  ----------------------
% 3.66/1.59  Preprocessing        : 0.34
% 3.66/1.59  Parsing              : 0.18
% 3.66/1.59  CNF conversion       : 0.02
% 3.66/1.59  Main loop            : 0.51
% 3.66/1.59  Inferencing          : 0.18
% 3.66/1.59  Reduction            : 0.15
% 3.66/1.59  Demodulation         : 0.11
% 3.66/1.59  BG Simplification    : 0.03
% 3.66/1.59  Subsumption          : 0.10
% 3.66/1.59  Abstraction          : 0.02
% 3.66/1.59  MUC search           : 0.00
% 3.66/1.59  Cooper               : 0.00
% 3.66/1.59  Total                : 0.88
% 3.66/1.59  Index Insertion      : 0.00
% 3.66/1.59  Index Deletion       : 0.00
% 3.66/1.59  Index Matching       : 0.00
% 3.66/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
