%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:31 EST 2020

% Result     : Theorem 3.97s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 187 expanded)
%              Number of leaves         :   47 (  85 expanded)
%              Depth                    :   12
%              Number of atoms          :  167 ( 474 expanded)
%              Number of equality atoms :   34 ( 113 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_171,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_111,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_130,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_152,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_134,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_126,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(B))
         => v5_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_116,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_94,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_157,plain,(
    ! [C_110,A_111,B_112] :
      ( v1_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_169,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_94,c_157])).

tff(c_98,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_1176,plain,(
    ! [A_293,B_294,D_295] :
      ( k1_funct_1(A_293,'#skF_5'(A_293,B_294,k9_relat_1(A_293,B_294),D_295)) = D_295
      | ~ r2_hidden(D_295,k9_relat_1(A_293,B_294))
      | ~ v1_funct_1(A_293)
      | ~ v1_relat_1(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_96,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_291,plain,(
    ! [A_153,B_154,C_155] :
      ( k1_relset_1(A_153,B_154,C_155) = k1_relat_1(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_305,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_94,c_291])).

tff(c_609,plain,(
    ! [B_209,A_210,C_211] :
      ( k1_xboole_0 = B_209
      | k1_relset_1(A_210,B_209,C_211) = A_210
      | ~ v1_funct_2(C_211,A_210,B_209)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_210,B_209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_612,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_94,c_609])).

tff(c_625,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_305,c_612])).

tff(c_629,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_625])).

tff(c_1127,plain,(
    ! [A_280,B_281,D_282] :
      ( r2_hidden('#skF_5'(A_280,B_281,k9_relat_1(A_280,B_281),D_282),k1_relat_1(A_280))
      | ~ r2_hidden(D_282,k9_relat_1(A_280,B_281))
      | ~ v1_funct_1(A_280)
      | ~ v1_relat_1(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1138,plain,(
    ! [B_281,D_282] :
      ( r2_hidden('#skF_5'('#skF_9',B_281,k9_relat_1('#skF_9',B_281),D_282),'#skF_6')
      | ~ r2_hidden(D_282,k9_relat_1('#skF_9',B_281))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_629,c_1127])).

tff(c_1144,plain,(
    ! [B_283,D_284] :
      ( r2_hidden('#skF_5'('#skF_9',B_283,k9_relat_1('#skF_9',B_283),D_284),'#skF_6')
      | ~ r2_hidden(D_284,k9_relat_1('#skF_9',B_283)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_98,c_1138])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1156,plain,(
    ! [B_285,D_286] :
      ( m1_subset_1('#skF_5'('#skF_9',B_285,k9_relat_1('#skF_9',B_285),D_286),'#skF_6')
      | ~ r2_hidden(D_286,k9_relat_1('#skF_9',B_285)) ) ),
    inference(resolution,[status(thm)],[c_1144,c_16])).

tff(c_848,plain,(
    ! [A_240,B_241,D_242] :
      ( r2_hidden('#skF_5'(A_240,B_241,k9_relat_1(A_240,B_241),D_242),B_241)
      | ~ r2_hidden(D_242,k9_relat_1(A_240,B_241))
      | ~ v1_funct_1(A_240)
      | ~ v1_relat_1(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_90,plain,(
    ! [F_96] :
      ( k1_funct_1('#skF_9',F_96) != '#skF_10'
      | ~ r2_hidden(F_96,'#skF_8')
      | ~ m1_subset_1(F_96,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_895,plain,(
    ! [A_240,D_242] :
      ( k1_funct_1('#skF_9','#skF_5'(A_240,'#skF_8',k9_relat_1(A_240,'#skF_8'),D_242)) != '#skF_10'
      | ~ m1_subset_1('#skF_5'(A_240,'#skF_8',k9_relat_1(A_240,'#skF_8'),D_242),'#skF_6')
      | ~ r2_hidden(D_242,k9_relat_1(A_240,'#skF_8'))
      | ~ v1_funct_1(A_240)
      | ~ v1_relat_1(A_240) ) ),
    inference(resolution,[status(thm)],[c_848,c_90])).

tff(c_1160,plain,(
    ! [D_286] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_286)) != '#skF_10'
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_286,k9_relat_1('#skF_9','#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_1156,c_895])).

tff(c_1163,plain,(
    ! [D_286] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_286)) != '#skF_10'
      | ~ r2_hidden(D_286,k9_relat_1('#skF_9','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_98,c_1160])).

tff(c_1187,plain,(
    ! [D_295] :
      ( D_295 != '#skF_10'
      | ~ r2_hidden(D_295,k9_relat_1('#skF_9','#skF_8'))
      | ~ r2_hidden(D_295,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1176,c_1163])).

tff(c_1215,plain,(
    ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_98,c_1187])).

tff(c_411,plain,(
    ! [A_188,B_189,C_190,D_191] :
      ( k7_relset_1(A_188,B_189,C_190,D_191) = k9_relat_1(C_190,D_191)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_421,plain,(
    ! [D_191] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_191) = k9_relat_1('#skF_9',D_191) ),
    inference(resolution,[status(thm)],[c_94,c_411])).

tff(c_92,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_425,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_92])).

tff(c_1217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1215,c_425])).

tff(c_1218,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_625])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_202,plain,(
    ! [C_122,B_123,A_124] :
      ( v5_relat_1(C_122,B_123)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_124,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_217,plain,(
    ! [B_123] : v5_relat_1(k1_xboole_0,B_123) ),
    inference(resolution,[status(thm)],[c_14,c_202])).

tff(c_1235,plain,(
    ! [B_123] : v5_relat_1('#skF_7',B_123) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1218,c_217])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1239,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1218,c_1218,c_10])).

tff(c_26,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_273,plain,(
    ! [C_149,A_150,B_151] :
      ( v5_relat_1(C_149,A_150)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(B_151))
      | ~ v5_relat_1(B_151,A_150)
      | ~ v1_relat_1(B_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_275,plain,(
    ! [A_150] :
      ( v5_relat_1('#skF_9',A_150)
      | ~ v5_relat_1(k2_zfmisc_1('#skF_6','#skF_7'),A_150)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_94,c_273])).

tff(c_280,plain,(
    ! [A_150] :
      ( v5_relat_1('#skF_9',A_150)
      | ~ v5_relat_1(k2_zfmisc_1('#skF_6','#skF_7'),A_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_275])).

tff(c_1310,plain,(
    ! [A_150] :
      ( v5_relat_1('#skF_9',A_150)
      | ~ v5_relat_1('#skF_7',A_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1239,c_280])).

tff(c_1314,plain,(
    ! [A_150] : v5_relat_1('#skF_9',A_150) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1235,c_1310])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v5_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_435,plain,(
    ! [A_193,B_194,C_195] :
      ( r2_hidden(k4_tarski('#skF_1'(A_193,B_194,C_195),A_193),C_195)
      | ~ r2_hidden(A_193,k9_relat_1(C_195,B_194))
      | ~ v1_relat_1(C_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_38,plain,(
    ! [B_30,C_31,A_29] :
      ( r2_hidden(B_30,k2_relat_1(C_31))
      | ~ r2_hidden(k4_tarski(A_29,B_30),C_31)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_510,plain,(
    ! [A_199,C_200,B_201] :
      ( r2_hidden(A_199,k2_relat_1(C_200))
      | ~ r2_hidden(A_199,k9_relat_1(C_200,B_201))
      | ~ v1_relat_1(C_200) ) ),
    inference(resolution,[status(thm)],[c_435,c_38])).

tff(c_513,plain,
    ( r2_hidden('#skF_10',k2_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_425,c_510])).

tff(c_524,plain,(
    r2_hidden('#skF_10',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_513])).

tff(c_66,plain,(
    ! [B_75,A_74] :
      ( ~ r1_tarski(B_75,A_74)
      | ~ r2_hidden(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_539,plain,(
    ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_10') ),
    inference(resolution,[status(thm)],[c_524,c_66])).

tff(c_542,plain,
    ( ~ v5_relat_1('#skF_9','#skF_10')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_24,c_539])).

tff(c_545,plain,(
    ~ v5_relat_1('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_542])).

tff(c_1343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1314,c_545])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:31:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.97/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/1.64  
% 3.97/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/1.65  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 3.97/1.65  
% 3.97/1.65  %Foreground sorts:
% 3.97/1.65  
% 3.97/1.65  
% 3.97/1.65  %Background operators:
% 3.97/1.65  
% 3.97/1.65  
% 3.97/1.65  %Foreground operators:
% 3.97/1.65  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.97/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.97/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.97/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.97/1.65  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.97/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.97/1.65  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.97/1.65  tff('#skF_7', type, '#skF_7': $i).
% 3.97/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.97/1.65  tff('#skF_10', type, '#skF_10': $i).
% 3.97/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.97/1.65  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.97/1.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.97/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.97/1.65  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.97/1.65  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.97/1.65  tff('#skF_9', type, '#skF_9': $i).
% 3.97/1.65  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.97/1.65  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.97/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.97/1.65  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.97/1.65  tff('#skF_8', type, '#skF_8': $i).
% 3.97/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.97/1.65  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.97/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.97/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.97/1.65  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.97/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.97/1.65  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.97/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.97/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.97/1.65  
% 3.97/1.66  tff(f_171, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 3.97/1.66  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.97/1.66  tff(f_111, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 3.97/1.66  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.97/1.66  tff(f_152, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.97/1.66  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.97/1.66  tff(f_134, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.97/1.66  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.97/1.66  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.97/1.66  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.97/1.66  tff(f_66, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.97/1.66  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(B)) => v5_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_relat_1)).
% 3.97/1.66  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.97/1.66  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 3.97/1.66  tff(f_94, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 3.97/1.66  tff(f_116, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.97/1.66  tff(c_94, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.97/1.66  tff(c_157, plain, (![C_110, A_111, B_112]: (v1_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.97/1.66  tff(c_169, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_94, c_157])).
% 3.97/1.66  tff(c_98, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.97/1.66  tff(c_1176, plain, (![A_293, B_294, D_295]: (k1_funct_1(A_293, '#skF_5'(A_293, B_294, k9_relat_1(A_293, B_294), D_295))=D_295 | ~r2_hidden(D_295, k9_relat_1(A_293, B_294)) | ~v1_funct_1(A_293) | ~v1_relat_1(A_293))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.97/1.66  tff(c_96, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.97/1.66  tff(c_291, plain, (![A_153, B_154, C_155]: (k1_relset_1(A_153, B_154, C_155)=k1_relat_1(C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.97/1.66  tff(c_305, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_94, c_291])).
% 3.97/1.66  tff(c_609, plain, (![B_209, A_210, C_211]: (k1_xboole_0=B_209 | k1_relset_1(A_210, B_209, C_211)=A_210 | ~v1_funct_2(C_211, A_210, B_209) | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_210, B_209))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.97/1.66  tff(c_612, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_94, c_609])).
% 3.97/1.66  tff(c_625, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_305, c_612])).
% 3.97/1.66  tff(c_629, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_625])).
% 3.97/1.66  tff(c_1127, plain, (![A_280, B_281, D_282]: (r2_hidden('#skF_5'(A_280, B_281, k9_relat_1(A_280, B_281), D_282), k1_relat_1(A_280)) | ~r2_hidden(D_282, k9_relat_1(A_280, B_281)) | ~v1_funct_1(A_280) | ~v1_relat_1(A_280))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.97/1.66  tff(c_1138, plain, (![B_281, D_282]: (r2_hidden('#skF_5'('#skF_9', B_281, k9_relat_1('#skF_9', B_281), D_282), '#skF_6') | ~r2_hidden(D_282, k9_relat_1('#skF_9', B_281)) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_629, c_1127])).
% 3.97/1.66  tff(c_1144, plain, (![B_283, D_284]: (r2_hidden('#skF_5'('#skF_9', B_283, k9_relat_1('#skF_9', B_283), D_284), '#skF_6') | ~r2_hidden(D_284, k9_relat_1('#skF_9', B_283)))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_98, c_1138])).
% 3.97/1.66  tff(c_16, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.97/1.66  tff(c_1156, plain, (![B_285, D_286]: (m1_subset_1('#skF_5'('#skF_9', B_285, k9_relat_1('#skF_9', B_285), D_286), '#skF_6') | ~r2_hidden(D_286, k9_relat_1('#skF_9', B_285)))), inference(resolution, [status(thm)], [c_1144, c_16])).
% 3.97/1.66  tff(c_848, plain, (![A_240, B_241, D_242]: (r2_hidden('#skF_5'(A_240, B_241, k9_relat_1(A_240, B_241), D_242), B_241) | ~r2_hidden(D_242, k9_relat_1(A_240, B_241)) | ~v1_funct_1(A_240) | ~v1_relat_1(A_240))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.97/1.66  tff(c_90, plain, (![F_96]: (k1_funct_1('#skF_9', F_96)!='#skF_10' | ~r2_hidden(F_96, '#skF_8') | ~m1_subset_1(F_96, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.97/1.66  tff(c_895, plain, (![A_240, D_242]: (k1_funct_1('#skF_9', '#skF_5'(A_240, '#skF_8', k9_relat_1(A_240, '#skF_8'), D_242))!='#skF_10' | ~m1_subset_1('#skF_5'(A_240, '#skF_8', k9_relat_1(A_240, '#skF_8'), D_242), '#skF_6') | ~r2_hidden(D_242, k9_relat_1(A_240, '#skF_8')) | ~v1_funct_1(A_240) | ~v1_relat_1(A_240))), inference(resolution, [status(thm)], [c_848, c_90])).
% 3.97/1.66  tff(c_1160, plain, (![D_286]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_286))!='#skF_10' | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_286, k9_relat_1('#skF_9', '#skF_8')))), inference(resolution, [status(thm)], [c_1156, c_895])).
% 3.97/1.66  tff(c_1163, plain, (![D_286]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_286))!='#skF_10' | ~r2_hidden(D_286, k9_relat_1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_98, c_1160])).
% 3.97/1.66  tff(c_1187, plain, (![D_295]: (D_295!='#skF_10' | ~r2_hidden(D_295, k9_relat_1('#skF_9', '#skF_8')) | ~r2_hidden(D_295, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1176, c_1163])).
% 3.97/1.66  tff(c_1215, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_98, c_1187])).
% 3.97/1.66  tff(c_411, plain, (![A_188, B_189, C_190, D_191]: (k7_relset_1(A_188, B_189, C_190, D_191)=k9_relat_1(C_190, D_191) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.97/1.66  tff(c_421, plain, (![D_191]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_191)=k9_relat_1('#skF_9', D_191))), inference(resolution, [status(thm)], [c_94, c_411])).
% 3.97/1.66  tff(c_92, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.97/1.66  tff(c_425, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_421, c_92])).
% 3.97/1.66  tff(c_1217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1215, c_425])).
% 3.97/1.66  tff(c_1218, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_625])).
% 3.97/1.66  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.97/1.66  tff(c_202, plain, (![C_122, B_123, A_124]: (v5_relat_1(C_122, B_123) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_124, B_123))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.97/1.66  tff(c_217, plain, (![B_123]: (v5_relat_1(k1_xboole_0, B_123))), inference(resolution, [status(thm)], [c_14, c_202])).
% 3.97/1.66  tff(c_1235, plain, (![B_123]: (v5_relat_1('#skF_7', B_123))), inference(demodulation, [status(thm), theory('equality')], [c_1218, c_217])).
% 3.97/1.66  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.97/1.66  tff(c_1239, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1218, c_1218, c_10])).
% 3.97/1.66  tff(c_26, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.97/1.66  tff(c_273, plain, (![C_149, A_150, B_151]: (v5_relat_1(C_149, A_150) | ~m1_subset_1(C_149, k1_zfmisc_1(B_151)) | ~v5_relat_1(B_151, A_150) | ~v1_relat_1(B_151))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.97/1.66  tff(c_275, plain, (![A_150]: (v5_relat_1('#skF_9', A_150) | ~v5_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'), A_150) | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_94, c_273])).
% 3.97/1.66  tff(c_280, plain, (![A_150]: (v5_relat_1('#skF_9', A_150) | ~v5_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'), A_150))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_275])).
% 3.97/1.66  tff(c_1310, plain, (![A_150]: (v5_relat_1('#skF_9', A_150) | ~v5_relat_1('#skF_7', A_150))), inference(demodulation, [status(thm), theory('equality')], [c_1239, c_280])).
% 3.97/1.66  tff(c_1314, plain, (![A_150]: (v5_relat_1('#skF_9', A_150))), inference(demodulation, [status(thm), theory('equality')], [c_1235, c_1310])).
% 3.97/1.66  tff(c_24, plain, (![B_16, A_15]: (r1_tarski(k2_relat_1(B_16), A_15) | ~v5_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.97/1.66  tff(c_435, plain, (![A_193, B_194, C_195]: (r2_hidden(k4_tarski('#skF_1'(A_193, B_194, C_195), A_193), C_195) | ~r2_hidden(A_193, k9_relat_1(C_195, B_194)) | ~v1_relat_1(C_195))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.97/1.66  tff(c_38, plain, (![B_30, C_31, A_29]: (r2_hidden(B_30, k2_relat_1(C_31)) | ~r2_hidden(k4_tarski(A_29, B_30), C_31) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.97/1.66  tff(c_510, plain, (![A_199, C_200, B_201]: (r2_hidden(A_199, k2_relat_1(C_200)) | ~r2_hidden(A_199, k9_relat_1(C_200, B_201)) | ~v1_relat_1(C_200))), inference(resolution, [status(thm)], [c_435, c_38])).
% 3.97/1.66  tff(c_513, plain, (r2_hidden('#skF_10', k2_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_425, c_510])).
% 3.97/1.66  tff(c_524, plain, (r2_hidden('#skF_10', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_513])).
% 3.97/1.66  tff(c_66, plain, (![B_75, A_74]: (~r1_tarski(B_75, A_74) | ~r2_hidden(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.97/1.66  tff(c_539, plain, (~r1_tarski(k2_relat_1('#skF_9'), '#skF_10')), inference(resolution, [status(thm)], [c_524, c_66])).
% 3.97/1.66  tff(c_542, plain, (~v5_relat_1('#skF_9', '#skF_10') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_24, c_539])).
% 3.97/1.66  tff(c_545, plain, (~v5_relat_1('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_542])).
% 3.97/1.66  tff(c_1343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1314, c_545])).
% 3.97/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/1.66  
% 3.97/1.66  Inference rules
% 3.97/1.66  ----------------------
% 3.97/1.66  #Ref     : 0
% 3.97/1.66  #Sup     : 253
% 3.97/1.66  #Fact    : 0
% 3.97/1.66  #Define  : 0
% 3.97/1.66  #Split   : 5
% 3.97/1.66  #Chain   : 0
% 3.97/1.66  #Close   : 0
% 3.97/1.66  
% 3.97/1.66  Ordering : KBO
% 3.97/1.66  
% 3.97/1.66  Simplification rules
% 3.97/1.66  ----------------------
% 3.97/1.66  #Subsume      : 15
% 3.97/1.66  #Demod        : 143
% 3.97/1.66  #Tautology    : 61
% 3.97/1.66  #SimpNegUnit  : 3
% 3.97/1.66  #BackRed      : 37
% 3.97/1.66  
% 3.97/1.66  #Partial instantiations: 0
% 3.97/1.66  #Strategies tried      : 1
% 3.97/1.66  
% 3.97/1.66  Timing (in seconds)
% 3.97/1.66  ----------------------
% 3.97/1.67  Preprocessing        : 0.37
% 3.97/1.67  Parsing              : 0.19
% 3.97/1.67  CNF conversion       : 0.03
% 3.97/1.67  Main loop            : 0.53
% 3.97/1.67  Inferencing          : 0.18
% 3.97/1.67  Reduction            : 0.17
% 3.97/1.67  Demodulation         : 0.12
% 3.97/1.67  BG Simplification    : 0.03
% 3.97/1.67  Subsumption          : 0.10
% 3.97/1.67  Abstraction          : 0.03
% 3.97/1.67  MUC search           : 0.00
% 3.97/1.67  Cooper               : 0.00
% 3.97/1.67  Total                : 0.93
% 3.97/1.67  Index Insertion      : 0.00
% 3.97/1.67  Index Deletion       : 0.00
% 3.97/1.67  Index Matching       : 0.00
% 3.97/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
