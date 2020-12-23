%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:39 EST 2020

% Result     : Theorem 4.84s
% Output     : CNFRefutation 4.84s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 537 expanded)
%              Number of leaves         :   37 ( 194 expanded)
%              Depth                    :   13
%              Number of atoms          :  203 (1518 expanded)
%              Number of equality atoms :   68 ( 288 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( r2_hidden(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_99,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_117,axiom,(
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

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_988,plain,(
    ! [A_180,B_181,D_182] :
      ( r2_relset_1(A_180,B_181,D_182,D_182)
      | ~ m1_subset_1(D_182,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1008,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_988])).

tff(c_139,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_159,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_139])).

tff(c_68,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_66,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1065,plain,(
    ! [A_193,B_194,C_195] :
      ( k1_relset_1(A_193,B_194,C_195) = k1_relat_1(C_195)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_193,B_194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1092,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_1065])).

tff(c_1252,plain,(
    ! [B_212,A_213,C_214] :
      ( k1_xboole_0 = B_212
      | k1_relset_1(A_213,B_212,C_214) = A_213
      | ~ v1_funct_2(C_214,A_213,B_212)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_213,B_212))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1267,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_1252])).

tff(c_1286,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1092,c_1267])).

tff(c_1316,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1286])).

tff(c_58,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_160,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_139])).

tff(c_62,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_60,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1093,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_1065])).

tff(c_1270,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_1252])).

tff(c_1289,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1093,c_1270])).

tff(c_1322,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1289])).

tff(c_1480,plain,(
    ! [A_232,B_233] :
      ( r2_hidden('#skF_3'(A_232,B_233),k1_relat_1(A_232))
      | B_233 = A_232
      | k1_relat_1(B_233) != k1_relat_1(A_232)
      | ~ v1_funct_1(B_233)
      | ~ v1_relat_1(B_233)
      | ~ v1_funct_1(A_232)
      | ~ v1_relat_1(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1490,plain,(
    ! [B_233] :
      ( r2_hidden('#skF_3'('#skF_7',B_233),'#skF_4')
      | B_233 = '#skF_7'
      | k1_relat_1(B_233) != k1_relat_1('#skF_7')
      | ~ v1_funct_1(B_233)
      | ~ v1_relat_1(B_233)
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1322,c_1480])).

tff(c_1622,plain,(
    ! [B_248] :
      ( r2_hidden('#skF_3'('#skF_7',B_248),'#skF_4')
      | B_248 = '#skF_7'
      | k1_relat_1(B_248) != '#skF_4'
      | ~ v1_funct_1(B_248)
      | ~ v1_relat_1(B_248) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_62,c_1322,c_1490])).

tff(c_56,plain,(
    ! [E_43] :
      ( k1_funct_1('#skF_7',E_43) = k1_funct_1('#skF_6',E_43)
      | ~ r2_hidden(E_43,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1842,plain,(
    ! [B_271] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_7',B_271)) = k1_funct_1('#skF_6','#skF_3'('#skF_7',B_271))
      | B_271 = '#skF_7'
      | k1_relat_1(B_271) != '#skF_4'
      | ~ v1_funct_1(B_271)
      | ~ v1_relat_1(B_271) ) ),
    inference(resolution,[status(thm)],[c_1622,c_56])).

tff(c_30,plain,(
    ! [B_24,A_20] :
      ( k1_funct_1(B_24,'#skF_3'(A_20,B_24)) != k1_funct_1(A_20,'#skF_3'(A_20,B_24))
      | B_24 = A_20
      | k1_relat_1(B_24) != k1_relat_1(A_20)
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1848,plain,(
    ! [B_271] :
      ( k1_funct_1(B_271,'#skF_3'('#skF_7',B_271)) != k1_funct_1('#skF_6','#skF_3'('#skF_7',B_271))
      | B_271 = '#skF_7'
      | k1_relat_1(B_271) != k1_relat_1('#skF_7')
      | ~ v1_funct_1(B_271)
      | ~ v1_relat_1(B_271)
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | B_271 = '#skF_7'
      | k1_relat_1(B_271) != '#skF_4'
      | ~ v1_funct_1(B_271)
      | ~ v1_relat_1(B_271) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1842,c_30])).

tff(c_1854,plain,(
    ! [B_271] :
      ( k1_funct_1(B_271,'#skF_3'('#skF_7',B_271)) != k1_funct_1('#skF_6','#skF_3'('#skF_7',B_271))
      | B_271 = '#skF_7'
      | k1_relat_1(B_271) != '#skF_4'
      | ~ v1_funct_1(B_271)
      | ~ v1_relat_1(B_271) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_62,c_1322,c_1848])).

tff(c_2264,plain,
    ( '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_6') != '#skF_4'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1854])).

tff(c_2266,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_68,c_1316,c_2264])).

tff(c_54,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2291,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2266,c_54])).

tff(c_2302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_2291])).

tff(c_2303,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1289])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2327,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2303,c_12])).

tff(c_18,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2325,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2303,c_2303,c_18])).

tff(c_115,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_130,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_58,c_115])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_885,plain,(
    ! [C_161,B_162,A_163] :
      ( r2_hidden(C_161,B_162)
      | ~ r2_hidden(C_161,A_163)
      | ~ r1_tarski(A_163,B_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_892,plain,(
    ! [A_164,B_165] :
      ( r2_hidden('#skF_1'(A_164),B_165)
      | ~ r1_tarski(A_164,B_165)
      | v1_xboole_0(A_164) ) ),
    inference(resolution,[status(thm)],[c_4,c_885])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_933,plain,(
    ! [B_171,A_172] :
      ( ~ v1_xboole_0(B_171)
      | ~ r1_tarski(A_172,B_171)
      | v1_xboole_0(A_172) ) ),
    inference(resolution,[status(thm)],[c_892,c_2])).

tff(c_951,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_130,c_933])).

tff(c_955,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_951])).

tff(c_2399,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2325,c_955])).

tff(c_2407,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2327,c_2399])).

tff(c_2408,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1286])).

tff(c_2432,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2408,c_12])).

tff(c_2430,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2408,c_2408,c_18])).

tff(c_2501,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2430,c_955])).

tff(c_2509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2432,c_2501])).

tff(c_2510,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_951])).

tff(c_2511,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_951])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( ~ v1_xboole_0(B_11)
      | B_11 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2590,plain,(
    ! [A_324] :
      ( A_324 = '#skF_7'
      | ~ v1_xboole_0(A_324) ) ),
    inference(resolution,[status(thm)],[c_2510,c_14])).

tff(c_2597,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_2511,c_2590])).

tff(c_129,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_64,c_115])).

tff(c_2645,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2597,c_129])).

tff(c_904,plain,(
    ! [B_165,A_164] :
      ( ~ v1_xboole_0(B_165)
      | ~ r1_tarski(A_164,B_165)
      | v1_xboole_0(A_164) ) ),
    inference(resolution,[status(thm)],[c_892,c_2])).

tff(c_2683,plain,
    ( ~ v1_xboole_0('#skF_7')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_2645,c_904])).

tff(c_2686,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2510,c_2683])).

tff(c_2523,plain,(
    ! [A_10] :
      ( A_10 = '#skF_7'
      | ~ v1_xboole_0(A_10) ) ),
    inference(resolution,[status(thm)],[c_2510,c_14])).

tff(c_2695,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2686,c_2523])).

tff(c_103,plain,(
    ! [B_50,A_51] :
      ( ~ v1_xboole_0(B_50)
      | B_50 = A_51
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_106,plain,(
    ! [A_51] :
      ( k1_xboole_0 = A_51
      | ~ v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_12,c_103])).

tff(c_2522,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_2510,c_106])).

tff(c_22,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2625,plain,(
    ! [A_326] : m1_subset_1('#skF_7',k1_zfmisc_1(A_326)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2522,c_22])).

tff(c_38,plain,(
    ! [A_32,B_33,D_35] :
      ( r2_relset_1(A_32,B_33,D_35,D_35)
      | ~ m1_subset_1(D_35,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2638,plain,(
    ! [A_32,B_33] : r2_relset_1(A_32,B_33,'#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_2625,c_38])).

tff(c_2865,plain,(
    ! [A_32,B_33] : r2_relset_1(A_32,B_33,'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2695,c_2695,c_2638])).

tff(c_2713,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2695,c_54])).

tff(c_2873,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2865,c_2713])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:52:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.84/1.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/1.86  
% 4.84/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/1.86  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 4.84/1.86  
% 4.84/1.86  %Foreground sorts:
% 4.84/1.86  
% 4.84/1.86  
% 4.84/1.86  %Background operators:
% 4.84/1.86  
% 4.84/1.86  
% 4.84/1.86  %Foreground operators:
% 4.84/1.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.84/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.84/1.86  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.84/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.84/1.86  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.84/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.84/1.86  tff('#skF_7', type, '#skF_7': $i).
% 4.84/1.86  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.84/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.84/1.86  tff('#skF_5', type, '#skF_5': $i).
% 4.84/1.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.84/1.86  tff('#skF_6', type, '#skF_6': $i).
% 4.84/1.86  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.84/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.84/1.86  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.84/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.84/1.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.84/1.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.84/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.84/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.84/1.86  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.84/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.84/1.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.84/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.84/1.86  
% 4.84/1.88  tff(f_138, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 4.84/1.88  tff(f_99, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.84/1.88  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.84/1.88  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.84/1.88  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.84/1.88  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 4.84/1.88  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.84/1.88  tff(f_53, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.84/1.88  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.84/1.88  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.84/1.88  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.84/1.88  tff(f_47, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 4.84/1.88  tff(f_55, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.84/1.88  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.84/1.88  tff(c_988, plain, (![A_180, B_181, D_182]: (r2_relset_1(A_180, B_181, D_182, D_182) | ~m1_subset_1(D_182, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.84/1.88  tff(c_1008, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_64, c_988])).
% 4.84/1.88  tff(c_139, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.84/1.88  tff(c_159, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_64, c_139])).
% 4.84/1.88  tff(c_68, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.84/1.88  tff(c_66, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.84/1.88  tff(c_1065, plain, (![A_193, B_194, C_195]: (k1_relset_1(A_193, B_194, C_195)=k1_relat_1(C_195) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_193, B_194))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.84/1.88  tff(c_1092, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_64, c_1065])).
% 4.84/1.88  tff(c_1252, plain, (![B_212, A_213, C_214]: (k1_xboole_0=B_212 | k1_relset_1(A_213, B_212, C_214)=A_213 | ~v1_funct_2(C_214, A_213, B_212) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_213, B_212))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.84/1.88  tff(c_1267, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_64, c_1252])).
% 4.84/1.88  tff(c_1286, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1092, c_1267])).
% 4.84/1.88  tff(c_1316, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_1286])).
% 4.84/1.88  tff(c_58, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.84/1.88  tff(c_160, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_58, c_139])).
% 4.84/1.88  tff(c_62, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.84/1.88  tff(c_60, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.84/1.88  tff(c_1093, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_58, c_1065])).
% 4.84/1.88  tff(c_1270, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_1252])).
% 4.84/1.88  tff(c_1289, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1093, c_1270])).
% 4.84/1.88  tff(c_1322, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_1289])).
% 4.84/1.88  tff(c_1480, plain, (![A_232, B_233]: (r2_hidden('#skF_3'(A_232, B_233), k1_relat_1(A_232)) | B_233=A_232 | k1_relat_1(B_233)!=k1_relat_1(A_232) | ~v1_funct_1(B_233) | ~v1_relat_1(B_233) | ~v1_funct_1(A_232) | ~v1_relat_1(A_232))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.84/1.88  tff(c_1490, plain, (![B_233]: (r2_hidden('#skF_3'('#skF_7', B_233), '#skF_4') | B_233='#skF_7' | k1_relat_1(B_233)!=k1_relat_1('#skF_7') | ~v1_funct_1(B_233) | ~v1_relat_1(B_233) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1322, c_1480])).
% 4.84/1.88  tff(c_1622, plain, (![B_248]: (r2_hidden('#skF_3'('#skF_7', B_248), '#skF_4') | B_248='#skF_7' | k1_relat_1(B_248)!='#skF_4' | ~v1_funct_1(B_248) | ~v1_relat_1(B_248))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_62, c_1322, c_1490])).
% 4.84/1.88  tff(c_56, plain, (![E_43]: (k1_funct_1('#skF_7', E_43)=k1_funct_1('#skF_6', E_43) | ~r2_hidden(E_43, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.84/1.88  tff(c_1842, plain, (![B_271]: (k1_funct_1('#skF_7', '#skF_3'('#skF_7', B_271))=k1_funct_1('#skF_6', '#skF_3'('#skF_7', B_271)) | B_271='#skF_7' | k1_relat_1(B_271)!='#skF_4' | ~v1_funct_1(B_271) | ~v1_relat_1(B_271))), inference(resolution, [status(thm)], [c_1622, c_56])).
% 4.84/1.88  tff(c_30, plain, (![B_24, A_20]: (k1_funct_1(B_24, '#skF_3'(A_20, B_24))!=k1_funct_1(A_20, '#skF_3'(A_20, B_24)) | B_24=A_20 | k1_relat_1(B_24)!=k1_relat_1(A_20) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.84/1.88  tff(c_1848, plain, (![B_271]: (k1_funct_1(B_271, '#skF_3'('#skF_7', B_271))!=k1_funct_1('#skF_6', '#skF_3'('#skF_7', B_271)) | B_271='#skF_7' | k1_relat_1(B_271)!=k1_relat_1('#skF_7') | ~v1_funct_1(B_271) | ~v1_relat_1(B_271) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | B_271='#skF_7' | k1_relat_1(B_271)!='#skF_4' | ~v1_funct_1(B_271) | ~v1_relat_1(B_271))), inference(superposition, [status(thm), theory('equality')], [c_1842, c_30])).
% 4.84/1.88  tff(c_1854, plain, (![B_271]: (k1_funct_1(B_271, '#skF_3'('#skF_7', B_271))!=k1_funct_1('#skF_6', '#skF_3'('#skF_7', B_271)) | B_271='#skF_7' | k1_relat_1(B_271)!='#skF_4' | ~v1_funct_1(B_271) | ~v1_relat_1(B_271))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_62, c_1322, c_1848])).
% 4.84/1.88  tff(c_2264, plain, ('#skF_7'='#skF_6' | k1_relat_1('#skF_6')!='#skF_4' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(reflexivity, [status(thm), theory('equality')], [c_1854])).
% 4.84/1.88  tff(c_2266, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_159, c_68, c_1316, c_2264])).
% 4.84/1.88  tff(c_54, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.84/1.88  tff(c_2291, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2266, c_54])).
% 4.84/1.88  tff(c_2302, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1008, c_2291])).
% 4.84/1.88  tff(c_2303, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1289])).
% 4.84/1.88  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.84/1.88  tff(c_2327, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2303, c_12])).
% 4.84/1.88  tff(c_18, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.84/1.88  tff(c_2325, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2303, c_2303, c_18])).
% 4.84/1.88  tff(c_115, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | ~m1_subset_1(A_56, k1_zfmisc_1(B_57)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.84/1.88  tff(c_130, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_58, c_115])).
% 4.84/1.88  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.84/1.88  tff(c_885, plain, (![C_161, B_162, A_163]: (r2_hidden(C_161, B_162) | ~r2_hidden(C_161, A_163) | ~r1_tarski(A_163, B_162))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.84/1.88  tff(c_892, plain, (![A_164, B_165]: (r2_hidden('#skF_1'(A_164), B_165) | ~r1_tarski(A_164, B_165) | v1_xboole_0(A_164))), inference(resolution, [status(thm)], [c_4, c_885])).
% 4.84/1.88  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.84/1.88  tff(c_933, plain, (![B_171, A_172]: (~v1_xboole_0(B_171) | ~r1_tarski(A_172, B_171) | v1_xboole_0(A_172))), inference(resolution, [status(thm)], [c_892, c_2])).
% 4.84/1.88  tff(c_951, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5')) | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_130, c_933])).
% 4.84/1.88  tff(c_955, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_951])).
% 4.84/1.88  tff(c_2399, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2325, c_955])).
% 4.84/1.88  tff(c_2407, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2327, c_2399])).
% 4.84/1.88  tff(c_2408, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1286])).
% 4.84/1.88  tff(c_2432, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2408, c_12])).
% 4.84/1.88  tff(c_2430, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2408, c_2408, c_18])).
% 4.84/1.88  tff(c_2501, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2430, c_955])).
% 4.84/1.88  tff(c_2509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2432, c_2501])).
% 4.84/1.88  tff(c_2510, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_951])).
% 4.84/1.88  tff(c_2511, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_951])).
% 4.84/1.88  tff(c_14, plain, (![B_11, A_10]: (~v1_xboole_0(B_11) | B_11=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.84/1.88  tff(c_2590, plain, (![A_324]: (A_324='#skF_7' | ~v1_xboole_0(A_324))), inference(resolution, [status(thm)], [c_2510, c_14])).
% 4.84/1.88  tff(c_2597, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_2511, c_2590])).
% 4.84/1.88  tff(c_129, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_64, c_115])).
% 4.84/1.88  tff(c_2645, plain, (r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2597, c_129])).
% 4.84/1.88  tff(c_904, plain, (![B_165, A_164]: (~v1_xboole_0(B_165) | ~r1_tarski(A_164, B_165) | v1_xboole_0(A_164))), inference(resolution, [status(thm)], [c_892, c_2])).
% 4.84/1.88  tff(c_2683, plain, (~v1_xboole_0('#skF_7') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_2645, c_904])).
% 4.84/1.88  tff(c_2686, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2510, c_2683])).
% 4.84/1.88  tff(c_2523, plain, (![A_10]: (A_10='#skF_7' | ~v1_xboole_0(A_10))), inference(resolution, [status(thm)], [c_2510, c_14])).
% 4.84/1.88  tff(c_2695, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_2686, c_2523])).
% 4.84/1.88  tff(c_103, plain, (![B_50, A_51]: (~v1_xboole_0(B_50) | B_50=A_51 | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.84/1.88  tff(c_106, plain, (![A_51]: (k1_xboole_0=A_51 | ~v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_12, c_103])).
% 4.84/1.88  tff(c_2522, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_2510, c_106])).
% 4.84/1.88  tff(c_22, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.84/1.88  tff(c_2625, plain, (![A_326]: (m1_subset_1('#skF_7', k1_zfmisc_1(A_326)))), inference(demodulation, [status(thm), theory('equality')], [c_2522, c_22])).
% 4.84/1.88  tff(c_38, plain, (![A_32, B_33, D_35]: (r2_relset_1(A_32, B_33, D_35, D_35) | ~m1_subset_1(D_35, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.84/1.88  tff(c_2638, plain, (![A_32, B_33]: (r2_relset_1(A_32, B_33, '#skF_7', '#skF_7'))), inference(resolution, [status(thm)], [c_2625, c_38])).
% 4.84/1.88  tff(c_2865, plain, (![A_32, B_33]: (r2_relset_1(A_32, B_33, '#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2695, c_2695, c_2638])).
% 4.84/1.88  tff(c_2713, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2695, c_54])).
% 4.84/1.88  tff(c_2873, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2865, c_2713])).
% 4.84/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/1.88  
% 4.84/1.88  Inference rules
% 4.84/1.88  ----------------------
% 4.84/1.88  #Ref     : 2
% 4.84/1.88  #Sup     : 592
% 4.84/1.88  #Fact    : 0
% 4.84/1.88  #Define  : 0
% 4.84/1.88  #Split   : 8
% 4.84/1.88  #Chain   : 0
% 4.84/1.88  #Close   : 0
% 4.84/1.88  
% 4.84/1.88  Ordering : KBO
% 4.84/1.88  
% 4.84/1.88  Simplification rules
% 4.84/1.88  ----------------------
% 4.84/1.88  #Subsume      : 97
% 4.84/1.88  #Demod        : 478
% 4.84/1.88  #Tautology    : 289
% 4.84/1.88  #SimpNegUnit  : 4
% 4.84/1.88  #BackRed      : 153
% 4.84/1.88  
% 4.84/1.88  #Partial instantiations: 0
% 4.84/1.88  #Strategies tried      : 1
% 4.84/1.88  
% 4.84/1.88  Timing (in seconds)
% 4.84/1.88  ----------------------
% 4.84/1.89  Preprocessing        : 0.35
% 4.84/1.89  Parsing              : 0.18
% 4.84/1.89  CNF conversion       : 0.03
% 4.84/1.89  Main loop            : 0.77
% 4.84/1.89  Inferencing          : 0.27
% 4.84/1.89  Reduction            : 0.24
% 4.84/1.89  Demodulation         : 0.17
% 4.84/1.89  BG Simplification    : 0.04
% 4.84/1.89  Subsumption          : 0.14
% 4.84/1.89  Abstraction          : 0.03
% 4.84/1.89  MUC search           : 0.00
% 4.84/1.89  Cooper               : 0.00
% 4.84/1.89  Total                : 1.16
% 4.84/1.89  Index Insertion      : 0.00
% 4.84/1.89  Index Deletion       : 0.00
% 4.84/1.89  Index Matching       : 0.00
% 4.84/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
