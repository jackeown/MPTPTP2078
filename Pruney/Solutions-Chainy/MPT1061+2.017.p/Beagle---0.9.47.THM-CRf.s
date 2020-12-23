%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:39 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 305 expanded)
%              Number of leaves         :   42 ( 117 expanded)
%              Depth                    :    9
%              Number of atoms          :  201 ( 898 expanded)
%              Number of equality atoms :   43 (  90 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_148,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ~ v1_xboole_0(D)
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,A,D)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,D))) )
           => ( ( r1_tarski(B,A)
                & r1_tarski(k7_relset_1(A,D,E,B),C) )
             => ( v1_funct_1(k2_partfun1(A,D,E,B))
                & v1_funct_2(k2_partfun1(A,D,E,B),B,C)
                & m1_subset_1(k2_partfun1(A,D,E,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_funct_2)).

tff(f_51,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_101,axiom,(
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

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_115,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v4_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v4_relat_1(k7_relat_1(C,A),A)
        & v4_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_127,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( k1_relset_1(A,B,C) = A
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_60,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_16,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_70,plain,(
    ! [B_45,A_46] :
      ( v1_relat_1(B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46))
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_73,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(resolution,[status(thm)],[c_62,c_70])).

tff(c_76,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_73])).

tff(c_64,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_704,plain,(
    ! [A_262,B_263,C_264] :
      ( k1_relset_1(A_262,B_263,C_264) = k1_relat_1(C_264)
      | ~ m1_subset_1(C_264,k1_zfmisc_1(k2_zfmisc_1(A_262,B_263))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_712,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_704])).

tff(c_1127,plain,(
    ! [B_359,A_360,C_361] :
      ( k1_xboole_0 = B_359
      | k1_relset_1(A_360,B_359,C_361) = A_360
      | ~ v1_funct_2(C_361,A_360,B_359)
      | ~ m1_subset_1(C_361,k1_zfmisc_1(k2_zfmisc_1(A_360,B_359))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1136,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_1127])).

tff(c_1143,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_712,c_1136])).

tff(c_1144,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1143])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( k1_relat_1(k7_relat_1(B_14,A_13)) = A_13
      | ~ r1_tarski(A_13,k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1152,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1144,c_20])).

tff(c_1220,plain,(
    ! [A_367] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_367)) = A_367
      | ~ r1_tarski(A_367,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1152])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_901,plain,(
    ! [A_326,B_327,C_328,D_329] :
      ( k2_partfun1(A_326,B_327,C_328,D_329) = k7_relat_1(C_328,D_329)
      | ~ m1_subset_1(C_328,k1_zfmisc_1(k2_zfmisc_1(A_326,B_327)))
      | ~ v1_funct_1(C_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_905,plain,(
    ! [D_329] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_329) = k7_relat_1('#skF_5',D_329)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_62,c_901])).

tff(c_911,plain,(
    ! [D_329] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_329) = k7_relat_1('#skF_5',D_329) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_905])).

tff(c_214,plain,(
    ! [C_110,A_111,B_112] :
      ( v4_relat_1(C_110,A_111)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_218,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_214])).

tff(c_224,plain,(
    ! [C_115,A_116,B_117] :
      ( v1_relat_1(k7_relat_1(C_115,A_116))
      | ~ v4_relat_1(C_115,B_117)
      | ~ v1_relat_1(C_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_226,plain,(
    ! [A_116] :
      ( v1_relat_1(k7_relat_1('#skF_5',A_116))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_218,c_224])).

tff(c_229,plain,(
    ! [A_116] : v1_relat_1(k7_relat_1('#skF_5',A_116)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_226])).

tff(c_231,plain,(
    ! [C_119,A_120,B_121] :
      ( v4_relat_1(k7_relat_1(C_119,A_120),A_120)
      | ~ v4_relat_1(C_119,B_121)
      | ~ v1_relat_1(C_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_233,plain,(
    ! [A_120] :
      ( v4_relat_1(k7_relat_1('#skF_5',A_120),A_120)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_218,c_231])).

tff(c_236,plain,(
    ! [A_120] : v4_relat_1(k7_relat_1('#skF_5',A_120),A_120) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_233])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_320,plain,(
    ! [A_162,B_163,C_164,D_165] :
      ( k7_relset_1(A_162,B_163,C_164,D_165) = k9_relat_1(C_164,D_165)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_323,plain,(
    ! [D_165] : k7_relset_1('#skF_1','#skF_4','#skF_5',D_165) = k9_relat_1('#skF_5',D_165) ),
    inference(resolution,[status(thm)],[c_62,c_320])).

tff(c_58,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_324,plain,(
    r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_58])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( k2_relat_1(k7_relat_1(B_12,A_11)) = k9_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_489,plain,(
    ! [A_204,B_205,C_206,D_207] :
      ( k2_partfun1(A_204,B_205,C_206,D_207) = k7_relat_1(C_206,D_207)
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_205)))
      | ~ v1_funct_1(C_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_493,plain,(
    ! [D_207] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_207) = k7_relat_1('#skF_5',D_207)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_62,c_489])).

tff(c_497,plain,(
    ! [D_207] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_207) = k7_relat_1('#skF_5',D_207) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_493])).

tff(c_472,plain,(
    ! [A_200,B_201,C_202,D_203] :
      ( k2_partfun1(A_200,B_201,C_202,D_203) = k7_relat_1(C_202,D_203)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201)))
      | ~ v1_funct_1(C_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_476,plain,(
    ! [D_203] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_203) = k7_relat_1('#skF_5',D_203)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_62,c_472])).

tff(c_480,plain,(
    ! [D_203] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_203) = k7_relat_1('#skF_5',D_203) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_476])).

tff(c_369,plain,(
    ! [C_184,A_185,B_186] :
      ( m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186)))
      | ~ r1_tarski(k2_relat_1(C_184),B_186)
      | ~ r1_tarski(k1_relat_1(C_184),A_185)
      | ~ v1_relat_1(C_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_187,plain,(
    ! [A_99,B_100,C_101,D_102] :
      ( v1_funct_1(k2_partfun1(A_99,B_100,C_101,D_102))
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100)))
      | ~ v1_funct_1(C_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_189,plain,(
    ! [D_102] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_102))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_62,c_187])).

tff(c_192,plain,(
    ! [D_102] : v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_102)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_189])).

tff(c_56,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_77,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_77])).

tff(c_196,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_198,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_412,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_369,c_198])).

tff(c_471,plain,(
    ~ v1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_412])).

tff(c_481,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_471])).

tff(c_486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_481])).

tff(c_487,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_2')
    | ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_412])).

tff(c_529,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_497,c_487])).

tff(c_530,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_529])).

tff(c_533,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_530])).

tff(c_536,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_324,c_533])).

tff(c_537,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_529])).

tff(c_551,plain,
    ( ~ v4_relat_1(k7_relat_1('#skF_5','#skF_2'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_8,c_537])).

tff(c_555,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_236,c_551])).

tff(c_556,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_928,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_911,c_556])).

tff(c_719,plain,(
    ! [A_269,B_270,C_271,D_272] :
      ( v1_funct_1(k2_partfun1(A_269,B_270,C_271,D_272))
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_269,B_270)))
      | ~ v1_funct_1(C_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_723,plain,(
    ! [D_272] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_272))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_62,c_719])).

tff(c_729,plain,(
    ! [D_272] : v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_272)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_723])).

tff(c_918,plain,(
    ! [D_272] : v1_funct_1(k7_relat_1('#skF_5',D_272)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_911,c_729])).

tff(c_557,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_711,plain,(
    k1_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) = k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_557,c_704])).

tff(c_916,plain,(
    k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) = k1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_911,c_911,c_711])).

tff(c_927,plain,(
    m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_911,c_557])).

tff(c_1105,plain,(
    ! [C_349,A_350,B_351] :
      ( v1_funct_2(C_349,A_350,B_351)
      | k1_relset_1(A_350,B_351,C_349) != A_350
      | ~ m1_subset_1(C_349,k1_zfmisc_1(k2_zfmisc_1(A_350,B_351)))
      | ~ v1_funct_1(C_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1111,plain,
    ( v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2'
    | ~ v1_funct_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_927,c_1105])).

tff(c_1118,plain,
    ( v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_916,c_1111])).

tff(c_1119,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_928,c_1118])).

tff(c_1226,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1220,c_1119])).

tff(c_1254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1226])).

tff(c_1255,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1143])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1263,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1255,c_2])).

tff(c_1265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1263])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n008.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 10:40:45 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.43/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.61  
% 3.43/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.62  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.43/1.62  
% 3.43/1.62  %Foreground sorts:
% 3.43/1.62  
% 3.43/1.62  
% 3.43/1.62  %Background operators:
% 3.43/1.62  
% 3.43/1.62  
% 3.43/1.62  %Foreground operators:
% 3.43/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.43/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.62  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.43/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.43/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.43/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.43/1.62  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.43/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.43/1.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.43/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.43/1.62  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.43/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.43/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.43/1.62  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.43/1.62  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.43/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.43/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.43/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.43/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.43/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.62  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.43/1.62  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.43/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.43/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.43/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.43/1.62  
% 3.81/1.64  tff(f_148, negated_conjecture, ~(![A, B, C, D]: (~v1_xboole_0(D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, D)))) => ((r1_tarski(B, A) & r1_tarski(k7_relset_1(A, D, E, B), C)) => ((v1_funct_1(k2_partfun1(A, D, E, B)) & v1_funct_2(k2_partfun1(A, D, E, B), B, C)) & m1_subset_1(k2_partfun1(A, D, E, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_funct_2)).
% 3.81/1.64  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.81/1.64  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.81/1.64  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.81/1.64  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.81/1.64  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 3.81/1.64  tff(f_115, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.81/1.64  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.81/1.64  tff(f_49, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc23_relat_1)).
% 3.81/1.64  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.81/1.64  tff(f_75, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.81/1.64  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.81/1.64  tff(f_83, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 3.81/1.64  tff(f_109, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 3.81/1.64  tff(f_127, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 3.81/1.64  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.81/1.64  tff(c_68, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.81/1.64  tff(c_60, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.81/1.64  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.81/1.64  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.81/1.64  tff(c_70, plain, (![B_45, A_46]: (v1_relat_1(B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.81/1.64  tff(c_73, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_70])).
% 3.81/1.64  tff(c_76, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_73])).
% 3.81/1.64  tff(c_64, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.81/1.64  tff(c_704, plain, (![A_262, B_263, C_264]: (k1_relset_1(A_262, B_263, C_264)=k1_relat_1(C_264) | ~m1_subset_1(C_264, k1_zfmisc_1(k2_zfmisc_1(A_262, B_263))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.81/1.64  tff(c_712, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_704])).
% 3.81/1.64  tff(c_1127, plain, (![B_359, A_360, C_361]: (k1_xboole_0=B_359 | k1_relset_1(A_360, B_359, C_361)=A_360 | ~v1_funct_2(C_361, A_360, B_359) | ~m1_subset_1(C_361, k1_zfmisc_1(k2_zfmisc_1(A_360, B_359))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.81/1.64  tff(c_1136, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_1127])).
% 3.81/1.64  tff(c_1143, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_712, c_1136])).
% 3.81/1.64  tff(c_1144, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_1143])).
% 3.81/1.64  tff(c_20, plain, (![B_14, A_13]: (k1_relat_1(k7_relat_1(B_14, A_13))=A_13 | ~r1_tarski(A_13, k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.81/1.64  tff(c_1152, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_5', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1144, c_20])).
% 3.81/1.64  tff(c_1220, plain, (![A_367]: (k1_relat_1(k7_relat_1('#skF_5', A_367))=A_367 | ~r1_tarski(A_367, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1152])).
% 3.81/1.64  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.81/1.64  tff(c_901, plain, (![A_326, B_327, C_328, D_329]: (k2_partfun1(A_326, B_327, C_328, D_329)=k7_relat_1(C_328, D_329) | ~m1_subset_1(C_328, k1_zfmisc_1(k2_zfmisc_1(A_326, B_327))) | ~v1_funct_1(C_328))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.81/1.64  tff(c_905, plain, (![D_329]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_329)=k7_relat_1('#skF_5', D_329) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_62, c_901])).
% 3.81/1.64  tff(c_911, plain, (![D_329]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_329)=k7_relat_1('#skF_5', D_329))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_905])).
% 3.81/1.64  tff(c_214, plain, (![C_110, A_111, B_112]: (v4_relat_1(C_110, A_111) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.81/1.64  tff(c_218, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_214])).
% 3.81/1.64  tff(c_224, plain, (![C_115, A_116, B_117]: (v1_relat_1(k7_relat_1(C_115, A_116)) | ~v4_relat_1(C_115, B_117) | ~v1_relat_1(C_115))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.81/1.64  tff(c_226, plain, (![A_116]: (v1_relat_1(k7_relat_1('#skF_5', A_116)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_218, c_224])).
% 3.81/1.64  tff(c_229, plain, (![A_116]: (v1_relat_1(k7_relat_1('#skF_5', A_116)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_226])).
% 3.81/1.64  tff(c_231, plain, (![C_119, A_120, B_121]: (v4_relat_1(k7_relat_1(C_119, A_120), A_120) | ~v4_relat_1(C_119, B_121) | ~v1_relat_1(C_119))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.81/1.64  tff(c_233, plain, (![A_120]: (v4_relat_1(k7_relat_1('#skF_5', A_120), A_120) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_218, c_231])).
% 3.81/1.64  tff(c_236, plain, (![A_120]: (v4_relat_1(k7_relat_1('#skF_5', A_120), A_120))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_233])).
% 3.81/1.64  tff(c_8, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.81/1.64  tff(c_320, plain, (![A_162, B_163, C_164, D_165]: (k7_relset_1(A_162, B_163, C_164, D_165)=k9_relat_1(C_164, D_165) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.81/1.64  tff(c_323, plain, (![D_165]: (k7_relset_1('#skF_1', '#skF_4', '#skF_5', D_165)=k9_relat_1('#skF_5', D_165))), inference(resolution, [status(thm)], [c_62, c_320])).
% 3.81/1.64  tff(c_58, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.81/1.64  tff(c_324, plain, (r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_323, c_58])).
% 3.81/1.64  tff(c_18, plain, (![B_12, A_11]: (k2_relat_1(k7_relat_1(B_12, A_11))=k9_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.81/1.64  tff(c_489, plain, (![A_204, B_205, C_206, D_207]: (k2_partfun1(A_204, B_205, C_206, D_207)=k7_relat_1(C_206, D_207) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))) | ~v1_funct_1(C_206))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.81/1.64  tff(c_493, plain, (![D_207]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_207)=k7_relat_1('#skF_5', D_207) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_62, c_489])).
% 3.81/1.64  tff(c_497, plain, (![D_207]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_207)=k7_relat_1('#skF_5', D_207))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_493])).
% 3.81/1.64  tff(c_472, plain, (![A_200, B_201, C_202, D_203]: (k2_partfun1(A_200, B_201, C_202, D_203)=k7_relat_1(C_202, D_203) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))) | ~v1_funct_1(C_202))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.81/1.64  tff(c_476, plain, (![D_203]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_203)=k7_relat_1('#skF_5', D_203) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_62, c_472])).
% 3.81/1.64  tff(c_480, plain, (![D_203]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_203)=k7_relat_1('#skF_5', D_203))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_476])).
% 3.81/1.64  tff(c_369, plain, (![C_184, A_185, B_186]: (m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))) | ~r1_tarski(k2_relat_1(C_184), B_186) | ~r1_tarski(k1_relat_1(C_184), A_185) | ~v1_relat_1(C_184))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.81/1.64  tff(c_187, plain, (![A_99, B_100, C_101, D_102]: (v1_funct_1(k2_partfun1(A_99, B_100, C_101, D_102)) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))) | ~v1_funct_1(C_101))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.81/1.64  tff(c_189, plain, (![D_102]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_102)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_62, c_187])).
% 3.81/1.64  tff(c_192, plain, (![D_102]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_102)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_189])).
% 3.81/1.64  tff(c_56, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.81/1.64  tff(c_77, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_56])).
% 3.81/1.64  tff(c_195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_192, c_77])).
% 3.81/1.64  tff(c_196, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_56])).
% 3.81/1.64  tff(c_198, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_196])).
% 3.81/1.64  tff(c_412, plain, (~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_2') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_369, c_198])).
% 3.81/1.64  tff(c_471, plain, (~v1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_412])).
% 3.81/1.64  tff(c_481, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_480, c_471])).
% 3.81/1.64  tff(c_486, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_229, c_481])).
% 3.81/1.64  tff(c_487, plain, (~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_2') | ~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_412])).
% 3.81/1.64  tff(c_529, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_497, c_497, c_487])).
% 3.81/1.64  tff(c_530, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3')), inference(splitLeft, [status(thm)], [c_529])).
% 3.81/1.64  tff(c_533, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_18, c_530])).
% 3.81/1.64  tff(c_536, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_324, c_533])).
% 3.81/1.64  tff(c_537, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2')), inference(splitRight, [status(thm)], [c_529])).
% 3.81/1.64  tff(c_551, plain, (~v4_relat_1(k7_relat_1('#skF_5', '#skF_2'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_8, c_537])).
% 3.81/1.64  tff(c_555, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_229, c_236, c_551])).
% 3.81/1.64  tff(c_556, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_196])).
% 3.81/1.64  tff(c_928, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_911, c_556])).
% 3.81/1.64  tff(c_719, plain, (![A_269, B_270, C_271, D_272]: (v1_funct_1(k2_partfun1(A_269, B_270, C_271, D_272)) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_269, B_270))) | ~v1_funct_1(C_271))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.81/1.64  tff(c_723, plain, (![D_272]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_272)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_62, c_719])).
% 3.81/1.64  tff(c_729, plain, (![D_272]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_272)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_723])).
% 3.81/1.64  tff(c_918, plain, (![D_272]: (v1_funct_1(k7_relat_1('#skF_5', D_272)))), inference(demodulation, [status(thm), theory('equality')], [c_911, c_729])).
% 3.81/1.64  tff(c_557, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_196])).
% 3.81/1.64  tff(c_711, plain, (k1_relset_1('#skF_2', '#skF_3', k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_557, c_704])).
% 3.81/1.64  tff(c_916, plain, (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))=k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_911, c_911, c_711])).
% 3.81/1.64  tff(c_927, plain, (m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_911, c_557])).
% 3.81/1.64  tff(c_1105, plain, (![C_349, A_350, B_351]: (v1_funct_2(C_349, A_350, B_351) | k1_relset_1(A_350, B_351, C_349)!=A_350 | ~m1_subset_1(C_349, k1_zfmisc_1(k2_zfmisc_1(A_350, B_351))) | ~v1_funct_1(C_349))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.81/1.64  tff(c_1111, plain, (v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2' | ~v1_funct_1(k7_relat_1('#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_927, c_1105])).
% 3.81/1.64  tff(c_1118, plain, (v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_918, c_916, c_1111])).
% 3.81/1.64  tff(c_1119, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_928, c_1118])).
% 3.81/1.64  tff(c_1226, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1220, c_1119])).
% 3.81/1.64  tff(c_1254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_1226])).
% 3.81/1.64  tff(c_1255, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1143])).
% 3.81/1.64  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.81/1.64  tff(c_1263, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1255, c_2])).
% 3.81/1.64  tff(c_1265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1263])).
% 3.81/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.64  
% 3.81/1.64  Inference rules
% 3.81/1.64  ----------------------
% 3.81/1.64  #Ref     : 0
% 3.81/1.64  #Sup     : 231
% 3.81/1.64  #Fact    : 0
% 3.81/1.64  #Define  : 0
% 3.81/1.64  #Split   : 6
% 3.81/1.64  #Chain   : 0
% 3.81/1.64  #Close   : 0
% 3.81/1.64  
% 3.81/1.64  Ordering : KBO
% 3.81/1.64  
% 3.81/1.64  Simplification rules
% 3.81/1.64  ----------------------
% 3.81/1.64  #Subsume      : 4
% 3.81/1.64  #Demod        : 246
% 3.81/1.64  #Tautology    : 96
% 3.81/1.64  #SimpNegUnit  : 4
% 3.81/1.64  #BackRed      : 35
% 3.81/1.64  
% 3.81/1.64  #Partial instantiations: 0
% 3.81/1.64  #Strategies tried      : 1
% 3.81/1.64  
% 3.81/1.64  Timing (in seconds)
% 3.81/1.64  ----------------------
% 3.81/1.64  Preprocessing        : 0.36
% 3.81/1.64  Parsing              : 0.19
% 3.81/1.64  CNF conversion       : 0.02
% 3.81/1.64  Main loop            : 0.48
% 3.81/1.64  Inferencing          : 0.16
% 3.81/1.64  Reduction            : 0.18
% 3.81/1.64  Demodulation         : 0.13
% 3.81/1.64  BG Simplification    : 0.03
% 3.81/1.64  Subsumption          : 0.08
% 3.81/1.64  Abstraction          : 0.02
% 3.81/1.64  MUC search           : 0.00
% 3.81/1.64  Cooper               : 0.00
% 3.81/1.64  Total                : 0.89
% 3.81/1.64  Index Insertion      : 0.00
% 3.81/1.64  Index Deletion       : 0.00
% 3.81/1.64  Index Matching       : 0.00
% 3.81/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
