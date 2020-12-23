%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:05 EST 2020

% Result     : Theorem 6.37s
% Output     : CNFRefutation 6.37s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 403 expanded)
%              Number of leaves         :   46 ( 162 expanded)
%              Depth                    :   12
%              Number of atoms          :  230 (1254 expanded)
%              Number of equality atoms :   54 ( 146 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_165,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_106,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_50,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_76,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_86,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_145,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_48,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_50,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_118,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_62,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_56,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_42,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_16,plain,(
    ! [A_8] : v2_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_66,plain,(
    ! [A_8] : v2_funct_1(k6_partfun1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_16])).

tff(c_1112,plain,(
    ! [A_185,F_184,C_181,D_186,B_182,E_183] :
      ( k4_relset_1(A_185,B_182,C_181,D_186,E_183,F_184) = k5_relat_1(E_183,F_184)
      | ~ m1_subset_1(F_184,k1_zfmisc_1(k2_zfmisc_1(C_181,D_186)))
      | ~ m1_subset_1(E_183,k1_zfmisc_1(k2_zfmisc_1(A_185,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1145,plain,(
    ! [A_191,B_192,E_193] :
      ( k4_relset_1(A_191,B_192,'#skF_2','#skF_1',E_193,'#skF_4') = k5_relat_1(E_193,'#skF_4')
      | ~ m1_subset_1(E_193,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192))) ) ),
    inference(resolution,[status(thm)],[c_54,c_1112])).

tff(c_1163,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_1145])).

tff(c_24,plain,(
    ! [B_16,A_15,D_18,E_19,F_20,C_17] :
      ( m1_subset_1(k4_relset_1(A_15,B_16,C_17,D_18,E_19,F_20),k1_zfmisc_1(k2_zfmisc_1(A_15,D_18)))
      | ~ m1_subset_1(F_20,k1_zfmisc_1(k2_zfmisc_1(C_17,D_18)))
      | ~ m1_subset_1(E_19,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1276,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1163,c_24])).

tff(c_1280,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_54,c_1276])).

tff(c_1324,plain,(
    ! [C_211,D_209,A_206,F_208,E_210,B_207] :
      ( k1_partfun1(A_206,B_207,C_211,D_209,E_210,F_208) = k5_relat_1(E_210,F_208)
      | ~ m1_subset_1(F_208,k1_zfmisc_1(k2_zfmisc_1(C_211,D_209)))
      | ~ v1_funct_1(F_208)
      | ~ m1_subset_1(E_210,k1_zfmisc_1(k2_zfmisc_1(A_206,B_207)))
      | ~ v1_funct_1(E_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1334,plain,(
    ! [A_206,B_207,E_210] :
      ( k1_partfun1(A_206,B_207,'#skF_2','#skF_1',E_210,'#skF_4') = k5_relat_1(E_210,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_210,k1_zfmisc_1(k2_zfmisc_1(A_206,B_207)))
      | ~ v1_funct_1(E_210) ) ),
    inference(resolution,[status(thm)],[c_54,c_1324])).

tff(c_1881,plain,(
    ! [A_243,B_244,E_245] :
      ( k1_partfun1(A_243,B_244,'#skF_2','#skF_1',E_245,'#skF_4') = k5_relat_1(E_245,'#skF_4')
      | ~ m1_subset_1(E_245,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244)))
      | ~ v1_funct_1(E_245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1334])).

tff(c_1911,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1881])).

tff(c_1931,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1911])).

tff(c_34,plain,(
    ! [A_34] : m1_subset_1(k6_relat_1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_65,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_34])).

tff(c_52,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_1043,plain,(
    ! [D_171,C_172,A_173,B_174] :
      ( D_171 = C_172
      | ~ r2_relset_1(A_173,B_174,C_172,D_171)
      | ~ m1_subset_1(D_171,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174)))
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1049,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_52,c_1043])).

tff(c_1060,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_1049])).

tff(c_1084,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1060])).

tff(c_2576,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1931,c_1084])).

tff(c_2580,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1280,c_2576])).

tff(c_2581,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1060])).

tff(c_3005,plain,(
    ! [A_330,C_328,B_329,D_331,E_327] :
      ( k1_xboole_0 = C_328
      | v2_funct_1(D_331)
      | ~ v2_funct_1(k1_partfun1(A_330,B_329,B_329,C_328,D_331,E_327))
      | ~ m1_subset_1(E_327,k1_zfmisc_1(k2_zfmisc_1(B_329,C_328)))
      | ~ v1_funct_2(E_327,B_329,C_328)
      | ~ v1_funct_1(E_327)
      | ~ m1_subset_1(D_331,k1_zfmisc_1(k2_zfmisc_1(A_330,B_329)))
      | ~ v1_funct_2(D_331,A_330,B_329)
      | ~ v1_funct_1(D_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_3007,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2581,c_3005])).

tff(c_3009,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_56,c_54,c_66,c_3007])).

tff(c_3010,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_3009])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_3038,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3010,c_2])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3036,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3010,c_3010,c_8])).

tff(c_2610,plain,(
    ! [A_293,C_289,F_292,B_290,D_294,E_291] :
      ( k4_relset_1(A_293,B_290,C_289,D_294,E_291,F_292) = k5_relat_1(E_291,F_292)
      | ~ m1_subset_1(F_292,k1_zfmisc_1(k2_zfmisc_1(C_289,D_294)))
      | ~ m1_subset_1(E_291,k1_zfmisc_1(k2_zfmisc_1(A_293,B_290))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2643,plain,(
    ! [A_299,B_300,E_301] :
      ( k4_relset_1(A_299,B_300,'#skF_2','#skF_1',E_301,'#skF_4') = k5_relat_1(E_301,'#skF_4')
      | ~ m1_subset_1(E_301,k1_zfmisc_1(k2_zfmisc_1(A_299,B_300))) ) ),
    inference(resolution,[status(thm)],[c_54,c_2610])).

tff(c_2661,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_2643])).

tff(c_2741,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2661,c_24])).

tff(c_2745,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_54,c_2741])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( v1_xboole_0(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2776,plain,
    ( v1_xboole_0(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_2745,c_12])).

tff(c_2855,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2776])).

tff(c_3151,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3036,c_2855])).

tff(c_3158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3038,c_3151])).

tff(c_3160,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_2776])).

tff(c_119,plain,(
    ! [B_60,A_61] :
      ( ~ v1_xboole_0(B_60)
      | B_60 = A_61
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_122,plain,(
    ! [A_61] :
      ( k1_xboole_0 = A_61
      | ~ v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_2,c_119])).

tff(c_3177,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3160,c_122])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3267,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_3177,c_6])).

tff(c_3328,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3267,c_2])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3325,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3267,c_3267,c_10])).

tff(c_146,plain,(
    ! [B_64,A_65] :
      ( v1_xboole_0(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_164,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_146])).

tff(c_177,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_3436,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3325,c_177])).

tff(c_3440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3328,c_3436])).

tff(c_3441,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_3448,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3441,c_122])).

tff(c_96,plain,(
    ! [A_59] : k6_relat_1(A_59) = k6_partfun1(A_59) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_14,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_102,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_14])).

tff(c_113,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_66])).

tff(c_3460,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3448,c_113])).

tff(c_3467,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_3460])).

tff(c_3468,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_3497,plain,(
    ! [C_362,A_363,B_364] :
      ( v1_relat_1(C_362)
      | ~ m1_subset_1(C_362,k1_zfmisc_1(k2_zfmisc_1(A_363,B_364))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3512,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_3497])).

tff(c_3578,plain,(
    ! [C_375,B_376,A_377] :
      ( v5_relat_1(C_375,B_376)
      | ~ m1_subset_1(C_375,k1_zfmisc_1(k2_zfmisc_1(A_377,B_376))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3595,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_3578])).

tff(c_3680,plain,(
    ! [A_391,B_392,C_393] :
      ( k2_relset_1(A_391,B_392,C_393) = k2_relat_1(C_393)
      | ~ m1_subset_1(C_393,k1_zfmisc_1(k2_zfmisc_1(A_391,B_392))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3697,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_3680])).

tff(c_4277,plain,(
    ! [A_453,B_454,C_455,D_456] :
      ( k2_relset_1(A_453,B_454,C_455) = B_454
      | ~ r2_relset_1(B_454,B_454,k1_partfun1(B_454,A_453,A_453,B_454,D_456,C_455),k6_partfun1(B_454))
      | ~ m1_subset_1(D_456,k1_zfmisc_1(k2_zfmisc_1(B_454,A_453)))
      | ~ v1_funct_2(D_456,B_454,A_453)
      | ~ v1_funct_1(D_456)
      | ~ m1_subset_1(C_455,k1_zfmisc_1(k2_zfmisc_1(A_453,B_454)))
      | ~ v1_funct_2(C_455,A_453,B_454)
      | ~ v1_funct_1(C_455) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_4280,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_4277])).

tff(c_4286,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_64,c_62,c_60,c_3697,c_4280])).

tff(c_36,plain,(
    ! [B_36] :
      ( v2_funct_2(B_36,k2_relat_1(B_36))
      | ~ v5_relat_1(B_36,k2_relat_1(B_36))
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4292,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4286,c_36])).

tff(c_4296,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3512,c_3595,c_4286,c_4292])).

tff(c_4298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3468,c_4296])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:23:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.37/2.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.37/2.26  
% 6.37/2.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.37/2.26  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.37/2.26  
% 6.37/2.26  %Foreground sorts:
% 6.37/2.26  
% 6.37/2.26  
% 6.37/2.26  %Background operators:
% 6.37/2.26  
% 6.37/2.26  
% 6.37/2.26  %Foreground operators:
% 6.37/2.26  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.37/2.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.37/2.26  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.37/2.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.37/2.26  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.37/2.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.37/2.26  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.37/2.26  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.37/2.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.37/2.26  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.37/2.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.37/2.26  tff('#skF_2', type, '#skF_2': $i).
% 6.37/2.26  tff('#skF_3', type, '#skF_3': $i).
% 6.37/2.26  tff('#skF_1', type, '#skF_1': $i).
% 6.37/2.26  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.37/2.26  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.37/2.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.37/2.26  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.37/2.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.37/2.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.37/2.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.37/2.26  tff('#skF_4', type, '#skF_4': $i).
% 6.37/2.26  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.37/2.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.37/2.26  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.37/2.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.37/2.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.37/2.26  
% 6.37/2.29  tff(f_165, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 6.37/2.29  tff(f_106, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.37/2.29  tff(f_50, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 6.37/2.29  tff(f_76, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 6.37/2.29  tff(f_66, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 6.37/2.29  tff(f_104, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.37/2.29  tff(f_86, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 6.37/2.29  tff(f_84, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.37/2.29  tff(f_145, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 6.37/2.29  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.37/2.29  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.37/2.29  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 6.37/2.29  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 6.37/2.29  tff(f_48, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 6.37/2.29  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.37/2.29  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.37/2.29  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.37/2.29  tff(f_123, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 6.37/2.29  tff(f_94, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.37/2.29  tff(c_50, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.37/2.29  tff(c_118, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 6.37/2.29  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.37/2.29  tff(c_62, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.37/2.29  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.37/2.29  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.37/2.29  tff(c_56, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.37/2.29  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.37/2.29  tff(c_42, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.37/2.29  tff(c_16, plain, (![A_8]: (v2_funct_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.37/2.29  tff(c_66, plain, (![A_8]: (v2_funct_1(k6_partfun1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_16])).
% 6.37/2.29  tff(c_1112, plain, (![A_185, F_184, C_181, D_186, B_182, E_183]: (k4_relset_1(A_185, B_182, C_181, D_186, E_183, F_184)=k5_relat_1(E_183, F_184) | ~m1_subset_1(F_184, k1_zfmisc_1(k2_zfmisc_1(C_181, D_186))) | ~m1_subset_1(E_183, k1_zfmisc_1(k2_zfmisc_1(A_185, B_182))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.37/2.29  tff(c_1145, plain, (![A_191, B_192, E_193]: (k4_relset_1(A_191, B_192, '#skF_2', '#skF_1', E_193, '#skF_4')=k5_relat_1(E_193, '#skF_4') | ~m1_subset_1(E_193, k1_zfmisc_1(k2_zfmisc_1(A_191, B_192))))), inference(resolution, [status(thm)], [c_54, c_1112])).
% 6.37/2.29  tff(c_1163, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_1145])).
% 6.37/2.29  tff(c_24, plain, (![B_16, A_15, D_18, E_19, F_20, C_17]: (m1_subset_1(k4_relset_1(A_15, B_16, C_17, D_18, E_19, F_20), k1_zfmisc_1(k2_zfmisc_1(A_15, D_18))) | ~m1_subset_1(F_20, k1_zfmisc_1(k2_zfmisc_1(C_17, D_18))) | ~m1_subset_1(E_19, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.37/2.29  tff(c_1276, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1163, c_24])).
% 6.37/2.29  tff(c_1280, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_54, c_1276])).
% 6.37/2.29  tff(c_1324, plain, (![C_211, D_209, A_206, F_208, E_210, B_207]: (k1_partfun1(A_206, B_207, C_211, D_209, E_210, F_208)=k5_relat_1(E_210, F_208) | ~m1_subset_1(F_208, k1_zfmisc_1(k2_zfmisc_1(C_211, D_209))) | ~v1_funct_1(F_208) | ~m1_subset_1(E_210, k1_zfmisc_1(k2_zfmisc_1(A_206, B_207))) | ~v1_funct_1(E_210))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.37/2.29  tff(c_1334, plain, (![A_206, B_207, E_210]: (k1_partfun1(A_206, B_207, '#skF_2', '#skF_1', E_210, '#skF_4')=k5_relat_1(E_210, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_210, k1_zfmisc_1(k2_zfmisc_1(A_206, B_207))) | ~v1_funct_1(E_210))), inference(resolution, [status(thm)], [c_54, c_1324])).
% 6.37/2.29  tff(c_1881, plain, (![A_243, B_244, E_245]: (k1_partfun1(A_243, B_244, '#skF_2', '#skF_1', E_245, '#skF_4')=k5_relat_1(E_245, '#skF_4') | ~m1_subset_1(E_245, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))) | ~v1_funct_1(E_245))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1334])).
% 6.37/2.29  tff(c_1911, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1881])).
% 6.37/2.29  tff(c_1931, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1911])).
% 6.37/2.29  tff(c_34, plain, (![A_34]: (m1_subset_1(k6_relat_1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.37/2.29  tff(c_65, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_34])).
% 6.37/2.29  tff(c_52, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.37/2.29  tff(c_1043, plain, (![D_171, C_172, A_173, B_174]: (D_171=C_172 | ~r2_relset_1(A_173, B_174, C_172, D_171) | ~m1_subset_1(D_171, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.37/2.29  tff(c_1049, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_52, c_1043])).
% 6.37/2.29  tff(c_1060, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_1049])).
% 6.37/2.29  tff(c_1084, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1060])).
% 6.37/2.29  tff(c_2576, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1931, c_1084])).
% 6.37/2.29  tff(c_2580, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1280, c_2576])).
% 6.37/2.29  tff(c_2581, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1060])).
% 6.37/2.29  tff(c_3005, plain, (![A_330, C_328, B_329, D_331, E_327]: (k1_xboole_0=C_328 | v2_funct_1(D_331) | ~v2_funct_1(k1_partfun1(A_330, B_329, B_329, C_328, D_331, E_327)) | ~m1_subset_1(E_327, k1_zfmisc_1(k2_zfmisc_1(B_329, C_328))) | ~v1_funct_2(E_327, B_329, C_328) | ~v1_funct_1(E_327) | ~m1_subset_1(D_331, k1_zfmisc_1(k2_zfmisc_1(A_330, B_329))) | ~v1_funct_2(D_331, A_330, B_329) | ~v1_funct_1(D_331))), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.37/2.29  tff(c_3007, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2581, c_3005])).
% 6.37/2.29  tff(c_3009, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_56, c_54, c_66, c_3007])).
% 6.37/2.29  tff(c_3010, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_118, c_3009])).
% 6.37/2.29  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.37/2.29  tff(c_3038, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3010, c_2])).
% 6.37/2.29  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.37/2.29  tff(c_3036, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3010, c_3010, c_8])).
% 6.37/2.29  tff(c_2610, plain, (![A_293, C_289, F_292, B_290, D_294, E_291]: (k4_relset_1(A_293, B_290, C_289, D_294, E_291, F_292)=k5_relat_1(E_291, F_292) | ~m1_subset_1(F_292, k1_zfmisc_1(k2_zfmisc_1(C_289, D_294))) | ~m1_subset_1(E_291, k1_zfmisc_1(k2_zfmisc_1(A_293, B_290))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.37/2.29  tff(c_2643, plain, (![A_299, B_300, E_301]: (k4_relset_1(A_299, B_300, '#skF_2', '#skF_1', E_301, '#skF_4')=k5_relat_1(E_301, '#skF_4') | ~m1_subset_1(E_301, k1_zfmisc_1(k2_zfmisc_1(A_299, B_300))))), inference(resolution, [status(thm)], [c_54, c_2610])).
% 6.37/2.29  tff(c_2661, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_2643])).
% 6.37/2.29  tff(c_2741, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2661, c_24])).
% 6.37/2.29  tff(c_2745, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_54, c_2741])).
% 6.37/2.29  tff(c_12, plain, (![B_7, A_5]: (v1_xboole_0(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.37/2.29  tff(c_2776, plain, (v1_xboole_0(k5_relat_1('#skF_3', '#skF_4')) | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_2745, c_12])).
% 6.37/2.29  tff(c_2855, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(splitLeft, [status(thm)], [c_2776])).
% 6.37/2.29  tff(c_3151, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3036, c_2855])).
% 6.37/2.29  tff(c_3158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3038, c_3151])).
% 6.37/2.29  tff(c_3160, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(splitRight, [status(thm)], [c_2776])).
% 6.37/2.29  tff(c_119, plain, (![B_60, A_61]: (~v1_xboole_0(B_60) | B_60=A_61 | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.37/2.29  tff(c_122, plain, (![A_61]: (k1_xboole_0=A_61 | ~v1_xboole_0(A_61))), inference(resolution, [status(thm)], [c_2, c_119])).
% 6.37/2.29  tff(c_3177, plain, (k2_zfmisc_1('#skF_1', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_3160, c_122])).
% 6.37/2.29  tff(c_6, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.37/2.29  tff(c_3267, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_3177, c_6])).
% 6.37/2.29  tff(c_3328, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3267, c_2])).
% 6.37/2.29  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.37/2.29  tff(c_3325, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3267, c_3267, c_10])).
% 6.37/2.29  tff(c_146, plain, (![B_64, A_65]: (v1_xboole_0(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.37/2.29  tff(c_164, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_146])).
% 6.37/2.29  tff(c_177, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_164])).
% 6.37/2.29  tff(c_3436, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3325, c_177])).
% 6.37/2.29  tff(c_3440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3328, c_3436])).
% 6.37/2.29  tff(c_3441, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_164])).
% 6.37/2.29  tff(c_3448, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3441, c_122])).
% 6.37/2.29  tff(c_96, plain, (![A_59]: (k6_relat_1(A_59)=k6_partfun1(A_59))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.37/2.29  tff(c_14, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.37/2.29  tff(c_102, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_96, c_14])).
% 6.37/2.29  tff(c_113, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_102, c_66])).
% 6.37/2.29  tff(c_3460, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3448, c_113])).
% 6.37/2.29  tff(c_3467, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_3460])).
% 6.37/2.29  tff(c_3468, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 6.37/2.29  tff(c_3497, plain, (![C_362, A_363, B_364]: (v1_relat_1(C_362) | ~m1_subset_1(C_362, k1_zfmisc_1(k2_zfmisc_1(A_363, B_364))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.37/2.29  tff(c_3512, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_3497])).
% 6.37/2.29  tff(c_3578, plain, (![C_375, B_376, A_377]: (v5_relat_1(C_375, B_376) | ~m1_subset_1(C_375, k1_zfmisc_1(k2_zfmisc_1(A_377, B_376))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.37/2.29  tff(c_3595, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_3578])).
% 6.37/2.29  tff(c_3680, plain, (![A_391, B_392, C_393]: (k2_relset_1(A_391, B_392, C_393)=k2_relat_1(C_393) | ~m1_subset_1(C_393, k1_zfmisc_1(k2_zfmisc_1(A_391, B_392))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.37/2.29  tff(c_3697, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_3680])).
% 6.37/2.29  tff(c_4277, plain, (![A_453, B_454, C_455, D_456]: (k2_relset_1(A_453, B_454, C_455)=B_454 | ~r2_relset_1(B_454, B_454, k1_partfun1(B_454, A_453, A_453, B_454, D_456, C_455), k6_partfun1(B_454)) | ~m1_subset_1(D_456, k1_zfmisc_1(k2_zfmisc_1(B_454, A_453))) | ~v1_funct_2(D_456, B_454, A_453) | ~v1_funct_1(D_456) | ~m1_subset_1(C_455, k1_zfmisc_1(k2_zfmisc_1(A_453, B_454))) | ~v1_funct_2(C_455, A_453, B_454) | ~v1_funct_1(C_455))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.37/2.29  tff(c_4280, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_4277])).
% 6.37/2.29  tff(c_4286, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_64, c_62, c_60, c_3697, c_4280])).
% 6.37/2.29  tff(c_36, plain, (![B_36]: (v2_funct_2(B_36, k2_relat_1(B_36)) | ~v5_relat_1(B_36, k2_relat_1(B_36)) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.37/2.29  tff(c_4292, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4286, c_36])).
% 6.37/2.29  tff(c_4296, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3512, c_3595, c_4286, c_4292])).
% 6.37/2.29  tff(c_4298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3468, c_4296])).
% 6.37/2.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.37/2.29  
% 6.37/2.29  Inference rules
% 6.37/2.29  ----------------------
% 6.37/2.29  #Ref     : 0
% 6.37/2.29  #Sup     : 1033
% 6.37/2.29  #Fact    : 0
% 6.37/2.29  #Define  : 0
% 6.37/2.29  #Split   : 22
% 6.37/2.29  #Chain   : 0
% 6.37/2.29  #Close   : 0
% 6.37/2.29  
% 6.37/2.29  Ordering : KBO
% 6.37/2.29  
% 6.37/2.29  Simplification rules
% 6.37/2.29  ----------------------
% 6.37/2.29  #Subsume      : 28
% 6.37/2.29  #Demod        : 636
% 6.37/2.29  #Tautology    : 342
% 6.37/2.29  #SimpNegUnit  : 4
% 6.37/2.29  #BackRed      : 105
% 6.37/2.29  
% 6.37/2.29  #Partial instantiations: 0
% 6.37/2.29  #Strategies tried      : 1
% 6.37/2.29  
% 6.37/2.29  Timing (in seconds)
% 6.37/2.29  ----------------------
% 6.37/2.29  Preprocessing        : 0.38
% 6.37/2.29  Parsing              : 0.21
% 6.37/2.29  CNF conversion       : 0.02
% 6.37/2.29  Main loop            : 1.11
% 6.37/2.29  Inferencing          : 0.38
% 6.37/2.29  Reduction            : 0.40
% 6.37/2.29  Demodulation         : 0.29
% 6.37/2.29  BG Simplification    : 0.04
% 6.37/2.29  Subsumption          : 0.18
% 6.37/2.29  Abstraction          : 0.05
% 6.37/2.29  MUC search           : 0.00
% 6.37/2.29  Cooper               : 0.00
% 6.37/2.29  Total                : 1.54
% 6.37/2.29  Index Insertion      : 0.00
% 6.37/2.29  Index Deletion       : 0.00
% 6.37/2.29  Index Matching       : 0.00
% 6.37/2.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
