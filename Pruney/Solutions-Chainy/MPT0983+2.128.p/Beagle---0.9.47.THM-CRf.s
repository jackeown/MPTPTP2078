%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:20 EST 2020

% Result     : Theorem 6.65s
% Output     : CNFRefutation 6.65s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 298 expanded)
%              Number of leaves         :   51 ( 124 expanded)
%              Depth                    :   10
%              Number of atoms          :  262 ( 929 expanded)
%              Number of equality atoms :   68 ( 134 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_183,negated_conjecture,(
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

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_126,axiom,(
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

tff(f_146,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ? [B] :
            ( v1_relat_1(B)
            & v1_funct_1(B)
            & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
       => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

tff(f_98,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_144,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_108,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

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

tff(f_57,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_59,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_163,axiom,(
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

tff(f_134,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_64,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_141,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_16,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_214,plain,(
    ! [B_76,A_77] :
      ( v1_relat_1(B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_77))
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_226,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_68,c_214])).

tff(c_238,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_226])).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_223,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_74,c_214])).

tff(c_235,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_223])).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_76,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_1214,plain,(
    ! [A_191,B_192,C_193] :
      ( k1_relset_1(A_191,B_192,C_193) = k1_relat_1(C_193)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1231,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1214])).

tff(c_1376,plain,(
    ! [B_216,A_217,C_218] :
      ( k1_xboole_0 = B_216
      | k1_relset_1(A_217,B_216,C_218) = A_217
      | ~ v1_funct_2(C_218,A_217,B_216)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_217,B_216))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1382,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_1376])).

tff(c_1396,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1231,c_1382])).

tff(c_1401,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1396])).

tff(c_60,plain,(
    ! [A_54] : k6_relat_1(A_54) = k6_partfun1(A_54) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_22,plain,(
    ! [A_14,B_16] :
      ( v2_funct_1(A_14)
      | k6_relat_1(k1_relat_1(A_14)) != k5_relat_1(A_14,B_16)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1519,plain,(
    ! [A_231,B_232] :
      ( v2_funct_1(A_231)
      | k6_partfun1(k1_relat_1(A_231)) != k5_relat_1(A_231,B_232)
      | ~ v1_funct_1(B_232)
      | ~ v1_relat_1(B_232)
      | ~ v1_funct_1(A_231)
      | ~ v1_relat_1(A_231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_22])).

tff(c_1523,plain,(
    ! [B_232] :
      ( v2_funct_1('#skF_3')
      | k5_relat_1('#skF_3',B_232) != k6_partfun1('#skF_1')
      | ~ v1_funct_1(B_232)
      | ~ v1_relat_1(B_232)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1401,c_1519])).

tff(c_1527,plain,(
    ! [B_232] :
      ( v2_funct_1('#skF_3')
      | k5_relat_1('#skF_3',B_232) != k6_partfun1('#skF_1')
      | ~ v1_funct_1(B_232)
      | ~ v1_relat_1(B_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_78,c_1523])).

tff(c_1529,plain,(
    ! [B_233] :
      ( k5_relat_1('#skF_3',B_233) != k6_partfun1('#skF_1')
      | ~ v1_funct_1(B_233)
      | ~ v1_relat_1(B_233) ) ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_1527])).

tff(c_1535,plain,
    ( k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_238,c_1529])).

tff(c_1548,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1535])).

tff(c_1587,plain,(
    ! [B_237,A_240,F_238,C_239,E_236,D_241] :
      ( k4_relset_1(A_240,B_237,C_239,D_241,E_236,F_238) = k5_relat_1(E_236,F_238)
      | ~ m1_subset_1(F_238,k1_zfmisc_1(k2_zfmisc_1(C_239,D_241)))
      | ~ m1_subset_1(E_236,k1_zfmisc_1(k2_zfmisc_1(A_240,B_237))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1606,plain,(
    ! [A_243,B_244,E_245] :
      ( k4_relset_1(A_243,B_244,'#skF_2','#skF_1',E_245,'#skF_4') = k5_relat_1(E_245,'#skF_4')
      | ~ m1_subset_1(E_245,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244))) ) ),
    inference(resolution,[status(thm)],[c_68,c_1587])).

tff(c_1623,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_1606])).

tff(c_1651,plain,(
    ! [B_251,A_254,E_253,C_250,F_255,D_252] :
      ( m1_subset_1(k4_relset_1(A_254,B_251,C_250,D_252,E_253,F_255),k1_zfmisc_1(k2_zfmisc_1(A_254,D_252)))
      | ~ m1_subset_1(F_255,k1_zfmisc_1(k2_zfmisc_1(C_250,D_252)))
      | ~ m1_subset_1(E_253,k1_zfmisc_1(k2_zfmisc_1(A_254,B_251))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1688,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1623,c_1651])).

tff(c_1711,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_68,c_1688])).

tff(c_1861,plain,(
    ! [B_261,C_263,D_260,E_264,A_262,F_259] :
      ( k1_partfun1(A_262,B_261,C_263,D_260,E_264,F_259) = k5_relat_1(E_264,F_259)
      | ~ m1_subset_1(F_259,k1_zfmisc_1(k2_zfmisc_1(C_263,D_260)))
      | ~ v1_funct_1(F_259)
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(A_262,B_261)))
      | ~ v1_funct_1(E_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1873,plain,(
    ! [A_262,B_261,E_264] :
      ( k1_partfun1(A_262,B_261,'#skF_2','#skF_1',E_264,'#skF_4') = k5_relat_1(E_264,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(A_262,B_261)))
      | ~ v1_funct_1(E_264) ) ),
    inference(resolution,[status(thm)],[c_68,c_1861])).

tff(c_2256,plain,(
    ! [A_274,B_275,E_276] :
      ( k1_partfun1(A_274,B_275,'#skF_2','#skF_1',E_276,'#skF_4') = k5_relat_1(E_276,'#skF_4')
      | ~ m1_subset_1(E_276,k1_zfmisc_1(k2_zfmisc_1(A_274,B_275)))
      | ~ v1_funct_1(E_276) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1873])).

tff(c_2280,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_2256])).

tff(c_2299,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2280])).

tff(c_40,plain,(
    ! [A_42] : m1_subset_1(k6_relat_1(A_42),k1_zfmisc_1(k2_zfmisc_1(A_42,A_42))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_79,plain,(
    ! [A_42] : m1_subset_1(k6_partfun1(A_42),k1_zfmisc_1(k2_zfmisc_1(A_42,A_42))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_40])).

tff(c_66,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_1435,plain,(
    ! [D_222,C_223,A_224,B_225] :
      ( D_222 = C_223
      | ~ r2_relset_1(A_224,B_225,C_223,D_222)
      | ~ m1_subset_1(D_222,k1_zfmisc_1(k2_zfmisc_1(A_224,B_225)))
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_224,B_225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1447,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_1435])).

tff(c_1470,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_1447])).

tff(c_1554,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1470])).

tff(c_2310,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2299,c_1554])).

tff(c_2314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1711,c_2310])).

tff(c_2315,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1470])).

tff(c_2629,plain,(
    ! [E_308,C_307,D_304,B_305,A_306,F_303] :
      ( k1_partfun1(A_306,B_305,C_307,D_304,E_308,F_303) = k5_relat_1(E_308,F_303)
      | ~ m1_subset_1(F_303,k1_zfmisc_1(k2_zfmisc_1(C_307,D_304)))
      | ~ v1_funct_1(F_303)
      | ~ m1_subset_1(E_308,k1_zfmisc_1(k2_zfmisc_1(A_306,B_305)))
      | ~ v1_funct_1(E_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2641,plain,(
    ! [A_306,B_305,E_308] :
      ( k1_partfun1(A_306,B_305,'#skF_2','#skF_1',E_308,'#skF_4') = k5_relat_1(E_308,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_308,k1_zfmisc_1(k2_zfmisc_1(A_306,B_305)))
      | ~ v1_funct_1(E_308) ) ),
    inference(resolution,[status(thm)],[c_68,c_2629])).

tff(c_3051,plain,(
    ! [A_319,B_320,E_321] :
      ( k1_partfun1(A_319,B_320,'#skF_2','#skF_1',E_321,'#skF_4') = k5_relat_1(E_321,'#skF_4')
      | ~ m1_subset_1(E_321,k1_zfmisc_1(k2_zfmisc_1(A_319,B_320)))
      | ~ v1_funct_1(E_321) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2641])).

tff(c_3075,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_3051])).

tff(c_3094,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2315,c_3075])).

tff(c_3096,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1548,c_3094])).

tff(c_3097,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1396])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_3129,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3097,c_2])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3123,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3097,c_3097,c_8])).

tff(c_180,plain,(
    ! [B_73,A_74] :
      ( v1_xboole_0(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74))
      | ~ v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_197,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_74,c_180])).

tff(c_199,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_197])).

tff(c_3224,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3123,c_199])).

tff(c_3228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3129,c_3224])).

tff(c_3229,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_142,plain,(
    ! [B_67,A_68] :
      ( ~ v1_xboole_0(B_67)
      | B_67 = A_68
      | ~ v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_145,plain,(
    ! [A_68] :
      ( k1_xboole_0 = A_68
      | ~ v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_2,c_142])).

tff(c_3236,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3229,c_145])).

tff(c_101,plain,(
    ! [A_65] : k6_relat_1(A_65) = k6_partfun1(A_65) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_18,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_107,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_18])).

tff(c_20,plain,(
    ! [A_13] : v2_funct_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_81,plain,(
    ! [A_13] : v2_funct_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_20])).

tff(c_118,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_81])).

tff(c_3267,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3236,c_118])).

tff(c_3274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_3267])).

tff(c_3275,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_3315,plain,(
    ! [B_334,A_335] :
      ( v1_relat_1(B_334)
      | ~ m1_subset_1(B_334,k1_zfmisc_1(A_335))
      | ~ v1_relat_1(A_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3327,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_68,c_3315])).

tff(c_3339,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_3327])).

tff(c_3401,plain,(
    ! [C_344,B_345,A_346] :
      ( v5_relat_1(C_344,B_345)
      | ~ m1_subset_1(C_344,k1_zfmisc_1(k2_zfmisc_1(A_346,B_345))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3419,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_3401])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_3565,plain,(
    ! [A_373,B_374,C_375] :
      ( k2_relset_1(A_373,B_374,C_375) = k2_relat_1(C_375)
      | ~ m1_subset_1(C_375,k1_zfmisc_1(k2_zfmisc_1(A_373,B_374))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3583,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_3565])).

tff(c_4227,plain,(
    ! [A_438,B_439,C_440,D_441] :
      ( k2_relset_1(A_438,B_439,C_440) = B_439
      | ~ r2_relset_1(B_439,B_439,k1_partfun1(B_439,A_438,A_438,B_439,D_441,C_440),k6_partfun1(B_439))
      | ~ m1_subset_1(D_441,k1_zfmisc_1(k2_zfmisc_1(B_439,A_438)))
      | ~ v1_funct_2(D_441,B_439,A_438)
      | ~ v1_funct_1(D_441)
      | ~ m1_subset_1(C_440,k1_zfmisc_1(k2_zfmisc_1(A_438,B_439)))
      | ~ v1_funct_2(C_440,A_438,B_439)
      | ~ v1_funct_1(C_440) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_4230,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_4227])).

tff(c_4236,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_78,c_76,c_74,c_3583,c_4230])).

tff(c_54,plain,(
    ! [B_47] :
      ( v2_funct_2(B_47,k2_relat_1(B_47))
      | ~ v5_relat_1(B_47,k2_relat_1(B_47))
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_4242,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4236,c_54])).

tff(c_4246,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3339,c_3419,c_4236,c_4242])).

tff(c_4248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3275,c_4246])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:11:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.65/2.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.65/2.38  
% 6.65/2.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.65/2.38  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.65/2.38  
% 6.65/2.38  %Foreground sorts:
% 6.65/2.38  
% 6.65/2.38  
% 6.65/2.38  %Background operators:
% 6.65/2.38  
% 6.65/2.38  
% 6.65/2.38  %Foreground operators:
% 6.65/2.38  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.65/2.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.65/2.38  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.65/2.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.65/2.38  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.65/2.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.65/2.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.65/2.38  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.65/2.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.65/2.38  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.65/2.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.65/2.38  tff('#skF_2', type, '#skF_2': $i).
% 6.65/2.38  tff('#skF_3', type, '#skF_3': $i).
% 6.65/2.38  tff('#skF_1', type, '#skF_1': $i).
% 6.65/2.38  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.65/2.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.65/2.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.65/2.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.65/2.38  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.65/2.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.65/2.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.65/2.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.65/2.38  tff('#skF_4', type, '#skF_4': $i).
% 6.65/2.38  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.65/2.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.65/2.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.65/2.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.65/2.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.65/2.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.65/2.38  
% 6.65/2.41  tff(f_183, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 6.65/2.41  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.65/2.41  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.65/2.41  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.65/2.41  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.65/2.41  tff(f_146, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.65/2.41  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((?[B]: ((v1_relat_1(B) & v1_funct_1(B)) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A))))) => v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_funct_1)).
% 6.65/2.41  tff(f_98, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 6.65/2.41  tff(f_84, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 6.65/2.41  tff(f_144, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.65/2.41  tff(f_108, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 6.65/2.41  tff(f_106, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.65/2.41  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.65/2.41  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.65/2.41  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 6.65/2.41  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 6.65/2.41  tff(f_57, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 6.65/2.41  tff(f_59, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 6.65/2.41  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.65/2.41  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.65/2.41  tff(f_163, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 6.65/2.41  tff(f_134, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.65/2.41  tff(c_64, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.65/2.41  tff(c_141, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_64])).
% 6.65/2.41  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.65/2.41  tff(c_16, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.65/2.41  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.65/2.41  tff(c_214, plain, (![B_76, A_77]: (v1_relat_1(B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_77)) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.65/2.41  tff(c_226, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_68, c_214])).
% 6.65/2.41  tff(c_238, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_226])).
% 6.65/2.41  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.65/2.41  tff(c_223, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_74, c_214])).
% 6.65/2.41  tff(c_235, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_223])).
% 6.65/2.41  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.65/2.41  tff(c_76, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.65/2.41  tff(c_1214, plain, (![A_191, B_192, C_193]: (k1_relset_1(A_191, B_192, C_193)=k1_relat_1(C_193) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_191, B_192))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.65/2.41  tff(c_1231, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1214])).
% 6.65/2.41  tff(c_1376, plain, (![B_216, A_217, C_218]: (k1_xboole_0=B_216 | k1_relset_1(A_217, B_216, C_218)=A_217 | ~v1_funct_2(C_218, A_217, B_216) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_217, B_216))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.65/2.41  tff(c_1382, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_1376])).
% 6.65/2.41  tff(c_1396, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1231, c_1382])).
% 6.65/2.41  tff(c_1401, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1396])).
% 6.65/2.41  tff(c_60, plain, (![A_54]: (k6_relat_1(A_54)=k6_partfun1(A_54))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.65/2.41  tff(c_22, plain, (![A_14, B_16]: (v2_funct_1(A_14) | k6_relat_1(k1_relat_1(A_14))!=k5_relat_1(A_14, B_16) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.65/2.41  tff(c_1519, plain, (![A_231, B_232]: (v2_funct_1(A_231) | k6_partfun1(k1_relat_1(A_231))!=k5_relat_1(A_231, B_232) | ~v1_funct_1(B_232) | ~v1_relat_1(B_232) | ~v1_funct_1(A_231) | ~v1_relat_1(A_231))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_22])).
% 6.65/2.41  tff(c_1523, plain, (![B_232]: (v2_funct_1('#skF_3') | k5_relat_1('#skF_3', B_232)!=k6_partfun1('#skF_1') | ~v1_funct_1(B_232) | ~v1_relat_1(B_232) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1401, c_1519])).
% 6.65/2.41  tff(c_1527, plain, (![B_232]: (v2_funct_1('#skF_3') | k5_relat_1('#skF_3', B_232)!=k6_partfun1('#skF_1') | ~v1_funct_1(B_232) | ~v1_relat_1(B_232))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_78, c_1523])).
% 6.65/2.41  tff(c_1529, plain, (![B_233]: (k5_relat_1('#skF_3', B_233)!=k6_partfun1('#skF_1') | ~v1_funct_1(B_233) | ~v1_relat_1(B_233))), inference(negUnitSimplification, [status(thm)], [c_141, c_1527])).
% 6.65/2.41  tff(c_1535, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_238, c_1529])).
% 6.65/2.41  tff(c_1548, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1535])).
% 6.65/2.41  tff(c_1587, plain, (![B_237, A_240, F_238, C_239, E_236, D_241]: (k4_relset_1(A_240, B_237, C_239, D_241, E_236, F_238)=k5_relat_1(E_236, F_238) | ~m1_subset_1(F_238, k1_zfmisc_1(k2_zfmisc_1(C_239, D_241))) | ~m1_subset_1(E_236, k1_zfmisc_1(k2_zfmisc_1(A_240, B_237))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.65/2.41  tff(c_1606, plain, (![A_243, B_244, E_245]: (k4_relset_1(A_243, B_244, '#skF_2', '#skF_1', E_245, '#skF_4')=k5_relat_1(E_245, '#skF_4') | ~m1_subset_1(E_245, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))))), inference(resolution, [status(thm)], [c_68, c_1587])).
% 6.65/2.41  tff(c_1623, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_1606])).
% 6.65/2.41  tff(c_1651, plain, (![B_251, A_254, E_253, C_250, F_255, D_252]: (m1_subset_1(k4_relset_1(A_254, B_251, C_250, D_252, E_253, F_255), k1_zfmisc_1(k2_zfmisc_1(A_254, D_252))) | ~m1_subset_1(F_255, k1_zfmisc_1(k2_zfmisc_1(C_250, D_252))) | ~m1_subset_1(E_253, k1_zfmisc_1(k2_zfmisc_1(A_254, B_251))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.65/2.41  tff(c_1688, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1623, c_1651])).
% 6.65/2.41  tff(c_1711, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_68, c_1688])).
% 6.65/2.41  tff(c_1861, plain, (![B_261, C_263, D_260, E_264, A_262, F_259]: (k1_partfun1(A_262, B_261, C_263, D_260, E_264, F_259)=k5_relat_1(E_264, F_259) | ~m1_subset_1(F_259, k1_zfmisc_1(k2_zfmisc_1(C_263, D_260))) | ~v1_funct_1(F_259) | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(A_262, B_261))) | ~v1_funct_1(E_264))), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.65/2.41  tff(c_1873, plain, (![A_262, B_261, E_264]: (k1_partfun1(A_262, B_261, '#skF_2', '#skF_1', E_264, '#skF_4')=k5_relat_1(E_264, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(A_262, B_261))) | ~v1_funct_1(E_264))), inference(resolution, [status(thm)], [c_68, c_1861])).
% 6.65/2.41  tff(c_2256, plain, (![A_274, B_275, E_276]: (k1_partfun1(A_274, B_275, '#skF_2', '#skF_1', E_276, '#skF_4')=k5_relat_1(E_276, '#skF_4') | ~m1_subset_1(E_276, k1_zfmisc_1(k2_zfmisc_1(A_274, B_275))) | ~v1_funct_1(E_276))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1873])).
% 6.65/2.41  tff(c_2280, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_2256])).
% 6.65/2.41  tff(c_2299, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2280])).
% 6.65/2.41  tff(c_40, plain, (![A_42]: (m1_subset_1(k6_relat_1(A_42), k1_zfmisc_1(k2_zfmisc_1(A_42, A_42))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.65/2.41  tff(c_79, plain, (![A_42]: (m1_subset_1(k6_partfun1(A_42), k1_zfmisc_1(k2_zfmisc_1(A_42, A_42))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_40])).
% 6.65/2.41  tff(c_66, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.65/2.41  tff(c_1435, plain, (![D_222, C_223, A_224, B_225]: (D_222=C_223 | ~r2_relset_1(A_224, B_225, C_223, D_222) | ~m1_subset_1(D_222, k1_zfmisc_1(k2_zfmisc_1(A_224, B_225))) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_224, B_225))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.65/2.41  tff(c_1447, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_1435])).
% 6.65/2.41  tff(c_1470, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_1447])).
% 6.65/2.41  tff(c_1554, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1470])).
% 6.65/2.41  tff(c_2310, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2299, c_1554])).
% 6.65/2.41  tff(c_2314, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1711, c_2310])).
% 6.65/2.41  tff(c_2315, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1470])).
% 6.65/2.41  tff(c_2629, plain, (![E_308, C_307, D_304, B_305, A_306, F_303]: (k1_partfun1(A_306, B_305, C_307, D_304, E_308, F_303)=k5_relat_1(E_308, F_303) | ~m1_subset_1(F_303, k1_zfmisc_1(k2_zfmisc_1(C_307, D_304))) | ~v1_funct_1(F_303) | ~m1_subset_1(E_308, k1_zfmisc_1(k2_zfmisc_1(A_306, B_305))) | ~v1_funct_1(E_308))), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.65/2.41  tff(c_2641, plain, (![A_306, B_305, E_308]: (k1_partfun1(A_306, B_305, '#skF_2', '#skF_1', E_308, '#skF_4')=k5_relat_1(E_308, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_308, k1_zfmisc_1(k2_zfmisc_1(A_306, B_305))) | ~v1_funct_1(E_308))), inference(resolution, [status(thm)], [c_68, c_2629])).
% 6.65/2.41  tff(c_3051, plain, (![A_319, B_320, E_321]: (k1_partfun1(A_319, B_320, '#skF_2', '#skF_1', E_321, '#skF_4')=k5_relat_1(E_321, '#skF_4') | ~m1_subset_1(E_321, k1_zfmisc_1(k2_zfmisc_1(A_319, B_320))) | ~v1_funct_1(E_321))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2641])).
% 6.65/2.41  tff(c_3075, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_3051])).
% 6.65/2.41  tff(c_3094, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2315, c_3075])).
% 6.65/2.41  tff(c_3096, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1548, c_3094])).
% 6.65/2.41  tff(c_3097, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1396])).
% 6.65/2.41  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.65/2.41  tff(c_3129, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3097, c_2])).
% 6.65/2.41  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.65/2.41  tff(c_3123, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3097, c_3097, c_8])).
% 6.65/2.41  tff(c_180, plain, (![B_73, A_74]: (v1_xboole_0(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)) | ~v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.65/2.41  tff(c_197, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_74, c_180])).
% 6.65/2.41  tff(c_199, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_197])).
% 6.65/2.41  tff(c_3224, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3123, c_199])).
% 6.65/2.41  tff(c_3228, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3129, c_3224])).
% 6.65/2.41  tff(c_3229, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_197])).
% 6.65/2.41  tff(c_142, plain, (![B_67, A_68]: (~v1_xboole_0(B_67) | B_67=A_68 | ~v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.65/2.41  tff(c_145, plain, (![A_68]: (k1_xboole_0=A_68 | ~v1_xboole_0(A_68))), inference(resolution, [status(thm)], [c_2, c_142])).
% 6.65/2.41  tff(c_3236, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3229, c_145])).
% 6.65/2.41  tff(c_101, plain, (![A_65]: (k6_relat_1(A_65)=k6_partfun1(A_65))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.65/2.41  tff(c_18, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.65/2.41  tff(c_107, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_101, c_18])).
% 6.65/2.41  tff(c_20, plain, (![A_13]: (v2_funct_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.65/2.41  tff(c_81, plain, (![A_13]: (v2_funct_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_20])).
% 6.65/2.41  tff(c_118, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_107, c_81])).
% 6.65/2.41  tff(c_3267, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3236, c_118])).
% 6.65/2.41  tff(c_3274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_141, c_3267])).
% 6.65/2.41  tff(c_3275, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 6.65/2.41  tff(c_3315, plain, (![B_334, A_335]: (v1_relat_1(B_334) | ~m1_subset_1(B_334, k1_zfmisc_1(A_335)) | ~v1_relat_1(A_335))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.65/2.41  tff(c_3327, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_68, c_3315])).
% 6.65/2.41  tff(c_3339, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_3327])).
% 6.65/2.41  tff(c_3401, plain, (![C_344, B_345, A_346]: (v5_relat_1(C_344, B_345) | ~m1_subset_1(C_344, k1_zfmisc_1(k2_zfmisc_1(A_346, B_345))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.65/2.41  tff(c_3419, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_3401])).
% 6.65/2.41  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.65/2.41  tff(c_3565, plain, (![A_373, B_374, C_375]: (k2_relset_1(A_373, B_374, C_375)=k2_relat_1(C_375) | ~m1_subset_1(C_375, k1_zfmisc_1(k2_zfmisc_1(A_373, B_374))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.65/2.41  tff(c_3583, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_3565])).
% 6.65/2.41  tff(c_4227, plain, (![A_438, B_439, C_440, D_441]: (k2_relset_1(A_438, B_439, C_440)=B_439 | ~r2_relset_1(B_439, B_439, k1_partfun1(B_439, A_438, A_438, B_439, D_441, C_440), k6_partfun1(B_439)) | ~m1_subset_1(D_441, k1_zfmisc_1(k2_zfmisc_1(B_439, A_438))) | ~v1_funct_2(D_441, B_439, A_438) | ~v1_funct_1(D_441) | ~m1_subset_1(C_440, k1_zfmisc_1(k2_zfmisc_1(A_438, B_439))) | ~v1_funct_2(C_440, A_438, B_439) | ~v1_funct_1(C_440))), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.65/2.41  tff(c_4230, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_4227])).
% 6.65/2.41  tff(c_4236, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_78, c_76, c_74, c_3583, c_4230])).
% 6.65/2.41  tff(c_54, plain, (![B_47]: (v2_funct_2(B_47, k2_relat_1(B_47)) | ~v5_relat_1(B_47, k2_relat_1(B_47)) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.65/2.41  tff(c_4242, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4236, c_54])).
% 6.65/2.41  tff(c_4246, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3339, c_3419, c_4236, c_4242])).
% 6.65/2.41  tff(c_4248, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3275, c_4246])).
% 6.65/2.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.65/2.41  
% 6.65/2.41  Inference rules
% 6.65/2.41  ----------------------
% 6.65/2.41  #Ref     : 0
% 6.65/2.41  #Sup     : 990
% 6.65/2.41  #Fact    : 0
% 6.65/2.41  #Define  : 0
% 6.65/2.41  #Split   : 37
% 6.65/2.41  #Chain   : 0
% 6.65/2.41  #Close   : 0
% 6.65/2.41  
% 6.65/2.41  Ordering : KBO
% 6.65/2.41  
% 6.65/2.41  Simplification rules
% 6.65/2.41  ----------------------
% 6.65/2.41  #Subsume      : 50
% 6.65/2.41  #Demod        : 556
% 6.65/2.41  #Tautology    : 306
% 6.65/2.41  #SimpNegUnit  : 12
% 6.65/2.41  #BackRed      : 65
% 6.65/2.41  
% 6.65/2.41  #Partial instantiations: 0
% 6.65/2.41  #Strategies tried      : 1
% 6.65/2.41  
% 6.65/2.41  Timing (in seconds)
% 6.65/2.41  ----------------------
% 6.65/2.42  Preprocessing        : 0.39
% 6.65/2.42  Parsing              : 0.20
% 6.65/2.42  CNF conversion       : 0.03
% 6.65/2.42  Main loop            : 1.23
% 6.65/2.42  Inferencing          : 0.41
% 6.65/2.42  Reduction            : 0.44
% 6.65/2.42  Demodulation         : 0.31
% 6.65/2.42  BG Simplification    : 0.05
% 6.65/2.42  Subsumption          : 0.20
% 6.65/2.42  Abstraction          : 0.06
% 6.65/2.42  MUC search           : 0.00
% 6.65/2.42  Cooper               : 0.00
% 6.65/2.42  Total                : 1.67
% 6.65/2.42  Index Insertion      : 0.00
% 6.65/2.42  Index Deletion       : 0.00
% 6.65/2.42  Index Matching       : 0.00
% 6.65/2.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
