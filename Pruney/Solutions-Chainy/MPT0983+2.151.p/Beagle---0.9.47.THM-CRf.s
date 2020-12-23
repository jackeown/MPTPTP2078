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
% DateTime   : Thu Dec  3 10:12:23 EST 2020

% Result     : Theorem 6.87s
% Output     : CNFRefutation 7.44s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 533 expanded)
%              Number of leaves         :   49 ( 207 expanded)
%              Depth                    :   17
%              Number of atoms          :  310 (1856 expanded)
%              Number of equality atoms :   58 ( 169 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_178,negated_conjecture,(
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

tff(f_134,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_124,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_104,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_158,axiom,(
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

tff(f_84,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_57,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_60,plain,(
    ! [A_44] : k6_relat_1(A_44) = k6_partfun1(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_38,plain,(
    ! [A_21] : v2_funct_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_82,plain,(
    ! [A_21] : v2_funct_1(k6_partfun1(A_21)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_38])).

tff(c_80,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_76,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_2674,plain,(
    ! [F_247,B_245,A_244,D_249,C_248,E_246] :
      ( k1_partfun1(A_244,B_245,C_248,D_249,E_246,F_247) = k5_relat_1(E_246,F_247)
      | ~ m1_subset_1(F_247,k1_zfmisc_1(k2_zfmisc_1(C_248,D_249)))
      | ~ v1_funct_1(F_247)
      | ~ m1_subset_1(E_246,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245)))
      | ~ v1_funct_1(E_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2684,plain,(
    ! [A_244,B_245,E_246] :
      ( k1_partfun1(A_244,B_245,'#skF_2','#skF_1',E_246,'#skF_4') = k5_relat_1(E_246,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_246,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245)))
      | ~ v1_funct_1(E_246) ) ),
    inference(resolution,[status(thm)],[c_70,c_2674])).

tff(c_2799,plain,(
    ! [A_256,B_257,E_258] :
      ( k1_partfun1(A_256,B_257,'#skF_2','#skF_1',E_258,'#skF_4') = k5_relat_1(E_258,'#skF_4')
      | ~ m1_subset_1(E_258,k1_zfmisc_1(k2_zfmisc_1(A_256,B_257)))
      | ~ v1_funct_1(E_258) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2684])).

tff(c_2811,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_2799])).

tff(c_2824,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2811])).

tff(c_2844,plain,(
    ! [A_263,D_264,F_261,E_259,B_260,C_262] :
      ( m1_subset_1(k1_partfun1(A_263,B_260,C_262,D_264,E_259,F_261),k1_zfmisc_1(k2_zfmisc_1(A_263,D_264)))
      | ~ m1_subset_1(F_261,k1_zfmisc_1(k2_zfmisc_1(C_262,D_264)))
      | ~ v1_funct_1(F_261)
      | ~ m1_subset_1(E_259,k1_zfmisc_1(k2_zfmisc_1(A_263,B_260)))
      | ~ v1_funct_1(E_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2874,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2824,c_2844])).

tff(c_2889,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_2874])).

tff(c_48,plain,(
    ! [A_29] : m1_subset_1(k6_relat_1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_81,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_48])).

tff(c_68,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_974,plain,(
    ! [D_141,C_142,A_143,B_144] :
      ( D_141 = C_142
      | ~ r2_relset_1(A_143,B_144,C_142,D_141)
      | ~ m1_subset_1(D_141,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144)))
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_984,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_974])).

tff(c_1003,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_984])).

tff(c_3139,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2889,c_2824,c_2824,c_1003])).

tff(c_66,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_153,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_78,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_3121,plain,(
    ! [E_274,D_275,A_273,B_272,C_276] :
      ( k1_xboole_0 = C_276
      | v2_funct_1(D_275)
      | ~ v2_funct_1(k1_partfun1(A_273,B_272,B_272,C_276,D_275,E_274))
      | ~ m1_subset_1(E_274,k1_zfmisc_1(k2_zfmisc_1(B_272,C_276)))
      | ~ v1_funct_2(E_274,B_272,C_276)
      | ~ v1_funct_1(E_274)
      | ~ m1_subset_1(D_275,k1_zfmisc_1(k2_zfmisc_1(A_273,B_272)))
      | ~ v1_funct_2(D_275,A_273,B_272)
      | ~ v1_funct_1(D_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3125,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2824,c_3121])).

tff(c_3129,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_3125])).

tff(c_3130,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_3129])).

tff(c_3137,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3130])).

tff(c_3140,plain,(
    ~ v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3139,c_3137])).

tff(c_3151,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3140])).

tff(c_3152,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3130])).

tff(c_101,plain,(
    ! [A_58] : k6_relat_1(A_58) = k6_partfun1(A_58) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_34,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_107,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_34])).

tff(c_120,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_82])).

tff(c_3196,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3152,c_120])).

tff(c_22,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_243,plain,(
    ! [B_68,A_69] :
      ( v1_relat_1(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69))
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_252,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_243])).

tff(c_264,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_252])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_3201,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3152,c_2])).

tff(c_418,plain,(
    ! [C_89,A_90,B_91] :
      ( v4_relat_1(C_89,A_90)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_433,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_418])).

tff(c_255,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_243])).

tff(c_267,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_255])).

tff(c_30,plain,(
    ! [A_20] : k1_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_85,plain,(
    ! [A_20] : k1_relat_1(k6_partfun1(A_20)) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_30])).

tff(c_3223,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2889,c_2824,c_2824,c_1003])).

tff(c_26,plain,(
    ! [A_14,B_16] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_14,B_16)),k1_relat_1(A_14))
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3244,plain,
    ( r1_tarski(k1_relat_1(k6_partfun1('#skF_1')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3223,c_26])).

tff(c_3253,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_267,c_85,c_3244])).

tff(c_303,plain,(
    ! [B_74,A_75] :
      ( r1_tarski(k1_relat_1(B_74),A_75)
      | ~ v4_relat_1(B_74,A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_312,plain,(
    ! [B_74,A_75] :
      ( k1_relat_1(B_74) = A_75
      | ~ r1_tarski(A_75,k1_relat_1(B_74))
      | ~ v4_relat_1(B_74,A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(resolution,[status(thm)],[c_303,c_6])).

tff(c_3489,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3253,c_312])).

tff(c_3494,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_433,c_3489])).

tff(c_24,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0(k1_relat_1(A_13))
      | ~ v1_relat_1(A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3522,plain,
    ( ~ v1_xboole_0('#skF_1')
    | ~ v1_relat_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3494,c_24])).

tff(c_3540,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_3201,c_3522])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_3199,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3152,c_4])).

tff(c_3545,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3540,c_3199])).

tff(c_3576,plain,(
    ~ v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3545,c_153])).

tff(c_3585,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3196,c_3576])).

tff(c_3586,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_3677,plain,(
    ! [B_291,A_292] :
      ( v1_relat_1(B_291)
      | ~ m1_subset_1(B_291,k1_zfmisc_1(A_292))
      | ~ v1_relat_1(A_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3686,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_3677])).

tff(c_3698,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_3686])).

tff(c_3822,plain,(
    ! [C_308,B_309,A_310] :
      ( v5_relat_1(C_308,B_309)
      | ~ m1_subset_1(C_308,k1_zfmisc_1(k2_zfmisc_1(A_310,B_309))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3839,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_3822])).

tff(c_3689,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_3677])).

tff(c_3701,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_3689])).

tff(c_32,plain,(
    ! [A_20] : k2_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_84,plain,(
    ! [A_20] : k2_relat_1(k6_partfun1(A_20)) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_32])).

tff(c_4447,plain,(
    ! [B_374,E_375,F_376,A_373,C_377,D_378] :
      ( k1_partfun1(A_373,B_374,C_377,D_378,E_375,F_376) = k5_relat_1(E_375,F_376)
      | ~ m1_subset_1(F_376,k1_zfmisc_1(k2_zfmisc_1(C_377,D_378)))
      | ~ v1_funct_1(F_376)
      | ~ m1_subset_1(E_375,k1_zfmisc_1(k2_zfmisc_1(A_373,B_374)))
      | ~ v1_funct_1(E_375) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_4453,plain,(
    ! [A_373,B_374,E_375] :
      ( k1_partfun1(A_373,B_374,'#skF_2','#skF_1',E_375,'#skF_4') = k5_relat_1(E_375,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_375,k1_zfmisc_1(k2_zfmisc_1(A_373,B_374)))
      | ~ v1_funct_1(E_375) ) ),
    inference(resolution,[status(thm)],[c_70,c_4447])).

tff(c_4799,plain,(
    ! [A_405,B_406,E_407] :
      ( k1_partfun1(A_405,B_406,'#skF_2','#skF_1',E_407,'#skF_4') = k5_relat_1(E_407,'#skF_4')
      | ~ m1_subset_1(E_407,k1_zfmisc_1(k2_zfmisc_1(A_405,B_406)))
      | ~ v1_funct_1(E_407) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4453])).

tff(c_4820,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_4799])).

tff(c_4833,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4820])).

tff(c_54,plain,(
    ! [B_33,C_34,E_36,F_37,A_32,D_35] :
      ( m1_subset_1(k1_partfun1(A_32,B_33,C_34,D_35,E_36,F_37),k1_zfmisc_1(k2_zfmisc_1(A_32,D_35)))
      | ~ m1_subset_1(F_37,k1_zfmisc_1(k2_zfmisc_1(C_34,D_35)))
      | ~ v1_funct_1(F_37)
      | ~ m1_subset_1(E_36,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_1(E_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_5082,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4833,c_54])).

tff(c_5088,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_5082])).

tff(c_4203,plain,(
    ! [D_345,C_346,A_347,B_348] :
      ( D_345 = C_346
      | ~ r2_relset_1(A_347,B_348,C_346,D_345)
      | ~ m1_subset_1(D_345,k1_zfmisc_1(k2_zfmisc_1(A_347,B_348)))
      | ~ m1_subset_1(C_346,k1_zfmisc_1(k2_zfmisc_1(A_347,B_348))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4213,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_4203])).

tff(c_4232,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_4213])).

tff(c_4280,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_4232])).

tff(c_5256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5088,c_4833,c_4280])).

tff(c_5257,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_4232])).

tff(c_5488,plain,(
    ! [F_446,A_443,C_447,D_448,B_444,E_445] :
      ( k1_partfun1(A_443,B_444,C_447,D_448,E_445,F_446) = k5_relat_1(E_445,F_446)
      | ~ m1_subset_1(F_446,k1_zfmisc_1(k2_zfmisc_1(C_447,D_448)))
      | ~ v1_funct_1(F_446)
      | ~ m1_subset_1(E_445,k1_zfmisc_1(k2_zfmisc_1(A_443,B_444)))
      | ~ v1_funct_1(E_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_5496,plain,(
    ! [A_443,B_444,E_445] :
      ( k1_partfun1(A_443,B_444,'#skF_2','#skF_1',E_445,'#skF_4') = k5_relat_1(E_445,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_445,k1_zfmisc_1(k2_zfmisc_1(A_443,B_444)))
      | ~ v1_funct_1(E_445) ) ),
    inference(resolution,[status(thm)],[c_70,c_5488])).

tff(c_6090,plain,(
    ! [A_493,B_494,E_495] :
      ( k1_partfun1(A_493,B_494,'#skF_2','#skF_1',E_495,'#skF_4') = k5_relat_1(E_495,'#skF_4')
      | ~ m1_subset_1(E_495,k1_zfmisc_1(k2_zfmisc_1(A_493,B_494)))
      | ~ v1_funct_1(E_495) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_5496])).

tff(c_6114,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_6090])).

tff(c_6130,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_5257,c_6114])).

tff(c_28,plain,(
    ! [A_17,B_19] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_17,B_19)),k2_relat_1(B_19))
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6137,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6130,c_28])).

tff(c_6146,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3701,c_3698,c_84,c_6137])).

tff(c_3763,plain,(
    ! [B_302,A_303] :
      ( r1_tarski(k2_relat_1(B_302),A_303)
      | ~ v5_relat_1(B_302,A_303)
      | ~ v1_relat_1(B_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3776,plain,(
    ! [B_302,A_303] :
      ( k2_relat_1(B_302) = A_303
      | ~ r1_tarski(A_303,k2_relat_1(B_302))
      | ~ v5_relat_1(B_302,A_303)
      | ~ v1_relat_1(B_302) ) ),
    inference(resolution,[status(thm)],[c_3763,c_6])).

tff(c_6152,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6146,c_3776])).

tff(c_6157,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3698,c_3839,c_6152])).

tff(c_10,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3702,plain,(
    ! [B_293,A_294] :
      ( v5_relat_1(B_293,A_294)
      | ~ r1_tarski(k2_relat_1(B_293),A_294)
      | ~ v1_relat_1(B_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3717,plain,(
    ! [B_293] :
      ( v5_relat_1(B_293,k2_relat_1(B_293))
      | ~ v1_relat_1(B_293) ) ),
    inference(resolution,[status(thm)],[c_10,c_3702])).

tff(c_3913,plain,(
    ! [B_320] :
      ( v2_funct_2(B_320,k2_relat_1(B_320))
      | ~ v5_relat_1(B_320,k2_relat_1(B_320))
      | ~ v1_relat_1(B_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3937,plain,(
    ! [B_293] :
      ( v2_funct_2(B_293,k2_relat_1(B_293))
      | ~ v1_relat_1(B_293) ) ),
    inference(resolution,[status(thm)],[c_3717,c_3913])).

tff(c_6170,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6157,c_3937])).

tff(c_6187,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3698,c_6170])).

tff(c_6189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3586,c_6187])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:27:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.87/2.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.49  
% 7.31/2.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.50  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.31/2.50  
% 7.31/2.50  %Foreground sorts:
% 7.31/2.50  
% 7.31/2.50  
% 7.31/2.50  %Background operators:
% 7.31/2.50  
% 7.31/2.50  
% 7.31/2.50  %Foreground operators:
% 7.31/2.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.31/2.50  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.31/2.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.31/2.50  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.31/2.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.31/2.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.31/2.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.31/2.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.31/2.50  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.31/2.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.31/2.50  tff('#skF_2', type, '#skF_2': $i).
% 7.31/2.50  tff('#skF_3', type, '#skF_3': $i).
% 7.31/2.50  tff('#skF_1', type, '#skF_1': $i).
% 7.31/2.50  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.31/2.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.31/2.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.31/2.50  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.31/2.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.31/2.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.31/2.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.31/2.50  tff('#skF_4', type, '#skF_4': $i).
% 7.31/2.50  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.31/2.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.31/2.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.31/2.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.31/2.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.31/2.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.31/2.50  
% 7.44/2.52  tff(f_136, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.44/2.52  tff(f_88, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.44/2.52  tff(f_178, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 7.44/2.52  tff(f_134, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.44/2.52  tff(f_124, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.44/2.52  tff(f_104, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 7.44/2.52  tff(f_102, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.44/2.52  tff(f_158, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 7.44/2.52  tff(f_84, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 7.44/2.52  tff(f_57, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.44/2.52  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.44/2.52  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.44/2.52  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.44/2.52  tff(f_83, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.44/2.52  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 7.44/2.52  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 7.44/2.52  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.44/2.52  tff(f_65, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 7.44/2.52  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 7.44/2.52  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 7.44/2.52  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 7.44/2.52  tff(f_112, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 7.44/2.52  tff(c_60, plain, (![A_44]: (k6_relat_1(A_44)=k6_partfun1(A_44))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.44/2.52  tff(c_38, plain, (![A_21]: (v2_funct_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.44/2.52  tff(c_82, plain, (![A_21]: (v2_funct_1(k6_partfun1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_38])).
% 7.44/2.52  tff(c_80, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.44/2.52  tff(c_76, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.44/2.52  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.44/2.52  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.44/2.52  tff(c_2674, plain, (![F_247, B_245, A_244, D_249, C_248, E_246]: (k1_partfun1(A_244, B_245, C_248, D_249, E_246, F_247)=k5_relat_1(E_246, F_247) | ~m1_subset_1(F_247, k1_zfmisc_1(k2_zfmisc_1(C_248, D_249))) | ~v1_funct_1(F_247) | ~m1_subset_1(E_246, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))) | ~v1_funct_1(E_246))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.44/2.52  tff(c_2684, plain, (![A_244, B_245, E_246]: (k1_partfun1(A_244, B_245, '#skF_2', '#skF_1', E_246, '#skF_4')=k5_relat_1(E_246, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_246, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))) | ~v1_funct_1(E_246))), inference(resolution, [status(thm)], [c_70, c_2674])).
% 7.44/2.52  tff(c_2799, plain, (![A_256, B_257, E_258]: (k1_partfun1(A_256, B_257, '#skF_2', '#skF_1', E_258, '#skF_4')=k5_relat_1(E_258, '#skF_4') | ~m1_subset_1(E_258, k1_zfmisc_1(k2_zfmisc_1(A_256, B_257))) | ~v1_funct_1(E_258))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2684])).
% 7.44/2.52  tff(c_2811, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_2799])).
% 7.44/2.52  tff(c_2824, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2811])).
% 7.44/2.52  tff(c_2844, plain, (![A_263, D_264, F_261, E_259, B_260, C_262]: (m1_subset_1(k1_partfun1(A_263, B_260, C_262, D_264, E_259, F_261), k1_zfmisc_1(k2_zfmisc_1(A_263, D_264))) | ~m1_subset_1(F_261, k1_zfmisc_1(k2_zfmisc_1(C_262, D_264))) | ~v1_funct_1(F_261) | ~m1_subset_1(E_259, k1_zfmisc_1(k2_zfmisc_1(A_263, B_260))) | ~v1_funct_1(E_259))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.44/2.52  tff(c_2874, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2824, c_2844])).
% 7.44/2.52  tff(c_2889, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_2874])).
% 7.44/2.52  tff(c_48, plain, (![A_29]: (m1_subset_1(k6_relat_1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.44/2.52  tff(c_81, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_48])).
% 7.44/2.52  tff(c_68, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.44/2.52  tff(c_974, plain, (![D_141, C_142, A_143, B_144]: (D_141=C_142 | ~r2_relset_1(A_143, B_144, C_142, D_141) | ~m1_subset_1(D_141, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.44/2.52  tff(c_984, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_974])).
% 7.44/2.52  tff(c_1003, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_984])).
% 7.44/2.52  tff(c_3139, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2889, c_2824, c_2824, c_1003])).
% 7.44/2.52  tff(c_66, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.44/2.52  tff(c_153, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_66])).
% 7.44/2.52  tff(c_78, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.44/2.52  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.44/2.52  tff(c_3121, plain, (![E_274, D_275, A_273, B_272, C_276]: (k1_xboole_0=C_276 | v2_funct_1(D_275) | ~v2_funct_1(k1_partfun1(A_273, B_272, B_272, C_276, D_275, E_274)) | ~m1_subset_1(E_274, k1_zfmisc_1(k2_zfmisc_1(B_272, C_276))) | ~v1_funct_2(E_274, B_272, C_276) | ~v1_funct_1(E_274) | ~m1_subset_1(D_275, k1_zfmisc_1(k2_zfmisc_1(A_273, B_272))) | ~v1_funct_2(D_275, A_273, B_272) | ~v1_funct_1(D_275))), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.44/2.52  tff(c_3125, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2824, c_3121])).
% 7.44/2.52  tff(c_3129, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_3125])).
% 7.44/2.52  tff(c_3130, plain, (k1_xboole_0='#skF_1' | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_153, c_3129])).
% 7.44/2.52  tff(c_3137, plain, (~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_3130])).
% 7.44/2.52  tff(c_3140, plain, (~v2_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3139, c_3137])).
% 7.44/2.52  tff(c_3151, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_3140])).
% 7.44/2.52  tff(c_3152, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_3130])).
% 7.44/2.52  tff(c_101, plain, (![A_58]: (k6_relat_1(A_58)=k6_partfun1(A_58))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.44/2.52  tff(c_34, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.44/2.52  tff(c_107, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_101, c_34])).
% 7.44/2.52  tff(c_120, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_107, c_82])).
% 7.44/2.52  tff(c_3196, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3152, c_120])).
% 7.44/2.52  tff(c_22, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.44/2.52  tff(c_243, plain, (![B_68, A_69]: (v1_relat_1(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.44/2.52  tff(c_252, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_76, c_243])).
% 7.44/2.52  tff(c_264, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_252])).
% 7.44/2.52  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.44/2.52  tff(c_3201, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3152, c_2])).
% 7.44/2.52  tff(c_418, plain, (![C_89, A_90, B_91]: (v4_relat_1(C_89, A_90) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.44/2.52  tff(c_433, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_76, c_418])).
% 7.44/2.52  tff(c_255, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_70, c_243])).
% 7.44/2.52  tff(c_267, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_255])).
% 7.44/2.52  tff(c_30, plain, (![A_20]: (k1_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.44/2.52  tff(c_85, plain, (![A_20]: (k1_relat_1(k6_partfun1(A_20))=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_30])).
% 7.44/2.52  tff(c_3223, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2889, c_2824, c_2824, c_1003])).
% 7.44/2.52  tff(c_26, plain, (![A_14, B_16]: (r1_tarski(k1_relat_1(k5_relat_1(A_14, B_16)), k1_relat_1(A_14)) | ~v1_relat_1(B_16) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.44/2.52  tff(c_3244, plain, (r1_tarski(k1_relat_1(k6_partfun1('#skF_1')), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3223, c_26])).
% 7.44/2.52  tff(c_3253, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_267, c_85, c_3244])).
% 7.44/2.52  tff(c_303, plain, (![B_74, A_75]: (r1_tarski(k1_relat_1(B_74), A_75) | ~v4_relat_1(B_74, A_75) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.44/2.52  tff(c_6, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.44/2.52  tff(c_312, plain, (![B_74, A_75]: (k1_relat_1(B_74)=A_75 | ~r1_tarski(A_75, k1_relat_1(B_74)) | ~v4_relat_1(B_74, A_75) | ~v1_relat_1(B_74))), inference(resolution, [status(thm)], [c_303, c_6])).
% 7.44/2.52  tff(c_3489, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3253, c_312])).
% 7.44/2.52  tff(c_3494, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_264, c_433, c_3489])).
% 7.44/2.52  tff(c_24, plain, (![A_13]: (~v1_xboole_0(k1_relat_1(A_13)) | ~v1_relat_1(A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.44/2.52  tff(c_3522, plain, (~v1_xboole_0('#skF_1') | ~v1_relat_1('#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3494, c_24])).
% 7.44/2.52  tff(c_3540, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_264, c_3201, c_3522])).
% 7.44/2.52  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 7.44/2.52  tff(c_3199, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_3152, c_4])).
% 7.44/2.52  tff(c_3545, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_3540, c_3199])).
% 7.44/2.52  tff(c_3576, plain, (~v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3545, c_153])).
% 7.44/2.52  tff(c_3585, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3196, c_3576])).
% 7.44/2.52  tff(c_3586, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_66])).
% 7.44/2.52  tff(c_3677, plain, (![B_291, A_292]: (v1_relat_1(B_291) | ~m1_subset_1(B_291, k1_zfmisc_1(A_292)) | ~v1_relat_1(A_292))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.44/2.52  tff(c_3686, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_70, c_3677])).
% 7.44/2.52  tff(c_3698, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_3686])).
% 7.44/2.52  tff(c_3822, plain, (![C_308, B_309, A_310]: (v5_relat_1(C_308, B_309) | ~m1_subset_1(C_308, k1_zfmisc_1(k2_zfmisc_1(A_310, B_309))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.44/2.52  tff(c_3839, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_3822])).
% 7.44/2.52  tff(c_3689, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_76, c_3677])).
% 7.44/2.52  tff(c_3701, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_3689])).
% 7.44/2.52  tff(c_32, plain, (![A_20]: (k2_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.44/2.52  tff(c_84, plain, (![A_20]: (k2_relat_1(k6_partfun1(A_20))=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_32])).
% 7.44/2.52  tff(c_4447, plain, (![B_374, E_375, F_376, A_373, C_377, D_378]: (k1_partfun1(A_373, B_374, C_377, D_378, E_375, F_376)=k5_relat_1(E_375, F_376) | ~m1_subset_1(F_376, k1_zfmisc_1(k2_zfmisc_1(C_377, D_378))) | ~v1_funct_1(F_376) | ~m1_subset_1(E_375, k1_zfmisc_1(k2_zfmisc_1(A_373, B_374))) | ~v1_funct_1(E_375))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.44/2.52  tff(c_4453, plain, (![A_373, B_374, E_375]: (k1_partfun1(A_373, B_374, '#skF_2', '#skF_1', E_375, '#skF_4')=k5_relat_1(E_375, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_375, k1_zfmisc_1(k2_zfmisc_1(A_373, B_374))) | ~v1_funct_1(E_375))), inference(resolution, [status(thm)], [c_70, c_4447])).
% 7.44/2.52  tff(c_4799, plain, (![A_405, B_406, E_407]: (k1_partfun1(A_405, B_406, '#skF_2', '#skF_1', E_407, '#skF_4')=k5_relat_1(E_407, '#skF_4') | ~m1_subset_1(E_407, k1_zfmisc_1(k2_zfmisc_1(A_405, B_406))) | ~v1_funct_1(E_407))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_4453])).
% 7.44/2.52  tff(c_4820, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_4799])).
% 7.44/2.52  tff(c_4833, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4820])).
% 7.44/2.52  tff(c_54, plain, (![B_33, C_34, E_36, F_37, A_32, D_35]: (m1_subset_1(k1_partfun1(A_32, B_33, C_34, D_35, E_36, F_37), k1_zfmisc_1(k2_zfmisc_1(A_32, D_35))) | ~m1_subset_1(F_37, k1_zfmisc_1(k2_zfmisc_1(C_34, D_35))) | ~v1_funct_1(F_37) | ~m1_subset_1(E_36, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_1(E_36))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.44/2.52  tff(c_5082, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4833, c_54])).
% 7.44/2.52  tff(c_5088, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_5082])).
% 7.44/2.52  tff(c_4203, plain, (![D_345, C_346, A_347, B_348]: (D_345=C_346 | ~r2_relset_1(A_347, B_348, C_346, D_345) | ~m1_subset_1(D_345, k1_zfmisc_1(k2_zfmisc_1(A_347, B_348))) | ~m1_subset_1(C_346, k1_zfmisc_1(k2_zfmisc_1(A_347, B_348))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.44/2.52  tff(c_4213, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_4203])).
% 7.44/2.52  tff(c_4232, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_4213])).
% 7.44/2.52  tff(c_4280, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_4232])).
% 7.44/2.52  tff(c_5256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5088, c_4833, c_4280])).
% 7.44/2.52  tff(c_5257, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_4232])).
% 7.44/2.52  tff(c_5488, plain, (![F_446, A_443, C_447, D_448, B_444, E_445]: (k1_partfun1(A_443, B_444, C_447, D_448, E_445, F_446)=k5_relat_1(E_445, F_446) | ~m1_subset_1(F_446, k1_zfmisc_1(k2_zfmisc_1(C_447, D_448))) | ~v1_funct_1(F_446) | ~m1_subset_1(E_445, k1_zfmisc_1(k2_zfmisc_1(A_443, B_444))) | ~v1_funct_1(E_445))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.44/2.52  tff(c_5496, plain, (![A_443, B_444, E_445]: (k1_partfun1(A_443, B_444, '#skF_2', '#skF_1', E_445, '#skF_4')=k5_relat_1(E_445, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_445, k1_zfmisc_1(k2_zfmisc_1(A_443, B_444))) | ~v1_funct_1(E_445))), inference(resolution, [status(thm)], [c_70, c_5488])).
% 7.44/2.52  tff(c_6090, plain, (![A_493, B_494, E_495]: (k1_partfun1(A_493, B_494, '#skF_2', '#skF_1', E_495, '#skF_4')=k5_relat_1(E_495, '#skF_4') | ~m1_subset_1(E_495, k1_zfmisc_1(k2_zfmisc_1(A_493, B_494))) | ~v1_funct_1(E_495))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_5496])).
% 7.44/2.52  tff(c_6114, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_6090])).
% 7.44/2.52  tff(c_6130, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_5257, c_6114])).
% 7.44/2.52  tff(c_28, plain, (![A_17, B_19]: (r1_tarski(k2_relat_1(k5_relat_1(A_17, B_19)), k2_relat_1(B_19)) | ~v1_relat_1(B_19) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.44/2.52  tff(c_6137, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6130, c_28])).
% 7.44/2.52  tff(c_6146, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3701, c_3698, c_84, c_6137])).
% 7.44/2.52  tff(c_3763, plain, (![B_302, A_303]: (r1_tarski(k2_relat_1(B_302), A_303) | ~v5_relat_1(B_302, A_303) | ~v1_relat_1(B_302))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.44/2.52  tff(c_3776, plain, (![B_302, A_303]: (k2_relat_1(B_302)=A_303 | ~r1_tarski(A_303, k2_relat_1(B_302)) | ~v5_relat_1(B_302, A_303) | ~v1_relat_1(B_302))), inference(resolution, [status(thm)], [c_3763, c_6])).
% 7.44/2.52  tff(c_6152, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6146, c_3776])).
% 7.44/2.52  tff(c_6157, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3698, c_3839, c_6152])).
% 7.44/2.52  tff(c_10, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.44/2.52  tff(c_3702, plain, (![B_293, A_294]: (v5_relat_1(B_293, A_294) | ~r1_tarski(k2_relat_1(B_293), A_294) | ~v1_relat_1(B_293))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.44/2.52  tff(c_3717, plain, (![B_293]: (v5_relat_1(B_293, k2_relat_1(B_293)) | ~v1_relat_1(B_293))), inference(resolution, [status(thm)], [c_10, c_3702])).
% 7.44/2.52  tff(c_3913, plain, (![B_320]: (v2_funct_2(B_320, k2_relat_1(B_320)) | ~v5_relat_1(B_320, k2_relat_1(B_320)) | ~v1_relat_1(B_320))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.44/2.52  tff(c_3937, plain, (![B_293]: (v2_funct_2(B_293, k2_relat_1(B_293)) | ~v1_relat_1(B_293))), inference(resolution, [status(thm)], [c_3717, c_3913])).
% 7.44/2.52  tff(c_6170, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6157, c_3937])).
% 7.44/2.52  tff(c_6187, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3698, c_6170])).
% 7.44/2.52  tff(c_6189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3586, c_6187])).
% 7.44/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.44/2.52  
% 7.44/2.52  Inference rules
% 7.44/2.52  ----------------------
% 7.44/2.52  #Ref     : 0
% 7.44/2.52  #Sup     : 1267
% 7.44/2.52  #Fact    : 0
% 7.44/2.52  #Define  : 0
% 7.44/2.52  #Split   : 18
% 7.44/2.52  #Chain   : 0
% 7.44/2.52  #Close   : 0
% 7.44/2.52  
% 7.44/2.52  Ordering : KBO
% 7.44/2.52  
% 7.44/2.52  Simplification rules
% 7.45/2.52  ----------------------
% 7.45/2.52  #Subsume      : 269
% 7.45/2.52  #Demod        : 1390
% 7.45/2.52  #Tautology    : 403
% 7.45/2.52  #SimpNegUnit  : 22
% 7.45/2.52  #BackRed      : 186
% 7.45/2.52  
% 7.45/2.52  #Partial instantiations: 0
% 7.45/2.52  #Strategies tried      : 1
% 7.45/2.52  
% 7.45/2.52  Timing (in seconds)
% 7.45/2.52  ----------------------
% 7.45/2.52  Preprocessing        : 0.35
% 7.45/2.53  Parsing              : 0.18
% 7.45/2.53  CNF conversion       : 0.02
% 7.45/2.53  Main loop            : 1.37
% 7.45/2.53  Inferencing          : 0.45
% 7.45/2.53  Reduction            : 0.50
% 7.45/2.53  Demodulation         : 0.36
% 7.45/2.53  BG Simplification    : 0.05
% 7.45/2.53  Subsumption          : 0.26
% 7.45/2.53  Abstraction          : 0.05
% 7.45/2.53  MUC search           : 0.00
% 7.45/2.53  Cooper               : 0.00
% 7.45/2.53  Total                : 1.78
% 7.45/2.53  Index Insertion      : 0.00
% 7.45/2.53  Index Deletion       : 0.00
% 7.45/2.53  Index Matching       : 0.00
% 7.45/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
