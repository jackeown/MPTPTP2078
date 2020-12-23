%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:42 EST 2020

% Result     : Theorem 9.58s
% Output     : CNFRefutation 9.84s
% Verified   : 
% Statistics : Number of formulae       :  178 (2555 expanded)
%              Number of leaves         :   39 ( 811 expanded)
%              Depth                    :   13
%              Number of atoms          :  293 (7935 expanded)
%              Number of equality atoms :   75 (3054 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_156,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_68,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_122,axiom,(
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

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_136,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v4_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v4_relat_1(k7_relat_1(C,A),A)
        & v4_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_130,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_66,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_26,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_148,plain,(
    ! [B_62,A_63] :
      ( v1_relat_1(B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63))
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_154,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_148])).

tff(c_158,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_154])).

tff(c_64,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_77,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_10954,plain,(
    ! [A_702,B_703,C_704] :
      ( k1_relset_1(A_702,B_703,C_704) = k1_relat_1(C_704)
      | ~ m1_subset_1(C_704,k1_zfmisc_1(k2_zfmisc_1(A_702,B_703))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_10973,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_10954])).

tff(c_12254,plain,(
    ! [B_798,A_799,C_800] :
      ( k1_xboole_0 = B_798
      | k1_relset_1(A_799,B_798,C_800) = A_799
      | ~ v1_funct_2(C_800,A_799,B_798)
      | ~ m1_subset_1(C_800,k1_zfmisc_1(k2_zfmisc_1(A_799,B_798))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_12267,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_12254])).

tff(c_12283,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_10973,c_12267])).

tff(c_12284,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_12283])).

tff(c_34,plain,(
    ! [B_26,A_25] :
      ( k1_relat_1(k7_relat_1(B_26,A_25)) = A_25
      | ~ r1_tarski(A_25,k1_relat_1(B_26))
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_12302,plain,(
    ! [A_25] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_25)) = A_25
      | ~ r1_tarski(A_25,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12284,c_34])).

tff(c_12346,plain,(
    ! [A_803] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_803)) = A_803
      | ~ r1_tarski(A_803,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_12302])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_11832,plain,(
    ! [A_766,B_767,C_768,D_769] :
      ( k2_partfun1(A_766,B_767,C_768,D_769) = k7_relat_1(C_768,D_769)
      | ~ m1_subset_1(C_768,k1_zfmisc_1(k2_zfmisc_1(A_766,B_767)))
      | ~ v1_funct_1(C_768) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_11839,plain,(
    ! [D_769] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_769) = k7_relat_1('#skF_4',D_769)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_11832])).

tff(c_11850,plain,(
    ! [D_769] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_769) = k7_relat_1('#skF_4',D_769) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_11839])).

tff(c_32,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k7_relat_1(B_24,A_23),B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_139,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(A_60,B_61)
      | ~ m1_subset_1(A_60,k1_zfmisc_1(B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_147,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_139])).

tff(c_2256,plain,(
    ! [A_225,C_226,B_227] :
      ( r1_tarski(A_225,C_226)
      | ~ r1_tarski(B_227,C_226)
      | ~ r1_tarski(A_225,B_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2527,plain,(
    ! [A_263] :
      ( r1_tarski(A_263,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_263,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_147,c_2256])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_155,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(A_7)
      | ~ v1_relat_1(B_8)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_148])).

tff(c_2538,plain,(
    ! [A_263] :
      ( v1_relat_1(A_263)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_263,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2527,c_155])).

tff(c_2545,plain,(
    ! [A_264] :
      ( v1_relat_1(A_264)
      | ~ r1_tarski(A_264,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2538])).

tff(c_2560,plain,(
    ! [A_23] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_23))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_2545])).

tff(c_2568,plain,(
    ! [A_23] : v1_relat_1(k7_relat_1('#skF_4',A_23)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_2560])).

tff(c_2305,plain,(
    ! [C_231,A_232,B_233] :
      ( v4_relat_1(C_231,A_232)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2320,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_2305])).

tff(c_2592,plain,(
    ! [C_271,A_272,B_273] :
      ( v4_relat_1(k7_relat_1(C_271,A_272),A_272)
      | ~ v4_relat_1(C_271,B_273)
      | ~ v1_relat_1(C_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2604,plain,(
    ! [A_272] :
      ( v4_relat_1(k7_relat_1('#skF_4',A_272),A_272)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2320,c_2592])).

tff(c_2615,plain,(
    ! [A_274] : v4_relat_1(k7_relat_1('#skF_4',A_274),A_274) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_2604])).

tff(c_28,plain,(
    ! [B_20,A_19] :
      ( k7_relat_1(B_20,A_19) = B_20
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2620,plain,(
    ! [A_274] :
      ( k7_relat_1(k7_relat_1('#skF_4',A_274),A_274) = k7_relat_1('#skF_4',A_274)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_274)) ) ),
    inference(resolution,[status(thm)],[c_2615,c_28])).

tff(c_2649,plain,(
    ! [A_278] : k7_relat_1(k7_relat_1('#skF_4',A_278),A_278) = k7_relat_1('#skF_4',A_278) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2568,c_2620])).

tff(c_2676,plain,(
    ! [A_278] :
      ( r1_tarski(k7_relat_1('#skF_4',A_278),k7_relat_1('#skF_4',A_278))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_278)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2649,c_32])).

tff(c_2699,plain,(
    ! [A_278] : r1_tarski(k7_relat_1('#skF_4',A_278),k7_relat_1('#skF_4',A_278)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2568,c_2676])).

tff(c_3619,plain,(
    ! [A_324,B_325,A_326] :
      ( r1_tarski(A_324,B_325)
      | ~ r1_tarski(A_324,k7_relat_1(B_325,A_326))
      | ~ v1_relat_1(B_325) ) ),
    inference(resolution,[status(thm)],[c_32,c_2256])).

tff(c_3633,plain,(
    ! [A_278] :
      ( r1_tarski(k7_relat_1('#skF_4',A_278),'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2699,c_3619])).

tff(c_3665,plain,(
    ! [A_278] : r1_tarski(k7_relat_1('#skF_4',A_278),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_3633])).

tff(c_30,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_22,A_21)),A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2673,plain,(
    ! [A_278] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_278)),A_278)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_278)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2649,c_30])).

tff(c_2697,plain,(
    ! [A_278] : r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_278)),A_278) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2568,c_2673])).

tff(c_2269,plain,(
    ! [A_225] :
      ( r1_tarski(A_225,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_225,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_147,c_2256])).

tff(c_4102,plain,(
    ! [D_364,B_365,C_366,A_367] :
      ( m1_subset_1(D_364,k1_zfmisc_1(k2_zfmisc_1(B_365,C_366)))
      | ~ r1_tarski(k1_relat_1(D_364),B_365)
      | ~ m1_subset_1(D_364,k1_zfmisc_1(k2_zfmisc_1(A_367,C_366))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_9515,plain,(
    ! [A_598,B_599,C_600,A_601] :
      ( m1_subset_1(A_598,k1_zfmisc_1(k2_zfmisc_1(B_599,C_600)))
      | ~ r1_tarski(k1_relat_1(A_598),B_599)
      | ~ r1_tarski(A_598,k2_zfmisc_1(A_601,C_600)) ) ),
    inference(resolution,[status(thm)],[c_14,c_4102])).

tff(c_9704,plain,(
    ! [A_608,B_609] :
      ( m1_subset_1(A_608,k1_zfmisc_1(k2_zfmisc_1(B_609,'#skF_2')))
      | ~ r1_tarski(k1_relat_1(A_608),B_609)
      | ~ r1_tarski(A_608,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2269,c_9515])).

tff(c_4243,plain,(
    ! [A_377,B_378,C_379,D_380] :
      ( k2_partfun1(A_377,B_378,C_379,D_380) = k7_relat_1(C_379,D_380)
      | ~ m1_subset_1(C_379,k1_zfmisc_1(k2_zfmisc_1(A_377,B_378)))
      | ~ v1_funct_1(C_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_4250,plain,(
    ! [D_380] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_380) = k7_relat_1('#skF_4',D_380)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_4243])).

tff(c_4261,plain,(
    ! [D_380] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_380) = k7_relat_1('#skF_4',D_380) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4250])).

tff(c_2135,plain,(
    ! [A_210,B_211,C_212,D_213] :
      ( v1_funct_1(k2_partfun1(A_210,B_211,C_212,D_213))
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(A_210,B_211)))
      | ~ v1_funct_1(C_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2140,plain,(
    ! [D_213] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_213))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_2135])).

tff(c_2148,plain,(
    ! [D_213] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_213)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2140])).

tff(c_62,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_159,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_2151,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2148,c_159])).

tff(c_2152,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2154,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2152])).

tff(c_4264,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4261,c_2154])).

tff(c_9717,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_9704,c_4264])).

tff(c_9754,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3665,c_2697,c_9717])).

tff(c_9755,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2152])).

tff(c_11860,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11850,c_9755])).

tff(c_9756,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_2152])).

tff(c_10971,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_9756,c_10954])).

tff(c_11853,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11850,c_11850,c_10971])).

tff(c_11859,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11850,c_9756])).

tff(c_12058,plain,(
    ! [B_785,C_786,A_787] :
      ( k1_xboole_0 = B_785
      | v1_funct_2(C_786,A_787,B_785)
      | k1_relset_1(A_787,B_785,C_786) != A_787
      | ~ m1_subset_1(C_786,k1_zfmisc_1(k2_zfmisc_1(A_787,B_785))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_12064,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_11859,c_12058])).

tff(c_12082,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11853,c_12064])).

tff(c_12083,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_11860,c_77,c_12082])).

tff(c_12356,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12346,c_12083])).

tff(c_12476,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_12356])).

tff(c_12477,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_8,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12490,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12477,c_12477,c_8])).

tff(c_12478,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_12483,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12477,c_12478])).

tff(c_12519,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12490,c_12483,c_68])).

tff(c_12563,plain,(
    ! [A_816,B_817] :
      ( r1_tarski(A_816,B_817)
      | ~ m1_subset_1(A_816,k1_zfmisc_1(B_817)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12571,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_12519,c_12563])).

tff(c_4,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12520,plain,(
    ! [A_4] :
      ( A_4 = '#skF_1'
      | ~ r1_tarski(A_4,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12477,c_12477,c_4])).

tff(c_13532,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_12571,c_12520])).

tff(c_12484,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12483,c_70])).

tff(c_13539,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13532,c_13532,c_12484])).

tff(c_12491,plain,(
    ! [A_806] : k2_zfmisc_1(A_806,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12477,c_12477,c_8])).

tff(c_12495,plain,(
    v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12491,c_26])).

tff(c_13542,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13532,c_12495])).

tff(c_12538,plain,(
    ! [B_813,A_814] :
      ( r1_tarski(k7_relat_1(B_813,A_814),B_813)
      | ~ v1_relat_1(B_813) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_12542,plain,(
    ! [A_814] :
      ( k7_relat_1('#skF_1',A_814) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_12538,c_12520])).

tff(c_12545,plain,(
    ! [A_814] : k7_relat_1('#skF_1',A_814) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12495,c_12542])).

tff(c_13535,plain,(
    ! [A_814] : k7_relat_1('#skF_4',A_814) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13532,c_13532,c_12545])).

tff(c_13637,plain,(
    ! [B_952,A_953] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_952,A_953)),A_953)
      | ~ v1_relat_1(B_952) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_13644,plain,(
    ! [A_814] :
      ( r1_tarski(k1_relat_1('#skF_4'),A_814)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13535,c_13637])).

tff(c_13648,plain,(
    ! [A_954] : r1_tarski(k1_relat_1('#skF_4'),A_954) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13542,c_13644])).

tff(c_13538,plain,(
    ! [A_4] :
      ( A_4 = '#skF_4'
      | ~ r1_tarski(A_4,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13532,c_13532,c_12520])).

tff(c_13653,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_13648,c_13538])).

tff(c_13647,plain,(
    ! [A_814] : r1_tarski(k1_relat_1('#skF_4'),A_814) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13542,c_13644])).

tff(c_13654,plain,(
    ! [A_814] : r1_tarski('#skF_4',A_814) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13653,c_13647])).

tff(c_13540,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13532,c_12519])).

tff(c_10,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12500,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12477,c_12477,c_10])).

tff(c_13541,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_4',B_6) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13532,c_13532,c_12500])).

tff(c_14912,plain,(
    ! [A_1121,B_1122,C_1123,D_1124] :
      ( k2_partfun1(A_1121,B_1122,C_1123,D_1124) = k7_relat_1(C_1123,D_1124)
      | ~ m1_subset_1(C_1123,k1_zfmisc_1(k2_zfmisc_1(A_1121,B_1122)))
      | ~ v1_funct_1(C_1123) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_15110,plain,(
    ! [B_1145,C_1146,D_1147] :
      ( k2_partfun1('#skF_4',B_1145,C_1146,D_1147) = k7_relat_1(C_1146,D_1147)
      | ~ m1_subset_1(C_1146,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_1146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13541,c_14912])).

tff(c_15112,plain,(
    ! [B_1145,D_1147] :
      ( k2_partfun1('#skF_4',B_1145,'#skF_4',D_1147) = k7_relat_1('#skF_4',D_1147)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_13540,c_15110])).

tff(c_15118,plain,(
    ! [B_1145,D_1147] : k2_partfun1('#skF_4',B_1145,'#skF_4',D_1147) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_13535,c_15112])).

tff(c_12577,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_12571,c_12520])).

tff(c_12584,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12577,c_12519])).

tff(c_12585,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_4',B_6) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12577,c_12577,c_12500])).

tff(c_13179,plain,(
    ! [A_902,B_903,C_904,D_905] :
      ( v1_funct_1(k2_partfun1(A_902,B_903,C_904,D_905))
      | ~ m1_subset_1(C_904,k1_zfmisc_1(k2_zfmisc_1(A_902,B_903)))
      | ~ v1_funct_1(C_904) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_13514,plain,(
    ! [B_943,C_944,D_945] :
      ( v1_funct_1(k2_partfun1('#skF_4',B_943,C_944,D_945))
      | ~ m1_subset_1(C_944,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_944) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12585,c_13179])).

tff(c_13516,plain,(
    ! [B_943,D_945] :
      ( v1_funct_1(k2_partfun1('#skF_4',B_943,'#skF_4',D_945))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12584,c_13514])).

tff(c_13522,plain,(
    ! [B_943,D_945] : v1_funct_1(k2_partfun1('#skF_4',B_943,'#skF_4',D_945)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_13516])).

tff(c_12521,plain,(
    ! [A_808] :
      ( A_808 = '#skF_1'
      | ~ r1_tarski(A_808,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12477,c_12477,c_4])).

tff(c_12525,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_66,c_12521])).

tff(c_12572,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12525,c_12483,c_12525,c_12525,c_12483,c_12483,c_12525,c_12490,c_12483,c_12483,c_62])).

tff(c_12573,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_12572])).

tff(c_12712,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12577,c_12577,c_12577,c_12573])).

tff(c_13526,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13522,c_12712])).

tff(c_13527,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_12572])).

tff(c_13667,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13532,c_13532,c_13532,c_13532,c_13532,c_13532,c_13532,c_13532,c_13532,c_13527])).

tff(c_13668,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_13667])).

tff(c_13717,plain,(
    ~ r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_13668])).

tff(c_15138,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15118,c_13717])).

tff(c_15142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13654,c_15138])).

tff(c_15144,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_13667])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_15187,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_15144,c_12])).

tff(c_15197,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_15187,c_13538])).

tff(c_15143,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_13667])).

tff(c_15223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13539,c_15197,c_15143])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:55:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.58/3.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.84/3.19  
% 9.84/3.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.84/3.19  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.84/3.19  
% 9.84/3.19  %Foreground sorts:
% 9.84/3.19  
% 9.84/3.19  
% 9.84/3.19  %Background operators:
% 9.84/3.19  
% 9.84/3.19  
% 9.84/3.19  %Foreground operators:
% 9.84/3.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.84/3.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.84/3.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.84/3.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.84/3.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.84/3.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.84/3.19  tff('#skF_2', type, '#skF_2': $i).
% 9.84/3.19  tff('#skF_3', type, '#skF_3': $i).
% 9.84/3.19  tff('#skF_1', type, '#skF_1': $i).
% 9.84/3.19  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.84/3.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.84/3.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.84/3.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.84/3.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.84/3.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.84/3.19  tff('#skF_4', type, '#skF_4': $i).
% 9.84/3.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.84/3.19  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 9.84/3.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.84/3.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.84/3.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.84/3.19  
% 9.84/3.22  tff(f_156, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 9.84/3.22  tff(f_68, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.84/3.22  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.84/3.22  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.84/3.22  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.84/3.22  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 9.84/3.22  tff(f_136, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 9.84/3.22  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 9.84/3.22  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.84/3.22  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 9.84/3.22  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.84/3.22  tff(f_66, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc23_relat_1)).
% 9.84/3.22  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 9.84/3.22  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 9.84/3.22  tff(f_104, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 9.84/3.22  tff(f_130, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 9.84/3.22  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.84/3.22  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 9.84/3.22  tff(c_66, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.84/3.22  tff(c_26, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.84/3.22  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.84/3.22  tff(c_148, plain, (![B_62, A_63]: (v1_relat_1(B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.84/3.22  tff(c_154, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_148])).
% 9.84/3.22  tff(c_158, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_154])).
% 9.84/3.22  tff(c_64, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.84/3.22  tff(c_77, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_64])).
% 9.84/3.22  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.84/3.22  tff(c_10954, plain, (![A_702, B_703, C_704]: (k1_relset_1(A_702, B_703, C_704)=k1_relat_1(C_704) | ~m1_subset_1(C_704, k1_zfmisc_1(k2_zfmisc_1(A_702, B_703))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.84/3.22  tff(c_10973, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_10954])).
% 9.84/3.22  tff(c_12254, plain, (![B_798, A_799, C_800]: (k1_xboole_0=B_798 | k1_relset_1(A_799, B_798, C_800)=A_799 | ~v1_funct_2(C_800, A_799, B_798) | ~m1_subset_1(C_800, k1_zfmisc_1(k2_zfmisc_1(A_799, B_798))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.84/3.22  tff(c_12267, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_12254])).
% 9.84/3.22  tff(c_12283, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_10973, c_12267])).
% 9.84/3.22  tff(c_12284, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_77, c_12283])).
% 9.84/3.22  tff(c_34, plain, (![B_26, A_25]: (k1_relat_1(k7_relat_1(B_26, A_25))=A_25 | ~r1_tarski(A_25, k1_relat_1(B_26)) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.84/3.22  tff(c_12302, plain, (![A_25]: (k1_relat_1(k7_relat_1('#skF_4', A_25))=A_25 | ~r1_tarski(A_25, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_12284, c_34])).
% 9.84/3.22  tff(c_12346, plain, (![A_803]: (k1_relat_1(k7_relat_1('#skF_4', A_803))=A_803 | ~r1_tarski(A_803, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_12302])).
% 9.84/3.22  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.84/3.22  tff(c_11832, plain, (![A_766, B_767, C_768, D_769]: (k2_partfun1(A_766, B_767, C_768, D_769)=k7_relat_1(C_768, D_769) | ~m1_subset_1(C_768, k1_zfmisc_1(k2_zfmisc_1(A_766, B_767))) | ~v1_funct_1(C_768))), inference(cnfTransformation, [status(thm)], [f_136])).
% 9.84/3.22  tff(c_11839, plain, (![D_769]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_769)=k7_relat_1('#skF_4', D_769) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_11832])).
% 9.84/3.22  tff(c_11850, plain, (![D_769]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_769)=k7_relat_1('#skF_4', D_769))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_11839])).
% 9.84/3.22  tff(c_32, plain, (![B_24, A_23]: (r1_tarski(k7_relat_1(B_24, A_23), B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.84/3.22  tff(c_139, plain, (![A_60, B_61]: (r1_tarski(A_60, B_61) | ~m1_subset_1(A_60, k1_zfmisc_1(B_61)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.84/3.22  tff(c_147, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_139])).
% 9.84/3.22  tff(c_2256, plain, (![A_225, C_226, B_227]: (r1_tarski(A_225, C_226) | ~r1_tarski(B_227, C_226) | ~r1_tarski(A_225, B_227))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.84/3.22  tff(c_2527, plain, (![A_263]: (r1_tarski(A_263, k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_263, '#skF_4'))), inference(resolution, [status(thm)], [c_147, c_2256])).
% 9.84/3.22  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.84/3.22  tff(c_155, plain, (![A_7, B_8]: (v1_relat_1(A_7) | ~v1_relat_1(B_8) | ~r1_tarski(A_7, B_8))), inference(resolution, [status(thm)], [c_14, c_148])).
% 9.84/3.22  tff(c_2538, plain, (![A_263]: (v1_relat_1(A_263) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_263, '#skF_4'))), inference(resolution, [status(thm)], [c_2527, c_155])).
% 9.84/3.22  tff(c_2545, plain, (![A_264]: (v1_relat_1(A_264) | ~r1_tarski(A_264, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2538])).
% 9.84/3.22  tff(c_2560, plain, (![A_23]: (v1_relat_1(k7_relat_1('#skF_4', A_23)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_2545])).
% 9.84/3.22  tff(c_2568, plain, (![A_23]: (v1_relat_1(k7_relat_1('#skF_4', A_23)))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_2560])).
% 9.84/3.22  tff(c_2305, plain, (![C_231, A_232, B_233]: (v4_relat_1(C_231, A_232) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.84/3.22  tff(c_2320, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_2305])).
% 9.84/3.22  tff(c_2592, plain, (![C_271, A_272, B_273]: (v4_relat_1(k7_relat_1(C_271, A_272), A_272) | ~v4_relat_1(C_271, B_273) | ~v1_relat_1(C_271))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.84/3.22  tff(c_2604, plain, (![A_272]: (v4_relat_1(k7_relat_1('#skF_4', A_272), A_272) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2320, c_2592])).
% 9.84/3.22  tff(c_2615, plain, (![A_274]: (v4_relat_1(k7_relat_1('#skF_4', A_274), A_274))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_2604])).
% 9.84/3.22  tff(c_28, plain, (![B_20, A_19]: (k7_relat_1(B_20, A_19)=B_20 | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.84/3.22  tff(c_2620, plain, (![A_274]: (k7_relat_1(k7_relat_1('#skF_4', A_274), A_274)=k7_relat_1('#skF_4', A_274) | ~v1_relat_1(k7_relat_1('#skF_4', A_274)))), inference(resolution, [status(thm)], [c_2615, c_28])).
% 9.84/3.22  tff(c_2649, plain, (![A_278]: (k7_relat_1(k7_relat_1('#skF_4', A_278), A_278)=k7_relat_1('#skF_4', A_278))), inference(demodulation, [status(thm), theory('equality')], [c_2568, c_2620])).
% 9.84/3.22  tff(c_2676, plain, (![A_278]: (r1_tarski(k7_relat_1('#skF_4', A_278), k7_relat_1('#skF_4', A_278)) | ~v1_relat_1(k7_relat_1('#skF_4', A_278)))), inference(superposition, [status(thm), theory('equality')], [c_2649, c_32])).
% 9.84/3.22  tff(c_2699, plain, (![A_278]: (r1_tarski(k7_relat_1('#skF_4', A_278), k7_relat_1('#skF_4', A_278)))), inference(demodulation, [status(thm), theory('equality')], [c_2568, c_2676])).
% 9.84/3.22  tff(c_3619, plain, (![A_324, B_325, A_326]: (r1_tarski(A_324, B_325) | ~r1_tarski(A_324, k7_relat_1(B_325, A_326)) | ~v1_relat_1(B_325))), inference(resolution, [status(thm)], [c_32, c_2256])).
% 9.84/3.22  tff(c_3633, plain, (![A_278]: (r1_tarski(k7_relat_1('#skF_4', A_278), '#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2699, c_3619])).
% 9.84/3.22  tff(c_3665, plain, (![A_278]: (r1_tarski(k7_relat_1('#skF_4', A_278), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_3633])).
% 9.84/3.22  tff(c_30, plain, (![B_22, A_21]: (r1_tarski(k1_relat_1(k7_relat_1(B_22, A_21)), A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.84/3.22  tff(c_2673, plain, (![A_278]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_278)), A_278) | ~v1_relat_1(k7_relat_1('#skF_4', A_278)))), inference(superposition, [status(thm), theory('equality')], [c_2649, c_30])).
% 9.84/3.22  tff(c_2697, plain, (![A_278]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_278)), A_278))), inference(demodulation, [status(thm), theory('equality')], [c_2568, c_2673])).
% 9.84/3.22  tff(c_2269, plain, (![A_225]: (r1_tarski(A_225, k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_225, '#skF_4'))), inference(resolution, [status(thm)], [c_147, c_2256])).
% 9.84/3.22  tff(c_4102, plain, (![D_364, B_365, C_366, A_367]: (m1_subset_1(D_364, k1_zfmisc_1(k2_zfmisc_1(B_365, C_366))) | ~r1_tarski(k1_relat_1(D_364), B_365) | ~m1_subset_1(D_364, k1_zfmisc_1(k2_zfmisc_1(A_367, C_366))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.84/3.22  tff(c_9515, plain, (![A_598, B_599, C_600, A_601]: (m1_subset_1(A_598, k1_zfmisc_1(k2_zfmisc_1(B_599, C_600))) | ~r1_tarski(k1_relat_1(A_598), B_599) | ~r1_tarski(A_598, k2_zfmisc_1(A_601, C_600)))), inference(resolution, [status(thm)], [c_14, c_4102])).
% 9.84/3.22  tff(c_9704, plain, (![A_608, B_609]: (m1_subset_1(A_608, k1_zfmisc_1(k2_zfmisc_1(B_609, '#skF_2'))) | ~r1_tarski(k1_relat_1(A_608), B_609) | ~r1_tarski(A_608, '#skF_4'))), inference(resolution, [status(thm)], [c_2269, c_9515])).
% 9.84/3.22  tff(c_4243, plain, (![A_377, B_378, C_379, D_380]: (k2_partfun1(A_377, B_378, C_379, D_380)=k7_relat_1(C_379, D_380) | ~m1_subset_1(C_379, k1_zfmisc_1(k2_zfmisc_1(A_377, B_378))) | ~v1_funct_1(C_379))), inference(cnfTransformation, [status(thm)], [f_136])).
% 9.84/3.22  tff(c_4250, plain, (![D_380]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_380)=k7_relat_1('#skF_4', D_380) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_4243])).
% 9.84/3.22  tff(c_4261, plain, (![D_380]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_380)=k7_relat_1('#skF_4', D_380))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4250])).
% 9.84/3.22  tff(c_2135, plain, (![A_210, B_211, C_212, D_213]: (v1_funct_1(k2_partfun1(A_210, B_211, C_212, D_213)) | ~m1_subset_1(C_212, k1_zfmisc_1(k2_zfmisc_1(A_210, B_211))) | ~v1_funct_1(C_212))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.84/3.22  tff(c_2140, plain, (![D_213]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_213)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_2135])).
% 9.84/3.22  tff(c_2148, plain, (![D_213]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_213)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2140])).
% 9.84/3.22  tff(c_62, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.84/3.22  tff(c_159, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_62])).
% 9.84/3.22  tff(c_2151, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2148, c_159])).
% 9.84/3.22  tff(c_2152, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_62])).
% 9.84/3.22  tff(c_2154, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2152])).
% 9.84/3.22  tff(c_4264, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4261, c_2154])).
% 9.84/3.22  tff(c_9717, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_9704, c_4264])).
% 9.84/3.22  tff(c_9754, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3665, c_2697, c_9717])).
% 9.84/3.22  tff(c_9755, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_2152])).
% 9.84/3.22  tff(c_11860, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11850, c_9755])).
% 9.84/3.22  tff(c_9756, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_2152])).
% 9.84/3.22  tff(c_10971, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_9756, c_10954])).
% 9.84/3.22  tff(c_11853, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_11850, c_11850, c_10971])).
% 9.84/3.22  tff(c_11859, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_11850, c_9756])).
% 9.84/3.22  tff(c_12058, plain, (![B_785, C_786, A_787]: (k1_xboole_0=B_785 | v1_funct_2(C_786, A_787, B_785) | k1_relset_1(A_787, B_785, C_786)!=A_787 | ~m1_subset_1(C_786, k1_zfmisc_1(k2_zfmisc_1(A_787, B_785))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.84/3.22  tff(c_12064, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_11859, c_12058])).
% 9.84/3.22  tff(c_12082, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11853, c_12064])).
% 9.84/3.22  tff(c_12083, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_11860, c_77, c_12082])).
% 9.84/3.22  tff(c_12356, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12346, c_12083])).
% 9.84/3.22  tff(c_12476, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_12356])).
% 9.84/3.22  tff(c_12477, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_64])).
% 9.84/3.22  tff(c_8, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.84/3.22  tff(c_12490, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12477, c_12477, c_8])).
% 9.84/3.22  tff(c_12478, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_64])).
% 9.84/3.22  tff(c_12483, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12477, c_12478])).
% 9.84/3.22  tff(c_12519, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12490, c_12483, c_68])).
% 9.84/3.22  tff(c_12563, plain, (![A_816, B_817]: (r1_tarski(A_816, B_817) | ~m1_subset_1(A_816, k1_zfmisc_1(B_817)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.84/3.22  tff(c_12571, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_12519, c_12563])).
% 9.84/3.22  tff(c_4, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.84/3.22  tff(c_12520, plain, (![A_4]: (A_4='#skF_1' | ~r1_tarski(A_4, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12477, c_12477, c_4])).
% 9.84/3.22  tff(c_13532, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_12571, c_12520])).
% 9.84/3.22  tff(c_12484, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12483, c_70])).
% 9.84/3.22  tff(c_13539, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13532, c_13532, c_12484])).
% 9.84/3.22  tff(c_12491, plain, (![A_806]: (k2_zfmisc_1(A_806, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12477, c_12477, c_8])).
% 9.84/3.22  tff(c_12495, plain, (v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12491, c_26])).
% 9.84/3.22  tff(c_13542, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13532, c_12495])).
% 9.84/3.22  tff(c_12538, plain, (![B_813, A_814]: (r1_tarski(k7_relat_1(B_813, A_814), B_813) | ~v1_relat_1(B_813))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.84/3.22  tff(c_12542, plain, (![A_814]: (k7_relat_1('#skF_1', A_814)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_12538, c_12520])).
% 9.84/3.22  tff(c_12545, plain, (![A_814]: (k7_relat_1('#skF_1', A_814)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12495, c_12542])).
% 9.84/3.22  tff(c_13535, plain, (![A_814]: (k7_relat_1('#skF_4', A_814)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13532, c_13532, c_12545])).
% 9.84/3.22  tff(c_13637, plain, (![B_952, A_953]: (r1_tarski(k1_relat_1(k7_relat_1(B_952, A_953)), A_953) | ~v1_relat_1(B_952))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.84/3.22  tff(c_13644, plain, (![A_814]: (r1_tarski(k1_relat_1('#skF_4'), A_814) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_13535, c_13637])).
% 9.84/3.22  tff(c_13648, plain, (![A_954]: (r1_tarski(k1_relat_1('#skF_4'), A_954))), inference(demodulation, [status(thm), theory('equality')], [c_13542, c_13644])).
% 9.84/3.22  tff(c_13538, plain, (![A_4]: (A_4='#skF_4' | ~r1_tarski(A_4, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13532, c_13532, c_12520])).
% 9.84/3.22  tff(c_13653, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_13648, c_13538])).
% 9.84/3.22  tff(c_13647, plain, (![A_814]: (r1_tarski(k1_relat_1('#skF_4'), A_814))), inference(demodulation, [status(thm), theory('equality')], [c_13542, c_13644])).
% 9.84/3.22  tff(c_13654, plain, (![A_814]: (r1_tarski('#skF_4', A_814))), inference(demodulation, [status(thm), theory('equality')], [c_13653, c_13647])).
% 9.84/3.22  tff(c_13540, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13532, c_12519])).
% 9.84/3.22  tff(c_10, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.84/3.22  tff(c_12500, plain, (![B_6]: (k2_zfmisc_1('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12477, c_12477, c_10])).
% 9.84/3.22  tff(c_13541, plain, (![B_6]: (k2_zfmisc_1('#skF_4', B_6)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13532, c_13532, c_12500])).
% 9.84/3.22  tff(c_14912, plain, (![A_1121, B_1122, C_1123, D_1124]: (k2_partfun1(A_1121, B_1122, C_1123, D_1124)=k7_relat_1(C_1123, D_1124) | ~m1_subset_1(C_1123, k1_zfmisc_1(k2_zfmisc_1(A_1121, B_1122))) | ~v1_funct_1(C_1123))), inference(cnfTransformation, [status(thm)], [f_136])).
% 9.84/3.22  tff(c_15110, plain, (![B_1145, C_1146, D_1147]: (k2_partfun1('#skF_4', B_1145, C_1146, D_1147)=k7_relat_1(C_1146, D_1147) | ~m1_subset_1(C_1146, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_1146))), inference(superposition, [status(thm), theory('equality')], [c_13541, c_14912])).
% 9.84/3.22  tff(c_15112, plain, (![B_1145, D_1147]: (k2_partfun1('#skF_4', B_1145, '#skF_4', D_1147)=k7_relat_1('#skF_4', D_1147) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_13540, c_15110])).
% 9.84/3.22  tff(c_15118, plain, (![B_1145, D_1147]: (k2_partfun1('#skF_4', B_1145, '#skF_4', D_1147)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_13535, c_15112])).
% 9.84/3.22  tff(c_12577, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_12571, c_12520])).
% 9.84/3.22  tff(c_12584, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12577, c_12519])).
% 9.84/3.22  tff(c_12585, plain, (![B_6]: (k2_zfmisc_1('#skF_4', B_6)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12577, c_12577, c_12500])).
% 9.84/3.22  tff(c_13179, plain, (![A_902, B_903, C_904, D_905]: (v1_funct_1(k2_partfun1(A_902, B_903, C_904, D_905)) | ~m1_subset_1(C_904, k1_zfmisc_1(k2_zfmisc_1(A_902, B_903))) | ~v1_funct_1(C_904))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.84/3.22  tff(c_13514, plain, (![B_943, C_944, D_945]: (v1_funct_1(k2_partfun1('#skF_4', B_943, C_944, D_945)) | ~m1_subset_1(C_944, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_944))), inference(superposition, [status(thm), theory('equality')], [c_12585, c_13179])).
% 9.84/3.22  tff(c_13516, plain, (![B_943, D_945]: (v1_funct_1(k2_partfun1('#skF_4', B_943, '#skF_4', D_945)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_12584, c_13514])).
% 9.84/3.22  tff(c_13522, plain, (![B_943, D_945]: (v1_funct_1(k2_partfun1('#skF_4', B_943, '#skF_4', D_945)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_13516])).
% 9.84/3.22  tff(c_12521, plain, (![A_808]: (A_808='#skF_1' | ~r1_tarski(A_808, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12477, c_12477, c_4])).
% 9.84/3.22  tff(c_12525, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_66, c_12521])).
% 9.84/3.22  tff(c_12572, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12525, c_12483, c_12525, c_12525, c_12483, c_12483, c_12525, c_12490, c_12483, c_12483, c_62])).
% 9.84/3.22  tff(c_12573, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_12572])).
% 9.84/3.22  tff(c_12712, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12577, c_12577, c_12577, c_12573])).
% 9.84/3.22  tff(c_13526, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13522, c_12712])).
% 9.84/3.22  tff(c_13527, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_12572])).
% 9.84/3.22  tff(c_13667, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13532, c_13532, c_13532, c_13532, c_13532, c_13532, c_13532, c_13532, c_13532, c_13527])).
% 9.84/3.22  tff(c_13668, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_13667])).
% 9.84/3.22  tff(c_13717, plain, (~r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_14, c_13668])).
% 9.84/3.22  tff(c_15138, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15118, c_13717])).
% 9.84/3.22  tff(c_15142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13654, c_15138])).
% 9.84/3.22  tff(c_15144, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_13667])).
% 9.84/3.22  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.84/3.22  tff(c_15187, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_15144, c_12])).
% 9.84/3.22  tff(c_15197, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_15187, c_13538])).
% 9.84/3.22  tff(c_15143, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_13667])).
% 9.84/3.22  tff(c_15223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13539, c_15197, c_15143])).
% 9.84/3.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.84/3.22  
% 9.84/3.22  Inference rules
% 9.84/3.22  ----------------------
% 9.84/3.22  #Ref     : 0
% 9.84/3.22  #Sup     : 3215
% 9.84/3.22  #Fact    : 0
% 9.84/3.22  #Define  : 0
% 9.84/3.22  #Split   : 29
% 9.84/3.22  #Chain   : 0
% 9.84/3.22  #Close   : 0
% 9.84/3.22  
% 9.84/3.22  Ordering : KBO
% 9.84/3.22  
% 9.84/3.22  Simplification rules
% 9.84/3.22  ----------------------
% 9.84/3.22  #Subsume      : 594
% 9.84/3.22  #Demod        : 3123
% 9.84/3.22  #Tautology    : 1481
% 9.84/3.22  #SimpNegUnit  : 45
% 9.84/3.22  #BackRed      : 84
% 9.84/3.22  
% 9.84/3.22  #Partial instantiations: 0
% 9.84/3.22  #Strategies tried      : 1
% 9.84/3.22  
% 9.84/3.22  Timing (in seconds)
% 9.84/3.22  ----------------------
% 9.84/3.22  Preprocessing        : 0.36
% 9.84/3.22  Parsing              : 0.19
% 9.84/3.22  CNF conversion       : 0.02
% 9.84/3.22  Main loop            : 2.07
% 9.84/3.22  Inferencing          : 0.65
% 9.84/3.22  Reduction            : 0.80
% 9.84/3.22  Demodulation         : 0.58
% 9.84/3.22  BG Simplification    : 0.06
% 9.84/3.22  Subsumption          : 0.41
% 9.84/3.22  Abstraction          : 0.08
% 9.84/3.22  MUC search           : 0.00
% 9.84/3.22  Cooper               : 0.00
% 9.84/3.22  Total                : 2.49
% 9.84/3.22  Index Insertion      : 0.00
% 9.84/3.22  Index Deletion       : 0.00
% 9.84/3.22  Index Matching       : 0.00
% 9.84/3.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
