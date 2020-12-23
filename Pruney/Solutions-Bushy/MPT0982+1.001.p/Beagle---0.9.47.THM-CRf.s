%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0982+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:11 EST 2020

% Result     : Theorem 5.61s
% Output     : CNFRefutation 5.61s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 231 expanded)
%              Number of leaves         :   35 (  96 expanded)
%              Depth                    :   11
%              Number of atoms          :  200 ( 763 expanded)
%              Number of equality atoms :   56 ( 208 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( ( k2_relset_1(A,C,k1_partfun1(A,B,B,C,D,E)) = C
                & v2_funct_1(E) )
             => ( C = k1_xboole_0
                | k2_relset_1(A,B,D) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_34,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_64,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_52,axiom,(
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

tff(f_112,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A)
              & v2_funct_1(A) )
           => r1_tarski(k1_relat_1(A),k2_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_77,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_89,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_77])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_90,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_77])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_153,plain,(
    ! [A_59,B_60,C_61] :
      ( k2_relset_1(A_59,B_60,C_61) = k2_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_166,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_153])).

tff(c_232,plain,(
    ! [A_74,B_75,C_76] :
      ( m1_subset_1(k2_relset_1(A_74,B_75,C_76),k1_zfmisc_1(B_75))
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_253,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_232])).

tff(c_265,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_253])).

tff(c_34,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,B_31)
      | ~ m1_subset_1(A_30,k1_zfmisc_1(B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_271,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_265,c_34])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( B_5 = A_4
      | ~ r1_tarski(B_5,A_4)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_274,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_271,c_4])).

tff(c_295,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_274])).

tff(c_2014,plain,(
    ! [B_289,E_286,D_288,C_285,A_284,F_287] :
      ( k1_partfun1(A_284,B_289,C_285,D_288,E_286,F_287) = k5_relat_1(E_286,F_287)
      | ~ m1_subset_1(F_287,k1_zfmisc_1(k2_zfmisc_1(C_285,D_288)))
      | ~ v1_funct_1(F_287)
      | ~ m1_subset_1(E_286,k1_zfmisc_1(k2_zfmisc_1(A_284,B_289)))
      | ~ v1_funct_1(E_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2032,plain,(
    ! [A_284,B_289,E_286] :
      ( k1_partfun1(A_284,B_289,'#skF_2','#skF_3',E_286,'#skF_5') = k5_relat_1(E_286,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_286,k1_zfmisc_1(k2_zfmisc_1(A_284,B_289)))
      | ~ v1_funct_1(E_286) ) ),
    inference(resolution,[status(thm)],[c_50,c_2014])).

tff(c_2213,plain,(
    ! [A_312,B_313,E_314] :
      ( k1_partfun1(A_312,B_313,'#skF_2','#skF_3',E_314,'#skF_5') = k5_relat_1(E_314,'#skF_5')
      | ~ m1_subset_1(E_314,k1_zfmisc_1(k2_zfmisc_1(A_312,B_313)))
      | ~ v1_funct_1(E_314) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2032])).

tff(c_2238,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_2213])).

tff(c_2252,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2238])).

tff(c_48,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1028,plain,(
    ! [C_182,A_185,E_184,D_183,F_180,B_181] :
      ( m1_subset_1(k1_partfun1(A_185,B_181,C_182,D_183,E_184,F_180),k1_zfmisc_1(k2_zfmisc_1(A_185,D_183)))
      | ~ m1_subset_1(F_180,k1_zfmisc_1(k2_zfmisc_1(C_182,D_183)))
      | ~ v1_funct_1(F_180)
      | ~ m1_subset_1(E_184,k1_zfmisc_1(k2_zfmisc_1(A_185,B_181)))
      | ~ v1_funct_1(E_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_259,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_232])).

tff(c_313,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_259])).

tff(c_1062,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1028,c_313])).

tff(c_1100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_54,c_50,c_1062])).

tff(c_1102,plain,(
    m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_259])).

tff(c_32,plain,(
    ! [A_27,B_28,C_29] :
      ( k2_relset_1(A_27,B_28,C_29) = k2_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1169,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = k2_relat_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1102,c_32])).

tff(c_1182,plain,(
    k2_relat_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1169])).

tff(c_2263,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2252,c_1182])).

tff(c_38,plain,(
    ! [A_32,B_34] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_32,B_34)),k2_relat_1(B_34))
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2295,plain,
    ( r1_tarski('#skF_3',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2263,c_38])).

tff(c_2312,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_90,c_2295])).

tff(c_2314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_295,c_2312])).

tff(c_2315,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_274])).

tff(c_46,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_52,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_131,plain,(
    ! [A_56,B_57,C_58] :
      ( k1_relset_1(A_56,B_57,C_58) = k1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_144,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_131])).

tff(c_2570,plain,(
    ! [B_360,A_361,C_362] :
      ( k1_xboole_0 = B_360
      | k1_relset_1(A_361,B_360,C_362) = A_361
      | ~ v1_funct_2(C_362,A_361,B_360)
      | ~ m1_subset_1(C_362,k1_zfmisc_1(k2_zfmisc_1(A_361,B_360))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2584,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2570])).

tff(c_2592,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_144,c_2584])).

tff(c_2593,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2592])).

tff(c_2613,plain,(
    ! [A_363,B_364] :
      ( r1_tarski(k1_relat_1(A_363),k2_relat_1(B_364))
      | ~ v2_funct_1(A_363)
      | k2_relat_1(k5_relat_1(B_364,A_363)) != k2_relat_1(A_363)
      | ~ v1_funct_1(B_364)
      | ~ v1_relat_1(B_364)
      | ~ v1_funct_1(A_363)
      | ~ v1_relat_1(A_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2625,plain,(
    ! [B_364] :
      ( r1_tarski('#skF_2',k2_relat_1(B_364))
      | ~ v2_funct_1('#skF_5')
      | k2_relat_1(k5_relat_1(B_364,'#skF_5')) != k2_relat_1('#skF_5')
      | ~ v1_funct_1(B_364)
      | ~ v1_relat_1(B_364)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2593,c_2613])).

tff(c_2737,plain,(
    ! [B_370] :
      ( r1_tarski('#skF_2',k2_relat_1(B_370))
      | k2_relat_1(k5_relat_1(B_370,'#skF_5')) != '#skF_3'
      | ~ v1_funct_1(B_370)
      | ~ v1_relat_1(B_370) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_54,c_2315,c_46,c_2625])).

tff(c_165,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_153])).

tff(c_42,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_167,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_42])).

tff(c_256,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_232])).

tff(c_267,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_256])).

tff(c_278,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_267,c_34])).

tff(c_280,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_278,c_4])).

tff(c_283,plain,(
    ~ r1_tarski('#skF_2',k2_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_280])).

tff(c_2744,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) != '#skF_3'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2737,c_283])).

tff(c_2755,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_60,c_2744])).

tff(c_2964,plain,(
    ! [F_401,B_403,D_402,E_400,A_398,C_399] :
      ( k1_partfun1(A_398,B_403,C_399,D_402,E_400,F_401) = k5_relat_1(E_400,F_401)
      | ~ m1_subset_1(F_401,k1_zfmisc_1(k2_zfmisc_1(C_399,D_402)))
      | ~ v1_funct_1(F_401)
      | ~ m1_subset_1(E_400,k1_zfmisc_1(k2_zfmisc_1(A_398,B_403)))
      | ~ v1_funct_1(E_400) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2977,plain,(
    ! [A_398,B_403,E_400] :
      ( k1_partfun1(A_398,B_403,'#skF_2','#skF_3',E_400,'#skF_5') = k5_relat_1(E_400,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_400,k1_zfmisc_1(k2_zfmisc_1(A_398,B_403)))
      | ~ v1_funct_1(E_400) ) ),
    inference(resolution,[status(thm)],[c_50,c_2964])).

tff(c_3227,plain,(
    ! [A_418,B_419,E_420] :
      ( k1_partfun1(A_418,B_419,'#skF_2','#skF_3',E_420,'#skF_5') = k5_relat_1(E_420,'#skF_5')
      | ~ m1_subset_1(E_420,k1_zfmisc_1(k2_zfmisc_1(A_418,B_419)))
      | ~ v1_funct_1(E_420) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2977])).

tff(c_3248,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_3227])).

tff(c_3261,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_3248])).

tff(c_3494,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3261,c_48])).

tff(c_22,plain,(
    ! [C_11,E_13,B_10,F_14,D_12,A_9] :
      ( m1_subset_1(k1_partfun1(A_9,B_10,C_11,D_12,E_13,F_14),k1_zfmisc_1(k2_zfmisc_1(A_9,D_12)))
      | ~ m1_subset_1(F_14,k1_zfmisc_1(k2_zfmisc_1(C_11,D_12)))
      | ~ v1_funct_1(F_14)
      | ~ m1_subset_1(E_13,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ v1_funct_1(E_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3498,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3261,c_22])).

tff(c_3502,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_54,c_50,c_3498])).

tff(c_3585,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_3502,c_32])).

tff(c_3625,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3494,c_3585])).

tff(c_3627,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2755,c_3625])).

%------------------------------------------------------------------------------
