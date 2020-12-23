%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:10 EST 2020

% Result     : Theorem 16.67s
% Output     : CNFRefutation 16.87s
% Verified   : 
% Statistics : Number of formulae       :  217 (4018 expanded)
%              Number of leaves         :   46 (1334 expanded)
%              Depth                    :   24
%              Number of atoms          :  410 (9317 expanded)
%              Number of equality atoms :  132 (3785 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_196,negated_conjecture,(
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

tff(f_137,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_73,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_135,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_125,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_105,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_176,axiom,(
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

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_154,axiom,(
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

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_68,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_120,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_60,plain,(
    ! [A_44] : k6_relat_1(A_44) = k6_partfun1(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_28,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_87,plain,(
    ! [A_13] : k2_relat_1(k6_partfun1(A_13)) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_28])).

tff(c_32,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_85,plain,(
    ! [A_15] : v1_relat_1(k6_partfun1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_32])).

tff(c_131,plain,(
    ! [A_66] :
      ( k2_relat_1(A_66) != k1_xboole_0
      | k1_xboole_0 = A_66
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_134,plain,(
    ! [A_15] :
      ( k2_relat_1(k6_partfun1(A_15)) != k1_xboole_0
      | k6_partfun1(A_15) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_85,c_131])).

tff(c_136,plain,(
    ! [A_15] :
      ( k1_xboole_0 != A_15
      | k6_partfun1(A_15) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_134])).

tff(c_70,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_159,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_70])).

tff(c_199,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_80,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_34,plain,(
    ! [A_15] : v2_funct_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_84,plain,(
    ! [A_15] : v2_funct_1(k6_partfun1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_34])).

tff(c_3256,plain,(
    ! [D_285,B_281,C_284,E_282,A_280,F_283] :
      ( k1_partfun1(A_280,B_281,C_284,D_285,E_282,F_283) = k5_relat_1(E_282,F_283)
      | ~ m1_subset_1(F_283,k1_zfmisc_1(k2_zfmisc_1(C_284,D_285)))
      | ~ v1_funct_1(F_283)
      | ~ m1_subset_1(E_282,k1_zfmisc_1(k2_zfmisc_1(A_280,B_281)))
      | ~ v1_funct_1(E_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_3264,plain,(
    ! [A_280,B_281,E_282] :
      ( k1_partfun1(A_280,B_281,'#skF_2','#skF_1',E_282,'#skF_4') = k5_relat_1(E_282,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_282,k1_zfmisc_1(k2_zfmisc_1(A_280,B_281)))
      | ~ v1_funct_1(E_282) ) ),
    inference(resolution,[status(thm)],[c_72,c_3256])).

tff(c_3943,plain,(
    ! [A_324,B_325,E_326] :
      ( k1_partfun1(A_324,B_325,'#skF_2','#skF_1',E_326,'#skF_4') = k5_relat_1(E_326,'#skF_4')
      | ~ m1_subset_1(E_326,k1_zfmisc_1(k2_zfmisc_1(A_324,B_325)))
      | ~ v1_funct_1(E_326) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3264])).

tff(c_3961,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_3943])).

tff(c_3977,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3961])).

tff(c_54,plain,(
    ! [B_33,C_34,E_36,F_37,A_32,D_35] :
      ( m1_subset_1(k1_partfun1(A_32,B_33,C_34,D_35,E_36,F_37),k1_zfmisc_1(k2_zfmisc_1(A_32,D_35)))
      | ~ m1_subset_1(F_37,k1_zfmisc_1(k2_zfmisc_1(C_34,D_35)))
      | ~ v1_funct_1(F_37)
      | ~ m1_subset_1(E_36,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_1(E_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_4022,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3977,c_54])).

tff(c_4031,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_4022])).

tff(c_48,plain,(
    ! [A_29] : m1_subset_1(k6_relat_1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_83,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_48])).

tff(c_2958,plain,(
    ! [D_255,C_256,A_257,B_258] :
      ( D_255 = C_256
      | ~ r2_relset_1(A_257,B_258,C_256,D_255)
      | ~ m1_subset_1(D_255,k1_zfmisc_1(k2_zfmisc_1(A_257,B_258)))
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_257,B_258))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2972,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_2958])).

tff(c_2995,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_2972])).

tff(c_3031,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2995])).

tff(c_4281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4031,c_3977,c_3031])).

tff(c_4282,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2995])).

tff(c_5182,plain,(
    ! [D_396,B_395,E_393,A_392,C_394] :
      ( k1_xboole_0 = C_394
      | v2_funct_1(D_396)
      | ~ v2_funct_1(k1_partfun1(A_392,B_395,B_395,C_394,D_396,E_393))
      | ~ m1_subset_1(E_393,k1_zfmisc_1(k2_zfmisc_1(B_395,C_394)))
      | ~ v1_funct_2(E_393,B_395,C_394)
      | ~ v1_funct_1(E_393)
      | ~ m1_subset_1(D_396,k1_zfmisc_1(k2_zfmisc_1(A_392,B_395)))
      | ~ v1_funct_2(D_396,A_392,B_395)
      | ~ v1_funct_1(D_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_5186,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4282,c_5182])).

tff(c_5190,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_74,c_72,c_84,c_5186])).

tff(c_5192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_199,c_5190])).

tff(c_5194,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_138,plain,(
    ! [A_67] :
      ( k1_xboole_0 != A_67
      | k6_partfun1(A_67) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_134])).

tff(c_151,plain,(
    ! [A_67] :
      ( v2_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_67 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_84])).

tff(c_174,plain,(
    ! [A_67] : k1_xboole_0 != A_67 ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_181,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_174])).

tff(c_182,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_5197,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5194,c_182])).

tff(c_144,plain,(
    ! [A_67] :
      ( k2_relat_1(k1_xboole_0) = A_67
      | k1_xboole_0 != A_67 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_87])).

tff(c_5223,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5194,c_5194,c_144])).

tff(c_6050,plain,(
    ! [E_488,F_489,A_486,D_491,C_490,B_487] :
      ( k1_partfun1(A_486,B_487,C_490,D_491,E_488,F_489) = k5_relat_1(E_488,F_489)
      | ~ m1_subset_1(F_489,k1_zfmisc_1(k2_zfmisc_1(C_490,D_491)))
      | ~ v1_funct_1(F_489)
      | ~ m1_subset_1(E_488,k1_zfmisc_1(k2_zfmisc_1(A_486,B_487)))
      | ~ v1_funct_1(E_488) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_6058,plain,(
    ! [A_486,B_487,E_488] :
      ( k1_partfun1(A_486,B_487,'#skF_2','#skF_1',E_488,'#skF_4') = k5_relat_1(E_488,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_488,k1_zfmisc_1(k2_zfmisc_1(A_486,B_487)))
      | ~ v1_funct_1(E_488) ) ),
    inference(resolution,[status(thm)],[c_72,c_6050])).

tff(c_6937,plain,(
    ! [A_541,B_542,E_543] :
      ( k1_partfun1(A_541,B_542,'#skF_2','#skF_1',E_543,'#skF_4') = k5_relat_1(E_543,'#skF_4')
      | ~ m1_subset_1(E_543,k1_zfmisc_1(k2_zfmisc_1(A_541,B_542)))
      | ~ v1_funct_1(E_543) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6058])).

tff(c_6955,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_6937])).

tff(c_6971,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_6955])).

tff(c_5193,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_5210,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5194,c_5193])).

tff(c_7155,plain,(
    r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6971,c_5210])).

tff(c_5294,plain,(
    ! [C_405,A_406,B_407] :
      ( v1_relat_1(C_405)
      | ~ m1_subset_1(C_405,k1_zfmisc_1(k2_zfmisc_1(A_406,B_407))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_5307,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_5294])).

tff(c_22,plain,(
    ! [A_12] :
      ( k2_relat_1(A_12) != k1_xboole_0
      | k1_xboole_0 = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_5200,plain,(
    ! [A_12] :
      ( k2_relat_1(A_12) != '#skF_1'
      | A_12 = '#skF_1'
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5194,c_5194,c_22])).

tff(c_5322,plain,
    ( k2_relat_1('#skF_4') != '#skF_1'
    | '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5307,c_5200])).

tff(c_5334,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5322])).

tff(c_5243,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5194,c_5194,c_136])).

tff(c_5679,plain,(
    ! [A_456,B_457,C_458] :
      ( k2_relset_1(A_456,B_457,C_458) = k2_relat_1(C_458)
      | ~ m1_subset_1(C_458,k1_zfmisc_1(k2_zfmisc_1(A_456,B_457))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_5697,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_5679])).

tff(c_62,plain,(
    ! [A_45,B_46,C_47,D_49] :
      ( k2_relset_1(A_45,B_46,C_47) = B_46
      | ~ r2_relset_1(B_46,B_46,k1_partfun1(B_46,A_45,A_45,B_46,D_49,C_47),k6_partfun1(B_46))
      | ~ m1_subset_1(D_49,k1_zfmisc_1(k2_zfmisc_1(B_46,A_45)))
      | ~ v1_funct_2(D_49,B_46,A_45)
      | ~ v1_funct_1(D_49)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46)))
      | ~ v1_funct_2(C_47,A_45,B_46)
      | ~ v1_funct_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_7159,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_4'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6971,c_62])).

tff(c_7168,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_82,c_80,c_78,c_5243,c_5697,c_7159])).

tff(c_7169,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_5334,c_7168])).

tff(c_7183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7155,c_7169])).

tff(c_7184,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5322])).

tff(c_26,plain,(
    ! [A_13] : k1_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_88,plain,(
    ! [A_13] : k1_relat_1(k6_partfun1(A_13)) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_26])).

tff(c_147,plain,(
    ! [A_67] :
      ( k1_relat_1(k1_xboole_0) = A_67
      | k1_xboole_0 != A_67 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_88])).

tff(c_5195,plain,(
    ! [A_67] :
      ( k1_relat_1('#skF_1') = A_67
      | A_67 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5194,c_5194,c_147])).

tff(c_7284,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7184,c_7184,c_5195])).

tff(c_24,plain,(
    ! [A_12] :
      ( k1_relat_1(A_12) != k1_xboole_0
      | k1_xboole_0 = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_5229,plain,(
    ! [A_12] :
      ( k1_relat_1(A_12) != '#skF_1'
      | A_12 = '#skF_1'
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5194,c_5194,c_24])).

tff(c_5323,plain,
    ( k1_relat_1('#skF_4') != '#skF_1'
    | '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5307,c_5229])).

tff(c_5333,plain,(
    k1_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5323])).

tff(c_7237,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7184,c_5333])).

tff(c_7287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7284,c_7237])).

tff(c_7288,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5323])).

tff(c_5306,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_5294])).

tff(c_5315,plain,
    ( k1_relat_1('#skF_3') != '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_5306,c_5229])).

tff(c_5332,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5315])).

tff(c_7409,plain,(
    k1_relat_1('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7288,c_5332])).

tff(c_7422,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7288,c_78])).

tff(c_7613,plain,(
    ! [C_576,A_577,B_578] :
      ( v4_relat_1(C_576,A_577)
      | ~ m1_subset_1(C_576,k1_zfmisc_1(k2_zfmisc_1(A_577,B_578))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_7623,plain,(
    v4_relat_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_7422,c_7613])).

tff(c_7289,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5323])).

tff(c_7444,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7288,c_7289])).

tff(c_5199,plain,(
    ! [A_15] :
      ( A_15 != '#skF_1'
      | k6_partfun1(A_15) = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5194,c_5194,c_136])).

tff(c_7412,plain,(
    ! [A_15] :
      ( A_15 != '#skF_4'
      | k6_partfun1(A_15) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7288,c_7288,c_5199])).

tff(c_7827,plain,(
    ! [C_594,B_595,A_596] :
      ( v5_relat_1(C_594,B_595)
      | ~ m1_subset_1(C_594,k1_zfmisc_1(k2_zfmisc_1(A_596,B_595))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_7843,plain,(
    ! [A_29] : v5_relat_1(k6_partfun1(A_29),A_29) ),
    inference(resolution,[status(thm)],[c_83,c_7827])).

tff(c_7848,plain,(
    ! [B_598] :
      ( v2_funct_2(B_598,k2_relat_1(B_598))
      | ~ v5_relat_1(B_598,k2_relat_1(B_598))
      | ~ v1_relat_1(B_598) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_7854,plain,(
    ! [A_13] :
      ( v2_funct_2(k6_partfun1(A_13),k2_relat_1(k6_partfun1(A_13)))
      | ~ v5_relat_1(k6_partfun1(A_13),A_13)
      | ~ v1_relat_1(k6_partfun1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_7848])).

tff(c_7859,plain,(
    ! [A_599] : v2_funct_2(k6_partfun1(A_599),A_599) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_7843,c_87,c_7854])).

tff(c_7873,plain,(
    v2_funct_2('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7412,c_7859])).

tff(c_7423,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7288,c_72])).

tff(c_9082,plain,(
    ! [B_675,E_676,F_677,A_674,C_678,D_679] :
      ( k1_partfun1(A_674,B_675,C_678,D_679,E_676,F_677) = k5_relat_1(E_676,F_677)
      | ~ m1_subset_1(F_677,k1_zfmisc_1(k2_zfmisc_1(C_678,D_679)))
      | ~ v1_funct_1(F_677)
      | ~ m1_subset_1(E_676,k1_zfmisc_1(k2_zfmisc_1(A_674,B_675)))
      | ~ v1_funct_1(E_676) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_9088,plain,(
    ! [A_674,B_675,E_676] :
      ( k1_partfun1(A_674,B_675,'#skF_2','#skF_4',E_676,'#skF_4') = k5_relat_1(E_676,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_676,k1_zfmisc_1(k2_zfmisc_1(A_674,B_675)))
      | ~ v1_funct_1(E_676) ) ),
    inference(resolution,[status(thm)],[c_7423,c_9082])).

tff(c_9589,plain,(
    ! [A_711,B_712,E_713] :
      ( k1_partfun1(A_711,B_712,'#skF_2','#skF_4',E_713,'#skF_4') = k5_relat_1(E_713,'#skF_4')
      | ~ m1_subset_1(E_713,k1_zfmisc_1(k2_zfmisc_1(A_711,B_712)))
      | ~ v1_funct_1(E_713) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_9088])).

tff(c_9604,plain,
    ( k1_partfun1('#skF_4','#skF_2','#skF_2','#skF_4','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7422,c_9589])).

tff(c_9623,plain,(
    k1_partfun1('#skF_4','#skF_2','#skF_2','#skF_4','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_9604])).

tff(c_9698,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9623,c_54])).

tff(c_9708,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_7422,c_76,c_7423,c_9698])).

tff(c_7421,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7288,c_5194])).

tff(c_183,plain,(
    ! [A_68] : m1_subset_1(k6_partfun1(A_68),k1_zfmisc_1(k2_zfmisc_1(A_68,A_68))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_48])).

tff(c_186,plain,(
    ! [A_15] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_15,A_15)))
      | k1_xboole_0 != A_15 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_183])).

tff(c_7649,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7421,c_7421,c_186])).

tff(c_7418,plain,(
    r2_relset_1('#skF_4','#skF_4',k1_partfun1('#skF_4','#skF_2','#skF_2','#skF_4','#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7288,c_7288,c_7288,c_7288,c_7288,c_5210])).

tff(c_9689,plain,(
    r2_relset_1('#skF_4','#skF_4',k5_relat_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9623,c_7418])).

tff(c_46,plain,(
    ! [D_28,C_27,A_25,B_26] :
      ( D_28 = C_27
      | ~ r2_relset_1(A_25,B_26,C_27,D_28)
      | ~ m1_subset_1(D_28,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_9711,plain,
    ( k5_relat_1('#skF_3','#skF_4') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_9689,c_46])).

tff(c_9714,plain,
    ( k5_relat_1('#skF_3','#skF_4') = '#skF_4'
    | ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7649,c_9711])).

tff(c_39408,plain,(
    k5_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9708,c_9714])).

tff(c_36,plain,(
    ! [C_18,A_16,B_17] :
      ( v1_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_9767,plain,(
    v1_relat_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_9708,c_36])).

tff(c_7411,plain,(
    ! [A_12] :
      ( k2_relat_1(A_12) != '#skF_4'
      | A_12 = '#skF_4'
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7288,c_7288,c_5200])).

tff(c_9789,plain,
    ( k2_relat_1(k5_relat_1('#skF_3','#skF_4')) != '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_9767,c_7411])).

tff(c_9994,plain,(
    k2_relat_1(k5_relat_1('#skF_3','#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_9789])).

tff(c_38,plain,(
    ! [C_21,B_20,A_19] :
      ( v5_relat_1(C_21,B_20)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_9765,plain,(
    v5_relat_1(k5_relat_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_9708,c_38])).

tff(c_52,plain,(
    ! [B_31,A_30] :
      ( k2_relat_1(B_31) = A_30
      | ~ v2_funct_2(B_31,A_30)
      | ~ v5_relat_1(B_31,A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_9793,plain,
    ( k2_relat_1(k5_relat_1('#skF_3','#skF_4')) = '#skF_4'
    | ~ v2_funct_2(k5_relat_1('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_9765,c_52])).

tff(c_9796,plain,
    ( k2_relat_1(k5_relat_1('#skF_3','#skF_4')) = '#skF_4'
    | ~ v2_funct_2(k5_relat_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9767,c_9793])).

tff(c_10928,plain,(
    ~ v2_funct_2(k5_relat_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_9994,c_9796])).

tff(c_39423,plain,(
    ~ v2_funct_2('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39408,c_10928])).

tff(c_39446,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7873,c_39423])).

tff(c_39447,plain,(
    k5_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9789])).

tff(c_7413,plain,(
    ! [A_12] :
      ( k1_relat_1(A_12) != '#skF_4'
      | A_12 = '#skF_4'
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7288,c_7288,c_5229])).

tff(c_9790,plain,
    ( k1_relat_1(k5_relat_1('#skF_3','#skF_4')) != '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_9767,c_7413])).

tff(c_9993,plain,(
    k1_relat_1(k5_relat_1('#skF_3','#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_9790])).

tff(c_39525,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39447,c_9993])).

tff(c_39537,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7444,c_39525])).

tff(c_39538,plain,(
    k5_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9790])).

tff(c_20,plain,(
    ! [A_9,B_11] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_9,B_11)),k1_relat_1(A_9))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_39565,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_39538,c_20])).

tff(c_39579,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5306,c_5307,c_7444,c_39565])).

tff(c_7709,plain,(
    ! [B_585,A_586] :
      ( r1_tarski(k1_relat_1(B_585),A_586)
      | ~ v4_relat_1(B_585,A_586)
      | ~ v1_relat_1(B_585) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7722,plain,(
    ! [B_585,A_586] :
      ( k1_relat_1(B_585) = A_586
      | ~ r1_tarski(A_586,k1_relat_1(B_585))
      | ~ v4_relat_1(B_585,A_586)
      | ~ v1_relat_1(B_585) ) ),
    inference(resolution,[status(thm)],[c_7709,c_4])).

tff(c_39587,plain,
    ( k1_relat_1('#skF_3') = '#skF_4'
    | ~ v4_relat_1('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_39579,c_7722])).

tff(c_39596,plain,(
    k1_relat_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5306,c_7623,c_39587])).

tff(c_39598,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7409,c_39596])).

tff(c_39599,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5315])).

tff(c_5314,plain,
    ( k2_relat_1('#skF_3') != '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_5306,c_5200])).

tff(c_5324,plain,(
    k2_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5314])).

tff(c_39602,plain,(
    k2_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39599,c_5324])).

tff(c_39611,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5223,c_39602])).

tff(c_39612,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5314])).

tff(c_39617,plain,(
    ~ v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39612,c_120])).

tff(c_39623,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5197,c_39617])).

tff(c_39624,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_39725,plain,(
    ! [C_1306,A_1307,B_1308] :
      ( v1_relat_1(C_1306)
      | ~ m1_subset_1(C_1306,k1_zfmisc_1(k2_zfmisc_1(A_1307,B_1308))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_39738,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_39725])).

tff(c_39823,plain,(
    ! [C_1315,B_1316,A_1317] :
      ( v5_relat_1(C_1315,B_1316)
      | ~ m1_subset_1(C_1315,k1_zfmisc_1(k2_zfmisc_1(A_1317,B_1316))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_39835,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_39823])).

tff(c_40284,plain,(
    ! [A_1366,B_1367,C_1368] :
      ( k2_relset_1(A_1366,B_1367,C_1368) = k2_relat_1(C_1368)
      | ~ m1_subset_1(C_1368,k1_zfmisc_1(k2_zfmisc_1(A_1366,B_1367))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_40302,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_40284])).

tff(c_41553,plain,(
    ! [A_1449,B_1450,C_1451,D_1452] :
      ( k2_relset_1(A_1449,B_1450,C_1451) = B_1450
      | ~ r2_relset_1(B_1450,B_1450,k1_partfun1(B_1450,A_1449,A_1449,B_1450,D_1452,C_1451),k6_partfun1(B_1450))
      | ~ m1_subset_1(D_1452,k1_zfmisc_1(k2_zfmisc_1(B_1450,A_1449)))
      | ~ v1_funct_2(D_1452,B_1450,A_1449)
      | ~ v1_funct_1(D_1452)
      | ~ m1_subset_1(C_1451,k1_zfmisc_1(k2_zfmisc_1(A_1449,B_1450)))
      | ~ v1_funct_2(C_1451,A_1449,B_1450)
      | ~ v1_funct_1(C_1451) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_41568,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_41553])).

tff(c_41573,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_82,c_80,c_78,c_40302,c_41568])).

tff(c_50,plain,(
    ! [B_31] :
      ( v2_funct_2(B_31,k2_relat_1(B_31))
      | ~ v5_relat_1(B_31,k2_relat_1(B_31))
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_41579,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_41573,c_50])).

tff(c_41583,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39738,c_39835,c_41573,c_41579])).

tff(c_41585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39624,c_41583])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.67/8.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.67/8.42  
% 16.67/8.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.67/8.42  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 16.67/8.42  
% 16.67/8.42  %Foreground sorts:
% 16.67/8.42  
% 16.67/8.42  
% 16.67/8.42  %Background operators:
% 16.67/8.42  
% 16.67/8.42  
% 16.67/8.42  %Foreground operators:
% 16.67/8.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 16.67/8.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 16.67/8.42  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 16.67/8.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.67/8.42  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 16.67/8.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.67/8.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 16.67/8.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.67/8.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 16.67/8.42  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 16.67/8.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 16.67/8.42  tff('#skF_2', type, '#skF_2': $i).
% 16.67/8.42  tff('#skF_3', type, '#skF_3': $i).
% 16.67/8.42  tff('#skF_1', type, '#skF_1': $i).
% 16.67/8.42  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 16.67/8.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 16.67/8.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.67/8.42  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 16.67/8.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.67/8.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.67/8.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.67/8.42  tff('#skF_4', type, '#skF_4': $i).
% 16.67/8.42  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 16.67/8.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.67/8.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 16.67/8.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 16.67/8.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 16.67/8.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.67/8.42  
% 16.87/8.45  tff(f_196, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 16.87/8.45  tff(f_137, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 16.87/8.45  tff(f_73, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 16.87/8.45  tff(f_81, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 16.87/8.45  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 16.87/8.45  tff(f_135, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 16.87/8.45  tff(f_125, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 16.87/8.45  tff(f_105, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 16.87/8.45  tff(f_103, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 16.87/8.45  tff(f_176, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 16.87/8.45  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 16.87/8.45  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 16.87/8.45  tff(f_154, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 16.87/8.45  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 16.87/8.45  tff(f_113, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 16.87/8.45  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 16.87/8.45  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 16.87/8.45  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.87/8.45  tff(c_68, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_196])).
% 16.87/8.45  tff(c_120, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_68])).
% 16.87/8.45  tff(c_60, plain, (![A_44]: (k6_relat_1(A_44)=k6_partfun1(A_44))), inference(cnfTransformation, [status(thm)], [f_137])).
% 16.87/8.45  tff(c_28, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.87/8.45  tff(c_87, plain, (![A_13]: (k2_relat_1(k6_partfun1(A_13))=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_28])).
% 16.87/8.45  tff(c_32, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 16.87/8.45  tff(c_85, plain, (![A_15]: (v1_relat_1(k6_partfun1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_32])).
% 16.87/8.45  tff(c_131, plain, (![A_66]: (k2_relat_1(A_66)!=k1_xboole_0 | k1_xboole_0=A_66 | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_69])).
% 16.87/8.45  tff(c_134, plain, (![A_15]: (k2_relat_1(k6_partfun1(A_15))!=k1_xboole_0 | k6_partfun1(A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_85, c_131])).
% 16.87/8.45  tff(c_136, plain, (![A_15]: (k1_xboole_0!=A_15 | k6_partfun1(A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_87, c_134])).
% 16.87/8.45  tff(c_70, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_196])).
% 16.87/8.45  tff(c_159, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_136, c_70])).
% 16.87/8.45  tff(c_199, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_159])).
% 16.87/8.45  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_196])).
% 16.87/8.45  tff(c_80, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_196])).
% 16.87/8.45  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_196])).
% 16.87/8.45  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_196])).
% 16.87/8.45  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_196])).
% 16.87/8.45  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_196])).
% 16.87/8.45  tff(c_34, plain, (![A_15]: (v2_funct_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 16.87/8.45  tff(c_84, plain, (![A_15]: (v2_funct_1(k6_partfun1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_34])).
% 16.87/8.45  tff(c_3256, plain, (![D_285, B_281, C_284, E_282, A_280, F_283]: (k1_partfun1(A_280, B_281, C_284, D_285, E_282, F_283)=k5_relat_1(E_282, F_283) | ~m1_subset_1(F_283, k1_zfmisc_1(k2_zfmisc_1(C_284, D_285))) | ~v1_funct_1(F_283) | ~m1_subset_1(E_282, k1_zfmisc_1(k2_zfmisc_1(A_280, B_281))) | ~v1_funct_1(E_282))), inference(cnfTransformation, [status(thm)], [f_135])).
% 16.87/8.45  tff(c_3264, plain, (![A_280, B_281, E_282]: (k1_partfun1(A_280, B_281, '#skF_2', '#skF_1', E_282, '#skF_4')=k5_relat_1(E_282, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_282, k1_zfmisc_1(k2_zfmisc_1(A_280, B_281))) | ~v1_funct_1(E_282))), inference(resolution, [status(thm)], [c_72, c_3256])).
% 16.87/8.45  tff(c_3943, plain, (![A_324, B_325, E_326]: (k1_partfun1(A_324, B_325, '#skF_2', '#skF_1', E_326, '#skF_4')=k5_relat_1(E_326, '#skF_4') | ~m1_subset_1(E_326, k1_zfmisc_1(k2_zfmisc_1(A_324, B_325))) | ~v1_funct_1(E_326))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_3264])).
% 16.87/8.45  tff(c_3961, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_3943])).
% 16.87/8.45  tff(c_3977, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_3961])).
% 16.87/8.45  tff(c_54, plain, (![B_33, C_34, E_36, F_37, A_32, D_35]: (m1_subset_1(k1_partfun1(A_32, B_33, C_34, D_35, E_36, F_37), k1_zfmisc_1(k2_zfmisc_1(A_32, D_35))) | ~m1_subset_1(F_37, k1_zfmisc_1(k2_zfmisc_1(C_34, D_35))) | ~v1_funct_1(F_37) | ~m1_subset_1(E_36, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_1(E_36))), inference(cnfTransformation, [status(thm)], [f_125])).
% 16.87/8.45  tff(c_4022, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3977, c_54])).
% 16.87/8.45  tff(c_4031, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_4022])).
% 16.87/8.45  tff(c_48, plain, (![A_29]: (m1_subset_1(k6_relat_1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 16.87/8.45  tff(c_83, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_48])).
% 16.87/8.45  tff(c_2958, plain, (![D_255, C_256, A_257, B_258]: (D_255=C_256 | ~r2_relset_1(A_257, B_258, C_256, D_255) | ~m1_subset_1(D_255, k1_zfmisc_1(k2_zfmisc_1(A_257, B_258))) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_257, B_258))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 16.87/8.45  tff(c_2972, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_2958])).
% 16.87/8.45  tff(c_2995, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_2972])).
% 16.87/8.45  tff(c_3031, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2995])).
% 16.87/8.45  tff(c_4281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4031, c_3977, c_3031])).
% 16.87/8.45  tff(c_4282, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2995])).
% 16.87/8.45  tff(c_5182, plain, (![D_396, B_395, E_393, A_392, C_394]: (k1_xboole_0=C_394 | v2_funct_1(D_396) | ~v2_funct_1(k1_partfun1(A_392, B_395, B_395, C_394, D_396, E_393)) | ~m1_subset_1(E_393, k1_zfmisc_1(k2_zfmisc_1(B_395, C_394))) | ~v1_funct_2(E_393, B_395, C_394) | ~v1_funct_1(E_393) | ~m1_subset_1(D_396, k1_zfmisc_1(k2_zfmisc_1(A_392, B_395))) | ~v1_funct_2(D_396, A_392, B_395) | ~v1_funct_1(D_396))), inference(cnfTransformation, [status(thm)], [f_176])).
% 16.87/8.45  tff(c_5186, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4282, c_5182])).
% 16.87/8.45  tff(c_5190, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_74, c_72, c_84, c_5186])).
% 16.87/8.45  tff(c_5192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_199, c_5190])).
% 16.87/8.45  tff(c_5194, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_159])).
% 16.87/8.45  tff(c_138, plain, (![A_67]: (k1_xboole_0!=A_67 | k6_partfun1(A_67)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_87, c_134])).
% 16.87/8.45  tff(c_151, plain, (![A_67]: (v2_funct_1(k1_xboole_0) | k1_xboole_0!=A_67)), inference(superposition, [status(thm), theory('equality')], [c_138, c_84])).
% 16.87/8.45  tff(c_174, plain, (![A_67]: (k1_xboole_0!=A_67)), inference(splitLeft, [status(thm)], [c_151])).
% 16.87/8.45  tff(c_181, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_174])).
% 16.87/8.45  tff(c_182, plain, (v2_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_151])).
% 16.87/8.45  tff(c_5197, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5194, c_182])).
% 16.87/8.45  tff(c_144, plain, (![A_67]: (k2_relat_1(k1_xboole_0)=A_67 | k1_xboole_0!=A_67)), inference(superposition, [status(thm), theory('equality')], [c_138, c_87])).
% 16.87/8.45  tff(c_5223, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5194, c_5194, c_144])).
% 16.87/8.45  tff(c_6050, plain, (![E_488, F_489, A_486, D_491, C_490, B_487]: (k1_partfun1(A_486, B_487, C_490, D_491, E_488, F_489)=k5_relat_1(E_488, F_489) | ~m1_subset_1(F_489, k1_zfmisc_1(k2_zfmisc_1(C_490, D_491))) | ~v1_funct_1(F_489) | ~m1_subset_1(E_488, k1_zfmisc_1(k2_zfmisc_1(A_486, B_487))) | ~v1_funct_1(E_488))), inference(cnfTransformation, [status(thm)], [f_135])).
% 16.87/8.45  tff(c_6058, plain, (![A_486, B_487, E_488]: (k1_partfun1(A_486, B_487, '#skF_2', '#skF_1', E_488, '#skF_4')=k5_relat_1(E_488, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_488, k1_zfmisc_1(k2_zfmisc_1(A_486, B_487))) | ~v1_funct_1(E_488))), inference(resolution, [status(thm)], [c_72, c_6050])).
% 16.87/8.45  tff(c_6937, plain, (![A_541, B_542, E_543]: (k1_partfun1(A_541, B_542, '#skF_2', '#skF_1', E_543, '#skF_4')=k5_relat_1(E_543, '#skF_4') | ~m1_subset_1(E_543, k1_zfmisc_1(k2_zfmisc_1(A_541, B_542))) | ~v1_funct_1(E_543))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_6058])).
% 16.87/8.45  tff(c_6955, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_6937])).
% 16.87/8.45  tff(c_6971, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_6955])).
% 16.87/8.45  tff(c_5193, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_159])).
% 16.87/8.45  tff(c_5210, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5194, c_5193])).
% 16.87/8.45  tff(c_7155, plain, (r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6971, c_5210])).
% 16.87/8.45  tff(c_5294, plain, (![C_405, A_406, B_407]: (v1_relat_1(C_405) | ~m1_subset_1(C_405, k1_zfmisc_1(k2_zfmisc_1(A_406, B_407))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 16.87/8.45  tff(c_5307, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_5294])).
% 16.87/8.45  tff(c_22, plain, (![A_12]: (k2_relat_1(A_12)!=k1_xboole_0 | k1_xboole_0=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_69])).
% 16.87/8.45  tff(c_5200, plain, (![A_12]: (k2_relat_1(A_12)!='#skF_1' | A_12='#skF_1' | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_5194, c_5194, c_22])).
% 16.87/8.45  tff(c_5322, plain, (k2_relat_1('#skF_4')!='#skF_1' | '#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_5307, c_5200])).
% 16.87/8.45  tff(c_5334, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_5322])).
% 16.87/8.45  tff(c_5243, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5194, c_5194, c_136])).
% 16.87/8.45  tff(c_5679, plain, (![A_456, B_457, C_458]: (k2_relset_1(A_456, B_457, C_458)=k2_relat_1(C_458) | ~m1_subset_1(C_458, k1_zfmisc_1(k2_zfmisc_1(A_456, B_457))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 16.87/8.45  tff(c_5697, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_5679])).
% 16.87/8.45  tff(c_62, plain, (![A_45, B_46, C_47, D_49]: (k2_relset_1(A_45, B_46, C_47)=B_46 | ~r2_relset_1(B_46, B_46, k1_partfun1(B_46, A_45, A_45, B_46, D_49, C_47), k6_partfun1(B_46)) | ~m1_subset_1(D_49, k1_zfmisc_1(k2_zfmisc_1(B_46, A_45))) | ~v1_funct_2(D_49, B_46, A_45) | ~v1_funct_1(D_49) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))) | ~v1_funct_2(C_47, A_45, B_46) | ~v1_funct_1(C_47))), inference(cnfTransformation, [status(thm)], [f_154])).
% 16.87/8.45  tff(c_7159, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_4'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6971, c_62])).
% 16.87/8.45  tff(c_7168, plain, (k2_relat_1('#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_82, c_80, c_78, c_5243, c_5697, c_7159])).
% 16.87/8.45  tff(c_7169, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_5334, c_7168])).
% 16.87/8.45  tff(c_7183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7155, c_7169])).
% 16.87/8.45  tff(c_7184, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_5322])).
% 16.87/8.45  tff(c_26, plain, (![A_13]: (k1_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.87/8.45  tff(c_88, plain, (![A_13]: (k1_relat_1(k6_partfun1(A_13))=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_26])).
% 16.87/8.45  tff(c_147, plain, (![A_67]: (k1_relat_1(k1_xboole_0)=A_67 | k1_xboole_0!=A_67)), inference(superposition, [status(thm), theory('equality')], [c_138, c_88])).
% 16.87/8.45  tff(c_5195, plain, (![A_67]: (k1_relat_1('#skF_1')=A_67 | A_67!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5194, c_5194, c_147])).
% 16.87/8.45  tff(c_7284, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7184, c_7184, c_5195])).
% 16.87/8.45  tff(c_24, plain, (![A_12]: (k1_relat_1(A_12)!=k1_xboole_0 | k1_xboole_0=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_69])).
% 16.87/8.45  tff(c_5229, plain, (![A_12]: (k1_relat_1(A_12)!='#skF_1' | A_12='#skF_1' | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_5194, c_5194, c_24])).
% 16.87/8.45  tff(c_5323, plain, (k1_relat_1('#skF_4')!='#skF_1' | '#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_5307, c_5229])).
% 16.87/8.45  tff(c_5333, plain, (k1_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_5323])).
% 16.87/8.45  tff(c_7237, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7184, c_5333])).
% 16.87/8.45  tff(c_7287, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7284, c_7237])).
% 16.87/8.45  tff(c_7288, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_5323])).
% 16.87/8.45  tff(c_5306, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_5294])).
% 16.87/8.45  tff(c_5315, plain, (k1_relat_1('#skF_3')!='#skF_1' | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_5306, c_5229])).
% 16.87/8.45  tff(c_5332, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_5315])).
% 16.87/8.45  tff(c_7409, plain, (k1_relat_1('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7288, c_5332])).
% 16.87/8.45  tff(c_7422, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_7288, c_78])).
% 16.87/8.45  tff(c_7613, plain, (![C_576, A_577, B_578]: (v4_relat_1(C_576, A_577) | ~m1_subset_1(C_576, k1_zfmisc_1(k2_zfmisc_1(A_577, B_578))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 16.87/8.45  tff(c_7623, plain, (v4_relat_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_7422, c_7613])).
% 16.87/8.45  tff(c_7289, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_5323])).
% 16.87/8.45  tff(c_7444, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7288, c_7289])).
% 16.87/8.45  tff(c_5199, plain, (![A_15]: (A_15!='#skF_1' | k6_partfun1(A_15)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5194, c_5194, c_136])).
% 16.87/8.45  tff(c_7412, plain, (![A_15]: (A_15!='#skF_4' | k6_partfun1(A_15)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7288, c_7288, c_5199])).
% 16.87/8.45  tff(c_7827, plain, (![C_594, B_595, A_596]: (v5_relat_1(C_594, B_595) | ~m1_subset_1(C_594, k1_zfmisc_1(k2_zfmisc_1(A_596, B_595))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 16.87/8.45  tff(c_7843, plain, (![A_29]: (v5_relat_1(k6_partfun1(A_29), A_29))), inference(resolution, [status(thm)], [c_83, c_7827])).
% 16.87/8.45  tff(c_7848, plain, (![B_598]: (v2_funct_2(B_598, k2_relat_1(B_598)) | ~v5_relat_1(B_598, k2_relat_1(B_598)) | ~v1_relat_1(B_598))), inference(cnfTransformation, [status(thm)], [f_113])).
% 16.87/8.45  tff(c_7854, plain, (![A_13]: (v2_funct_2(k6_partfun1(A_13), k2_relat_1(k6_partfun1(A_13))) | ~v5_relat_1(k6_partfun1(A_13), A_13) | ~v1_relat_1(k6_partfun1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_7848])).
% 16.87/8.45  tff(c_7859, plain, (![A_599]: (v2_funct_2(k6_partfun1(A_599), A_599))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_7843, c_87, c_7854])).
% 16.87/8.45  tff(c_7873, plain, (v2_funct_2('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7412, c_7859])).
% 16.87/8.45  tff(c_7423, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_7288, c_72])).
% 16.87/8.45  tff(c_9082, plain, (![B_675, E_676, F_677, A_674, C_678, D_679]: (k1_partfun1(A_674, B_675, C_678, D_679, E_676, F_677)=k5_relat_1(E_676, F_677) | ~m1_subset_1(F_677, k1_zfmisc_1(k2_zfmisc_1(C_678, D_679))) | ~v1_funct_1(F_677) | ~m1_subset_1(E_676, k1_zfmisc_1(k2_zfmisc_1(A_674, B_675))) | ~v1_funct_1(E_676))), inference(cnfTransformation, [status(thm)], [f_135])).
% 16.87/8.45  tff(c_9088, plain, (![A_674, B_675, E_676]: (k1_partfun1(A_674, B_675, '#skF_2', '#skF_4', E_676, '#skF_4')=k5_relat_1(E_676, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_676, k1_zfmisc_1(k2_zfmisc_1(A_674, B_675))) | ~v1_funct_1(E_676))), inference(resolution, [status(thm)], [c_7423, c_9082])).
% 16.87/8.45  tff(c_9589, plain, (![A_711, B_712, E_713]: (k1_partfun1(A_711, B_712, '#skF_2', '#skF_4', E_713, '#skF_4')=k5_relat_1(E_713, '#skF_4') | ~m1_subset_1(E_713, k1_zfmisc_1(k2_zfmisc_1(A_711, B_712))) | ~v1_funct_1(E_713))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_9088])).
% 16.87/8.45  tff(c_9604, plain, (k1_partfun1('#skF_4', '#skF_2', '#skF_2', '#skF_4', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_7422, c_9589])).
% 16.87/8.45  tff(c_9623, plain, (k1_partfun1('#skF_4', '#skF_2', '#skF_2', '#skF_4', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_9604])).
% 16.87/8.45  tff(c_9698, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9623, c_54])).
% 16.87/8.45  tff(c_9708, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_7422, c_76, c_7423, c_9698])).
% 16.87/8.45  tff(c_7421, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7288, c_5194])).
% 16.87/8.45  tff(c_183, plain, (![A_68]: (m1_subset_1(k6_partfun1(A_68), k1_zfmisc_1(k2_zfmisc_1(A_68, A_68))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_48])).
% 16.87/8.45  tff(c_186, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_15, A_15))) | k1_xboole_0!=A_15)), inference(superposition, [status(thm), theory('equality')], [c_136, c_183])).
% 16.87/8.45  tff(c_7649, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_7421, c_7421, c_186])).
% 16.87/8.45  tff(c_7418, plain, (r2_relset_1('#skF_4', '#skF_4', k1_partfun1('#skF_4', '#skF_2', '#skF_2', '#skF_4', '#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7288, c_7288, c_7288, c_7288, c_7288, c_5210])).
% 16.87/8.45  tff(c_9689, plain, (r2_relset_1('#skF_4', '#skF_4', k5_relat_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9623, c_7418])).
% 16.87/8.45  tff(c_46, plain, (![D_28, C_27, A_25, B_26]: (D_28=C_27 | ~r2_relset_1(A_25, B_26, C_27, D_28) | ~m1_subset_1(D_28, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 16.87/8.45  tff(c_9711, plain, (k5_relat_1('#skF_3', '#skF_4')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(resolution, [status(thm)], [c_9689, c_46])).
% 16.87/8.45  tff(c_9714, plain, (k5_relat_1('#skF_3', '#skF_4')='#skF_4' | ~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_7649, c_9711])).
% 16.87/8.45  tff(c_39408, plain, (k5_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9708, c_9714])).
% 16.87/8.45  tff(c_36, plain, (![C_18, A_16, B_17]: (v1_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 16.87/8.45  tff(c_9767, plain, (v1_relat_1(k5_relat_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_9708, c_36])).
% 16.87/8.45  tff(c_7411, plain, (![A_12]: (k2_relat_1(A_12)!='#skF_4' | A_12='#skF_4' | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_7288, c_7288, c_5200])).
% 16.87/8.45  tff(c_9789, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_4'))!='#skF_4' | k5_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_9767, c_7411])).
% 16.87/8.45  tff(c_9994, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_9789])).
% 16.87/8.45  tff(c_38, plain, (![C_21, B_20, A_19]: (v5_relat_1(C_21, B_20) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 16.87/8.45  tff(c_9765, plain, (v5_relat_1(k5_relat_1('#skF_3', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_9708, c_38])).
% 16.87/8.45  tff(c_52, plain, (![B_31, A_30]: (k2_relat_1(B_31)=A_30 | ~v2_funct_2(B_31, A_30) | ~v5_relat_1(B_31, A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_113])).
% 16.87/8.45  tff(c_9793, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_4'))='#skF_4' | ~v2_funct_2(k5_relat_1('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1(k5_relat_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_9765, c_52])).
% 16.87/8.45  tff(c_9796, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_4'))='#skF_4' | ~v2_funct_2(k5_relat_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9767, c_9793])).
% 16.87/8.45  tff(c_10928, plain, (~v2_funct_2(k5_relat_1('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_9994, c_9796])).
% 16.87/8.45  tff(c_39423, plain, (~v2_funct_2('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_39408, c_10928])).
% 16.87/8.45  tff(c_39446, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7873, c_39423])).
% 16.87/8.45  tff(c_39447, plain, (k5_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_9789])).
% 16.87/8.45  tff(c_7413, plain, (![A_12]: (k1_relat_1(A_12)!='#skF_4' | A_12='#skF_4' | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_7288, c_7288, c_5229])).
% 16.87/8.45  tff(c_9790, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_4'))!='#skF_4' | k5_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_9767, c_7413])).
% 16.87/8.45  tff(c_9993, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_9790])).
% 16.87/8.45  tff(c_39525, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_39447, c_9993])).
% 16.87/8.45  tff(c_39537, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7444, c_39525])).
% 16.87/8.45  tff(c_39538, plain, (k5_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_9790])).
% 16.87/8.45  tff(c_20, plain, (![A_9, B_11]: (r1_tarski(k1_relat_1(k5_relat_1(A_9, B_11)), k1_relat_1(A_9)) | ~v1_relat_1(B_11) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_61])).
% 16.87/8.45  tff(c_39565, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_39538, c_20])).
% 16.87/8.45  tff(c_39579, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5306, c_5307, c_7444, c_39565])).
% 16.87/8.45  tff(c_7709, plain, (![B_585, A_586]: (r1_tarski(k1_relat_1(B_585), A_586) | ~v4_relat_1(B_585, A_586) | ~v1_relat_1(B_585))), inference(cnfTransformation, [status(thm)], [f_46])).
% 16.87/8.45  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.87/8.45  tff(c_7722, plain, (![B_585, A_586]: (k1_relat_1(B_585)=A_586 | ~r1_tarski(A_586, k1_relat_1(B_585)) | ~v4_relat_1(B_585, A_586) | ~v1_relat_1(B_585))), inference(resolution, [status(thm)], [c_7709, c_4])).
% 16.87/8.45  tff(c_39587, plain, (k1_relat_1('#skF_3')='#skF_4' | ~v4_relat_1('#skF_3', '#skF_4') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_39579, c_7722])).
% 16.87/8.45  tff(c_39596, plain, (k1_relat_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5306, c_7623, c_39587])).
% 16.87/8.45  tff(c_39598, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7409, c_39596])).
% 16.87/8.45  tff(c_39599, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_5315])).
% 16.87/8.45  tff(c_5314, plain, (k2_relat_1('#skF_3')!='#skF_1' | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_5306, c_5200])).
% 16.87/8.45  tff(c_5324, plain, (k2_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_5314])).
% 16.87/8.45  tff(c_39602, plain, (k2_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_39599, c_5324])).
% 16.87/8.45  tff(c_39611, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5223, c_39602])).
% 16.87/8.45  tff(c_39612, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_5314])).
% 16.87/8.45  tff(c_39617, plain, (~v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_39612, c_120])).
% 16.87/8.45  tff(c_39623, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5197, c_39617])).
% 16.87/8.45  tff(c_39624, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_68])).
% 16.87/8.45  tff(c_39725, plain, (![C_1306, A_1307, B_1308]: (v1_relat_1(C_1306) | ~m1_subset_1(C_1306, k1_zfmisc_1(k2_zfmisc_1(A_1307, B_1308))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 16.87/8.45  tff(c_39738, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_39725])).
% 16.87/8.45  tff(c_39823, plain, (![C_1315, B_1316, A_1317]: (v5_relat_1(C_1315, B_1316) | ~m1_subset_1(C_1315, k1_zfmisc_1(k2_zfmisc_1(A_1317, B_1316))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 16.87/8.45  tff(c_39835, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_39823])).
% 16.87/8.45  tff(c_40284, plain, (![A_1366, B_1367, C_1368]: (k2_relset_1(A_1366, B_1367, C_1368)=k2_relat_1(C_1368) | ~m1_subset_1(C_1368, k1_zfmisc_1(k2_zfmisc_1(A_1366, B_1367))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 16.87/8.45  tff(c_40302, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_40284])).
% 16.87/8.45  tff(c_41553, plain, (![A_1449, B_1450, C_1451, D_1452]: (k2_relset_1(A_1449, B_1450, C_1451)=B_1450 | ~r2_relset_1(B_1450, B_1450, k1_partfun1(B_1450, A_1449, A_1449, B_1450, D_1452, C_1451), k6_partfun1(B_1450)) | ~m1_subset_1(D_1452, k1_zfmisc_1(k2_zfmisc_1(B_1450, A_1449))) | ~v1_funct_2(D_1452, B_1450, A_1449) | ~v1_funct_1(D_1452) | ~m1_subset_1(C_1451, k1_zfmisc_1(k2_zfmisc_1(A_1449, B_1450))) | ~v1_funct_2(C_1451, A_1449, B_1450) | ~v1_funct_1(C_1451))), inference(cnfTransformation, [status(thm)], [f_154])).
% 16.87/8.45  tff(c_41568, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_41553])).
% 16.87/8.45  tff(c_41573, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_82, c_80, c_78, c_40302, c_41568])).
% 16.87/8.45  tff(c_50, plain, (![B_31]: (v2_funct_2(B_31, k2_relat_1(B_31)) | ~v5_relat_1(B_31, k2_relat_1(B_31)) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_113])).
% 16.87/8.45  tff(c_41579, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_41573, c_50])).
% 16.87/8.45  tff(c_41583, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_39738, c_39835, c_41573, c_41579])).
% 16.87/8.45  tff(c_41585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39624, c_41583])).
% 16.87/8.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.87/8.45  
% 16.87/8.45  Inference rules
% 16.87/8.45  ----------------------
% 16.87/8.45  #Ref     : 33
% 16.87/8.45  #Sup     : 10277
% 16.87/8.45  #Fact    : 0
% 16.87/8.45  #Define  : 0
% 16.87/8.45  #Split   : 86
% 16.87/8.45  #Chain   : 0
% 16.87/8.45  #Close   : 0
% 16.87/8.45  
% 16.87/8.45  Ordering : KBO
% 16.87/8.45  
% 16.87/8.45  Simplification rules
% 16.87/8.45  ----------------------
% 16.87/8.45  #Subsume      : 7722
% 16.87/8.45  #Demod        : 6359
% 16.87/8.45  #Tautology    : 1622
% 16.87/8.45  #SimpNegUnit  : 1911
% 16.87/8.45  #BackRed      : 1407
% 16.87/8.45  
% 16.87/8.45  #Partial instantiations: 0
% 16.87/8.45  #Strategies tried      : 1
% 16.87/8.45  
% 16.87/8.45  Timing (in seconds)
% 16.87/8.45  ----------------------
% 16.87/8.45  Preprocessing        : 0.38
% 16.87/8.45  Parsing              : 0.21
% 16.87/8.45  CNF conversion       : 0.03
% 16.87/8.45  Main loop            : 7.19
% 16.87/8.45  Inferencing          : 1.28
% 16.87/8.45  Reduction            : 3.05
% 16.87/8.45  Demodulation         : 2.43
% 16.87/8.45  BG Simplification    : 0.13
% 16.87/8.45  Subsumption          : 2.36
% 16.87/8.45  Abstraction          : 0.18
% 16.87/8.45  MUC search           : 0.00
% 16.87/8.45  Cooper               : 0.00
% 16.87/8.45  Total                : 7.63
% 16.87/8.45  Index Insertion      : 0.00
% 16.87/8.45  Index Deletion       : 0.00
% 16.87/8.45  Index Matching       : 0.00
% 16.87/8.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
