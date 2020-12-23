%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:06 EST 2020

% Result     : Theorem 6.29s
% Output     : CNFRefutation 6.62s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 339 expanded)
%              Number of leaves         :   46 ( 136 expanded)
%              Depth                    :   12
%              Number of atoms          :  255 (1011 expanded)
%              Number of equality atoms :   50 ( 109 expanded)
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

tff(f_163,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_121,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_119,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_109,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_89,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_143,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_58,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_58,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_142,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_338,plain,(
    ! [C_83,A_84,B_85] :
      ( v1_xboole_0(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_355,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_338])).

tff(c_358,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_355])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_70,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_52,plain,(
    ! [A_41] : k6_relat_1(A_41) = k6_partfun1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_26,plain,(
    ! [A_11] : v2_funct_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_74,plain,(
    ! [A_11] : v2_funct_1(k6_partfun1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_26])).

tff(c_836,plain,(
    ! [A_134,D_138,F_135,C_136,E_137,B_139] :
      ( k1_partfun1(A_134,B_139,C_136,D_138,E_137,F_135) = k5_relat_1(E_137,F_135)
      | ~ m1_subset_1(F_135,k1_zfmisc_1(k2_zfmisc_1(C_136,D_138)))
      | ~ v1_funct_1(F_135)
      | ~ m1_subset_1(E_137,k1_zfmisc_1(k2_zfmisc_1(A_134,B_139)))
      | ~ v1_funct_1(E_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_846,plain,(
    ! [A_134,B_139,E_137] :
      ( k1_partfun1(A_134,B_139,'#skF_2','#skF_1',E_137,'#skF_4') = k5_relat_1(E_137,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_137,k1_zfmisc_1(k2_zfmisc_1(A_134,B_139)))
      | ~ v1_funct_1(E_137) ) ),
    inference(resolution,[status(thm)],[c_62,c_836])).

tff(c_1632,plain,(
    ! [A_176,B_177,E_178] :
      ( k1_partfun1(A_176,B_177,'#skF_2','#skF_1',E_178,'#skF_4') = k5_relat_1(E_178,'#skF_4')
      | ~ m1_subset_1(E_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177)))
      | ~ v1_funct_1(E_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_846])).

tff(c_1653,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1632])).

tff(c_1669,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1653])).

tff(c_46,plain,(
    ! [E_33,A_29,F_34,D_32,C_31,B_30] :
      ( m1_subset_1(k1_partfun1(A_29,B_30,C_31,D_32,E_33,F_34),k1_zfmisc_1(k2_zfmisc_1(A_29,D_32)))
      | ~ m1_subset_1(F_34,k1_zfmisc_1(k2_zfmisc_1(C_31,D_32)))
      | ~ v1_funct_1(F_34)
      | ~ m1_subset_1(E_33,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ v1_funct_1(E_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1680,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1669,c_46])).

tff(c_1687,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_1680])).

tff(c_40,plain,(
    ! [A_26] : m1_subset_1(k6_relat_1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_73,plain,(
    ! [A_26] : m1_subset_1(k6_partfun1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_40])).

tff(c_60,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_578,plain,(
    ! [D_102,C_103,A_104,B_105] :
      ( D_102 = C_103
      | ~ r2_relset_1(A_104,B_105,C_103,D_102)
      | ~ m1_subset_1(D_102,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105)))
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_586,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_578])).

tff(c_601,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_586])).

tff(c_643,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_601])).

tff(c_1877,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1687,c_1669,c_643])).

tff(c_1878,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_601])).

tff(c_2871,plain,(
    ! [E_249,B_247,A_248,C_250,D_246] :
      ( k1_xboole_0 = C_250
      | v2_funct_1(D_246)
      | ~ v2_funct_1(k1_partfun1(A_248,B_247,B_247,C_250,D_246,E_249))
      | ~ m1_subset_1(E_249,k1_zfmisc_1(k2_zfmisc_1(B_247,C_250)))
      | ~ v1_funct_2(E_249,B_247,C_250)
      | ~ v1_funct_1(E_249)
      | ~ m1_subset_1(D_246,k1_zfmisc_1(k2_zfmisc_1(A_248,B_247)))
      | ~ v1_funct_2(D_246,A_248,B_247)
      | ~ v1_funct_1(D_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2875,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1878,c_2871])).

tff(c_2879,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_64,c_62,c_74,c_2875])).

tff(c_2880,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_2879])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_2914,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2880,c_2])).

tff(c_2916,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_358,c_2914])).

tff(c_2917,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_355])).

tff(c_143,plain,(
    ! [B_55,A_56] :
      ( ~ v1_xboole_0(B_55)
      | B_55 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_146,plain,(
    ! [A_56] :
      ( k1_xboole_0 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_2,c_143])).

tff(c_2924,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2917,c_146])).

tff(c_95,plain,(
    ! [A_53] : k6_relat_1(A_53) = k6_partfun1(A_53) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_22,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_101,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_22])).

tff(c_117,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_74])).

tff(c_2943,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2924,c_117])).

tff(c_2949,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_2943])).

tff(c_2950,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2973,plain,(
    ! [C_257,A_258,B_259] :
      ( v1_relat_1(C_257)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_258,B_259))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2991,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_2973])).

tff(c_3033,plain,(
    ! [C_269,B_270,A_271] :
      ( v5_relat_1(C_269,B_270)
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1(A_271,B_270))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3049,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_3033])).

tff(c_14,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k2_relat_1(B_6),A_5)
      | ~ v5_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2990,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2973])).

tff(c_20,plain,(
    ! [A_10] : k2_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_76,plain,(
    ! [A_10] : k2_relat_1(k6_partfun1(A_10)) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_20])).

tff(c_3628,plain,(
    ! [A_330,C_332,F_331,E_333,D_334,B_335] :
      ( k1_partfun1(A_330,B_335,C_332,D_334,E_333,F_331) = k5_relat_1(E_333,F_331)
      | ~ m1_subset_1(F_331,k1_zfmisc_1(k2_zfmisc_1(C_332,D_334)))
      | ~ v1_funct_1(F_331)
      | ~ m1_subset_1(E_333,k1_zfmisc_1(k2_zfmisc_1(A_330,B_335)))
      | ~ v1_funct_1(E_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_3638,plain,(
    ! [A_330,B_335,E_333] :
      ( k1_partfun1(A_330,B_335,'#skF_2','#skF_1',E_333,'#skF_4') = k5_relat_1(E_333,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_333,k1_zfmisc_1(k2_zfmisc_1(A_330,B_335)))
      | ~ v1_funct_1(E_333) ) ),
    inference(resolution,[status(thm)],[c_62,c_3628])).

tff(c_4224,plain,(
    ! [A_359,B_360,E_361] :
      ( k1_partfun1(A_359,B_360,'#skF_2','#skF_1',E_361,'#skF_4') = k5_relat_1(E_361,'#skF_4')
      | ~ m1_subset_1(E_361,k1_zfmisc_1(k2_zfmisc_1(A_359,B_360)))
      | ~ v1_funct_1(E_361) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3638])).

tff(c_4239,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_4224])).

tff(c_4249,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4239])).

tff(c_4284,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4249,c_46])).

tff(c_4288,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_4284])).

tff(c_3366,plain,(
    ! [D_297,C_298,A_299,B_300] :
      ( D_297 = C_298
      | ~ r2_relset_1(A_299,B_300,C_298,D_297)
      | ~ m1_subset_1(D_297,k1_zfmisc_1(k2_zfmisc_1(A_299,B_300)))
      | ~ m1_subset_1(C_298,k1_zfmisc_1(k2_zfmisc_1(A_299,B_300))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3374,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_3366])).

tff(c_3389,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_3374])).

tff(c_3435,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_3389])).

tff(c_4706,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4288,c_4249,c_3435])).

tff(c_4707,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3389])).

tff(c_5206,plain,(
    ! [B_414,A_409,D_413,F_410,C_411,E_412] :
      ( k1_partfun1(A_409,B_414,C_411,D_413,E_412,F_410) = k5_relat_1(E_412,F_410)
      | ~ m1_subset_1(F_410,k1_zfmisc_1(k2_zfmisc_1(C_411,D_413)))
      | ~ v1_funct_1(F_410)
      | ~ m1_subset_1(E_412,k1_zfmisc_1(k2_zfmisc_1(A_409,B_414)))
      | ~ v1_funct_1(E_412) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_5216,plain,(
    ! [A_409,B_414,E_412] :
      ( k1_partfun1(A_409,B_414,'#skF_2','#skF_1',E_412,'#skF_4') = k5_relat_1(E_412,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_412,k1_zfmisc_1(k2_zfmisc_1(A_409,B_414)))
      | ~ v1_funct_1(E_412) ) ),
    inference(resolution,[status(thm)],[c_62,c_5206])).

tff(c_5534,plain,(
    ! [A_434,B_435,E_436] :
      ( k1_partfun1(A_434,B_435,'#skF_2','#skF_1',E_436,'#skF_4') = k5_relat_1(E_436,'#skF_4')
      | ~ m1_subset_1(E_436,k1_zfmisc_1(k2_zfmisc_1(A_434,B_435)))
      | ~ v1_funct_1(E_436) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5216])).

tff(c_5549,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_5534])).

tff(c_5559,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4707,c_5549])).

tff(c_16,plain,(
    ! [A_7,B_9] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_7,B_9)),k2_relat_1(B_9))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5566,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5559,c_16])).

tff(c_5570,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2990,c_2991,c_76,c_5566])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5574,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_5570,c_4])).

tff(c_5575,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5574])).

tff(c_5578,plain,
    ( ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_5575])).

tff(c_5582,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2991,c_3049,c_5578])).

tff(c_5583,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5574])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3050,plain,(
    ! [B_272,A_273] :
      ( v5_relat_1(B_272,A_273)
      | ~ r1_tarski(k2_relat_1(B_272),A_273)
      | ~ v1_relat_1(B_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3163,plain,(
    ! [B_284] :
      ( v5_relat_1(B_284,k2_relat_1(B_284))
      | ~ v1_relat_1(B_284) ) ),
    inference(resolution,[status(thm)],[c_8,c_3050])).

tff(c_42,plain,(
    ! [B_28] :
      ( v2_funct_2(B_28,k2_relat_1(B_28))
      | ~ v5_relat_1(B_28,k2_relat_1(B_28))
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_3181,plain,(
    ! [B_284] :
      ( v2_funct_2(B_284,k2_relat_1(B_284))
      | ~ v1_relat_1(B_284) ) ),
    inference(resolution,[status(thm)],[c_3163,c_42])).

tff(c_5590,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5583,c_3181])).

tff(c_5606,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2991,c_5590])).

tff(c_5608,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2950,c_5606])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:09:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.29/2.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.62/2.31  
% 6.62/2.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.62/2.31  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.62/2.31  
% 6.62/2.31  %Foreground sorts:
% 6.62/2.31  
% 6.62/2.31  
% 6.62/2.31  %Background operators:
% 6.62/2.31  
% 6.62/2.31  
% 6.62/2.31  %Foreground operators:
% 6.62/2.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.62/2.31  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.62/2.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.62/2.31  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.62/2.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.62/2.31  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.62/2.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.62/2.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.62/2.31  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.62/2.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.62/2.31  tff('#skF_2', type, '#skF_2': $i).
% 6.62/2.31  tff('#skF_3', type, '#skF_3': $i).
% 6.62/2.31  tff('#skF_1', type, '#skF_1': $i).
% 6.62/2.31  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.62/2.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.62/2.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.62/2.31  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.62/2.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.62/2.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.62/2.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.62/2.31  tff('#skF_4', type, '#skF_4': $i).
% 6.62/2.31  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.62/2.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.62/2.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.62/2.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.62/2.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.62/2.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.62/2.31  
% 6.62/2.33  tff(f_163, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 6.62/2.33  tff(f_79, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 6.62/2.33  tff(f_121, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.62/2.33  tff(f_62, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.62/2.33  tff(f_119, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.62/2.33  tff(f_109, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.62/2.33  tff(f_89, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 6.62/2.33  tff(f_87, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.62/2.33  tff(f_143, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 6.62/2.34  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.62/2.34  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 6.62/2.34  tff(f_58, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 6.62/2.34  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.62/2.34  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.62/2.34  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 6.62/2.34  tff(f_57, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 6.62/2.34  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 6.62/2.34  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.62/2.34  tff(f_97, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 6.62/2.34  tff(c_58, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.62/2.34  tff(c_142, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_58])).
% 6.62/2.34  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.62/2.34  tff(c_338, plain, (![C_83, A_84, B_85]: (v1_xboole_0(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.62/2.34  tff(c_355, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_338])).
% 6.62/2.34  tff(c_358, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_355])).
% 6.62/2.34  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.62/2.34  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.62/2.34  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.62/2.34  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.62/2.34  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.62/2.34  tff(c_52, plain, (![A_41]: (k6_relat_1(A_41)=k6_partfun1(A_41))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.62/2.34  tff(c_26, plain, (![A_11]: (v2_funct_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.62/2.34  tff(c_74, plain, (![A_11]: (v2_funct_1(k6_partfun1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_26])).
% 6.62/2.34  tff(c_836, plain, (![A_134, D_138, F_135, C_136, E_137, B_139]: (k1_partfun1(A_134, B_139, C_136, D_138, E_137, F_135)=k5_relat_1(E_137, F_135) | ~m1_subset_1(F_135, k1_zfmisc_1(k2_zfmisc_1(C_136, D_138))) | ~v1_funct_1(F_135) | ~m1_subset_1(E_137, k1_zfmisc_1(k2_zfmisc_1(A_134, B_139))) | ~v1_funct_1(E_137))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.62/2.34  tff(c_846, plain, (![A_134, B_139, E_137]: (k1_partfun1(A_134, B_139, '#skF_2', '#skF_1', E_137, '#skF_4')=k5_relat_1(E_137, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_137, k1_zfmisc_1(k2_zfmisc_1(A_134, B_139))) | ~v1_funct_1(E_137))), inference(resolution, [status(thm)], [c_62, c_836])).
% 6.62/2.34  tff(c_1632, plain, (![A_176, B_177, E_178]: (k1_partfun1(A_176, B_177, '#skF_2', '#skF_1', E_178, '#skF_4')=k5_relat_1(E_178, '#skF_4') | ~m1_subset_1(E_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))) | ~v1_funct_1(E_178))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_846])).
% 6.62/2.34  tff(c_1653, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1632])).
% 6.62/2.34  tff(c_1669, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1653])).
% 6.62/2.34  tff(c_46, plain, (![E_33, A_29, F_34, D_32, C_31, B_30]: (m1_subset_1(k1_partfun1(A_29, B_30, C_31, D_32, E_33, F_34), k1_zfmisc_1(k2_zfmisc_1(A_29, D_32))) | ~m1_subset_1(F_34, k1_zfmisc_1(k2_zfmisc_1(C_31, D_32))) | ~v1_funct_1(F_34) | ~m1_subset_1(E_33, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~v1_funct_1(E_33))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.62/2.34  tff(c_1680, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1669, c_46])).
% 6.62/2.34  tff(c_1687, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_1680])).
% 6.62/2.34  tff(c_40, plain, (![A_26]: (m1_subset_1(k6_relat_1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.62/2.34  tff(c_73, plain, (![A_26]: (m1_subset_1(k6_partfun1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_40])).
% 6.62/2.34  tff(c_60, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.62/2.34  tff(c_578, plain, (![D_102, C_103, A_104, B_105]: (D_102=C_103 | ~r2_relset_1(A_104, B_105, C_103, D_102) | ~m1_subset_1(D_102, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.62/2.34  tff(c_586, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_578])).
% 6.62/2.34  tff(c_601, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_586])).
% 6.62/2.34  tff(c_643, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_601])).
% 6.62/2.34  tff(c_1877, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1687, c_1669, c_643])).
% 6.62/2.34  tff(c_1878, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_601])).
% 6.62/2.34  tff(c_2871, plain, (![E_249, B_247, A_248, C_250, D_246]: (k1_xboole_0=C_250 | v2_funct_1(D_246) | ~v2_funct_1(k1_partfun1(A_248, B_247, B_247, C_250, D_246, E_249)) | ~m1_subset_1(E_249, k1_zfmisc_1(k2_zfmisc_1(B_247, C_250))) | ~v1_funct_2(E_249, B_247, C_250) | ~v1_funct_1(E_249) | ~m1_subset_1(D_246, k1_zfmisc_1(k2_zfmisc_1(A_248, B_247))) | ~v1_funct_2(D_246, A_248, B_247) | ~v1_funct_1(D_246))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.62/2.34  tff(c_2875, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1878, c_2871])).
% 6.62/2.34  tff(c_2879, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_64, c_62, c_74, c_2875])).
% 6.62/2.34  tff(c_2880, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_142, c_2879])).
% 6.62/2.34  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.62/2.34  tff(c_2914, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2880, c_2])).
% 6.62/2.34  tff(c_2916, plain, $false, inference(negUnitSimplification, [status(thm)], [c_358, c_2914])).
% 6.62/2.34  tff(c_2917, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_355])).
% 6.62/2.34  tff(c_143, plain, (![B_55, A_56]: (~v1_xboole_0(B_55) | B_55=A_56 | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.62/2.34  tff(c_146, plain, (![A_56]: (k1_xboole_0=A_56 | ~v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_2, c_143])).
% 6.62/2.34  tff(c_2924, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2917, c_146])).
% 6.62/2.34  tff(c_95, plain, (![A_53]: (k6_relat_1(A_53)=k6_partfun1(A_53))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.62/2.34  tff(c_22, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.62/2.34  tff(c_101, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_95, c_22])).
% 6.62/2.34  tff(c_117, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_101, c_74])).
% 6.62/2.34  tff(c_2943, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2924, c_117])).
% 6.62/2.34  tff(c_2949, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_2943])).
% 6.62/2.34  tff(c_2950, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 6.62/2.34  tff(c_2973, plain, (![C_257, A_258, B_259]: (v1_relat_1(C_257) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(A_258, B_259))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.62/2.34  tff(c_2991, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_2973])).
% 6.62/2.34  tff(c_3033, plain, (![C_269, B_270, A_271]: (v5_relat_1(C_269, B_270) | ~m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1(A_271, B_270))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.62/2.34  tff(c_3049, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_3033])).
% 6.62/2.34  tff(c_14, plain, (![B_6, A_5]: (r1_tarski(k2_relat_1(B_6), A_5) | ~v5_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.62/2.34  tff(c_2990, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_2973])).
% 6.62/2.34  tff(c_20, plain, (![A_10]: (k2_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.62/2.34  tff(c_76, plain, (![A_10]: (k2_relat_1(k6_partfun1(A_10))=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_20])).
% 6.62/2.34  tff(c_3628, plain, (![A_330, C_332, F_331, E_333, D_334, B_335]: (k1_partfun1(A_330, B_335, C_332, D_334, E_333, F_331)=k5_relat_1(E_333, F_331) | ~m1_subset_1(F_331, k1_zfmisc_1(k2_zfmisc_1(C_332, D_334))) | ~v1_funct_1(F_331) | ~m1_subset_1(E_333, k1_zfmisc_1(k2_zfmisc_1(A_330, B_335))) | ~v1_funct_1(E_333))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.62/2.34  tff(c_3638, plain, (![A_330, B_335, E_333]: (k1_partfun1(A_330, B_335, '#skF_2', '#skF_1', E_333, '#skF_4')=k5_relat_1(E_333, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_333, k1_zfmisc_1(k2_zfmisc_1(A_330, B_335))) | ~v1_funct_1(E_333))), inference(resolution, [status(thm)], [c_62, c_3628])).
% 6.62/2.34  tff(c_4224, plain, (![A_359, B_360, E_361]: (k1_partfun1(A_359, B_360, '#skF_2', '#skF_1', E_361, '#skF_4')=k5_relat_1(E_361, '#skF_4') | ~m1_subset_1(E_361, k1_zfmisc_1(k2_zfmisc_1(A_359, B_360))) | ~v1_funct_1(E_361))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3638])).
% 6.62/2.34  tff(c_4239, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_4224])).
% 6.62/2.34  tff(c_4249, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4239])).
% 6.62/2.34  tff(c_4284, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4249, c_46])).
% 6.62/2.34  tff(c_4288, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_4284])).
% 6.62/2.34  tff(c_3366, plain, (![D_297, C_298, A_299, B_300]: (D_297=C_298 | ~r2_relset_1(A_299, B_300, C_298, D_297) | ~m1_subset_1(D_297, k1_zfmisc_1(k2_zfmisc_1(A_299, B_300))) | ~m1_subset_1(C_298, k1_zfmisc_1(k2_zfmisc_1(A_299, B_300))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.62/2.34  tff(c_3374, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_3366])).
% 6.62/2.34  tff(c_3389, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_3374])).
% 6.62/2.34  tff(c_3435, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_3389])).
% 6.62/2.34  tff(c_4706, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4288, c_4249, c_3435])).
% 6.62/2.34  tff(c_4707, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_3389])).
% 6.62/2.34  tff(c_5206, plain, (![B_414, A_409, D_413, F_410, C_411, E_412]: (k1_partfun1(A_409, B_414, C_411, D_413, E_412, F_410)=k5_relat_1(E_412, F_410) | ~m1_subset_1(F_410, k1_zfmisc_1(k2_zfmisc_1(C_411, D_413))) | ~v1_funct_1(F_410) | ~m1_subset_1(E_412, k1_zfmisc_1(k2_zfmisc_1(A_409, B_414))) | ~v1_funct_1(E_412))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.62/2.34  tff(c_5216, plain, (![A_409, B_414, E_412]: (k1_partfun1(A_409, B_414, '#skF_2', '#skF_1', E_412, '#skF_4')=k5_relat_1(E_412, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_412, k1_zfmisc_1(k2_zfmisc_1(A_409, B_414))) | ~v1_funct_1(E_412))), inference(resolution, [status(thm)], [c_62, c_5206])).
% 6.62/2.34  tff(c_5534, plain, (![A_434, B_435, E_436]: (k1_partfun1(A_434, B_435, '#skF_2', '#skF_1', E_436, '#skF_4')=k5_relat_1(E_436, '#skF_4') | ~m1_subset_1(E_436, k1_zfmisc_1(k2_zfmisc_1(A_434, B_435))) | ~v1_funct_1(E_436))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_5216])).
% 6.62/2.34  tff(c_5549, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_5534])).
% 6.62/2.34  tff(c_5559, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4707, c_5549])).
% 6.62/2.34  tff(c_16, plain, (![A_7, B_9]: (r1_tarski(k2_relat_1(k5_relat_1(A_7, B_9)), k2_relat_1(B_9)) | ~v1_relat_1(B_9) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.62/2.34  tff(c_5566, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5559, c_16])).
% 6.62/2.34  tff(c_5570, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2990, c_2991, c_76, c_5566])).
% 6.62/2.34  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.62/2.34  tff(c_5574, plain, (k2_relat_1('#skF_4')='#skF_1' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_5570, c_4])).
% 6.62/2.34  tff(c_5575, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_5574])).
% 6.62/2.34  tff(c_5578, plain, (~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_5575])).
% 6.62/2.34  tff(c_5582, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2991, c_3049, c_5578])).
% 6.62/2.34  tff(c_5583, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_5574])).
% 6.62/2.34  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.62/2.34  tff(c_3050, plain, (![B_272, A_273]: (v5_relat_1(B_272, A_273) | ~r1_tarski(k2_relat_1(B_272), A_273) | ~v1_relat_1(B_272))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.62/2.34  tff(c_3163, plain, (![B_284]: (v5_relat_1(B_284, k2_relat_1(B_284)) | ~v1_relat_1(B_284))), inference(resolution, [status(thm)], [c_8, c_3050])).
% 6.62/2.34  tff(c_42, plain, (![B_28]: (v2_funct_2(B_28, k2_relat_1(B_28)) | ~v5_relat_1(B_28, k2_relat_1(B_28)) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.62/2.34  tff(c_3181, plain, (![B_284]: (v2_funct_2(B_284, k2_relat_1(B_284)) | ~v1_relat_1(B_284))), inference(resolution, [status(thm)], [c_3163, c_42])).
% 6.62/2.34  tff(c_5590, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5583, c_3181])).
% 6.62/2.34  tff(c_5606, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2991, c_5590])).
% 6.62/2.34  tff(c_5608, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2950, c_5606])).
% 6.62/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.62/2.34  
% 6.62/2.34  Inference rules
% 6.62/2.34  ----------------------
% 6.62/2.34  #Ref     : 0
% 6.62/2.34  #Sup     : 1353
% 6.62/2.34  #Fact    : 0
% 6.62/2.34  #Define  : 0
% 6.62/2.34  #Split   : 20
% 6.62/2.34  #Chain   : 0
% 6.62/2.34  #Close   : 0
% 6.62/2.34  
% 6.62/2.34  Ordering : KBO
% 6.62/2.34  
% 6.62/2.34  Simplification rules
% 6.62/2.34  ----------------------
% 6.62/2.34  #Subsume      : 328
% 6.62/2.34  #Demod        : 843
% 6.62/2.34  #Tautology    : 270
% 6.62/2.34  #SimpNegUnit  : 5
% 6.62/2.34  #BackRed      : 63
% 6.62/2.34  
% 6.62/2.34  #Partial instantiations: 0
% 6.62/2.34  #Strategies tried      : 1
% 6.62/2.34  
% 6.62/2.34  Timing (in seconds)
% 6.62/2.34  ----------------------
% 6.62/2.34  Preprocessing        : 0.36
% 6.62/2.34  Parsing              : 0.20
% 6.62/2.34  CNF conversion       : 0.02
% 6.62/2.34  Main loop            : 1.17
% 6.62/2.34  Inferencing          : 0.38
% 6.62/2.34  Reduction            : 0.41
% 6.62/2.34  Demodulation         : 0.30
% 6.62/2.34  BG Simplification    : 0.04
% 6.62/2.34  Subsumption          : 0.25
% 6.62/2.34  Abstraction          : 0.05
% 6.62/2.34  MUC search           : 0.00
% 6.62/2.34  Cooper               : 0.00
% 6.62/2.34  Total                : 1.58
% 6.62/2.34  Index Insertion      : 0.00
% 6.62/2.34  Index Deletion       : 0.00
% 6.62/2.34  Index Matching       : 0.00
% 6.62/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
