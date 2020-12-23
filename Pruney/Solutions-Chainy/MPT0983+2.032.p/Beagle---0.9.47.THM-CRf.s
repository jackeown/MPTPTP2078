%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:05 EST 2020

% Result     : Theorem 6.02s
% Output     : CNFRefutation 6.02s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 668 expanded)
%              Number of leaves         :   46 ( 247 expanded)
%              Depth                    :   12
%              Number of atoms          :  251 (2099 expanded)
%              Number of equality atoms :   65 ( 250 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_108,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_167,negated_conjecture,(
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

tff(f_78,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_88,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_147,axiom,(
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
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_48,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_125,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_44,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_18,plain,(
    ! [A_8] : v2_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_68,plain,(
    ! [A_8] : v2_funct_1(k6_partfun1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_18])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_1075,plain,(
    ! [A_174,F_173,C_170,D_175,B_171,E_172] :
      ( k4_relset_1(A_174,B_171,C_170,D_175,E_172,F_173) = k5_relat_1(E_172,F_173)
      | ~ m1_subset_1(F_173,k1_zfmisc_1(k2_zfmisc_1(C_170,D_175)))
      | ~ m1_subset_1(E_172,k1_zfmisc_1(k2_zfmisc_1(A_174,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1327,plain,(
    ! [A_204,B_205,E_206] :
      ( k4_relset_1(A_204,B_205,'#skF_2','#skF_1',E_206,'#skF_4') = k5_relat_1(E_206,'#skF_4')
      | ~ m1_subset_1(E_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_205))) ) ),
    inference(resolution,[status(thm)],[c_56,c_1075])).

tff(c_1357,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_1327])).

tff(c_26,plain,(
    ! [B_16,A_15,D_18,E_19,F_20,C_17] :
      ( m1_subset_1(k4_relset_1(A_15,B_16,C_17,D_18,E_19,F_20),k1_zfmisc_1(k2_zfmisc_1(A_15,D_18)))
      | ~ m1_subset_1(F_20,k1_zfmisc_1(k2_zfmisc_1(C_17,D_18)))
      | ~ m1_subset_1(E_19,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1421,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1357,c_26])).

tff(c_1425,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56,c_1421])).

tff(c_36,plain,(
    ! [A_34] : m1_subset_1(k6_relat_1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_67,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36])).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_1294,plain,(
    ! [C_203,B_199,D_201,A_198,E_202,F_200] :
      ( k1_partfun1(A_198,B_199,C_203,D_201,E_202,F_200) = k5_relat_1(E_202,F_200)
      | ~ m1_subset_1(F_200,k1_zfmisc_1(k2_zfmisc_1(C_203,D_201)))
      | ~ v1_funct_1(F_200)
      | ~ m1_subset_1(E_202,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199)))
      | ~ v1_funct_1(E_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1304,plain,(
    ! [A_198,B_199,E_202] :
      ( k1_partfun1(A_198,B_199,'#skF_2','#skF_1',E_202,'#skF_4') = k5_relat_1(E_202,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_202,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199)))
      | ~ v1_funct_1(E_202) ) ),
    inference(resolution,[status(thm)],[c_56,c_1294])).

tff(c_1809,plain,(
    ! [A_232,B_233,E_234] :
      ( k1_partfun1(A_232,B_233,'#skF_2','#skF_1',E_234,'#skF_4') = k5_relat_1(E_234,'#skF_4')
      | ~ m1_subset_1(E_234,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233)))
      | ~ v1_funct_1(E_234) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1304])).

tff(c_1839,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_1809])).

tff(c_1859,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1839])).

tff(c_54,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_2211,plain,(
    r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1859,c_54])).

tff(c_34,plain,(
    ! [D_33,C_32,A_30,B_31] :
      ( D_33 = C_32
      | ~ r2_relset_1(A_30,B_31,C_32,D_33)
      | ~ m1_subset_1(D_33,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2250,plain,
    ( k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2211,c_34])).

tff(c_2253,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1425,c_67,c_2250])).

tff(c_52,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_124,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_64,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_50,plain,(
    ! [D_52,C_51,E_54,B_50,A_49] :
      ( k1_xboole_0 = C_51
      | v2_funct_1(D_52)
      | ~ v2_funct_1(k1_partfun1(A_49,B_50,B_50,C_51,D_52,E_54))
      | ~ m1_subset_1(E_54,k1_zfmisc_1(k2_zfmisc_1(B_50,C_51)))
      | ~ v1_funct_2(E_54,B_50,C_51)
      | ~ v1_funct_1(E_54)
      | ~ m1_subset_1(D_52,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | ~ v1_funct_2(D_52,A_49,B_50)
      | ~ v1_funct_1(D_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2217,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1859,c_50])).

tff(c_2223,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_58,c_56,c_2217])).

tff(c_2224,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_2223])).

tff(c_2226,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2224])).

tff(c_2259,plain,(
    ~ v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2253,c_2226])).

tff(c_2270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2259])).

tff(c_2271,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2224])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_2308,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2271,c_2])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2305,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2271,c_2271,c_10])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( v1_xboole_0(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1469,plain,
    ( v1_xboole_0(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_1425,c_12])).

tff(c_1477,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1469])).

tff(c_2474,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2305,c_1477])).

tff(c_2481,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2308,c_2474])).

tff(c_2483,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1469])).

tff(c_125,plain,(
    ! [B_61,A_62] :
      ( ~ v1_xboole_0(B_61)
      | B_61 = A_62
      | ~ v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_128,plain,(
    ! [A_62] :
      ( k1_xboole_0 = A_62
      | ~ v1_xboole_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_2,c_125])).

tff(c_2518,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2483,c_128])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2627,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2518,c_6])).

tff(c_2668,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2627,c_2])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2666,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2627,c_2627,c_8])).

tff(c_163,plain,(
    ! [B_67,A_68] :
      ( v1_xboole_0(B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68))
      | ~ v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_180,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_56,c_163])).

tff(c_182,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_2839,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2666,c_182])).

tff(c_2843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2668,c_2839])).

tff(c_2844,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_2851,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2844,c_128])).

tff(c_100,plain,(
    ! [A_60] : k6_relat_1(A_60) = k6_partfun1(A_60) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_14,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_106,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_14])).

tff(c_119,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_68])).

tff(c_2856,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2851,c_119])).

tff(c_2859,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2851,c_2851,c_10])).

tff(c_2860,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2851,c_2851,c_8])).

tff(c_2845,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_2929,plain,(
    ! [A_295] :
      ( A_295 = '#skF_4'
      | ~ v1_xboole_0(A_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2851,c_128])).

tff(c_2936,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2845,c_2929])).

tff(c_3188,plain,(
    ! [B_325,A_326] :
      ( B_325 = '#skF_4'
      | A_326 = '#skF_4'
      | k2_zfmisc_1(A_326,B_325) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2851,c_2851,c_2851,c_6])).

tff(c_3202,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2936,c_3188])).

tff(c_3203,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3202])).

tff(c_181,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_163])).

tff(c_2925,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_3241,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3203,c_2925])).

tff(c_3249,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2844,c_2860,c_3241])).

tff(c_3250,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3202])).

tff(c_3258,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3250,c_2925])).

tff(c_3267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2844,c_2859,c_3258])).

tff(c_3268,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3279,plain,(
    ! [A_331] :
      ( A_331 = '#skF_4'
      | ~ v1_xboole_0(A_331) ) ),
    inference(resolution,[status(thm)],[c_2844,c_4])).

tff(c_3294,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3268,c_3279])).

tff(c_3302,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3294,c_124])).

tff(c_3309,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2856,c_3302])).

tff(c_3310,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_3339,plain,(
    ! [C_336,A_337,B_338] :
      ( v1_relat_1(C_336)
      | ~ m1_subset_1(C_336,k1_zfmisc_1(k2_zfmisc_1(A_337,B_338))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3355,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_3339])).

tff(c_3443,plain,(
    ! [C_353,B_354,A_355] :
      ( v5_relat_1(C_353,B_354)
      | ~ m1_subset_1(C_353,k1_zfmisc_1(k2_zfmisc_1(A_355,B_354))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3460,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_3443])).

tff(c_3542,plain,(
    ! [A_369,B_370,C_371] :
      ( k2_relset_1(A_369,B_370,C_371) = k2_relat_1(C_371)
      | ~ m1_subset_1(C_371,k1_zfmisc_1(k2_zfmisc_1(A_369,B_370))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3559,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_3542])).

tff(c_4154,plain,(
    ! [A_429,B_430,C_431,D_432] :
      ( k2_relset_1(A_429,B_430,C_431) = B_430
      | ~ r2_relset_1(B_430,B_430,k1_partfun1(B_430,A_429,A_429,B_430,D_432,C_431),k6_partfun1(B_430))
      | ~ m1_subset_1(D_432,k1_zfmisc_1(k2_zfmisc_1(B_430,A_429)))
      | ~ v1_funct_2(D_432,B_430,A_429)
      | ~ v1_funct_1(D_432)
      | ~ m1_subset_1(C_431,k1_zfmisc_1(k2_zfmisc_1(A_429,B_430)))
      | ~ v1_funct_2(C_431,A_429,B_430)
      | ~ v1_funct_1(C_431) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_4157,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_4154])).

tff(c_4163,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_66,c_64,c_62,c_3559,c_4157])).

tff(c_38,plain,(
    ! [B_36] :
      ( v2_funct_2(B_36,k2_relat_1(B_36))
      | ~ v5_relat_1(B_36,k2_relat_1(B_36))
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4169,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4163,c_38])).

tff(c_4173,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3355,c_3460,c_4163,c_4169])).

tff(c_4175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3310,c_4173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.02/2.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.02/2.19  
% 6.02/2.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.02/2.20  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.02/2.20  
% 6.02/2.20  %Foreground sorts:
% 6.02/2.20  
% 6.02/2.20  
% 6.02/2.20  %Background operators:
% 6.02/2.20  
% 6.02/2.20  
% 6.02/2.20  %Foreground operators:
% 6.02/2.20  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.02/2.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.02/2.20  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.02/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.02/2.20  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.02/2.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.02/2.20  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.02/2.20  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.02/2.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.02/2.20  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.02/2.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.02/2.20  tff('#skF_2', type, '#skF_2': $i).
% 6.02/2.20  tff('#skF_3', type, '#skF_3': $i).
% 6.02/2.20  tff('#skF_1', type, '#skF_1': $i).
% 6.02/2.20  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.02/2.20  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.02/2.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.02/2.20  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.02/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.02/2.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.02/2.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.02/2.20  tff('#skF_4', type, '#skF_4': $i).
% 6.02/2.20  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.02/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.02/2.20  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.02/2.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.02/2.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.02/2.20  
% 6.02/2.22  tff(f_108, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.02/2.22  tff(f_52, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.02/2.22  tff(f_167, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 6.02/2.22  tff(f_78, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 6.02/2.22  tff(f_68, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 6.02/2.22  tff(f_88, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 6.02/2.22  tff(f_106, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.02/2.22  tff(f_86, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.02/2.22  tff(f_147, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 6.02/2.22  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.02/2.22  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.02/2.22  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 6.02/2.22  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 6.02/2.22  tff(f_48, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 6.02/2.22  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.02/2.22  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.02/2.22  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.02/2.22  tff(f_125, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 6.02/2.22  tff(f_96, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 6.02/2.22  tff(c_44, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.02/2.22  tff(c_18, plain, (![A_8]: (v2_funct_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.02/2.22  tff(c_68, plain, (![A_8]: (v2_funct_1(k6_partfun1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_18])).
% 6.02/2.22  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.02/2.22  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.02/2.22  tff(c_1075, plain, (![A_174, F_173, C_170, D_175, B_171, E_172]: (k4_relset_1(A_174, B_171, C_170, D_175, E_172, F_173)=k5_relat_1(E_172, F_173) | ~m1_subset_1(F_173, k1_zfmisc_1(k2_zfmisc_1(C_170, D_175))) | ~m1_subset_1(E_172, k1_zfmisc_1(k2_zfmisc_1(A_174, B_171))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.02/2.22  tff(c_1327, plain, (![A_204, B_205, E_206]: (k4_relset_1(A_204, B_205, '#skF_2', '#skF_1', E_206, '#skF_4')=k5_relat_1(E_206, '#skF_4') | ~m1_subset_1(E_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))))), inference(resolution, [status(thm)], [c_56, c_1075])).
% 6.02/2.22  tff(c_1357, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_1327])).
% 6.02/2.22  tff(c_26, plain, (![B_16, A_15, D_18, E_19, F_20, C_17]: (m1_subset_1(k4_relset_1(A_15, B_16, C_17, D_18, E_19, F_20), k1_zfmisc_1(k2_zfmisc_1(A_15, D_18))) | ~m1_subset_1(F_20, k1_zfmisc_1(k2_zfmisc_1(C_17, D_18))) | ~m1_subset_1(E_19, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.02/2.22  tff(c_1421, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1357, c_26])).
% 6.02/2.22  tff(c_1425, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_56, c_1421])).
% 6.02/2.22  tff(c_36, plain, (![A_34]: (m1_subset_1(k6_relat_1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.02/2.22  tff(c_67, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36])).
% 6.02/2.22  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.02/2.22  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.02/2.22  tff(c_1294, plain, (![C_203, B_199, D_201, A_198, E_202, F_200]: (k1_partfun1(A_198, B_199, C_203, D_201, E_202, F_200)=k5_relat_1(E_202, F_200) | ~m1_subset_1(F_200, k1_zfmisc_1(k2_zfmisc_1(C_203, D_201))) | ~v1_funct_1(F_200) | ~m1_subset_1(E_202, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))) | ~v1_funct_1(E_202))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.02/2.22  tff(c_1304, plain, (![A_198, B_199, E_202]: (k1_partfun1(A_198, B_199, '#skF_2', '#skF_1', E_202, '#skF_4')=k5_relat_1(E_202, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_202, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))) | ~v1_funct_1(E_202))), inference(resolution, [status(thm)], [c_56, c_1294])).
% 6.02/2.22  tff(c_1809, plain, (![A_232, B_233, E_234]: (k1_partfun1(A_232, B_233, '#skF_2', '#skF_1', E_234, '#skF_4')=k5_relat_1(E_234, '#skF_4') | ~m1_subset_1(E_234, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))) | ~v1_funct_1(E_234))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1304])).
% 6.02/2.22  tff(c_1839, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_1809])).
% 6.02/2.22  tff(c_1859, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1839])).
% 6.02/2.22  tff(c_54, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.02/2.22  tff(c_2211, plain, (r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1859, c_54])).
% 6.02/2.22  tff(c_34, plain, (![D_33, C_32, A_30, B_31]: (D_33=C_32 | ~r2_relset_1(A_30, B_31, C_32, D_33) | ~m1_subset_1(D_33, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.02/2.22  tff(c_2250, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_2211, c_34])).
% 6.02/2.22  tff(c_2253, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1425, c_67, c_2250])).
% 6.02/2.22  tff(c_52, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.02/2.22  tff(c_124, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_52])).
% 6.02/2.22  tff(c_64, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.02/2.22  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.02/2.22  tff(c_50, plain, (![D_52, C_51, E_54, B_50, A_49]: (k1_xboole_0=C_51 | v2_funct_1(D_52) | ~v2_funct_1(k1_partfun1(A_49, B_50, B_50, C_51, D_52, E_54)) | ~m1_subset_1(E_54, k1_zfmisc_1(k2_zfmisc_1(B_50, C_51))) | ~v1_funct_2(E_54, B_50, C_51) | ~v1_funct_1(E_54) | ~m1_subset_1(D_52, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | ~v1_funct_2(D_52, A_49, B_50) | ~v1_funct_1(D_52))), inference(cnfTransformation, [status(thm)], [f_147])).
% 6.02/2.22  tff(c_2217, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1859, c_50])).
% 6.02/2.22  tff(c_2223, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_58, c_56, c_2217])).
% 6.02/2.22  tff(c_2224, plain, (k1_xboole_0='#skF_1' | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_124, c_2223])).
% 6.02/2.22  tff(c_2226, plain, (~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_2224])).
% 6.02/2.22  tff(c_2259, plain, (~v2_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2253, c_2226])).
% 6.02/2.22  tff(c_2270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_2259])).
% 6.02/2.22  tff(c_2271, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_2224])).
% 6.02/2.22  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.02/2.22  tff(c_2308, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2271, c_2])).
% 6.02/2.22  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.02/2.22  tff(c_2305, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2271, c_2271, c_10])).
% 6.02/2.22  tff(c_12, plain, (![B_7, A_5]: (v1_xboole_0(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.02/2.22  tff(c_1469, plain, (v1_xboole_0(k5_relat_1('#skF_3', '#skF_4')) | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_1425, c_12])).
% 6.02/2.22  tff(c_1477, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(splitLeft, [status(thm)], [c_1469])).
% 6.02/2.22  tff(c_2474, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2305, c_1477])).
% 6.02/2.22  tff(c_2481, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2308, c_2474])).
% 6.02/2.22  tff(c_2483, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(splitRight, [status(thm)], [c_1469])).
% 6.02/2.22  tff(c_125, plain, (![B_61, A_62]: (~v1_xboole_0(B_61) | B_61=A_62 | ~v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.02/2.22  tff(c_128, plain, (![A_62]: (k1_xboole_0=A_62 | ~v1_xboole_0(A_62))), inference(resolution, [status(thm)], [c_2, c_125])).
% 6.02/2.22  tff(c_2518, plain, (k2_zfmisc_1('#skF_1', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_2483, c_128])).
% 6.02/2.22  tff(c_6, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.02/2.22  tff(c_2627, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2518, c_6])).
% 6.02/2.22  tff(c_2668, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2627, c_2])).
% 6.02/2.22  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.02/2.22  tff(c_2666, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2627, c_2627, c_8])).
% 6.02/2.22  tff(c_163, plain, (![B_67, A_68]: (v1_xboole_0(B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(A_68)) | ~v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.02/2.22  tff(c_180, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_56, c_163])).
% 6.02/2.22  tff(c_182, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_180])).
% 6.02/2.22  tff(c_2839, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2666, c_182])).
% 6.02/2.22  tff(c_2843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2668, c_2839])).
% 6.02/2.22  tff(c_2844, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_180])).
% 6.02/2.22  tff(c_2851, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2844, c_128])).
% 6.02/2.22  tff(c_100, plain, (![A_60]: (k6_relat_1(A_60)=k6_partfun1(A_60))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.02/2.22  tff(c_14, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.02/2.22  tff(c_106, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_100, c_14])).
% 6.02/2.22  tff(c_119, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_106, c_68])).
% 6.02/2.22  tff(c_2856, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2851, c_119])).
% 6.02/2.22  tff(c_2859, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2851, c_2851, c_10])).
% 6.02/2.22  tff(c_2860, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2851, c_2851, c_8])).
% 6.02/2.22  tff(c_2845, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_180])).
% 6.02/2.22  tff(c_2929, plain, (![A_295]: (A_295='#skF_4' | ~v1_xboole_0(A_295))), inference(demodulation, [status(thm), theory('equality')], [c_2851, c_128])).
% 6.02/2.22  tff(c_2936, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4'), inference(resolution, [status(thm)], [c_2845, c_2929])).
% 6.02/2.22  tff(c_3188, plain, (![B_325, A_326]: (B_325='#skF_4' | A_326='#skF_4' | k2_zfmisc_1(A_326, B_325)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2851, c_2851, c_2851, c_6])).
% 6.02/2.22  tff(c_3202, plain, ('#skF_1'='#skF_4' | '#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2936, c_3188])).
% 6.02/2.22  tff(c_3203, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_3202])).
% 6.02/2.22  tff(c_181, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_163])).
% 6.02/2.22  tff(c_2925, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_181])).
% 6.02/2.22  tff(c_3241, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3203, c_2925])).
% 6.02/2.22  tff(c_3249, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2844, c_2860, c_3241])).
% 6.02/2.22  tff(c_3250, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_3202])).
% 6.02/2.22  tff(c_3258, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3250, c_2925])).
% 6.02/2.22  tff(c_3267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2844, c_2859, c_3258])).
% 6.02/2.22  tff(c_3268, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_181])).
% 6.02/2.22  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.02/2.22  tff(c_3279, plain, (![A_331]: (A_331='#skF_4' | ~v1_xboole_0(A_331))), inference(resolution, [status(thm)], [c_2844, c_4])).
% 6.02/2.22  tff(c_3294, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_3268, c_3279])).
% 6.02/2.22  tff(c_3302, plain, (~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3294, c_124])).
% 6.02/2.22  tff(c_3309, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2856, c_3302])).
% 6.02/2.22  tff(c_3310, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 6.02/2.22  tff(c_3339, plain, (![C_336, A_337, B_338]: (v1_relat_1(C_336) | ~m1_subset_1(C_336, k1_zfmisc_1(k2_zfmisc_1(A_337, B_338))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.02/2.22  tff(c_3355, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_3339])).
% 6.02/2.22  tff(c_3443, plain, (![C_353, B_354, A_355]: (v5_relat_1(C_353, B_354) | ~m1_subset_1(C_353, k1_zfmisc_1(k2_zfmisc_1(A_355, B_354))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.02/2.22  tff(c_3460, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_3443])).
% 6.02/2.22  tff(c_3542, plain, (![A_369, B_370, C_371]: (k2_relset_1(A_369, B_370, C_371)=k2_relat_1(C_371) | ~m1_subset_1(C_371, k1_zfmisc_1(k2_zfmisc_1(A_369, B_370))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.02/2.22  tff(c_3559, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_3542])).
% 6.02/2.22  tff(c_4154, plain, (![A_429, B_430, C_431, D_432]: (k2_relset_1(A_429, B_430, C_431)=B_430 | ~r2_relset_1(B_430, B_430, k1_partfun1(B_430, A_429, A_429, B_430, D_432, C_431), k6_partfun1(B_430)) | ~m1_subset_1(D_432, k1_zfmisc_1(k2_zfmisc_1(B_430, A_429))) | ~v1_funct_2(D_432, B_430, A_429) | ~v1_funct_1(D_432) | ~m1_subset_1(C_431, k1_zfmisc_1(k2_zfmisc_1(A_429, B_430))) | ~v1_funct_2(C_431, A_429, B_430) | ~v1_funct_1(C_431))), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.02/2.22  tff(c_4157, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_4154])).
% 6.02/2.22  tff(c_4163, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_66, c_64, c_62, c_3559, c_4157])).
% 6.02/2.22  tff(c_38, plain, (![B_36]: (v2_funct_2(B_36, k2_relat_1(B_36)) | ~v5_relat_1(B_36, k2_relat_1(B_36)) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.02/2.22  tff(c_4169, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4163, c_38])).
% 6.02/2.22  tff(c_4173, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3355, c_3460, c_4163, c_4169])).
% 6.02/2.22  tff(c_4175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3310, c_4173])).
% 6.02/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.02/2.22  
% 6.02/2.22  Inference rules
% 6.02/2.22  ----------------------
% 6.02/2.22  #Ref     : 0
% 6.02/2.22  #Sup     : 985
% 6.02/2.22  #Fact    : 0
% 6.02/2.22  #Define  : 0
% 6.02/2.22  #Split   : 23
% 6.02/2.22  #Chain   : 0
% 6.02/2.22  #Close   : 0
% 6.02/2.22  
% 6.02/2.22  Ordering : KBO
% 6.02/2.22  
% 6.02/2.22  Simplification rules
% 6.02/2.22  ----------------------
% 6.02/2.22  #Subsume      : 38
% 6.02/2.22  #Demod        : 731
% 6.02/2.22  #Tautology    : 337
% 6.02/2.22  #SimpNegUnit  : 3
% 6.02/2.22  #BackRed      : 157
% 6.02/2.22  
% 6.02/2.22  #Partial instantiations: 0
% 6.02/2.22  #Strategies tried      : 1
% 6.02/2.22  
% 6.02/2.22  Timing (in seconds)
% 6.02/2.22  ----------------------
% 6.02/2.22  Preprocessing        : 0.36
% 6.02/2.22  Parsing              : 0.20
% 6.02/2.22  CNF conversion       : 0.02
% 6.02/2.22  Main loop            : 1.03
% 6.02/2.22  Inferencing          : 0.34
% 6.02/2.22  Reduction            : 0.37
% 6.02/2.22  Demodulation         : 0.27
% 6.02/2.22  BG Simplification    : 0.04
% 6.02/2.22  Subsumption          : 0.16
% 6.02/2.22  Abstraction          : 0.05
% 6.02/2.22  MUC search           : 0.00
% 6.02/2.22  Cooper               : 0.00
% 6.02/2.22  Total                : 1.44
% 6.02/2.22  Index Insertion      : 0.00
% 6.02/2.22  Index Deletion       : 0.00
% 6.02/2.22  Index Matching       : 0.00
% 6.02/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
