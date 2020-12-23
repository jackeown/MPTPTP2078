%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:02 EST 2020

% Result     : Theorem 4.68s
% Output     : CNFRefutation 4.68s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 286 expanded)
%              Number of leaves         :   42 ( 124 expanded)
%              Depth                    :   10
%              Number of atoms          :  204 ( 983 expanded)
%              Number of equality atoms :   30 (  79 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_166,negated_conjecture,(
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

tff(f_107,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_101,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_105,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_146,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_124,axiom,(
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

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_56,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_114,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_48,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_22,plain,(
    ! [A_8] : v2_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_71,plain,(
    ! [A_8] : v2_funct_1(k6_partfun1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_22])).

tff(c_40,plain,(
    ! [A_24,B_25,F_29,D_27,C_26,E_28] :
      ( m1_subset_1(k1_partfun1(A_24,B_25,C_26,D_27,E_28,F_29),k1_zfmisc_1(k2_zfmisc_1(A_24,D_27)))
      | ~ m1_subset_1(F_29,k1_zfmisc_1(k2_zfmisc_1(C_26,D_27)))
      | ~ v1_funct_1(F_29)
      | ~ m1_subset_1(E_28,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ v1_funct_1(E_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_46,plain,(
    ! [A_30] : m1_subset_1(k6_partfun1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_890,plain,(
    ! [D_189,C_190,A_191,B_192] :
      ( D_189 = C_190
      | ~ r2_relset_1(A_191,B_192,C_190,D_189)
      | ~ m1_subset_1(D_189,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192)))
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_896,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_890])).

tff(c_907,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_896])).

tff(c_1138,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_907])).

tff(c_1141,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_1138])).

tff(c_1145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_1141])).

tff(c_1146,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_907])).

tff(c_1182,plain,(
    ! [B_248,D_249,E_250,A_247,C_251] :
      ( k1_xboole_0 = C_251
      | v2_funct_1(D_249)
      | ~ v2_funct_1(k1_partfun1(A_247,B_248,B_248,C_251,D_249,E_250))
      | ~ m1_subset_1(E_250,k1_zfmisc_1(k2_zfmisc_1(B_248,C_251)))
      | ~ v1_funct_2(E_250,B_248,C_251)
      | ~ v1_funct_1(E_250)
      | ~ m1_subset_1(D_249,k1_zfmisc_1(k2_zfmisc_1(A_247,B_248)))
      | ~ v1_funct_2(D_249,A_247,B_248)
      | ~ v1_funct_1(D_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1184,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1146,c_1182])).

tff(c_1189,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_60,c_71,c_1184])).

tff(c_1190,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_1189])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1224,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1190,c_2])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1223,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1190,c_1190,c_8])).

tff(c_125,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_142,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_125])).

tff(c_730,plain,(
    ! [A_161] :
      ( v2_funct_1(A_161)
      | ~ v1_funct_1(A_161)
      | ~ v1_relat_1(A_161)
      | ~ v1_xboole_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_733,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_730,c_114])).

tff(c_736,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_70,c_733])).

tff(c_160,plain,(
    ! [B_58,A_59] :
      ( v1_xboole_0(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59))
      | ~ v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_178,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_160])).

tff(c_737,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_736,c_178])).

tff(c_1290,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1223,c_737])).

tff(c_1294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1224,c_1290])).

tff(c_1295,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1307,plain,(
    ! [C_255,A_256,B_257] :
      ( v1_relat_1(C_255)
      | ~ m1_subset_1(C_255,k1_zfmisc_1(k2_zfmisc_1(A_256,B_257))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1323,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_1307])).

tff(c_1381,plain,(
    ! [C_265,B_266,A_267] :
      ( v5_relat_1(C_265,B_266)
      | ~ m1_subset_1(C_265,k1_zfmisc_1(k2_zfmisc_1(A_267,B_266))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1398,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_1381])).

tff(c_1465,plain,(
    ! [A_282,B_283,D_284] :
      ( r2_relset_1(A_282,B_283,D_284,D_284)
      | ~ m1_subset_1(D_284,k1_zfmisc_1(k2_zfmisc_1(A_282,B_283))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1476,plain,(
    ! [A_30] : r2_relset_1(A_30,A_30,k6_partfun1(A_30),k6_partfun1(A_30)) ),
    inference(resolution,[status(thm)],[c_46,c_1465])).

tff(c_1480,plain,(
    ! [A_286,B_287,C_288] :
      ( k2_relset_1(A_286,B_287,C_288) = k2_relat_1(C_288)
      | ~ m1_subset_1(C_288,k1_zfmisc_1(k2_zfmisc_1(A_286,B_287))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1497,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_1480])).

tff(c_1676,plain,(
    ! [A_328,C_324,B_325,F_327,E_326,D_329] :
      ( m1_subset_1(k1_partfun1(A_328,B_325,C_324,D_329,E_326,F_327),k1_zfmisc_1(k2_zfmisc_1(A_328,D_329)))
      | ~ m1_subset_1(F_327,k1_zfmisc_1(k2_zfmisc_1(C_324,D_329)))
      | ~ v1_funct_1(F_327)
      | ~ m1_subset_1(E_326,k1_zfmisc_1(k2_zfmisc_1(A_328,B_325)))
      | ~ v1_funct_1(E_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1523,plain,(
    ! [D_292,C_293,A_294,B_295] :
      ( D_292 = C_293
      | ~ r2_relset_1(A_294,B_295,C_293,D_292)
      | ~ m1_subset_1(D_292,k1_zfmisc_1(k2_zfmisc_1(A_294,B_295)))
      | ~ m1_subset_1(C_293,k1_zfmisc_1(k2_zfmisc_1(A_294,B_295))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1531,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_1523])).

tff(c_1546,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1531])).

tff(c_1562,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1546])).

tff(c_1682,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1676,c_1562])).

tff(c_1712,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_1682])).

tff(c_1713,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1546])).

tff(c_2012,plain,(
    ! [A_411,B_412,C_413,D_414] :
      ( k2_relset_1(A_411,B_412,C_413) = B_412
      | ~ r2_relset_1(B_412,B_412,k1_partfun1(B_412,A_411,A_411,B_412,D_414,C_413),k6_partfun1(B_412))
      | ~ m1_subset_1(D_414,k1_zfmisc_1(k2_zfmisc_1(B_412,A_411)))
      | ~ v1_funct_2(D_414,B_412,A_411)
      | ~ v1_funct_1(D_414)
      | ~ m1_subset_1(C_413,k1_zfmisc_1(k2_zfmisc_1(A_411,B_412)))
      | ~ v1_funct_2(C_413,A_411,B_412)
      | ~ v1_funct_1(C_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2015,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1713,c_2012])).

tff(c_2017,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_70,c_68,c_66,c_1476,c_1497,c_2015])).

tff(c_36,plain,(
    ! [B_23] :
      ( v2_funct_2(B_23,k2_relat_1(B_23))
      | ~ v5_relat_1(B_23,k2_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2022,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2017,c_36])).

tff(c_2026,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1323,c_1398,c_2017,c_2022])).

tff(c_2028,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1295,c_2026])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.68/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.79  
% 4.68/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.80  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.68/1.80  
% 4.68/1.80  %Foreground sorts:
% 4.68/1.80  
% 4.68/1.80  
% 4.68/1.80  %Background operators:
% 4.68/1.80  
% 4.68/1.80  
% 4.68/1.80  %Foreground operators:
% 4.68/1.80  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.68/1.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.68/1.80  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.68/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.68/1.80  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.68/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.68/1.80  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.68/1.80  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.68/1.80  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.68/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.68/1.80  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.68/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.68/1.80  tff('#skF_1', type, '#skF_1': $i).
% 4.68/1.80  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.68/1.80  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.68/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.68/1.80  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.68/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.68/1.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.68/1.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.68/1.80  tff('#skF_4', type, '#skF_4': $i).
% 4.68/1.80  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.68/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.68/1.80  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.68/1.80  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.68/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.68/1.80  
% 4.68/1.82  tff(f_166, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 4.68/1.82  tff(f_107, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.68/1.82  tff(f_59, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.68/1.82  tff(f_101, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.68/1.82  tff(f_105, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.68/1.82  tff(f_81, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.68/1.82  tff(f_146, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 4.68/1.82  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.68/1.82  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.68/1.82  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.68/1.82  tff(f_55, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_1)).
% 4.68/1.82  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 4.68/1.82  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.68/1.82  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.68/1.82  tff(f_124, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 4.68/1.82  tff(f_89, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 4.68/1.82  tff(c_56, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.68/1.82  tff(c_114, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 4.68/1.82  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.68/1.82  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.68/1.82  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.68/1.82  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.68/1.82  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.68/1.82  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.68/1.82  tff(c_48, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.68/1.82  tff(c_22, plain, (![A_8]: (v2_funct_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.68/1.82  tff(c_71, plain, (![A_8]: (v2_funct_1(k6_partfun1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_22])).
% 4.68/1.82  tff(c_40, plain, (![A_24, B_25, F_29, D_27, C_26, E_28]: (m1_subset_1(k1_partfun1(A_24, B_25, C_26, D_27, E_28, F_29), k1_zfmisc_1(k2_zfmisc_1(A_24, D_27))) | ~m1_subset_1(F_29, k1_zfmisc_1(k2_zfmisc_1(C_26, D_27))) | ~v1_funct_1(F_29) | ~m1_subset_1(E_28, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~v1_funct_1(E_28))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.68/1.82  tff(c_46, plain, (![A_30]: (m1_subset_1(k6_partfun1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.68/1.82  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.68/1.82  tff(c_890, plain, (![D_189, C_190, A_191, B_192]: (D_189=C_190 | ~r2_relset_1(A_191, B_192, C_190, D_189) | ~m1_subset_1(D_189, k1_zfmisc_1(k2_zfmisc_1(A_191, B_192))) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_191, B_192))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.68/1.82  tff(c_896, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_890])).
% 4.68/1.82  tff(c_907, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_896])).
% 4.68/1.82  tff(c_1138, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_907])).
% 4.68/1.82  tff(c_1141, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_1138])).
% 4.68/1.82  tff(c_1145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_1141])).
% 4.68/1.82  tff(c_1146, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_907])).
% 4.68/1.82  tff(c_1182, plain, (![B_248, D_249, E_250, A_247, C_251]: (k1_xboole_0=C_251 | v2_funct_1(D_249) | ~v2_funct_1(k1_partfun1(A_247, B_248, B_248, C_251, D_249, E_250)) | ~m1_subset_1(E_250, k1_zfmisc_1(k2_zfmisc_1(B_248, C_251))) | ~v1_funct_2(E_250, B_248, C_251) | ~v1_funct_1(E_250) | ~m1_subset_1(D_249, k1_zfmisc_1(k2_zfmisc_1(A_247, B_248))) | ~v1_funct_2(D_249, A_247, B_248) | ~v1_funct_1(D_249))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.68/1.82  tff(c_1184, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1146, c_1182])).
% 4.68/1.82  tff(c_1189, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_60, c_71, c_1184])).
% 4.68/1.82  tff(c_1190, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_114, c_1189])).
% 4.68/1.82  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.68/1.82  tff(c_1224, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1190, c_2])).
% 4.68/1.82  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.68/1.82  tff(c_1223, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1190, c_1190, c_8])).
% 4.68/1.82  tff(c_125, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.68/1.82  tff(c_142, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_125])).
% 4.68/1.82  tff(c_730, plain, (![A_161]: (v2_funct_1(A_161) | ~v1_funct_1(A_161) | ~v1_relat_1(A_161) | ~v1_xboole_0(A_161))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.68/1.82  tff(c_733, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_730, c_114])).
% 4.68/1.82  tff(c_736, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_70, c_733])).
% 4.68/1.82  tff(c_160, plain, (![B_58, A_59]: (v1_xboole_0(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)) | ~v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.68/1.82  tff(c_178, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_160])).
% 4.68/1.82  tff(c_737, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_736, c_178])).
% 4.68/1.82  tff(c_1290, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1223, c_737])).
% 4.68/1.82  tff(c_1294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1224, c_1290])).
% 4.68/1.82  tff(c_1295, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 4.68/1.82  tff(c_1307, plain, (![C_255, A_256, B_257]: (v1_relat_1(C_255) | ~m1_subset_1(C_255, k1_zfmisc_1(k2_zfmisc_1(A_256, B_257))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.68/1.82  tff(c_1323, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_1307])).
% 4.68/1.82  tff(c_1381, plain, (![C_265, B_266, A_267]: (v5_relat_1(C_265, B_266) | ~m1_subset_1(C_265, k1_zfmisc_1(k2_zfmisc_1(A_267, B_266))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.68/1.82  tff(c_1398, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_1381])).
% 4.68/1.82  tff(c_1465, plain, (![A_282, B_283, D_284]: (r2_relset_1(A_282, B_283, D_284, D_284) | ~m1_subset_1(D_284, k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.68/1.82  tff(c_1476, plain, (![A_30]: (r2_relset_1(A_30, A_30, k6_partfun1(A_30), k6_partfun1(A_30)))), inference(resolution, [status(thm)], [c_46, c_1465])).
% 4.68/1.82  tff(c_1480, plain, (![A_286, B_287, C_288]: (k2_relset_1(A_286, B_287, C_288)=k2_relat_1(C_288) | ~m1_subset_1(C_288, k1_zfmisc_1(k2_zfmisc_1(A_286, B_287))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.68/1.82  tff(c_1497, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_1480])).
% 4.68/1.82  tff(c_1676, plain, (![A_328, C_324, B_325, F_327, E_326, D_329]: (m1_subset_1(k1_partfun1(A_328, B_325, C_324, D_329, E_326, F_327), k1_zfmisc_1(k2_zfmisc_1(A_328, D_329))) | ~m1_subset_1(F_327, k1_zfmisc_1(k2_zfmisc_1(C_324, D_329))) | ~v1_funct_1(F_327) | ~m1_subset_1(E_326, k1_zfmisc_1(k2_zfmisc_1(A_328, B_325))) | ~v1_funct_1(E_326))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.68/1.82  tff(c_1523, plain, (![D_292, C_293, A_294, B_295]: (D_292=C_293 | ~r2_relset_1(A_294, B_295, C_293, D_292) | ~m1_subset_1(D_292, k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))) | ~m1_subset_1(C_293, k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.68/1.82  tff(c_1531, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_1523])).
% 4.68/1.82  tff(c_1546, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1531])).
% 4.68/1.82  tff(c_1562, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1546])).
% 4.68/1.82  tff(c_1682, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1676, c_1562])).
% 4.68/1.82  tff(c_1712, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_1682])).
% 4.68/1.82  tff(c_1713, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1546])).
% 4.68/1.82  tff(c_2012, plain, (![A_411, B_412, C_413, D_414]: (k2_relset_1(A_411, B_412, C_413)=B_412 | ~r2_relset_1(B_412, B_412, k1_partfun1(B_412, A_411, A_411, B_412, D_414, C_413), k6_partfun1(B_412)) | ~m1_subset_1(D_414, k1_zfmisc_1(k2_zfmisc_1(B_412, A_411))) | ~v1_funct_2(D_414, B_412, A_411) | ~v1_funct_1(D_414) | ~m1_subset_1(C_413, k1_zfmisc_1(k2_zfmisc_1(A_411, B_412))) | ~v1_funct_2(C_413, A_411, B_412) | ~v1_funct_1(C_413))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.68/1.82  tff(c_2015, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1713, c_2012])).
% 4.68/1.82  tff(c_2017, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_70, c_68, c_66, c_1476, c_1497, c_2015])).
% 4.68/1.82  tff(c_36, plain, (![B_23]: (v2_funct_2(B_23, k2_relat_1(B_23)) | ~v5_relat_1(B_23, k2_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.68/1.82  tff(c_2022, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2017, c_36])).
% 4.68/1.82  tff(c_2026, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1323, c_1398, c_2017, c_2022])).
% 4.68/1.82  tff(c_2028, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1295, c_2026])).
% 4.68/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.82  
% 4.68/1.82  Inference rules
% 4.68/1.82  ----------------------
% 4.68/1.82  #Ref     : 0
% 4.68/1.82  #Sup     : 420
% 4.68/1.82  #Fact    : 0
% 4.68/1.82  #Define  : 0
% 4.68/1.82  #Split   : 13
% 4.68/1.82  #Chain   : 0
% 4.68/1.82  #Close   : 0
% 4.68/1.82  
% 4.68/1.82  Ordering : KBO
% 4.68/1.82  
% 4.68/1.82  Simplification rules
% 4.68/1.82  ----------------------
% 4.68/1.82  #Subsume      : 9
% 4.68/1.82  #Demod        : 353
% 4.68/1.82  #Tautology    : 138
% 4.68/1.82  #SimpNegUnit  : 4
% 4.68/1.82  #BackRed      : 79
% 4.68/1.82  
% 4.68/1.82  #Partial instantiations: 0
% 4.68/1.82  #Strategies tried      : 1
% 4.68/1.82  
% 4.68/1.82  Timing (in seconds)
% 4.68/1.82  ----------------------
% 4.68/1.82  Preprocessing        : 0.36
% 4.68/1.82  Parsing              : 0.20
% 4.68/1.82  CNF conversion       : 0.02
% 4.68/1.82  Main loop            : 0.69
% 4.68/1.82  Inferencing          : 0.25
% 4.68/1.82  Reduction            : 0.24
% 4.68/1.82  Demodulation         : 0.17
% 4.68/1.82  BG Simplification    : 0.03
% 4.68/1.82  Subsumption          : 0.11
% 4.68/1.82  Abstraction          : 0.03
% 4.68/1.82  MUC search           : 0.00
% 4.68/1.82  Cooper               : 0.00
% 4.68/1.82  Total                : 1.09
% 4.68/1.82  Index Insertion      : 0.00
% 4.68/1.82  Index Deletion       : 0.00
% 4.68/1.82  Index Matching       : 0.00
% 4.68/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
