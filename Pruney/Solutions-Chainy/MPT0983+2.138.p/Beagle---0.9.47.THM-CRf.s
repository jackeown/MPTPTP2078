%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:21 EST 2020

% Result     : Theorem 7.16s
% Output     : CNFRefutation 7.31s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 365 expanded)
%              Number of leaves         :   52 ( 146 expanded)
%              Depth                    :   12
%              Number of atoms          :  261 (1043 expanded)
%              Number of equality atoms :   46 ( 101 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(f_208,negated_conjecture,(
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

tff(f_115,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_166,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_102,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_164,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_150,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_154,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_130,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_188,axiom,(
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

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_122,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_72,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_138,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_96,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_429,plain,(
    ! [C_120,A_121,B_122] :
      ( v1_xboole_0(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122)))
      | ~ v1_xboole_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_450,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_429])).

tff(c_456,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_450])).

tff(c_86,plain,
    ( ~ v2_funct_2('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_181,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_100,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_98,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_94,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_92,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_90,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_80,plain,(
    ! [A_62] : k6_relat_1(A_62) = k6_partfun1(A_62) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_52,plain,(
    ! [A_31] : v2_funct_1(k6_relat_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_101,plain,(
    ! [A_31] : v2_funct_1(k6_partfun1(A_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_52])).

tff(c_1786,plain,(
    ! [D_242,E_241,B_238,F_239,A_243,C_240] :
      ( k1_partfun1(A_243,B_238,C_240,D_242,E_241,F_239) = k5_relat_1(E_241,F_239)
      | ~ m1_subset_1(F_239,k1_zfmisc_1(k2_zfmisc_1(C_240,D_242)))
      | ~ v1_funct_1(F_239)
      | ~ m1_subset_1(E_241,k1_zfmisc_1(k2_zfmisc_1(A_243,B_238)))
      | ~ v1_funct_1(E_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_1792,plain,(
    ! [A_243,B_238,E_241] :
      ( k1_partfun1(A_243,B_238,'#skF_4','#skF_3',E_241,'#skF_6') = k5_relat_1(E_241,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_241,k1_zfmisc_1(k2_zfmisc_1(A_243,B_238)))
      | ~ v1_funct_1(E_241) ) ),
    inference(resolution,[status(thm)],[c_90,c_1786])).

tff(c_1963,plain,(
    ! [A_267,B_268,E_269] :
      ( k1_partfun1(A_267,B_268,'#skF_4','#skF_3',E_269,'#skF_6') = k5_relat_1(E_269,'#skF_6')
      | ~ m1_subset_1(E_269,k1_zfmisc_1(k2_zfmisc_1(A_267,B_268)))
      | ~ v1_funct_1(E_269) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1792])).

tff(c_1972,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_1963])).

tff(c_1990,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1972])).

tff(c_70,plain,(
    ! [D_52,C_51,F_54,B_50,A_49,E_53] :
      ( m1_subset_1(k1_partfun1(A_49,B_50,C_51,D_52,E_53,F_54),k1_zfmisc_1(k2_zfmisc_1(A_49,D_52)))
      | ~ m1_subset_1(F_54,k1_zfmisc_1(k2_zfmisc_1(C_51,D_52)))
      | ~ v1_funct_1(F_54)
      | ~ m1_subset_1(E_53,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | ~ v1_funct_1(E_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2012,plain,
    ( m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1990,c_70])).

tff(c_2016,plain,(
    m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_96,c_94,c_90,c_2012])).

tff(c_76,plain,(
    ! [A_55] : m1_subset_1(k6_partfun1(A_55),k1_zfmisc_1(k2_zfmisc_1(A_55,A_55))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_88,plain,(
    r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k6_partfun1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_1325,plain,(
    ! [D_187,C_188,A_189,B_190] :
      ( D_187 = C_188
      | ~ r2_relset_1(A_189,B_190,C_188,D_187)
      | ~ m1_subset_1(D_187,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190)))
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1335,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_88,c_1325])).

tff(c_1354,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1335])).

tff(c_1465,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1354])).

tff(c_2402,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2016,c_1990,c_1465])).

tff(c_2403,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1354])).

tff(c_3113,plain,(
    ! [D_362,E_361,B_359,A_360,C_358] :
      ( k1_xboole_0 = C_358
      | v2_funct_1(D_362)
      | ~ v2_funct_1(k1_partfun1(A_360,B_359,B_359,C_358,D_362,E_361))
      | ~ m1_subset_1(E_361,k1_zfmisc_1(k2_zfmisc_1(B_359,C_358)))
      | ~ v1_funct_2(E_361,B_359,C_358)
      | ~ v1_funct_1(E_361)
      | ~ m1_subset_1(D_362,k1_zfmisc_1(k2_zfmisc_1(A_360,B_359)))
      | ~ v1_funct_2(D_362,A_360,B_359)
      | ~ v1_funct_1(D_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_3117,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_funct_1('#skF_5')
    | ~ v2_funct_1(k6_partfun1('#skF_3'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2403,c_3113])).

tff(c_3124,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_96,c_94,c_92,c_90,c_101,c_3117])).

tff(c_3125,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_3124])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_3172,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3125,c_2])).

tff(c_3174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_456,c_3172])).

tff(c_3176,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_450])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_3192,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3176,c_4])).

tff(c_3175,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_450])).

tff(c_3184,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3175,c_4])).

tff(c_3219,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3192,c_3184])).

tff(c_3230,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3219,c_181])).

tff(c_3273,plain,(
    ! [C_367,B_368,A_369] :
      ( v1_xboole_0(C_367)
      | ~ m1_subset_1(C_367,k1_zfmisc_1(k2_zfmisc_1(B_368,A_369)))
      | ~ v1_xboole_0(A_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_3476,plain,(
    ! [A_380] :
      ( v1_xboole_0(k6_partfun1(A_380))
      | ~ v1_xboole_0(A_380) ) ),
    inference(resolution,[status(thm)],[c_76,c_3273])).

tff(c_3211,plain,(
    ! [A_1] :
      ( A_1 = '#skF_5'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3184,c_4])).

tff(c_3431,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3219,c_3211])).

tff(c_3518,plain,(
    ! [A_383] :
      ( k6_partfun1(A_383) = '#skF_3'
      | ~ v1_xboole_0(A_383) ) ),
    inference(resolution,[status(thm)],[c_3476,c_3431])).

tff(c_3529,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3176,c_3518])).

tff(c_3571,plain,(
    v2_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3529,c_101])).

tff(c_3586,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3230,c_3571])).

tff(c_3587,plain,(
    ~ v2_funct_2('#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_32,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3675,plain,(
    ! [B_395,A_396] :
      ( v1_relat_1(B_395)
      | ~ m1_subset_1(B_395,k1_zfmisc_1(A_396))
      | ~ v1_relat_1(A_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3684,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_90,c_3675])).

tff(c_3699,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3684])).

tff(c_3748,plain,(
    ! [C_405,B_406,A_407] :
      ( v5_relat_1(C_405,B_406)
      | ~ m1_subset_1(C_405,k1_zfmisc_1(k2_zfmisc_1(A_407,B_406))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_3770,plain,(
    v5_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_3748])).

tff(c_28,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v5_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3687,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_96,c_3675])).

tff(c_3702,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3687])).

tff(c_38,plain,(
    ! [A_23] : k2_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_103,plain,(
    ! [A_23] : k2_relat_1(k6_partfun1(A_23)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_38])).

tff(c_5309,plain,(
    ! [D_564,A_563,C_559,E_560,F_562,B_561] :
      ( m1_subset_1(k1_partfun1(A_563,B_561,C_559,D_564,E_560,F_562),k1_zfmisc_1(k2_zfmisc_1(A_563,D_564)))
      | ~ m1_subset_1(F_562,k1_zfmisc_1(k2_zfmisc_1(C_559,D_564)))
      | ~ v1_funct_1(F_562)
      | ~ m1_subset_1(E_560,k1_zfmisc_1(k2_zfmisc_1(A_563,B_561)))
      | ~ v1_funct_1(E_560) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_4698,plain,(
    ! [D_484,C_485,A_486,B_487] :
      ( D_484 = C_485
      | ~ r2_relset_1(A_486,B_487,C_485,D_484)
      | ~ m1_subset_1(D_484,k1_zfmisc_1(k2_zfmisc_1(A_486,B_487)))
      | ~ m1_subset_1(C_485,k1_zfmisc_1(k2_zfmisc_1(A_486,B_487))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4708,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_88,c_4698])).

tff(c_4727,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_4708])).

tff(c_4763,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_4727])).

tff(c_5322,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_5309,c_4763])).

tff(c_5355,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_96,c_94,c_90,c_5322])).

tff(c_5356,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_4727])).

tff(c_5828,plain,(
    ! [D_622,E_621,F_619,A_623,C_620,B_618] :
      ( k1_partfun1(A_623,B_618,C_620,D_622,E_621,F_619) = k5_relat_1(E_621,F_619)
      | ~ m1_subset_1(F_619,k1_zfmisc_1(k2_zfmisc_1(C_620,D_622)))
      | ~ v1_funct_1(F_619)
      | ~ m1_subset_1(E_621,k1_zfmisc_1(k2_zfmisc_1(A_623,B_618)))
      | ~ v1_funct_1(E_621) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_5832,plain,(
    ! [A_623,B_618,E_621] :
      ( k1_partfun1(A_623,B_618,'#skF_4','#skF_3',E_621,'#skF_6') = k5_relat_1(E_621,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_621,k1_zfmisc_1(k2_zfmisc_1(A_623,B_618)))
      | ~ v1_funct_1(E_621) ) ),
    inference(resolution,[status(thm)],[c_90,c_5828])).

tff(c_5989,plain,(
    ! [A_643,B_644,E_645] :
      ( k1_partfun1(A_643,B_644,'#skF_4','#skF_3',E_645,'#skF_6') = k5_relat_1(E_645,'#skF_6')
      | ~ m1_subset_1(E_645,k1_zfmisc_1(k2_zfmisc_1(A_643,B_644)))
      | ~ v1_funct_1(E_645) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_5832])).

tff(c_6001,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_5989])).

tff(c_6019,plain,(
    k5_relat_1('#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_5356,c_6001])).

tff(c_34,plain,(
    ! [A_20,B_22] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_20,B_22)),k2_relat_1(B_22))
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6024,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_3')),k2_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6019,c_34])).

tff(c_6028,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3702,c_3699,c_103,c_6024])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6039,plain,
    ( k2_relat_1('#skF_6') = '#skF_3'
    | ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_6028,c_6])).

tff(c_6041,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_6039])).

tff(c_6052,plain,
    ( ~ v5_relat_1('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_28,c_6041])).

tff(c_6057,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3699,c_3770,c_6052])).

tff(c_6058,plain,(
    k2_relat_1('#skF_6') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6039])).

tff(c_10,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3705,plain,(
    ! [B_397,A_398] :
      ( v5_relat_1(B_397,A_398)
      | ~ r1_tarski(k2_relat_1(B_397),A_398)
      | ~ v1_relat_1(B_397) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3715,plain,(
    ! [B_397] :
      ( v5_relat_1(B_397,k2_relat_1(B_397))
      | ~ v1_relat_1(B_397) ) ),
    inference(resolution,[status(thm)],[c_10,c_3705])).

tff(c_4245,plain,(
    ! [B_444] :
      ( v2_funct_2(B_444,k2_relat_1(B_444))
      | ~ v5_relat_1(B_444,k2_relat_1(B_444))
      | ~ v1_relat_1(B_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_4271,plain,(
    ! [B_397] :
      ( v2_funct_2(B_397,k2_relat_1(B_397))
      | ~ v1_relat_1(B_397) ) ),
    inference(resolution,[status(thm)],[c_3715,c_4245])).

tff(c_6071,plain,
    ( v2_funct_2('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6058,c_4271])).

tff(c_6088,plain,(
    v2_funct_2('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3699,c_6071])).

tff(c_6090,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3587,c_6088])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:32:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.16/2.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.16/2.43  
% 7.16/2.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.16/2.44  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 7.16/2.44  
% 7.16/2.44  %Foreground sorts:
% 7.16/2.44  
% 7.16/2.44  
% 7.16/2.44  %Background operators:
% 7.16/2.44  
% 7.16/2.44  
% 7.16/2.44  %Foreground operators:
% 7.16/2.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.16/2.44  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.16/2.44  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.16/2.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.16/2.44  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.16/2.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.16/2.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.16/2.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.16/2.44  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.16/2.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.16/2.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.16/2.44  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.16/2.44  tff('#skF_5', type, '#skF_5': $i).
% 7.16/2.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.16/2.44  tff('#skF_6', type, '#skF_6': $i).
% 7.16/2.44  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.16/2.44  tff('#skF_3', type, '#skF_3': $i).
% 7.16/2.44  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.16/2.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.16/2.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.16/2.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.16/2.44  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.16/2.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.16/2.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.16/2.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.16/2.44  tff('#skF_4', type, '#skF_4': $i).
% 7.16/2.44  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.16/2.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.16/2.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.16/2.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.16/2.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.16/2.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.16/2.44  
% 7.31/2.46  tff(f_208, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 7.31/2.46  tff(f_115, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 7.31/2.46  tff(f_166, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.31/2.46  tff(f_102, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.31/2.46  tff(f_164, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.31/2.46  tff(f_150, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.31/2.46  tff(f_154, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.31/2.46  tff(f_130, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.31/2.46  tff(f_188, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 7.31/2.46  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.31/2.46  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 7.31/2.46  tff(f_122, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 7.31/2.46  tff(f_72, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.31/2.46  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.31/2.46  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.31/2.46  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 7.31/2.46  tff(f_83, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.31/2.46  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 7.31/2.46  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.31/2.46  tff(f_138, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 7.31/2.46  tff(c_96, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.31/2.46  tff(c_429, plain, (![C_120, A_121, B_122]: (v1_xboole_0(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))) | ~v1_xboole_0(A_121))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.31/2.46  tff(c_450, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_96, c_429])).
% 7.31/2.46  tff(c_456, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_450])).
% 7.31/2.46  tff(c_86, plain, (~v2_funct_2('#skF_6', '#skF_3') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.31/2.46  tff(c_181, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_86])).
% 7.31/2.46  tff(c_100, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.31/2.46  tff(c_98, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.31/2.46  tff(c_94, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.31/2.46  tff(c_92, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.31/2.46  tff(c_90, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.31/2.46  tff(c_80, plain, (![A_62]: (k6_relat_1(A_62)=k6_partfun1(A_62))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.31/2.46  tff(c_52, plain, (![A_31]: (v2_funct_1(k6_relat_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.31/2.46  tff(c_101, plain, (![A_31]: (v2_funct_1(k6_partfun1(A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_52])).
% 7.31/2.46  tff(c_1786, plain, (![D_242, E_241, B_238, F_239, A_243, C_240]: (k1_partfun1(A_243, B_238, C_240, D_242, E_241, F_239)=k5_relat_1(E_241, F_239) | ~m1_subset_1(F_239, k1_zfmisc_1(k2_zfmisc_1(C_240, D_242))) | ~v1_funct_1(F_239) | ~m1_subset_1(E_241, k1_zfmisc_1(k2_zfmisc_1(A_243, B_238))) | ~v1_funct_1(E_241))), inference(cnfTransformation, [status(thm)], [f_164])).
% 7.31/2.46  tff(c_1792, plain, (![A_243, B_238, E_241]: (k1_partfun1(A_243, B_238, '#skF_4', '#skF_3', E_241, '#skF_6')=k5_relat_1(E_241, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_241, k1_zfmisc_1(k2_zfmisc_1(A_243, B_238))) | ~v1_funct_1(E_241))), inference(resolution, [status(thm)], [c_90, c_1786])).
% 7.31/2.46  tff(c_1963, plain, (![A_267, B_268, E_269]: (k1_partfun1(A_267, B_268, '#skF_4', '#skF_3', E_269, '#skF_6')=k5_relat_1(E_269, '#skF_6') | ~m1_subset_1(E_269, k1_zfmisc_1(k2_zfmisc_1(A_267, B_268))) | ~v1_funct_1(E_269))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_1792])).
% 7.31/2.46  tff(c_1972, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_96, c_1963])).
% 7.31/2.46  tff(c_1990, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_1972])).
% 7.31/2.46  tff(c_70, plain, (![D_52, C_51, F_54, B_50, A_49, E_53]: (m1_subset_1(k1_partfun1(A_49, B_50, C_51, D_52, E_53, F_54), k1_zfmisc_1(k2_zfmisc_1(A_49, D_52))) | ~m1_subset_1(F_54, k1_zfmisc_1(k2_zfmisc_1(C_51, D_52))) | ~v1_funct_1(F_54) | ~m1_subset_1(E_53, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | ~v1_funct_1(E_53))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.31/2.46  tff(c_2012, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1990, c_70])).
% 7.31/2.46  tff(c_2016, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_96, c_94, c_90, c_2012])).
% 7.31/2.46  tff(c_76, plain, (![A_55]: (m1_subset_1(k6_partfun1(A_55), k1_zfmisc_1(k2_zfmisc_1(A_55, A_55))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 7.31/2.46  tff(c_88, plain, (r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k6_partfun1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.31/2.46  tff(c_1325, plain, (![D_187, C_188, A_189, B_190]: (D_187=C_188 | ~r2_relset_1(A_189, B_190, C_188, D_187) | ~m1_subset_1(D_187, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.31/2.46  tff(c_1335, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_88, c_1325])).
% 7.31/2.46  tff(c_1354, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1335])).
% 7.31/2.46  tff(c_1465, plain, (~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(splitLeft, [status(thm)], [c_1354])).
% 7.31/2.46  tff(c_2402, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2016, c_1990, c_1465])).
% 7.31/2.46  tff(c_2403, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_1354])).
% 7.31/2.46  tff(c_3113, plain, (![D_362, E_361, B_359, A_360, C_358]: (k1_xboole_0=C_358 | v2_funct_1(D_362) | ~v2_funct_1(k1_partfun1(A_360, B_359, B_359, C_358, D_362, E_361)) | ~m1_subset_1(E_361, k1_zfmisc_1(k2_zfmisc_1(B_359, C_358))) | ~v1_funct_2(E_361, B_359, C_358) | ~v1_funct_1(E_361) | ~m1_subset_1(D_362, k1_zfmisc_1(k2_zfmisc_1(A_360, B_359))) | ~v1_funct_2(D_362, A_360, B_359) | ~v1_funct_1(D_362))), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.31/2.46  tff(c_3117, plain, (k1_xboole_0='#skF_3' | v2_funct_1('#skF_5') | ~v2_funct_1(k6_partfun1('#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2403, c_3113])).
% 7.31/2.46  tff(c_3124, plain, (k1_xboole_0='#skF_3' | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_96, c_94, c_92, c_90, c_101, c_3117])).
% 7.31/2.46  tff(c_3125, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_181, c_3124])).
% 7.31/2.46  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.31/2.46  tff(c_3172, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3125, c_2])).
% 7.31/2.46  tff(c_3174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_456, c_3172])).
% 7.31/2.46  tff(c_3176, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_450])).
% 7.31/2.46  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 7.31/2.46  tff(c_3192, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3176, c_4])).
% 7.31/2.46  tff(c_3175, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_450])).
% 7.31/2.46  tff(c_3184, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3175, c_4])).
% 7.31/2.46  tff(c_3219, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3192, c_3184])).
% 7.31/2.46  tff(c_3230, plain, (~v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3219, c_181])).
% 7.31/2.46  tff(c_3273, plain, (![C_367, B_368, A_369]: (v1_xboole_0(C_367) | ~m1_subset_1(C_367, k1_zfmisc_1(k2_zfmisc_1(B_368, A_369))) | ~v1_xboole_0(A_369))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.31/2.46  tff(c_3476, plain, (![A_380]: (v1_xboole_0(k6_partfun1(A_380)) | ~v1_xboole_0(A_380))), inference(resolution, [status(thm)], [c_76, c_3273])).
% 7.31/2.46  tff(c_3211, plain, (![A_1]: (A_1='#skF_5' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_3184, c_4])).
% 7.31/2.46  tff(c_3431, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_3219, c_3211])).
% 7.31/2.46  tff(c_3518, plain, (![A_383]: (k6_partfun1(A_383)='#skF_3' | ~v1_xboole_0(A_383))), inference(resolution, [status(thm)], [c_3476, c_3431])).
% 7.31/2.46  tff(c_3529, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_3176, c_3518])).
% 7.31/2.46  tff(c_3571, plain, (v2_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3529, c_101])).
% 7.31/2.46  tff(c_3586, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3230, c_3571])).
% 7.31/2.46  tff(c_3587, plain, (~v2_funct_2('#skF_6', '#skF_3')), inference(splitRight, [status(thm)], [c_86])).
% 7.31/2.46  tff(c_32, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.31/2.46  tff(c_3675, plain, (![B_395, A_396]: (v1_relat_1(B_395) | ~m1_subset_1(B_395, k1_zfmisc_1(A_396)) | ~v1_relat_1(A_396))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.31/2.46  tff(c_3684, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_90, c_3675])).
% 7.31/2.46  tff(c_3699, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3684])).
% 7.31/2.46  tff(c_3748, plain, (![C_405, B_406, A_407]: (v5_relat_1(C_405, B_406) | ~m1_subset_1(C_405, k1_zfmisc_1(k2_zfmisc_1(A_407, B_406))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.31/2.46  tff(c_3770, plain, (v5_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_90, c_3748])).
% 7.31/2.46  tff(c_28, plain, (![B_16, A_15]: (r1_tarski(k2_relat_1(B_16), A_15) | ~v5_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.31/2.46  tff(c_3687, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_96, c_3675])).
% 7.31/2.46  tff(c_3702, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3687])).
% 7.31/2.46  tff(c_38, plain, (![A_23]: (k2_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.31/2.46  tff(c_103, plain, (![A_23]: (k2_relat_1(k6_partfun1(A_23))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_38])).
% 7.31/2.46  tff(c_5309, plain, (![D_564, A_563, C_559, E_560, F_562, B_561]: (m1_subset_1(k1_partfun1(A_563, B_561, C_559, D_564, E_560, F_562), k1_zfmisc_1(k2_zfmisc_1(A_563, D_564))) | ~m1_subset_1(F_562, k1_zfmisc_1(k2_zfmisc_1(C_559, D_564))) | ~v1_funct_1(F_562) | ~m1_subset_1(E_560, k1_zfmisc_1(k2_zfmisc_1(A_563, B_561))) | ~v1_funct_1(E_560))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.31/2.46  tff(c_4698, plain, (![D_484, C_485, A_486, B_487]: (D_484=C_485 | ~r2_relset_1(A_486, B_487, C_485, D_484) | ~m1_subset_1(D_484, k1_zfmisc_1(k2_zfmisc_1(A_486, B_487))) | ~m1_subset_1(C_485, k1_zfmisc_1(k2_zfmisc_1(A_486, B_487))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.31/2.46  tff(c_4708, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_88, c_4698])).
% 7.31/2.46  tff(c_4727, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_4708])).
% 7.31/2.46  tff(c_4763, plain, (~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(splitLeft, [status(thm)], [c_4727])).
% 7.31/2.46  tff(c_5322, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_5309, c_4763])).
% 7.31/2.46  tff(c_5355, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_96, c_94, c_90, c_5322])).
% 7.31/2.46  tff(c_5356, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_4727])).
% 7.31/2.46  tff(c_5828, plain, (![D_622, E_621, F_619, A_623, C_620, B_618]: (k1_partfun1(A_623, B_618, C_620, D_622, E_621, F_619)=k5_relat_1(E_621, F_619) | ~m1_subset_1(F_619, k1_zfmisc_1(k2_zfmisc_1(C_620, D_622))) | ~v1_funct_1(F_619) | ~m1_subset_1(E_621, k1_zfmisc_1(k2_zfmisc_1(A_623, B_618))) | ~v1_funct_1(E_621))), inference(cnfTransformation, [status(thm)], [f_164])).
% 7.31/2.46  tff(c_5832, plain, (![A_623, B_618, E_621]: (k1_partfun1(A_623, B_618, '#skF_4', '#skF_3', E_621, '#skF_6')=k5_relat_1(E_621, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_621, k1_zfmisc_1(k2_zfmisc_1(A_623, B_618))) | ~v1_funct_1(E_621))), inference(resolution, [status(thm)], [c_90, c_5828])).
% 7.31/2.46  tff(c_5989, plain, (![A_643, B_644, E_645]: (k1_partfun1(A_643, B_644, '#skF_4', '#skF_3', E_645, '#skF_6')=k5_relat_1(E_645, '#skF_6') | ~m1_subset_1(E_645, k1_zfmisc_1(k2_zfmisc_1(A_643, B_644))) | ~v1_funct_1(E_645))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_5832])).
% 7.31/2.46  tff(c_6001, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_96, c_5989])).
% 7.31/2.46  tff(c_6019, plain, (k5_relat_1('#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_5356, c_6001])).
% 7.31/2.46  tff(c_34, plain, (![A_20, B_22]: (r1_tarski(k2_relat_1(k5_relat_1(A_20, B_22)), k2_relat_1(B_22)) | ~v1_relat_1(B_22) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.31/2.46  tff(c_6024, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_3')), k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6019, c_34])).
% 7.31/2.46  tff(c_6028, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3702, c_3699, c_103, c_6024])).
% 7.31/2.46  tff(c_6, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.31/2.46  tff(c_6039, plain, (k2_relat_1('#skF_6')='#skF_3' | ~r1_tarski(k2_relat_1('#skF_6'), '#skF_3')), inference(resolution, [status(thm)], [c_6028, c_6])).
% 7.31/2.46  tff(c_6041, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_3')), inference(splitLeft, [status(thm)], [c_6039])).
% 7.31/2.46  tff(c_6052, plain, (~v5_relat_1('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_28, c_6041])).
% 7.31/2.46  tff(c_6057, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3699, c_3770, c_6052])).
% 7.31/2.46  tff(c_6058, plain, (k2_relat_1('#skF_6')='#skF_3'), inference(splitRight, [status(thm)], [c_6039])).
% 7.31/2.46  tff(c_10, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.31/2.46  tff(c_3705, plain, (![B_397, A_398]: (v5_relat_1(B_397, A_398) | ~r1_tarski(k2_relat_1(B_397), A_398) | ~v1_relat_1(B_397))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.31/2.46  tff(c_3715, plain, (![B_397]: (v5_relat_1(B_397, k2_relat_1(B_397)) | ~v1_relat_1(B_397))), inference(resolution, [status(thm)], [c_10, c_3705])).
% 7.31/2.46  tff(c_4245, plain, (![B_444]: (v2_funct_2(B_444, k2_relat_1(B_444)) | ~v5_relat_1(B_444, k2_relat_1(B_444)) | ~v1_relat_1(B_444))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.31/2.46  tff(c_4271, plain, (![B_397]: (v2_funct_2(B_397, k2_relat_1(B_397)) | ~v1_relat_1(B_397))), inference(resolution, [status(thm)], [c_3715, c_4245])).
% 7.31/2.46  tff(c_6071, plain, (v2_funct_2('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6058, c_4271])).
% 7.31/2.46  tff(c_6088, plain, (v2_funct_2('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3699, c_6071])).
% 7.31/2.46  tff(c_6090, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3587, c_6088])).
% 7.31/2.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.46  
% 7.31/2.46  Inference rules
% 7.31/2.46  ----------------------
% 7.31/2.46  #Ref     : 3
% 7.31/2.46  #Sup     : 1342
% 7.31/2.46  #Fact    : 0
% 7.31/2.46  #Define  : 0
% 7.31/2.46  #Split   : 17
% 7.31/2.46  #Chain   : 0
% 7.31/2.46  #Close   : 0
% 7.31/2.46  
% 7.31/2.46  Ordering : KBO
% 7.31/2.46  
% 7.31/2.46  Simplification rules
% 7.31/2.46  ----------------------
% 7.31/2.46  #Subsume      : 325
% 7.31/2.46  #Demod        : 974
% 7.31/2.46  #Tautology    : 399
% 7.31/2.46  #SimpNegUnit  : 13
% 7.31/2.46  #BackRed      : 99
% 7.31/2.46  
% 7.31/2.46  #Partial instantiations: 0
% 7.31/2.46  #Strategies tried      : 1
% 7.31/2.46  
% 7.31/2.46  Timing (in seconds)
% 7.31/2.46  ----------------------
% 7.31/2.46  Preprocessing        : 0.44
% 7.31/2.46  Parsing              : 0.25
% 7.31/2.46  CNF conversion       : 0.03
% 7.31/2.46  Main loop            : 1.22
% 7.31/2.46  Inferencing          : 0.40
% 7.31/2.46  Reduction            : 0.41
% 7.31/2.46  Demodulation         : 0.30
% 7.31/2.46  BG Simplification    : 0.05
% 7.31/2.46  Subsumption          : 0.26
% 7.31/2.46  Abstraction          : 0.05
% 7.31/2.46  MUC search           : 0.00
% 7.31/2.46  Cooper               : 0.00
% 7.31/2.46  Total                : 1.70
% 7.31/2.46  Index Insertion      : 0.00
% 7.31/2.46  Index Deletion       : 0.00
% 7.31/2.46  Index Matching       : 0.00
% 7.31/2.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
