%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:16 EST 2020

% Result     : Theorem 7.02s
% Output     : CNFRefutation 7.22s
% Verified   : 
% Statistics : Number of formulae       :  222 (1861 expanded)
%              Number of leaves         :   45 ( 612 expanded)
%              Depth                    :   13
%              Number of atoms          :  402 (5134 expanded)
%              Number of equality atoms :  104 (1353 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_104,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_64,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_102,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_82,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_121,axiom,(
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

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_60,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_113,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_68,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_66,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_52,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_32,plain,(
    ! [A_17] : v2_funct_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_76,plain,(
    ! [A_17] : v2_funct_1(k6_partfun1(A_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_32])).

tff(c_48,plain,(
    ! [A_31,C_33,B_32,F_36,E_35,D_34] :
      ( m1_subset_1(k1_partfun1(A_31,B_32,C_33,D_34,E_35,F_36),k1_zfmisc_1(k2_zfmisc_1(A_31,D_34)))
      | ~ m1_subset_1(F_36,k1_zfmisc_1(k2_zfmisc_1(C_33,D_34)))
      | ~ v1_funct_1(F_36)
      | ~ m1_subset_1(E_35,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ v1_funct_1(E_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_42,plain,(
    ! [A_28] : m1_subset_1(k6_relat_1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_75,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_42])).

tff(c_62,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_819,plain,(
    ! [D_162,C_163,A_164,B_165] :
      ( D_162 = C_163
      | ~ r2_relset_1(A_164,B_165,C_163,D_162)
      | ~ m1_subset_1(D_162,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165)))
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_829,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_62,c_819])).

tff(c_848,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_829])).

tff(c_871,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_848])).

tff(c_1263,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_871])).

tff(c_1270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_68,c_64,c_1263])).

tff(c_1271,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_848])).

tff(c_1752,plain,(
    ! [A_308,E_305,D_307,C_306,B_309] :
      ( k1_xboole_0 = C_306
      | v2_funct_1(D_307)
      | ~ v2_funct_1(k1_partfun1(A_308,B_309,B_309,C_306,D_307,E_305))
      | ~ m1_subset_1(E_305,k1_zfmisc_1(k2_zfmisc_1(B_309,C_306)))
      | ~ v1_funct_2(E_305,B_309,C_306)
      | ~ v1_funct_1(E_305)
      | ~ m1_subset_1(D_307,k1_zfmisc_1(k2_zfmisc_1(A_308,B_309)))
      | ~ v1_funct_2(D_307,A_308,B_309)
      | ~ v1_funct_1(D_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1754,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1271,c_1752])).

tff(c_1756,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_64,c_76,c_1754])).

tff(c_1757,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_1756])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1787,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1757,c_8])).

tff(c_18,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1786,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1757,c_1757,c_18])).

tff(c_533,plain,(
    ! [C_121,B_122,A_123] :
      ( ~ v1_xboole_0(C_121)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(C_121))
      | ~ r2_hidden(A_123,B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_550,plain,(
    ! [A_123] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2'))
      | ~ r2_hidden(A_123,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_533])).

tff(c_598,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_550])).

tff(c_1881,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1786,c_598])).

tff(c_1887,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1787,c_1881])).

tff(c_1889,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_550])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2168,plain,(
    ! [B_338,A_339,A_340] :
      ( ~ v1_xboole_0(B_338)
      | ~ r2_hidden(A_339,A_340)
      | ~ r1_tarski(A_340,B_338) ) ),
    inference(resolution,[status(thm)],[c_24,c_533])).

tff(c_2222,plain,(
    ! [B_350,A_351,B_352] :
      ( ~ v1_xboole_0(B_350)
      | ~ r1_tarski(A_351,B_350)
      | r1_tarski(A_351,B_352) ) ),
    inference(resolution,[status(thm)],[c_6,c_2168])).

tff(c_2239,plain,(
    ! [B_353,B_354] :
      ( ~ v1_xboole_0(B_353)
      | r1_tarski(B_353,B_354) ) ),
    inference(resolution,[status(thm)],[c_14,c_2222])).

tff(c_125,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(A_58,B_59)
      | ~ m1_subset_1(A_58,k1_zfmisc_1(B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_145,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_125])).

tff(c_169,plain,(
    ! [B_65,A_66] :
      ( B_65 = A_66
      | ~ r1_tarski(B_65,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_181,plain,
    ( k2_zfmisc_1('#skF_3','#skF_2') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_145,c_169])).

tff(c_420,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_2263,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2239,c_420])).

tff(c_2275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1889,c_2263])).

tff(c_2276,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_2280,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2276,c_64])).

tff(c_2720,plain,(
    ! [D_424,C_425,A_426,B_427] :
      ( D_424 = C_425
      | ~ r2_relset_1(A_426,B_427,C_425,D_424)
      | ~ m1_subset_1(D_424,k1_zfmisc_1(k2_zfmisc_1(A_426,B_427)))
      | ~ m1_subset_1(C_425,k1_zfmisc_1(k2_zfmisc_1(A_426,B_427))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2734,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_62,c_2720])).

tff(c_2759,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_2734])).

tff(c_2781,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2759])).

tff(c_3173,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_2781])).

tff(c_3180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_68,c_2280,c_2276,c_3173])).

tff(c_3181,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2759])).

tff(c_3611,plain,(
    ! [B_563,A_562,D_561,E_559,C_560] :
      ( k1_xboole_0 = C_560
      | v2_funct_1(D_561)
      | ~ v2_funct_1(k1_partfun1(A_562,B_563,B_563,C_560,D_561,E_559))
      | ~ m1_subset_1(E_559,k1_zfmisc_1(k2_zfmisc_1(B_563,C_560)))
      | ~ v1_funct_2(E_559,B_563,C_560)
      | ~ v1_funct_1(E_559)
      | ~ m1_subset_1(D_561,k1_zfmisc_1(k2_zfmisc_1(A_562,B_563)))
      | ~ v1_funct_2(D_561,A_562,B_563)
      | ~ v1_funct_1(D_561) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3613,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3181,c_3611])).

tff(c_3615,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_2280,c_2276,c_76,c_3613])).

tff(c_3616,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_3615])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( k1_xboole_0 = B_9
      | k1_xboole_0 = A_8
      | k2_zfmisc_1(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2285,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2276,c_16])).

tff(c_2342,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2285])).

tff(c_3644,plain,(
    '#skF_5' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3616,c_2342])).

tff(c_3653,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3616,c_3616,c_18])).

tff(c_3765,plain,(
    '#skF_5' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3653,c_2276])).

tff(c_3767,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3644,c_3765])).

tff(c_3769,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2285])).

tff(c_3768,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2285])).

tff(c_3864,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3769,c_3769,c_3768])).

tff(c_3865,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3864])).

tff(c_3779,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3769,c_8])).

tff(c_3872,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3865,c_3779])).

tff(c_3874,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3865,c_3865,c_2280])).

tff(c_26,plain,(
    ! [C_14,B_13,A_12] :
      ( ~ v1_xboole_0(C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(C_14))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4000,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_12,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3874,c_26])).

tff(c_4009,plain,(
    ! [A_588] : ~ r2_hidden(A_588,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3872,c_4000])).

tff(c_4014,plain,(
    ! [B_2] : r1_tarski('#skF_2',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_4009])).

tff(c_20,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3777,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_5',B_9) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3769,c_3769,c_20])).

tff(c_3867,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_2',B_9) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3865,c_3865,c_3777])).

tff(c_144,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_70,c_125])).

tff(c_182,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_144,c_169])).

tff(c_2278,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_3917,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3867,c_2278])).

tff(c_4017,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4014,c_3917])).

tff(c_4018,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3864])).

tff(c_4026,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4018,c_3779])).

tff(c_4028,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4018,c_4018,c_2280])).

tff(c_4097,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_12,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4028,c_26])).

tff(c_4106,plain,(
    ! [A_595] : ~ r2_hidden(A_595,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4026,c_4097])).

tff(c_4111,plain,(
    ! [B_2] : r1_tarski('#skF_3',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_4106])).

tff(c_3778,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3769,c_3769,c_18])).

tff(c_4022,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4018,c_4018,c_3778])).

tff(c_4142,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4022,c_2278])).

tff(c_4147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4111,c_4142])).

tff(c_4148,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_4161,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4148,c_70])).

tff(c_4151,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2276,c_64])).

tff(c_4926,plain,(
    ! [C_727,B_723,D_722,A_725,F_726,E_724] :
      ( m1_subset_1(k1_partfun1(A_725,B_723,C_727,D_722,E_724,F_726),k1_zfmisc_1(k2_zfmisc_1(A_725,D_722)))
      | ~ m1_subset_1(F_726,k1_zfmisc_1(k2_zfmisc_1(C_727,D_722)))
      | ~ v1_funct_1(F_726)
      | ~ m1_subset_1(E_724,k1_zfmisc_1(k2_zfmisc_1(A_725,B_723)))
      | ~ v1_funct_1(E_724) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4668,plain,(
    ! [D_684,C_685,A_686,B_687] :
      ( D_684 = C_685
      | ~ r2_relset_1(A_686,B_687,C_685,D_684)
      | ~ m1_subset_1(D_684,k1_zfmisc_1(k2_zfmisc_1(A_686,B_687)))
      | ~ m1_subset_1(C_685,k1_zfmisc_1(k2_zfmisc_1(A_686,B_687))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4684,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_62,c_4668])).

tff(c_4712,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_4684])).

tff(c_4734,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_4712])).

tff(c_4929,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4926,c_4734])).

tff(c_4960,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4161,c_4148,c_68,c_4151,c_2276,c_4929])).

tff(c_4961,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_4712])).

tff(c_5545,plain,(
    ! [A_808,D_807,C_806,E_805,B_809] :
      ( k1_xboole_0 = C_806
      | v2_funct_1(D_807)
      | ~ v2_funct_1(k1_partfun1(A_808,B_809,B_809,C_806,D_807,E_805))
      | ~ m1_subset_1(E_805,k1_zfmisc_1(k2_zfmisc_1(B_809,C_806)))
      | ~ v1_funct_2(E_805,B_809,C_806)
      | ~ v1_funct_1(E_805)
      | ~ m1_subset_1(D_807,k1_zfmisc_1(k2_zfmisc_1(A_808,B_809)))
      | ~ v1_funct_2(D_807,A_808,B_809)
      | ~ v1_funct_1(D_807) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_5547,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4961,c_5545])).

tff(c_5549,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_4161,c_4148,c_68,c_66,c_4151,c_2276,c_76,c_5547])).

tff(c_5550,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_5549])).

tff(c_4156,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2276,c_16])).

tff(c_4249,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_4156])).

tff(c_5573,plain,(
    '#skF_5' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5550,c_4249])).

tff(c_5583,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5550,c_5550,c_18])).

tff(c_5720,plain,(
    '#skF_5' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5583,c_2276])).

tff(c_5722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5573,c_5720])).

tff(c_5724,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4156])).

tff(c_5723,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4156])).

tff(c_5823,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5724,c_5724,c_5723])).

tff(c_5824,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_5823])).

tff(c_4166,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_4148,c_16])).

tff(c_4220,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4166])).

tff(c_5726,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5724,c_4220])).

tff(c_5829,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5824,c_5726])).

tff(c_5733,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_5',B_9) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5724,c_5724,c_20])).

tff(c_5893,plain,(
    ! [B_826] : k2_zfmisc_1('#skF_2',B_826) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5824,c_5824,c_5733])).

tff(c_5902,plain,(
    '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_5893,c_4148])).

tff(c_5921,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5829,c_5902])).

tff(c_5922,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5823])).

tff(c_5928,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5922,c_5726])).

tff(c_5734,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5724,c_5724,c_18])).

tff(c_5974,plain,(
    ! [A_830] : k2_zfmisc_1(A_830,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5922,c_5922,c_5734])).

tff(c_5980,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_5974,c_4148])).

tff(c_5995,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5928,c_5980])).

tff(c_5997,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4166])).

tff(c_219,plain,(
    ! [C_72,B_73,A_74] :
      ( ~ v1_xboole_0(C_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(C_72))
      | ~ r2_hidden(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_340,plain,(
    ! [B_91,A_92,A_93] :
      ( ~ v1_xboole_0(B_91)
      | ~ r2_hidden(A_92,A_93)
      | ~ r1_tarski(A_93,B_91) ) ),
    inference(resolution,[status(thm)],[c_24,c_219])).

tff(c_344,plain,(
    ! [B_94,A_95,B_96] :
      ( ~ v1_xboole_0(B_94)
      | ~ r1_tarski(A_95,B_94)
      | r1_tarski(A_95,B_96) ) ),
    inference(resolution,[status(thm)],[c_6,c_340])).

tff(c_361,plain,(
    ! [B_97,B_98] :
      ( ~ v1_xboole_0(B_97)
      | r1_tarski(B_97,B_98) ) ),
    inference(resolution,[status(thm)],[c_14,c_344])).

tff(c_115,plain,(
    ! [A_57] : m1_subset_1(k6_partfun1(A_57),k1_zfmisc_1(k2_zfmisc_1(A_57,A_57))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_42])).

tff(c_119,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_115])).

tff(c_141,plain,(
    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_119,c_125])).

tff(c_183,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_141,c_169])).

tff(c_188,plain,(
    ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_381,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_361,c_188])).

tff(c_392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_381])).

tff(c_393,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_413,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_76])).

tff(c_6005,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5997,c_413])).

tff(c_6013,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_6005])).

tff(c_6014,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_6329,plain,(
    ! [C_880,A_881,B_882] :
      ( v1_relat_1(C_880)
      | ~ m1_subset_1(C_880,k1_zfmisc_1(k2_zfmisc_1(A_881,B_882))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6350,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_6329])).

tff(c_6627,plain,(
    ! [A_926,B_927,D_928] :
      ( r2_relset_1(A_926,B_927,D_928,D_928)
      | ~ m1_subset_1(D_928,k1_zfmisc_1(k2_zfmisc_1(A_926,B_927))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6642,plain,(
    ! [A_28] : r2_relset_1(A_28,A_28,k6_partfun1(A_28),k6_partfun1(A_28)) ),
    inference(resolution,[status(thm)],[c_75,c_6627])).

tff(c_6706,plain,(
    ! [A_938,B_939,C_940] :
      ( k2_relset_1(A_938,B_939,C_940) = k2_relat_1(C_940)
      | ~ m1_subset_1(C_940,k1_zfmisc_1(k2_zfmisc_1(A_938,B_939))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6729,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_6706])).

tff(c_6756,plain,(
    ! [D_944,C_945,A_946,B_947] :
      ( D_944 = C_945
      | ~ r2_relset_1(A_946,B_947,C_945,D_944)
      | ~ m1_subset_1(D_944,k1_zfmisc_1(k2_zfmisc_1(A_946,B_947)))
      | ~ m1_subset_1(C_945,k1_zfmisc_1(k2_zfmisc_1(A_946,B_947))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6766,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_62,c_6756])).

tff(c_6785,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_6766])).

tff(c_6803,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_6785])).

tff(c_7169,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_6803])).

tff(c_7176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_68,c_64,c_7169])).

tff(c_7177,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_6785])).

tff(c_7735,plain,(
    ! [A_1105,B_1106,C_1107,D_1108] :
      ( k2_relset_1(A_1105,B_1106,C_1107) = B_1106
      | ~ r2_relset_1(B_1106,B_1106,k1_partfun1(B_1106,A_1105,A_1105,B_1106,D_1108,C_1107),k6_partfun1(B_1106))
      | ~ m1_subset_1(D_1108,k1_zfmisc_1(k2_zfmisc_1(B_1106,A_1105)))
      | ~ v1_funct_2(D_1108,B_1106,A_1105)
      | ~ v1_funct_1(D_1108)
      | ~ m1_subset_1(C_1107,k1_zfmisc_1(k2_zfmisc_1(A_1105,B_1106)))
      | ~ v1_funct_2(C_1107,A_1105,B_1106)
      | ~ v1_funct_1(C_1107) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_7738,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7177,c_7735])).

tff(c_7743,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_74,c_72,c_70,c_6642,c_6729,c_7738])).

tff(c_6449,plain,(
    ! [B_897,A_898] :
      ( v5_relat_1(B_897,A_898)
      | ~ r1_tarski(k2_relat_1(B_897),A_898)
      | ~ v1_relat_1(B_897) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6454,plain,(
    ! [B_897] :
      ( v5_relat_1(B_897,k2_relat_1(B_897))
      | ~ v1_relat_1(B_897) ) ),
    inference(resolution,[status(thm)],[c_14,c_6449])).

tff(c_6615,plain,(
    ! [B_923] :
      ( v2_funct_2(B_923,k2_relat_1(B_923))
      | ~ v5_relat_1(B_923,k2_relat_1(B_923))
      | ~ v1_relat_1(B_923) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6619,plain,(
    ! [B_897] :
      ( v2_funct_2(B_897,k2_relat_1(B_897))
      | ~ v1_relat_1(B_897) ) ),
    inference(resolution,[status(thm)],[c_6454,c_6615])).

tff(c_7754,plain,
    ( v2_funct_2('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7743,c_6619])).

tff(c_7774,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6350,c_7754])).

tff(c_7776,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6014,c_7774])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:53:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.02/2.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.10/2.51  
% 7.10/2.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.10/2.51  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.10/2.51  
% 7.10/2.51  %Foreground sorts:
% 7.10/2.51  
% 7.10/2.51  
% 7.10/2.51  %Background operators:
% 7.10/2.51  
% 7.10/2.51  
% 7.10/2.51  %Foreground operators:
% 7.10/2.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.10/2.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.10/2.51  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.10/2.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.10/2.51  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.10/2.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.10/2.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.10/2.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.10/2.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.10/2.51  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.10/2.51  tff('#skF_5', type, '#skF_5': $i).
% 7.10/2.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.10/2.51  tff('#skF_2', type, '#skF_2': $i).
% 7.10/2.51  tff('#skF_3', type, '#skF_3': $i).
% 7.10/2.51  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.10/2.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.10/2.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.10/2.51  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.10/2.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.10/2.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.10/2.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.10/2.51  tff('#skF_4', type, '#skF_4': $i).
% 7.10/2.51  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.10/2.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.10/2.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.10/2.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.10/2.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.10/2.51  
% 7.22/2.54  tff(f_163, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 7.22/2.54  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.22/2.54  tff(f_104, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.22/2.54  tff(f_64, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 7.22/2.54  tff(f_102, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.22/2.54  tff(f_82, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 7.22/2.54  tff(f_80, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.22/2.54  tff(f_143, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 7.22/2.54  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.22/2.54  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.22/2.54  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 7.22/2.54  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.22/2.54  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.22/2.54  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.22/2.54  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.22/2.54  tff(f_121, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 7.22/2.54  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 7.22/2.54  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 7.22/2.54  tff(c_60, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.22/2.54  tff(c_113, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_60])).
% 7.22/2.54  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.22/2.54  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.22/2.54  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.22/2.54  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.22/2.54  tff(c_68, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.22/2.54  tff(c_66, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.22/2.54  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.22/2.54  tff(c_52, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.22/2.54  tff(c_32, plain, (![A_17]: (v2_funct_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.22/2.54  tff(c_76, plain, (![A_17]: (v2_funct_1(k6_partfun1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_32])).
% 7.22/2.54  tff(c_48, plain, (![A_31, C_33, B_32, F_36, E_35, D_34]: (m1_subset_1(k1_partfun1(A_31, B_32, C_33, D_34, E_35, F_36), k1_zfmisc_1(k2_zfmisc_1(A_31, D_34))) | ~m1_subset_1(F_36, k1_zfmisc_1(k2_zfmisc_1(C_33, D_34))) | ~v1_funct_1(F_36) | ~m1_subset_1(E_35, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~v1_funct_1(E_35))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.22/2.54  tff(c_42, plain, (![A_28]: (m1_subset_1(k6_relat_1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.22/2.54  tff(c_75, plain, (![A_28]: (m1_subset_1(k6_partfun1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_42])).
% 7.22/2.54  tff(c_62, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.22/2.54  tff(c_819, plain, (![D_162, C_163, A_164, B_165]: (D_162=C_163 | ~r2_relset_1(A_164, B_165, C_163, D_162) | ~m1_subset_1(D_162, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.22/2.54  tff(c_829, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_62, c_819])).
% 7.22/2.54  tff(c_848, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_829])).
% 7.22/2.54  tff(c_871, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_848])).
% 7.22/2.54  tff(c_1263, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_871])).
% 7.22/2.54  tff(c_1270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_68, c_64, c_1263])).
% 7.22/2.54  tff(c_1271, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_848])).
% 7.22/2.54  tff(c_1752, plain, (![A_308, E_305, D_307, C_306, B_309]: (k1_xboole_0=C_306 | v2_funct_1(D_307) | ~v2_funct_1(k1_partfun1(A_308, B_309, B_309, C_306, D_307, E_305)) | ~m1_subset_1(E_305, k1_zfmisc_1(k2_zfmisc_1(B_309, C_306))) | ~v1_funct_2(E_305, B_309, C_306) | ~v1_funct_1(E_305) | ~m1_subset_1(D_307, k1_zfmisc_1(k2_zfmisc_1(A_308, B_309))) | ~v1_funct_2(D_307, A_308, B_309) | ~v1_funct_1(D_307))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.22/2.54  tff(c_1754, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1271, c_1752])).
% 7.22/2.54  tff(c_1756, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_66, c_64, c_76, c_1754])).
% 7.22/2.54  tff(c_1757, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_113, c_1756])).
% 7.22/2.54  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.22/2.54  tff(c_1787, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1757, c_8])).
% 7.22/2.54  tff(c_18, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.22/2.54  tff(c_1786, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1757, c_1757, c_18])).
% 7.22/2.54  tff(c_533, plain, (![C_121, B_122, A_123]: (~v1_xboole_0(C_121) | ~m1_subset_1(B_122, k1_zfmisc_1(C_121)) | ~r2_hidden(A_123, B_122))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.22/2.54  tff(c_550, plain, (![A_123]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2')) | ~r2_hidden(A_123, '#skF_5'))), inference(resolution, [status(thm)], [c_64, c_533])).
% 7.22/2.54  tff(c_598, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_550])).
% 7.22/2.54  tff(c_1881, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1786, c_598])).
% 7.22/2.54  tff(c_1887, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1787, c_1881])).
% 7.22/2.54  tff(c_1889, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_550])).
% 7.22/2.54  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.22/2.54  tff(c_24, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.22/2.54  tff(c_2168, plain, (![B_338, A_339, A_340]: (~v1_xboole_0(B_338) | ~r2_hidden(A_339, A_340) | ~r1_tarski(A_340, B_338))), inference(resolution, [status(thm)], [c_24, c_533])).
% 7.22/2.54  tff(c_2222, plain, (![B_350, A_351, B_352]: (~v1_xboole_0(B_350) | ~r1_tarski(A_351, B_350) | r1_tarski(A_351, B_352))), inference(resolution, [status(thm)], [c_6, c_2168])).
% 7.22/2.54  tff(c_2239, plain, (![B_353, B_354]: (~v1_xboole_0(B_353) | r1_tarski(B_353, B_354))), inference(resolution, [status(thm)], [c_14, c_2222])).
% 7.22/2.54  tff(c_125, plain, (![A_58, B_59]: (r1_tarski(A_58, B_59) | ~m1_subset_1(A_58, k1_zfmisc_1(B_59)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.22/2.54  tff(c_145, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_125])).
% 7.22/2.54  tff(c_169, plain, (![B_65, A_66]: (B_65=A_66 | ~r1_tarski(B_65, A_66) | ~r1_tarski(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.22/2.54  tff(c_181, plain, (k2_zfmisc_1('#skF_3', '#skF_2')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), '#skF_5')), inference(resolution, [status(thm)], [c_145, c_169])).
% 7.22/2.54  tff(c_420, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), '#skF_5')), inference(splitLeft, [status(thm)], [c_181])).
% 7.22/2.54  tff(c_2263, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_2239, c_420])).
% 7.22/2.54  tff(c_2275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1889, c_2263])).
% 7.22/2.54  tff(c_2276, plain, (k2_zfmisc_1('#skF_3', '#skF_2')='#skF_5'), inference(splitRight, [status(thm)], [c_181])).
% 7.22/2.54  tff(c_2280, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2276, c_64])).
% 7.22/2.54  tff(c_2720, plain, (![D_424, C_425, A_426, B_427]: (D_424=C_425 | ~r2_relset_1(A_426, B_427, C_425, D_424) | ~m1_subset_1(D_424, k1_zfmisc_1(k2_zfmisc_1(A_426, B_427))) | ~m1_subset_1(C_425, k1_zfmisc_1(k2_zfmisc_1(A_426, B_427))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.22/2.54  tff(c_2734, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_62, c_2720])).
% 7.22/2.54  tff(c_2759, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_2734])).
% 7.22/2.54  tff(c_2781, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2759])).
% 7.22/2.54  tff(c_3173, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_2781])).
% 7.22/2.54  tff(c_3180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_68, c_2280, c_2276, c_3173])).
% 7.22/2.54  tff(c_3181, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2759])).
% 7.22/2.54  tff(c_3611, plain, (![B_563, A_562, D_561, E_559, C_560]: (k1_xboole_0=C_560 | v2_funct_1(D_561) | ~v2_funct_1(k1_partfun1(A_562, B_563, B_563, C_560, D_561, E_559)) | ~m1_subset_1(E_559, k1_zfmisc_1(k2_zfmisc_1(B_563, C_560))) | ~v1_funct_2(E_559, B_563, C_560) | ~v1_funct_1(E_559) | ~m1_subset_1(D_561, k1_zfmisc_1(k2_zfmisc_1(A_562, B_563))) | ~v1_funct_2(D_561, A_562, B_563) | ~v1_funct_1(D_561))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.22/2.54  tff(c_3613, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3181, c_3611])).
% 7.22/2.54  tff(c_3615, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_66, c_2280, c_2276, c_76, c_3613])).
% 7.22/2.54  tff(c_3616, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_113, c_3615])).
% 7.22/2.54  tff(c_16, plain, (![B_9, A_8]: (k1_xboole_0=B_9 | k1_xboole_0=A_8 | k2_zfmisc_1(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.22/2.54  tff(c_2285, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2276, c_16])).
% 7.22/2.54  tff(c_2342, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_2285])).
% 7.22/2.54  tff(c_3644, plain, ('#skF_5'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3616, c_2342])).
% 7.22/2.54  tff(c_3653, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3616, c_3616, c_18])).
% 7.22/2.54  tff(c_3765, plain, ('#skF_5'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3653, c_2276])).
% 7.22/2.54  tff(c_3767, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3644, c_3765])).
% 7.22/2.54  tff(c_3769, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2285])).
% 7.22/2.54  tff(c_3768, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_2285])).
% 7.22/2.54  tff(c_3864, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3769, c_3769, c_3768])).
% 7.22/2.54  tff(c_3865, plain, ('#skF_5'='#skF_2'), inference(splitLeft, [status(thm)], [c_3864])).
% 7.22/2.54  tff(c_3779, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3769, c_8])).
% 7.22/2.54  tff(c_3872, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3865, c_3779])).
% 7.22/2.54  tff(c_3874, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3865, c_3865, c_2280])).
% 7.22/2.54  tff(c_26, plain, (![C_14, B_13, A_12]: (~v1_xboole_0(C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(C_14)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.22/2.54  tff(c_4000, plain, (![A_12]: (~v1_xboole_0('#skF_2') | ~r2_hidden(A_12, '#skF_2'))), inference(resolution, [status(thm)], [c_3874, c_26])).
% 7.22/2.54  tff(c_4009, plain, (![A_588]: (~r2_hidden(A_588, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3872, c_4000])).
% 7.22/2.54  tff(c_4014, plain, (![B_2]: (r1_tarski('#skF_2', B_2))), inference(resolution, [status(thm)], [c_6, c_4009])).
% 7.22/2.54  tff(c_20, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.22/2.54  tff(c_3777, plain, (![B_9]: (k2_zfmisc_1('#skF_5', B_9)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3769, c_3769, c_20])).
% 7.22/2.54  tff(c_3867, plain, (![B_9]: (k2_zfmisc_1('#skF_2', B_9)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3865, c_3865, c_3777])).
% 7.22/2.54  tff(c_144, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_70, c_125])).
% 7.22/2.54  tff(c_182, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_144, c_169])).
% 7.22/2.54  tff(c_2278, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_182])).
% 7.22/2.54  tff(c_3917, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3867, c_2278])).
% 7.22/2.54  tff(c_4017, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4014, c_3917])).
% 7.22/2.54  tff(c_4018, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_3864])).
% 7.22/2.54  tff(c_4026, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4018, c_3779])).
% 7.22/2.54  tff(c_4028, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4018, c_4018, c_2280])).
% 7.22/2.54  tff(c_4097, plain, (![A_12]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_12, '#skF_3'))), inference(resolution, [status(thm)], [c_4028, c_26])).
% 7.22/2.54  tff(c_4106, plain, (![A_595]: (~r2_hidden(A_595, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4026, c_4097])).
% 7.22/2.54  tff(c_4111, plain, (![B_2]: (r1_tarski('#skF_3', B_2))), inference(resolution, [status(thm)], [c_6, c_4106])).
% 7.22/2.54  tff(c_3778, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3769, c_3769, c_18])).
% 7.22/2.54  tff(c_4022, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4018, c_4018, c_3778])).
% 7.22/2.54  tff(c_4142, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4022, c_2278])).
% 7.22/2.54  tff(c_4147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4111, c_4142])).
% 7.22/2.54  tff(c_4148, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_182])).
% 7.22/2.54  tff(c_4161, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4148, c_70])).
% 7.22/2.54  tff(c_4151, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2276, c_64])).
% 7.22/2.54  tff(c_4926, plain, (![C_727, B_723, D_722, A_725, F_726, E_724]: (m1_subset_1(k1_partfun1(A_725, B_723, C_727, D_722, E_724, F_726), k1_zfmisc_1(k2_zfmisc_1(A_725, D_722))) | ~m1_subset_1(F_726, k1_zfmisc_1(k2_zfmisc_1(C_727, D_722))) | ~v1_funct_1(F_726) | ~m1_subset_1(E_724, k1_zfmisc_1(k2_zfmisc_1(A_725, B_723))) | ~v1_funct_1(E_724))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.22/2.54  tff(c_4668, plain, (![D_684, C_685, A_686, B_687]: (D_684=C_685 | ~r2_relset_1(A_686, B_687, C_685, D_684) | ~m1_subset_1(D_684, k1_zfmisc_1(k2_zfmisc_1(A_686, B_687))) | ~m1_subset_1(C_685, k1_zfmisc_1(k2_zfmisc_1(A_686, B_687))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.22/2.54  tff(c_4684, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_62, c_4668])).
% 7.22/2.54  tff(c_4712, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_4684])).
% 7.22/2.54  tff(c_4734, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_4712])).
% 7.22/2.54  tff(c_4929, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_4926, c_4734])).
% 7.22/2.54  tff(c_4960, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_4161, c_4148, c_68, c_4151, c_2276, c_4929])).
% 7.22/2.54  tff(c_4961, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_4712])).
% 7.22/2.54  tff(c_5545, plain, (![A_808, D_807, C_806, E_805, B_809]: (k1_xboole_0=C_806 | v2_funct_1(D_807) | ~v2_funct_1(k1_partfun1(A_808, B_809, B_809, C_806, D_807, E_805)) | ~m1_subset_1(E_805, k1_zfmisc_1(k2_zfmisc_1(B_809, C_806))) | ~v1_funct_2(E_805, B_809, C_806) | ~v1_funct_1(E_805) | ~m1_subset_1(D_807, k1_zfmisc_1(k2_zfmisc_1(A_808, B_809))) | ~v1_funct_2(D_807, A_808, B_809) | ~v1_funct_1(D_807))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.22/2.54  tff(c_5547, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4961, c_5545])).
% 7.22/2.54  tff(c_5549, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_4161, c_4148, c_68, c_66, c_4151, c_2276, c_76, c_5547])).
% 7.22/2.54  tff(c_5550, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_113, c_5549])).
% 7.22/2.54  tff(c_4156, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2276, c_16])).
% 7.22/2.54  tff(c_4249, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_4156])).
% 7.22/2.54  tff(c_5573, plain, ('#skF_5'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5550, c_4249])).
% 7.22/2.54  tff(c_5583, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5550, c_5550, c_18])).
% 7.22/2.54  tff(c_5720, plain, ('#skF_5'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5583, c_2276])).
% 7.22/2.54  tff(c_5722, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5573, c_5720])).
% 7.22/2.54  tff(c_5724, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_4156])).
% 7.22/2.54  tff(c_5723, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_4156])).
% 7.22/2.54  tff(c_5823, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5724, c_5724, c_5723])).
% 7.22/2.54  tff(c_5824, plain, ('#skF_5'='#skF_2'), inference(splitLeft, [status(thm)], [c_5823])).
% 7.22/2.54  tff(c_4166, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_4148, c_16])).
% 7.22/2.54  tff(c_4220, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_4166])).
% 7.22/2.54  tff(c_5726, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5724, c_4220])).
% 7.22/2.54  tff(c_5829, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5824, c_5726])).
% 7.22/2.54  tff(c_5733, plain, (![B_9]: (k2_zfmisc_1('#skF_5', B_9)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5724, c_5724, c_20])).
% 7.22/2.54  tff(c_5893, plain, (![B_826]: (k2_zfmisc_1('#skF_2', B_826)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5824, c_5824, c_5733])).
% 7.22/2.54  tff(c_5902, plain, ('#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_5893, c_4148])).
% 7.22/2.54  tff(c_5921, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5829, c_5902])).
% 7.22/2.54  tff(c_5922, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_5823])).
% 7.22/2.54  tff(c_5928, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5922, c_5726])).
% 7.22/2.54  tff(c_5734, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5724, c_5724, c_18])).
% 7.22/2.54  tff(c_5974, plain, (![A_830]: (k2_zfmisc_1(A_830, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5922, c_5922, c_5734])).
% 7.22/2.54  tff(c_5980, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_5974, c_4148])).
% 7.22/2.54  tff(c_5995, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5928, c_5980])).
% 7.22/2.54  tff(c_5997, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_4166])).
% 7.22/2.54  tff(c_219, plain, (![C_72, B_73, A_74]: (~v1_xboole_0(C_72) | ~m1_subset_1(B_73, k1_zfmisc_1(C_72)) | ~r2_hidden(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.22/2.54  tff(c_340, plain, (![B_91, A_92, A_93]: (~v1_xboole_0(B_91) | ~r2_hidden(A_92, A_93) | ~r1_tarski(A_93, B_91))), inference(resolution, [status(thm)], [c_24, c_219])).
% 7.22/2.54  tff(c_344, plain, (![B_94, A_95, B_96]: (~v1_xboole_0(B_94) | ~r1_tarski(A_95, B_94) | r1_tarski(A_95, B_96))), inference(resolution, [status(thm)], [c_6, c_340])).
% 7.22/2.54  tff(c_361, plain, (![B_97, B_98]: (~v1_xboole_0(B_97) | r1_tarski(B_97, B_98))), inference(resolution, [status(thm)], [c_14, c_344])).
% 7.22/2.54  tff(c_115, plain, (![A_57]: (m1_subset_1(k6_partfun1(A_57), k1_zfmisc_1(k2_zfmisc_1(A_57, A_57))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_42])).
% 7.22/2.54  tff(c_119, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_115])).
% 7.22/2.54  tff(c_141, plain, (r1_tarski(k6_partfun1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_119, c_125])).
% 7.22/2.54  tff(c_183, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_141, c_169])).
% 7.22/2.54  tff(c_188, plain, (~r1_tarski(k1_xboole_0, k6_partfun1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_183])).
% 7.22/2.54  tff(c_381, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_361, c_188])).
% 7.22/2.54  tff(c_392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_381])).
% 7.22/2.54  tff(c_393, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_183])).
% 7.22/2.54  tff(c_413, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_393, c_76])).
% 7.22/2.54  tff(c_6005, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5997, c_413])).
% 7.22/2.54  tff(c_6013, plain, $false, inference(negUnitSimplification, [status(thm)], [c_113, c_6005])).
% 7.22/2.54  tff(c_6014, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_60])).
% 7.22/2.54  tff(c_6329, plain, (![C_880, A_881, B_882]: (v1_relat_1(C_880) | ~m1_subset_1(C_880, k1_zfmisc_1(k2_zfmisc_1(A_881, B_882))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.22/2.54  tff(c_6350, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_6329])).
% 7.22/2.54  tff(c_6627, plain, (![A_926, B_927, D_928]: (r2_relset_1(A_926, B_927, D_928, D_928) | ~m1_subset_1(D_928, k1_zfmisc_1(k2_zfmisc_1(A_926, B_927))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.22/2.54  tff(c_6642, plain, (![A_28]: (r2_relset_1(A_28, A_28, k6_partfun1(A_28), k6_partfun1(A_28)))), inference(resolution, [status(thm)], [c_75, c_6627])).
% 7.22/2.54  tff(c_6706, plain, (![A_938, B_939, C_940]: (k2_relset_1(A_938, B_939, C_940)=k2_relat_1(C_940) | ~m1_subset_1(C_940, k1_zfmisc_1(k2_zfmisc_1(A_938, B_939))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.22/2.54  tff(c_6729, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_6706])).
% 7.22/2.54  tff(c_6756, plain, (![D_944, C_945, A_946, B_947]: (D_944=C_945 | ~r2_relset_1(A_946, B_947, C_945, D_944) | ~m1_subset_1(D_944, k1_zfmisc_1(k2_zfmisc_1(A_946, B_947))) | ~m1_subset_1(C_945, k1_zfmisc_1(k2_zfmisc_1(A_946, B_947))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.22/2.54  tff(c_6766, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_62, c_6756])).
% 7.22/2.54  tff(c_6785, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_6766])).
% 7.22/2.54  tff(c_6803, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_6785])).
% 7.22/2.54  tff(c_7169, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_6803])).
% 7.22/2.54  tff(c_7176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_68, c_64, c_7169])).
% 7.22/2.54  tff(c_7177, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_6785])).
% 7.22/2.54  tff(c_7735, plain, (![A_1105, B_1106, C_1107, D_1108]: (k2_relset_1(A_1105, B_1106, C_1107)=B_1106 | ~r2_relset_1(B_1106, B_1106, k1_partfun1(B_1106, A_1105, A_1105, B_1106, D_1108, C_1107), k6_partfun1(B_1106)) | ~m1_subset_1(D_1108, k1_zfmisc_1(k2_zfmisc_1(B_1106, A_1105))) | ~v1_funct_2(D_1108, B_1106, A_1105) | ~v1_funct_1(D_1108) | ~m1_subset_1(C_1107, k1_zfmisc_1(k2_zfmisc_1(A_1105, B_1106))) | ~v1_funct_2(C_1107, A_1105, B_1106) | ~v1_funct_1(C_1107))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.22/2.54  tff(c_7738, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7177, c_7735])).
% 7.22/2.54  tff(c_7743, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_74, c_72, c_70, c_6642, c_6729, c_7738])).
% 7.22/2.54  tff(c_6449, plain, (![B_897, A_898]: (v5_relat_1(B_897, A_898) | ~r1_tarski(k2_relat_1(B_897), A_898) | ~v1_relat_1(B_897))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.22/2.54  tff(c_6454, plain, (![B_897]: (v5_relat_1(B_897, k2_relat_1(B_897)) | ~v1_relat_1(B_897))), inference(resolution, [status(thm)], [c_14, c_6449])).
% 7.22/2.54  tff(c_6615, plain, (![B_923]: (v2_funct_2(B_923, k2_relat_1(B_923)) | ~v5_relat_1(B_923, k2_relat_1(B_923)) | ~v1_relat_1(B_923))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.22/2.54  tff(c_6619, plain, (![B_897]: (v2_funct_2(B_897, k2_relat_1(B_897)) | ~v1_relat_1(B_897))), inference(resolution, [status(thm)], [c_6454, c_6615])).
% 7.22/2.54  tff(c_7754, plain, (v2_funct_2('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7743, c_6619])).
% 7.22/2.54  tff(c_7774, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6350, c_7754])).
% 7.22/2.54  tff(c_7776, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6014, c_7774])).
% 7.22/2.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.22/2.54  
% 7.22/2.54  Inference rules
% 7.22/2.54  ----------------------
% 7.22/2.54  #Ref     : 0
% 7.22/2.54  #Sup     : 1757
% 7.22/2.54  #Fact    : 0
% 7.22/2.54  #Define  : 0
% 7.22/2.54  #Split   : 35
% 7.22/2.54  #Chain   : 0
% 7.22/2.54  #Close   : 0
% 7.22/2.54  
% 7.22/2.54  Ordering : KBO
% 7.22/2.54  
% 7.22/2.54  Simplification rules
% 7.22/2.54  ----------------------
% 7.22/2.54  #Subsume      : 208
% 7.22/2.54  #Demod        : 1217
% 7.22/2.54  #Tautology    : 770
% 7.22/2.54  #SimpNegUnit  : 9
% 7.22/2.54  #BackRed      : 238
% 7.22/2.54  
% 7.22/2.54  #Partial instantiations: 0
% 7.22/2.54  #Strategies tried      : 1
% 7.22/2.54  
% 7.22/2.54  Timing (in seconds)
% 7.22/2.54  ----------------------
% 7.22/2.55  Preprocessing        : 0.35
% 7.22/2.55  Parsing              : 0.18
% 7.22/2.55  CNF conversion       : 0.03
% 7.22/2.55  Main loop            : 1.39
% 7.22/2.55  Inferencing          : 0.50
% 7.22/2.55  Reduction            : 0.46
% 7.22/2.55  Demodulation         : 0.32
% 7.22/2.55  BG Simplification    : 0.05
% 7.22/2.55  Subsumption          : 0.24
% 7.22/2.55  Abstraction          : 0.06
% 7.22/2.55  MUC search           : 0.00
% 7.22/2.55  Cooper               : 0.00
% 7.22/2.55  Total                : 1.81
% 7.22/2.55  Index Insertion      : 0.00
% 7.22/2.55  Index Deletion       : 0.00
% 7.22/2.55  Index Matching       : 0.00
% 7.22/2.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
