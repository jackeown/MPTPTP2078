%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:16 EST 2020

% Result     : Theorem 5.02s
% Output     : CNFRefutation 5.28s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 362 expanded)
%              Number of leaves         :   45 ( 146 expanded)
%              Depth                    :   14
%              Number of atoms          :  239 ( 992 expanded)
%              Number of equality atoms :   37 ( 123 expanded)
%              Maximal formula depth    :   15 (   4 average)
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

tff(f_165,negated_conjecture,(
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

tff(f_106,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_104,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_84,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_145,axiom,(
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

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_123,axiom,(
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

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_62,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_117,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_70,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_68,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_66,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_54,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_34,plain,(
    ! [A_17] : v2_funct_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_78,plain,(
    ! [A_17] : v2_funct_1(k6_partfun1(A_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_34])).

tff(c_50,plain,(
    ! [A_31,C_33,B_32,F_36,E_35,D_34] :
      ( m1_subset_1(k1_partfun1(A_31,B_32,C_33,D_34,E_35,F_36),k1_zfmisc_1(k2_zfmisc_1(A_31,D_34)))
      | ~ m1_subset_1(F_36,k1_zfmisc_1(k2_zfmisc_1(C_33,D_34)))
      | ~ v1_funct_1(F_36)
      | ~ m1_subset_1(E_35,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ v1_funct_1(E_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_44,plain,(
    ! [A_28] : m1_subset_1(k6_relat_1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_77,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_44])).

tff(c_64,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_857,plain,(
    ! [D_172,C_173,A_174,B_175] :
      ( D_172 = C_173
      | ~ r2_relset_1(A_174,B_175,C_173,D_172)
      | ~ m1_subset_1(D_172,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175)))
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_869,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_64,c_857])).

tff(c_891,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_869])).

tff(c_1249,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_891])).

tff(c_1409,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1249])).

tff(c_1416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_1409])).

tff(c_1417,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_891])).

tff(c_1484,plain,(
    ! [E_267,C_268,D_269,A_270,B_271] :
      ( k1_xboole_0 = C_268
      | v2_funct_1(D_269)
      | ~ v2_funct_1(k1_partfun1(A_270,B_271,B_271,C_268,D_269,E_267))
      | ~ m1_subset_1(E_267,k1_zfmisc_1(k2_zfmisc_1(B_271,C_268)))
      | ~ v1_funct_2(E_267,B_271,C_268)
      | ~ v1_funct_1(E_267)
      | ~ m1_subset_1(D_269,k1_zfmisc_1(k2_zfmisc_1(A_270,B_271)))
      | ~ v1_funct_2(D_269,A_270,B_271)
      | ~ v1_funct_1(D_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1486,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1417,c_1484])).

tff(c_1488,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_68,c_66,c_78,c_1486])).

tff(c_1489,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_1488])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1518,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1489,c_8])).

tff(c_20,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1516,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_2',B_9) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1489,c_1489,c_20])).

tff(c_524,plain,(
    ! [C_115,B_116,A_117] :
      ( ~ v1_xboole_0(C_115)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(C_115))
      | ~ r2_hidden(A_117,B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_541,plain,(
    ! [A_117] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_117,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_524])).

tff(c_578,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_541])).

tff(c_1608,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1516,c_578])).

tff(c_1614,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1518,c_1608])).

tff(c_1617,plain,(
    ! [A_278] : ~ r2_hidden(A_278,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_541])).

tff(c_1624,plain,(
    ! [B_279] : r1_tarski('#skF_4',B_279) ),
    inference(resolution,[status(thm)],[c_6,c_1617])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_278,plain,(
    ! [C_80,B_81,A_82] :
      ( ~ v1_xboole_0(C_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(C_80))
      | ~ r2_hidden(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_338,plain,(
    ! [B_89,A_90,A_91] :
      ( ~ v1_xboole_0(B_89)
      | ~ r2_hidden(A_90,A_91)
      | ~ r1_tarski(A_91,B_89) ) ),
    inference(resolution,[status(thm)],[c_24,c_278])).

tff(c_353,plain,(
    ! [B_94,A_95,B_96] :
      ( ~ v1_xboole_0(B_94)
      | ~ r1_tarski(A_95,B_94)
      | r1_tarski(A_95,B_96) ) ),
    inference(resolution,[status(thm)],[c_6,c_338])).

tff(c_370,plain,(
    ! [B_97,B_98] :
      ( ~ v1_xboole_0(B_97)
      | r1_tarski(B_97,B_98) ) ),
    inference(resolution,[status(thm)],[c_14,c_353])).

tff(c_118,plain,(
    ! [A_56] : m1_subset_1(k6_partfun1(A_56),k1_zfmisc_1(k2_zfmisc_1(A_56,A_56))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_44])).

tff(c_122,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_118])).

tff(c_128,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_141,plain,(
    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_122,c_128])).

tff(c_161,plain,(
    ! [B_62,A_63] :
      ( B_62 = A_63
      | ~ r1_tarski(B_62,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_175,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_141,c_161])).

tff(c_180,plain,(
    ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_390,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_370,c_180])).

tff(c_401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_390])).

tff(c_402,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_416,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_122])).

tff(c_526,plain,(
    ! [A_117] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_117,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_416,c_524])).

tff(c_542,plain,(
    ! [A_118] : ~ r2_hidden(A_118,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_526])).

tff(c_548,plain,(
    ! [B_119] : r1_tarski(k1_xboole_0,B_119) ),
    inference(resolution,[status(thm)],[c_6,c_542])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_563,plain,(
    ! [B_119] :
      ( k1_xboole_0 = B_119
      | ~ r1_tarski(B_119,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_548,c_10])).

tff(c_1639,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1624,c_563])).

tff(c_428,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_78])).

tff(c_1651,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1639,c_428])).

tff(c_1660,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_1651])).

tff(c_1661,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1725,plain,(
    ! [C_292,A_293,B_294] :
      ( v1_relat_1(C_292)
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(A_293,B_294))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1746,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_1725])).

tff(c_2257,plain,(
    ! [A_372,B_373,D_374] :
      ( r2_relset_1(A_372,B_373,D_374,D_374)
      | ~ m1_subset_1(D_374,k1_zfmisc_1(k2_zfmisc_1(A_372,B_373))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2271,plain,(
    ! [A_28] : r2_relset_1(A_28,A_28,k6_partfun1(A_28),k6_partfun1(A_28)) ),
    inference(resolution,[status(thm)],[c_77,c_2257])).

tff(c_2275,plain,(
    ! [A_375,B_376,C_377] :
      ( k2_relset_1(A_375,B_376,C_377) = k2_relat_1(C_377)
      | ~ m1_subset_1(C_377,k1_zfmisc_1(k2_zfmisc_1(A_375,B_376))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2297,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_2275])).

tff(c_2317,plain,(
    ! [D_379,C_380,A_381,B_382] :
      ( D_379 = C_380
      | ~ r2_relset_1(A_381,B_382,C_380,D_379)
      | ~ m1_subset_1(D_379,k1_zfmisc_1(k2_zfmisc_1(A_381,B_382)))
      | ~ m1_subset_1(C_380,k1_zfmisc_1(k2_zfmisc_1(A_381,B_382))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2327,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_64,c_2317])).

tff(c_2346,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_2327])).

tff(c_2372,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2346])).

tff(c_2736,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_2372])).

tff(c_2743,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_2736])).

tff(c_2744,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2346])).

tff(c_3301,plain,(
    ! [A_540,B_541,C_542,D_543] :
      ( k2_relset_1(A_540,B_541,C_542) = B_541
      | ~ r2_relset_1(B_541,B_541,k1_partfun1(B_541,A_540,A_540,B_541,D_543,C_542),k6_partfun1(B_541))
      | ~ m1_subset_1(D_543,k1_zfmisc_1(k2_zfmisc_1(B_541,A_540)))
      | ~ v1_funct_2(D_543,B_541,A_540)
      | ~ v1_funct_1(D_543)
      | ~ m1_subset_1(C_542,k1_zfmisc_1(k2_zfmisc_1(A_540,B_541)))
      | ~ v1_funct_2(C_542,A_540,B_541)
      | ~ v1_funct_1(C_542) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_3304,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2744,c_3301])).

tff(c_3309,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_76,c_74,c_72,c_2271,c_2297,c_3304])).

tff(c_2129,plain,(
    ! [B_346,A_347] :
      ( v5_relat_1(B_346,A_347)
      | ~ r1_tarski(k2_relat_1(B_346),A_347)
      | ~ v1_relat_1(B_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2139,plain,(
    ! [B_346] :
      ( v5_relat_1(B_346,k2_relat_1(B_346))
      | ~ v1_relat_1(B_346) ) ),
    inference(resolution,[status(thm)],[c_14,c_2129])).

tff(c_2220,plain,(
    ! [B_361] :
      ( v2_funct_2(B_361,k2_relat_1(B_361))
      | ~ v5_relat_1(B_361,k2_relat_1(B_361))
      | ~ v1_relat_1(B_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2224,plain,(
    ! [B_346] :
      ( v2_funct_2(B_346,k2_relat_1(B_346))
      | ~ v1_relat_1(B_346) ) ),
    inference(resolution,[status(thm)],[c_2139,c_2220])).

tff(c_3318,plain,
    ( v2_funct_2('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3309,c_2224])).

tff(c_3338,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1746,c_3318])).

tff(c_3340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1661,c_3338])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:56:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.02/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.28/1.99  
% 5.28/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.28/1.99  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.28/1.99  
% 5.28/1.99  %Foreground sorts:
% 5.28/1.99  
% 5.28/1.99  
% 5.28/1.99  %Background operators:
% 5.28/1.99  
% 5.28/1.99  
% 5.28/1.99  %Foreground operators:
% 5.28/1.99  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.28/1.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.28/1.99  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.28/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.28/1.99  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.28/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.28/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.28/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.28/1.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.28/1.99  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.28/1.99  tff('#skF_5', type, '#skF_5': $i).
% 5.28/1.99  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.28/1.99  tff('#skF_2', type, '#skF_2': $i).
% 5.28/1.99  tff('#skF_3', type, '#skF_3': $i).
% 5.28/1.99  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.28/1.99  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.28/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.28/1.99  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.28/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.28/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.28/1.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.28/1.99  tff('#skF_4', type, '#skF_4': $i).
% 5.28/1.99  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.28/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.28/1.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.28/1.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.28/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.28/1.99  
% 5.28/2.02  tff(f_165, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 5.28/2.02  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.28/2.02  tff(f_106, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.28/2.02  tff(f_66, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.28/2.02  tff(f_104, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.28/2.02  tff(f_84, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 5.28/2.02  tff(f_82, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.28/2.02  tff(f_145, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 5.28/2.02  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.28/2.02  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.28/2.02  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.28/2.02  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.28/2.02  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.28/2.02  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.28/2.02  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.28/2.02  tff(f_123, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 5.28/2.02  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 5.28/2.02  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.28/2.02  tff(c_62, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.28/2.02  tff(c_117, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_62])).
% 5.28/2.02  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.28/2.02  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.28/2.02  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.28/2.02  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.28/2.02  tff(c_70, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.28/2.02  tff(c_68, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.28/2.02  tff(c_66, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.28/2.02  tff(c_54, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.28/2.02  tff(c_34, plain, (![A_17]: (v2_funct_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.28/2.02  tff(c_78, plain, (![A_17]: (v2_funct_1(k6_partfun1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_34])).
% 5.28/2.02  tff(c_50, plain, (![A_31, C_33, B_32, F_36, E_35, D_34]: (m1_subset_1(k1_partfun1(A_31, B_32, C_33, D_34, E_35, F_36), k1_zfmisc_1(k2_zfmisc_1(A_31, D_34))) | ~m1_subset_1(F_36, k1_zfmisc_1(k2_zfmisc_1(C_33, D_34))) | ~v1_funct_1(F_36) | ~m1_subset_1(E_35, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~v1_funct_1(E_35))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.28/2.02  tff(c_44, plain, (![A_28]: (m1_subset_1(k6_relat_1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.28/2.02  tff(c_77, plain, (![A_28]: (m1_subset_1(k6_partfun1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_44])).
% 5.28/2.02  tff(c_64, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.28/2.02  tff(c_857, plain, (![D_172, C_173, A_174, B_175]: (D_172=C_173 | ~r2_relset_1(A_174, B_175, C_173, D_172) | ~m1_subset_1(D_172, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.28/2.02  tff(c_869, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_64, c_857])).
% 5.28/2.02  tff(c_891, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_869])).
% 5.28/2.02  tff(c_1249, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_891])).
% 5.28/2.02  tff(c_1409, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_1249])).
% 5.28/2.02  tff(c_1416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_1409])).
% 5.28/2.02  tff(c_1417, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_891])).
% 5.28/2.02  tff(c_1484, plain, (![E_267, C_268, D_269, A_270, B_271]: (k1_xboole_0=C_268 | v2_funct_1(D_269) | ~v2_funct_1(k1_partfun1(A_270, B_271, B_271, C_268, D_269, E_267)) | ~m1_subset_1(E_267, k1_zfmisc_1(k2_zfmisc_1(B_271, C_268))) | ~v1_funct_2(E_267, B_271, C_268) | ~v1_funct_1(E_267) | ~m1_subset_1(D_269, k1_zfmisc_1(k2_zfmisc_1(A_270, B_271))) | ~v1_funct_2(D_269, A_270, B_271) | ~v1_funct_1(D_269))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.28/2.02  tff(c_1486, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1417, c_1484])).
% 5.28/2.02  tff(c_1488, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_68, c_66, c_78, c_1486])).
% 5.28/2.02  tff(c_1489, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_117, c_1488])).
% 5.28/2.02  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.28/2.02  tff(c_1518, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1489, c_8])).
% 5.28/2.02  tff(c_20, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.28/2.02  tff(c_1516, plain, (![B_9]: (k2_zfmisc_1('#skF_2', B_9)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1489, c_1489, c_20])).
% 5.28/2.02  tff(c_524, plain, (![C_115, B_116, A_117]: (~v1_xboole_0(C_115) | ~m1_subset_1(B_116, k1_zfmisc_1(C_115)) | ~r2_hidden(A_117, B_116))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.28/2.02  tff(c_541, plain, (![A_117]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_117, '#skF_4'))), inference(resolution, [status(thm)], [c_72, c_524])).
% 5.28/2.02  tff(c_578, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_541])).
% 5.28/2.02  tff(c_1608, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1516, c_578])).
% 5.28/2.02  tff(c_1614, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1518, c_1608])).
% 5.28/2.02  tff(c_1617, plain, (![A_278]: (~r2_hidden(A_278, '#skF_4'))), inference(splitRight, [status(thm)], [c_541])).
% 5.28/2.02  tff(c_1624, plain, (![B_279]: (r1_tarski('#skF_4', B_279))), inference(resolution, [status(thm)], [c_6, c_1617])).
% 5.28/2.02  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.28/2.02  tff(c_24, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.28/2.02  tff(c_278, plain, (![C_80, B_81, A_82]: (~v1_xboole_0(C_80) | ~m1_subset_1(B_81, k1_zfmisc_1(C_80)) | ~r2_hidden(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.28/2.02  tff(c_338, plain, (![B_89, A_90, A_91]: (~v1_xboole_0(B_89) | ~r2_hidden(A_90, A_91) | ~r1_tarski(A_91, B_89))), inference(resolution, [status(thm)], [c_24, c_278])).
% 5.28/2.02  tff(c_353, plain, (![B_94, A_95, B_96]: (~v1_xboole_0(B_94) | ~r1_tarski(A_95, B_94) | r1_tarski(A_95, B_96))), inference(resolution, [status(thm)], [c_6, c_338])).
% 5.28/2.02  tff(c_370, plain, (![B_97, B_98]: (~v1_xboole_0(B_97) | r1_tarski(B_97, B_98))), inference(resolution, [status(thm)], [c_14, c_353])).
% 5.28/2.02  tff(c_118, plain, (![A_56]: (m1_subset_1(k6_partfun1(A_56), k1_zfmisc_1(k2_zfmisc_1(A_56, A_56))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_44])).
% 5.28/2.02  tff(c_122, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_118])).
% 5.28/2.02  tff(c_128, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~m1_subset_1(A_57, k1_zfmisc_1(B_58)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.28/2.02  tff(c_141, plain, (r1_tarski(k6_partfun1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_122, c_128])).
% 5.28/2.02  tff(c_161, plain, (![B_62, A_63]: (B_62=A_63 | ~r1_tarski(B_62, A_63) | ~r1_tarski(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.28/2.02  tff(c_175, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_141, c_161])).
% 5.28/2.02  tff(c_180, plain, (~r1_tarski(k1_xboole_0, k6_partfun1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_175])).
% 5.28/2.02  tff(c_390, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_370, c_180])).
% 5.28/2.02  tff(c_401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_390])).
% 5.28/2.02  tff(c_402, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_175])).
% 5.28/2.02  tff(c_416, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_402, c_122])).
% 5.28/2.02  tff(c_526, plain, (![A_117]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_117, k1_xboole_0))), inference(resolution, [status(thm)], [c_416, c_524])).
% 5.28/2.02  tff(c_542, plain, (![A_118]: (~r2_hidden(A_118, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_526])).
% 5.28/2.02  tff(c_548, plain, (![B_119]: (r1_tarski(k1_xboole_0, B_119))), inference(resolution, [status(thm)], [c_6, c_542])).
% 5.28/2.02  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.28/2.02  tff(c_563, plain, (![B_119]: (k1_xboole_0=B_119 | ~r1_tarski(B_119, k1_xboole_0))), inference(resolution, [status(thm)], [c_548, c_10])).
% 5.28/2.02  tff(c_1639, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1624, c_563])).
% 5.28/2.02  tff(c_428, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_402, c_78])).
% 5.28/2.02  tff(c_1651, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1639, c_428])).
% 5.28/2.02  tff(c_1660, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_1651])).
% 5.28/2.02  tff(c_1661, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_62])).
% 5.28/2.02  tff(c_1725, plain, (![C_292, A_293, B_294]: (v1_relat_1(C_292) | ~m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(A_293, B_294))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.28/2.02  tff(c_1746, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_1725])).
% 5.28/2.02  tff(c_2257, plain, (![A_372, B_373, D_374]: (r2_relset_1(A_372, B_373, D_374, D_374) | ~m1_subset_1(D_374, k1_zfmisc_1(k2_zfmisc_1(A_372, B_373))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.28/2.02  tff(c_2271, plain, (![A_28]: (r2_relset_1(A_28, A_28, k6_partfun1(A_28), k6_partfun1(A_28)))), inference(resolution, [status(thm)], [c_77, c_2257])).
% 5.28/2.02  tff(c_2275, plain, (![A_375, B_376, C_377]: (k2_relset_1(A_375, B_376, C_377)=k2_relat_1(C_377) | ~m1_subset_1(C_377, k1_zfmisc_1(k2_zfmisc_1(A_375, B_376))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.28/2.02  tff(c_2297, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_2275])).
% 5.28/2.02  tff(c_2317, plain, (![D_379, C_380, A_381, B_382]: (D_379=C_380 | ~r2_relset_1(A_381, B_382, C_380, D_379) | ~m1_subset_1(D_379, k1_zfmisc_1(k2_zfmisc_1(A_381, B_382))) | ~m1_subset_1(C_380, k1_zfmisc_1(k2_zfmisc_1(A_381, B_382))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.28/2.02  tff(c_2327, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_64, c_2317])).
% 5.28/2.02  tff(c_2346, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_2327])).
% 5.28/2.02  tff(c_2372, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2346])).
% 5.28/2.02  tff(c_2736, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_2372])).
% 5.28/2.02  tff(c_2743, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_2736])).
% 5.28/2.02  tff(c_2744, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2346])).
% 5.28/2.02  tff(c_3301, plain, (![A_540, B_541, C_542, D_543]: (k2_relset_1(A_540, B_541, C_542)=B_541 | ~r2_relset_1(B_541, B_541, k1_partfun1(B_541, A_540, A_540, B_541, D_543, C_542), k6_partfun1(B_541)) | ~m1_subset_1(D_543, k1_zfmisc_1(k2_zfmisc_1(B_541, A_540))) | ~v1_funct_2(D_543, B_541, A_540) | ~v1_funct_1(D_543) | ~m1_subset_1(C_542, k1_zfmisc_1(k2_zfmisc_1(A_540, B_541))) | ~v1_funct_2(C_542, A_540, B_541) | ~v1_funct_1(C_542))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.28/2.02  tff(c_3304, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2744, c_3301])).
% 5.28/2.02  tff(c_3309, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_76, c_74, c_72, c_2271, c_2297, c_3304])).
% 5.28/2.02  tff(c_2129, plain, (![B_346, A_347]: (v5_relat_1(B_346, A_347) | ~r1_tarski(k2_relat_1(B_346), A_347) | ~v1_relat_1(B_346))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.28/2.02  tff(c_2139, plain, (![B_346]: (v5_relat_1(B_346, k2_relat_1(B_346)) | ~v1_relat_1(B_346))), inference(resolution, [status(thm)], [c_14, c_2129])).
% 5.28/2.02  tff(c_2220, plain, (![B_361]: (v2_funct_2(B_361, k2_relat_1(B_361)) | ~v5_relat_1(B_361, k2_relat_1(B_361)) | ~v1_relat_1(B_361))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.28/2.02  tff(c_2224, plain, (![B_346]: (v2_funct_2(B_346, k2_relat_1(B_346)) | ~v1_relat_1(B_346))), inference(resolution, [status(thm)], [c_2139, c_2220])).
% 5.28/2.02  tff(c_3318, plain, (v2_funct_2('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3309, c_2224])).
% 5.28/2.02  tff(c_3338, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1746, c_3318])).
% 5.28/2.02  tff(c_3340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1661, c_3338])).
% 5.28/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.28/2.02  
% 5.28/2.02  Inference rules
% 5.28/2.02  ----------------------
% 5.28/2.02  #Ref     : 0
% 5.28/2.02  #Sup     : 726
% 5.28/2.02  #Fact    : 0
% 5.28/2.02  #Define  : 0
% 5.28/2.02  #Split   : 19
% 5.28/2.02  #Chain   : 0
% 5.28/2.02  #Close   : 0
% 5.28/2.02  
% 5.28/2.02  Ordering : KBO
% 5.28/2.02  
% 5.28/2.02  Simplification rules
% 5.28/2.02  ----------------------
% 5.28/2.02  #Subsume      : 99
% 5.28/2.02  #Demod        : 455
% 5.28/2.02  #Tautology    : 302
% 5.28/2.02  #SimpNegUnit  : 3
% 5.28/2.02  #BackRed      : 56
% 5.28/2.02  
% 5.28/2.02  #Partial instantiations: 0
% 5.28/2.02  #Strategies tried      : 1
% 5.28/2.02  
% 5.28/2.02  Timing (in seconds)
% 5.28/2.02  ----------------------
% 5.28/2.02  Preprocessing        : 0.37
% 5.28/2.02  Parsing              : 0.20
% 5.28/2.02  CNF conversion       : 0.03
% 5.28/2.02  Main loop            : 0.84
% 5.28/2.02  Inferencing          : 0.31
% 5.28/2.02  Reduction            : 0.27
% 5.28/2.02  Demodulation         : 0.19
% 5.28/2.02  BG Simplification    : 0.03
% 5.28/2.02  Subsumption          : 0.15
% 5.28/2.02  Abstraction          : 0.04
% 5.28/2.02  MUC search           : 0.00
% 5.28/2.02  Cooper               : 0.00
% 5.28/2.02  Total                : 1.26
% 5.28/2.02  Index Insertion      : 0.00
% 5.28/2.02  Index Deletion       : 0.00
% 5.28/2.02  Index Matching       : 0.00
% 5.28/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
