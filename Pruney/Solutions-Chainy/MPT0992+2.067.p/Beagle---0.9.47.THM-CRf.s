%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:41 EST 2020

% Result     : Theorem 12.38s
% Output     : CNFRefutation 12.70s
% Verified   : 
% Statistics : Number of formulae       :  283 (3841 expanded)
%              Number of leaves         :   44 (1216 expanded)
%              Depth                    :   16
%              Number of atoms          :  482 (10772 expanded)
%              Number of equality atoms :  118 (3962 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_176,negated_conjecture,(
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

tff(f_144,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_138,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_73,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_130,axiom,(
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

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_156,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_82,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_84,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_80,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_16354,plain,(
    ! [A_946,B_947,C_948,D_949] :
      ( k2_partfun1(A_946,B_947,C_948,D_949) = k7_relat_1(C_948,D_949)
      | ~ m1_subset_1(C_948,k1_zfmisc_1(k2_zfmisc_1(A_946,B_947)))
      | ~ v1_funct_1(C_948) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_16370,plain,(
    ! [D_949] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_949) = k7_relat_1('#skF_4',D_949)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_80,c_16354])).

tff(c_16380,plain,(
    ! [D_949] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_949) = k7_relat_1('#skF_4',D_949) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_16370])).

tff(c_3932,plain,(
    ! [A_427,B_428,C_429,D_430] :
      ( k2_partfun1(A_427,B_428,C_429,D_430) = k7_relat_1(C_429,D_430)
      | ~ m1_subset_1(C_429,k1_zfmisc_1(k2_zfmisc_1(A_427,B_428)))
      | ~ v1_funct_1(C_429) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_3948,plain,(
    ! [D_430] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_430) = k7_relat_1('#skF_4',D_430)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_80,c_3932])).

tff(c_3958,plain,(
    ! [D_430] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_430) = k7_relat_1('#skF_4',D_430) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_3948])).

tff(c_4433,plain,(
    ! [A_454,B_455,C_456,D_457] :
      ( m1_subset_1(k2_partfun1(A_454,B_455,C_456,D_457),k1_zfmisc_1(k2_zfmisc_1(A_454,B_455)))
      | ~ m1_subset_1(C_456,k1_zfmisc_1(k2_zfmisc_1(A_454,B_455)))
      | ~ v1_funct_1(C_456) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_4465,plain,(
    ! [D_430] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_430),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3958,c_4433])).

tff(c_4494,plain,(
    ! [D_459] : m1_subset_1(k7_relat_1('#skF_4',D_459),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_4465])).

tff(c_42,plain,(
    ! [C_31,B_30,A_29] :
      ( v5_relat_1(C_31,B_30)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4542,plain,(
    ! [D_459] : v5_relat_1(k7_relat_1('#skF_4',D_459),'#skF_2') ),
    inference(resolution,[status(thm)],[c_4494,c_42])).

tff(c_28,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22,plain,(
    ! [B_16,A_14] :
      ( v1_relat_1(B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_14))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4520,plain,(
    ! [D_459] :
      ( v1_relat_1(k7_relat_1('#skF_4',D_459))
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_4494,c_22])).

tff(c_4545,plain,(
    ! [D_459] : v1_relat_1(k7_relat_1('#skF_4',D_459)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4520])).

tff(c_44,plain,(
    ! [C_31,A_29,B_30] :
      ( v4_relat_1(C_31,A_29)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4573,plain,(
    ! [D_462] : v4_relat_1(k7_relat_1('#skF_4',D_462),'#skF_1') ),
    inference(resolution,[status(thm)],[c_4494,c_44])).

tff(c_30,plain,(
    ! [B_22,A_21] :
      ( k7_relat_1(B_22,A_21) = B_22
      | ~ v4_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4576,plain,(
    ! [D_462] :
      ( k7_relat_1(k7_relat_1('#skF_4',D_462),'#skF_1') = k7_relat_1('#skF_4',D_462)
      | ~ v1_relat_1(k7_relat_1('#skF_4',D_462)) ) ),
    inference(resolution,[status(thm)],[c_4573,c_30])).

tff(c_4581,plain,(
    ! [D_462] : k7_relat_1(k7_relat_1('#skF_4',D_462),'#skF_1') = k7_relat_1('#skF_4',D_462) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4545,c_4576])).

tff(c_40,plain,(
    ! [B_28,A_27] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_28,A_27)),k2_relat_1(B_28))
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_26,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k2_relat_1(B_18),A_17)
      | ~ v5_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2115,plain,(
    ! [A_267,C_268,B_269] :
      ( r1_tarski(A_267,C_268)
      | ~ r1_tarski(B_269,C_268)
      | ~ r1_tarski(A_267,B_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3987,plain,(
    ! [A_435,A_436,B_437] :
      ( r1_tarski(A_435,A_436)
      | ~ r1_tarski(A_435,k2_relat_1(B_437))
      | ~ v5_relat_1(B_437,A_436)
      | ~ v1_relat_1(B_437) ) ),
    inference(resolution,[status(thm)],[c_26,c_2115])).

tff(c_11365,plain,(
    ! [B_679,A_680,A_681] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_679,A_680)),A_681)
      | ~ v5_relat_1(B_679,A_681)
      | ~ v1_relat_1(B_679) ) ),
    inference(resolution,[status(thm)],[c_40,c_3987])).

tff(c_11515,plain,(
    ! [D_462,A_681] :
      ( r1_tarski(k2_relat_1(k7_relat_1('#skF_4',D_462)),A_681)
      | ~ v5_relat_1(k7_relat_1('#skF_4',D_462),A_681)
      | ~ v1_relat_1(k7_relat_1('#skF_4',D_462)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4581,c_11365])).

tff(c_11568,plain,(
    ! [D_462,A_681] :
      ( r1_tarski(k2_relat_1(k7_relat_1('#skF_4',D_462)),A_681)
      | ~ v5_relat_1(k7_relat_1('#skF_4',D_462),A_681) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4545,c_11515])).

tff(c_3373,plain,(
    ! [A_381,B_382,C_383,D_384] :
      ( v1_funct_1(k2_partfun1(A_381,B_382,C_383,D_384))
      | ~ m1_subset_1(C_383,k1_zfmisc_1(k2_zfmisc_1(A_381,B_382)))
      | ~ v1_funct_1(C_383) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_3385,plain,(
    ! [D_384] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_384))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_80,c_3373])).

tff(c_3390,plain,(
    ! [D_384] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_384)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_3385])).

tff(c_3959,plain,(
    ! [D_384] : v1_funct_1(k7_relat_1('#skF_4',D_384)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3958,c_3390])).

tff(c_1937,plain,(
    ! [B_238,A_239] :
      ( v1_relat_1(B_238)
      | ~ m1_subset_1(B_238,k1_zfmisc_1(A_239))
      | ~ v1_relat_1(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1946,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_80,c_1937])).

tff(c_1952,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1946])).

tff(c_4859,plain,(
    ! [D_474] : k7_relat_1(k7_relat_1('#skF_4',D_474),'#skF_1') = k7_relat_1('#skF_4',D_474) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4545,c_4576])).

tff(c_36,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_24,A_23)),A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4886,plain,(
    ! [D_474] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_474)),'#skF_1')
      | ~ v1_relat_1(k7_relat_1('#skF_4',D_474)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4859,c_36])).

tff(c_4912,plain,(
    ! [D_475] : r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_475)),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4545,c_4886])).

tff(c_76,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_99,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_82,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_2475,plain,(
    ! [A_302,B_303,C_304] :
      ( k1_relset_1(A_302,B_303,C_304) = k1_relat_1(C_304)
      | ~ m1_subset_1(C_304,k1_zfmisc_1(k2_zfmisc_1(A_302,B_303))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2496,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_2475])).

tff(c_4144,plain,(
    ! [B_439,A_440,C_441] :
      ( k1_xboole_0 = B_439
      | k1_relset_1(A_440,B_439,C_441) = A_440
      | ~ v1_funct_2(C_441,A_440,B_439)
      | ~ m1_subset_1(C_441,k1_zfmisc_1(k2_zfmisc_1(A_440,B_439))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4167,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_4144])).

tff(c_4178,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2496,c_4167])).

tff(c_4179,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_4178])).

tff(c_38,plain,(
    ! [B_26,A_25] :
      ( k1_relat_1(k7_relat_1(B_26,A_25)) = A_25
      | ~ r1_tarski(A_25,k1_relat_1(B_26))
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_4202,plain,(
    ! [A_25] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_25)) = A_25
      | ~ r1_tarski(A_25,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4179,c_38])).

tff(c_4668,plain,(
    ! [A_469] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_469)) = A_469
      | ~ r1_tarski(A_469,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1952,c_4202])).

tff(c_4732,plain,(
    ! [A_469] :
      ( r1_tarski(A_469,A_469)
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski(A_469,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4668,c_36])).

tff(c_4778,plain,(
    ! [A_469] :
      ( r1_tarski(A_469,A_469)
      | ~ r1_tarski(A_469,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1952,c_4732])).

tff(c_5217,plain,(
    ! [D_495] : r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_495)),k1_relat_1(k7_relat_1('#skF_4',D_495))) ),
    inference(resolution,[status(thm)],[c_4912,c_4778])).

tff(c_2133,plain,(
    ! [A_267,A_23,B_24] :
      ( r1_tarski(A_267,A_23)
      | ~ r1_tarski(A_267,k1_relat_1(k7_relat_1(B_24,A_23)))
      | ~ v1_relat_1(B_24) ) ),
    inference(resolution,[status(thm)],[c_36,c_2115])).

tff(c_5226,plain,(
    ! [D_495] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_495)),D_495)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5217,c_2133])).

tff(c_5268,plain,(
    ! [D_495] : r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_495)),D_495) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1952,c_5226])).

tff(c_68,plain,(
    ! [B_51,A_50] :
      ( m1_subset_1(B_51,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_51),A_50)))
      | ~ r1_tarski(k2_relat_1(B_51),A_50)
      | ~ v1_funct_1(B_51)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_3827,plain,(
    ! [D_417,B_418,C_419,A_420] :
      ( m1_subset_1(D_417,k1_zfmisc_1(k2_zfmisc_1(B_418,C_419)))
      | ~ r1_tarski(k1_relat_1(D_417),B_418)
      | ~ m1_subset_1(D_417,k1_zfmisc_1(k2_zfmisc_1(A_420,C_419))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_14331,plain,(
    ! [B_760,B_761,A_762] :
      ( m1_subset_1(B_760,k1_zfmisc_1(k2_zfmisc_1(B_761,A_762)))
      | ~ r1_tarski(k1_relat_1(B_760),B_761)
      | ~ r1_tarski(k2_relat_1(B_760),A_762)
      | ~ v1_funct_1(B_760)
      | ~ v1_relat_1(B_760) ) ),
    inference(resolution,[status(thm)],[c_68,c_3827])).

tff(c_1896,plain,(
    ! [A_228,B_229,C_230,D_231] :
      ( v1_funct_1(k2_partfun1(A_228,B_229,C_230,D_231))
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_228,B_229)))
      | ~ v1_funct_1(C_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1908,plain,(
    ! [D_231] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_231))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_80,c_1896])).

tff(c_1913,plain,(
    ! [D_231] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_231)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1908])).

tff(c_74,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_149,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_1916,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1913,c_149])).

tff(c_1917,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_1919,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1917])).

tff(c_3961,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3958,c_1919])).

tff(c_14346,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ v1_funct_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_14331,c_3961])).

tff(c_14383,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4545,c_3959,c_5268,c_14346])).

tff(c_14397,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_11568,c_14383])).

tff(c_14422,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4542,c_14397])).

tff(c_14423,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1917])).

tff(c_16393,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16380,c_14423])).

tff(c_14424,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1917])).

tff(c_16392,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16380,c_14424])).

tff(c_16761,plain,(
    ! [B_966,C_967,A_968] :
      ( k1_xboole_0 = B_966
      | v1_funct_2(C_967,A_968,B_966)
      | k1_relset_1(A_968,B_966,C_967) != A_968
      | ~ m1_subset_1(C_967,k1_zfmisc_1(k2_zfmisc_1(A_968,B_966))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_16764,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_16392,c_16761])).

tff(c_16787,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_16393,c_99,c_16764])).

tff(c_17112,plain,(
    ! [A_976,B_977,C_978,D_979] :
      ( m1_subset_1(k2_partfun1(A_976,B_977,C_978,D_979),k1_zfmisc_1(k2_zfmisc_1(A_976,B_977)))
      | ~ m1_subset_1(C_978,k1_zfmisc_1(k2_zfmisc_1(A_976,B_977)))
      | ~ v1_funct_1(C_978) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_17144,plain,(
    ! [D_949] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_949),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16380,c_17112])).

tff(c_17168,plain,(
    ! [D_980] : m1_subset_1(k7_relat_1('#skF_4',D_980),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_17144])).

tff(c_17194,plain,(
    ! [D_980] :
      ( v1_relat_1(k7_relat_1('#skF_4',D_980))
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_17168,c_22])).

tff(c_17219,plain,(
    ! [D_980] : v1_relat_1(k7_relat_1('#skF_4',D_980)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_17194])).

tff(c_14506,plain,
    ( v1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_14424,c_22])).

tff(c_14513,plain,(
    v1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_14506])).

tff(c_16391,plain,(
    v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16380,c_14513])).

tff(c_14510,plain,(
    v4_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_14424,c_44])).

tff(c_16390,plain,(
    v4_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16380,c_14510])).

tff(c_16409,plain,
    ( k7_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_3') = k7_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16390,c_30])).

tff(c_16412,plain,(
    k7_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_3') = k7_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16391,c_16409])).

tff(c_78,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_14442,plain,(
    ! [B_769,A_770] :
      ( v1_relat_1(B_769)
      | ~ m1_subset_1(B_769,k1_zfmisc_1(A_770))
      | ~ v1_relat_1(A_770) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14451,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_80,c_14442])).

tff(c_14457,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_14451])).

tff(c_15365,plain,(
    ! [A_863,B_864,C_865] :
      ( k1_relset_1(A_863,B_864,C_865) = k1_relat_1(C_865)
      | ~ m1_subset_1(C_865,k1_zfmisc_1(k2_zfmisc_1(A_863,B_864))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_15390,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_15365])).

tff(c_16633,plain,(
    ! [B_959,A_960,C_961] :
      ( k1_xboole_0 = B_959
      | k1_relset_1(A_960,B_959,C_961) = A_960
      | ~ v1_funct_2(C_961,A_960,B_959)
      | ~ m1_subset_1(C_961,k1_zfmisc_1(k2_zfmisc_1(A_960,B_959))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_16659,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_16633])).

tff(c_16672,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_15390,c_16659])).

tff(c_16673,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_16672])).

tff(c_16690,plain,(
    ! [A_25] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_25)) = A_25
      | ~ r1_tarski(A_25,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16673,c_38])).

tff(c_16698,plain,(
    ! [A_25] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_25)) = A_25
      | ~ r1_tarski(A_25,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14457,c_16690])).

tff(c_14716,plain,(
    ! [A_804,C_805,B_806] :
      ( r1_tarski(A_804,C_805)
      | ~ r1_tarski(B_806,C_805)
      | ~ r1_tarski(A_804,B_806) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14738,plain,(
    ! [A_807] :
      ( r1_tarski(A_807,'#skF_1')
      | ~ r1_tarski(A_807,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_78,c_14716])).

tff(c_14752,plain,(
    ! [B_24] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_24,'#skF_3')),'#skF_1')
      | ~ v1_relat_1(B_24) ) ),
    inference(resolution,[status(thm)],[c_36,c_14738])).

tff(c_16526,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_16412,c_14752])).

tff(c_16546,plain,(
    r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16391,c_16526])).

tff(c_16816,plain,(
    ! [A_971] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_971)) = A_971
      | ~ r1_tarski(A_971,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14457,c_16690])).

tff(c_16886,plain,(
    ! [A_971] :
      ( r1_tarski(A_971,A_971)
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski(A_971,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16816,c_36])).

tff(c_17015,plain,(
    ! [A_973] :
      ( r1_tarski(A_973,A_973)
      | ~ r1_tarski(A_973,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14457,c_16886])).

tff(c_17050,plain,(
    r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),k1_relat_1(k7_relat_1('#skF_4','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_16546,c_17015])).

tff(c_17635,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k7_relat_1('#skF_4','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16698,c_17050])).

tff(c_17656,plain,(
    r1_tarski('#skF_3',k1_relat_1(k7_relat_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_17635])).

tff(c_17675,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_17656,c_38])).

tff(c_17697,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17219,c_16412,c_17675])).

tff(c_46,plain,(
    ! [A_32,B_33,C_34] :
      ( k1_relset_1(A_32,B_33,C_34) = k1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_16497,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16392,c_46])).

tff(c_19584,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17697,c_16497])).

tff(c_19585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16787,c_19584])).

tff(c_19586,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_12,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_19610,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_1',B_7) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19586,c_19586,c_12])).

tff(c_19587,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_19595,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19586,c_19587])).

tff(c_19596,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19595,c_80])).

tff(c_21351,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19610,c_19596])).

tff(c_21364,plain,(
    ! [A_1208,B_1209] :
      ( r1_tarski(A_1208,B_1209)
      | ~ m1_subset_1(A_1208,k1_zfmisc_1(B_1209)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_21371,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_21351,c_21364])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_19620,plain,(
    ! [A_8] : m1_subset_1('#skF_1',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19586,c_14])).

tff(c_21372,plain,(
    ! [A_8] : r1_tarski('#skF_1',A_8) ),
    inference(resolution,[status(thm)],[c_19620,c_21364])).

tff(c_22888,plain,(
    ! [A_1360,C_1361,B_1362] :
      ( r1_tarski(A_1360,C_1361)
      | ~ r1_tarski(B_1362,C_1361)
      | ~ r1_tarski(A_1360,B_1362) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_23054,plain,(
    ! [A_1375,A_1376] :
      ( r1_tarski(A_1375,A_1376)
      | ~ r1_tarski(A_1375,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_21372,c_22888])).

tff(c_23083,plain,(
    ! [A_1376] : r1_tarski('#skF_4',A_1376) ),
    inference(resolution,[status(thm)],[c_21371,c_23054])).

tff(c_19611,plain,(
    ! [B_1058] : k2_zfmisc_1('#skF_1',B_1058) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19586,c_19586,c_12])).

tff(c_19615,plain,(
    v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_19611,c_28])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_19589,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19586,c_19586,c_34])).

tff(c_22818,plain,(
    ! [C_1345,A_1346,B_1347] :
      ( v4_relat_1(C_1345,A_1346)
      | ~ m1_subset_1(C_1345,k1_zfmisc_1(k2_zfmisc_1(A_1346,B_1347))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_22834,plain,(
    ! [A_1346] : v4_relat_1('#skF_1',A_1346) ),
    inference(resolution,[status(thm)],[c_19620,c_22818])).

tff(c_22907,plain,(
    ! [B_1363,A_1364] :
      ( k7_relat_1(B_1363,A_1364) = B_1363
      | ~ v4_relat_1(B_1363,A_1364)
      | ~ v1_relat_1(B_1363) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22919,plain,(
    ! [A_1346] :
      ( k7_relat_1('#skF_1',A_1346) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22834,c_22907])).

tff(c_22929,plain,(
    ! [A_1346] : k7_relat_1('#skF_1',A_1346) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19615,c_22919])).

tff(c_23633,plain,(
    ! [B_1414,A_1415] :
      ( k1_relat_1(k7_relat_1(B_1414,A_1415)) = A_1415
      | ~ r1_tarski(A_1415,k1_relat_1(B_1414))
      | ~ v1_relat_1(B_1414) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_23672,plain,(
    ! [A_1415] :
      ( k1_relat_1(k7_relat_1('#skF_1',A_1415)) = A_1415
      | ~ r1_tarski(A_1415,'#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19589,c_23633])).

tff(c_23684,plain,(
    ! [A_1416] :
      ( A_1416 = '#skF_1'
      | ~ r1_tarski(A_1416,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19615,c_19589,c_22929,c_23672])).

tff(c_23732,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_23083,c_23684])).

tff(c_23769,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23732,c_23732,c_19589])).

tff(c_23911,plain,(
    ! [A_1422] : m1_subset_1('#skF_4',k1_zfmisc_1(A_1422)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23732,c_19620])).

tff(c_23915,plain,(
    ! [A_32,B_33] : k1_relset_1(A_32,B_33,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_23911,c_46])).

tff(c_23933,plain,(
    ! [A_32,B_33] : k1_relset_1(A_32,B_33,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23769,c_23915])).

tff(c_23766,plain,(
    ! [A_8] : m1_subset_1('#skF_4',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23732,c_19620])).

tff(c_23773,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23732,c_19586])).

tff(c_54,plain,(
    ! [C_41,B_40] :
      ( v1_funct_2(C_41,k1_xboole_0,B_40)
      | k1_relset_1(k1_xboole_0,B_40,C_41) != k1_xboole_0
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_88,plain,(
    ! [C_41,B_40] :
      ( v1_funct_2(C_41,k1_xboole_0,B_40)
      | k1_relset_1(k1_xboole_0,B_40,C_41) != k1_xboole_0
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_54])).

tff(c_24078,plain,(
    ! [C_1440,B_1441] :
      ( v1_funct_2(C_1440,'#skF_4',B_1441)
      | k1_relset_1('#skF_4',B_1441,C_1440) != '#skF_4'
      | ~ m1_subset_1(C_1440,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23773,c_23773,c_23773,c_23773,c_88])).

tff(c_24081,plain,(
    ! [B_1441] :
      ( v1_funct_2('#skF_4','#skF_4',B_1441)
      | k1_relset_1('#skF_4',B_1441,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_23766,c_24078])).

tff(c_24087,plain,(
    ! [B_1441] : v1_funct_2('#skF_4','#skF_4',B_1441) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23933,c_24081])).

tff(c_23084,plain,(
    ! [A_1376] : r1_tarski('#skF_3',A_1376) ),
    inference(resolution,[status(thm)],[c_78,c_23054])).

tff(c_23733,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_23084,c_23684])).

tff(c_23783,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23732,c_23733])).

tff(c_21586,plain,(
    ! [A_1251,C_1252,B_1253] :
      ( r1_tarski(A_1251,C_1252)
      | ~ r1_tarski(B_1253,C_1252)
      | ~ r1_tarski(A_1251,B_1253) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_21697,plain,(
    ! [A_1262,A_1263] :
      ( r1_tarski(A_1262,A_1263)
      | ~ r1_tarski(A_1262,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_21372,c_21586])).

tff(c_21724,plain,(
    ! [A_1263] : r1_tarski('#skF_4',A_1263) ),
    inference(resolution,[status(thm)],[c_21371,c_21697])).

tff(c_21394,plain,(
    ! [B_1217,A_1218] :
      ( v1_relat_1(B_1217)
      | ~ m1_subset_1(B_1217,k1_zfmisc_1(A_1218))
      | ~ v1_relat_1(A_1218) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_21400,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_21351,c_21394])).

tff(c_21407,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19615,c_21400])).

tff(c_10,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_21332,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19586,c_19586,c_10])).

tff(c_21505,plain,(
    ! [C_1235,A_1236,B_1237] :
      ( v4_relat_1(C_1235,A_1236)
      | ~ m1_subset_1(C_1235,k1_zfmisc_1(k2_zfmisc_1(A_1236,B_1237))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_21523,plain,(
    ! [C_1239,A_1240] :
      ( v4_relat_1(C_1239,A_1240)
      | ~ m1_subset_1(C_1239,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21332,c_21505])).

tff(c_21533,plain,(
    ! [A_1240] : v4_relat_1('#skF_4',A_1240) ),
    inference(resolution,[status(thm)],[c_21351,c_21523])).

tff(c_21802,plain,(
    ! [B_1266,A_1267] :
      ( k7_relat_1(B_1266,A_1267) = B_1266
      | ~ v4_relat_1(B_1266,A_1267)
      | ~ v1_relat_1(B_1266) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_21808,plain,(
    ! [A_1240] :
      ( k7_relat_1('#skF_4',A_1240) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_21533,c_21802])).

tff(c_21815,plain,(
    ! [A_1240] : k7_relat_1('#skF_4',A_1240) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21407,c_21808])).

tff(c_21521,plain,(
    ! [A_1236] : v4_relat_1('#skF_1',A_1236) ),
    inference(resolution,[status(thm)],[c_19620,c_21505])).

tff(c_21811,plain,(
    ! [A_1236] :
      ( k7_relat_1('#skF_1',A_1236) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_21521,c_21802])).

tff(c_21818,plain,(
    ! [A_1236] : k7_relat_1('#skF_1',A_1236) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19615,c_21811])).

tff(c_22069,plain,(
    ! [B_1284,A_1285] :
      ( k1_relat_1(k7_relat_1(B_1284,A_1285)) = A_1285
      | ~ r1_tarski(A_1285,k1_relat_1(B_1284))
      | ~ v1_relat_1(B_1284) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_22100,plain,(
    ! [A_1285] :
      ( k1_relat_1(k7_relat_1('#skF_1',A_1285)) = A_1285
      | ~ r1_tarski(A_1285,'#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19589,c_22069])).

tff(c_22111,plain,(
    ! [A_1287] :
      ( A_1287 = '#skF_1'
      | ~ r1_tarski(A_1287,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19615,c_19589,c_21818,c_22100])).

tff(c_22153,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_21724,c_22111])).

tff(c_22236,plain,(
    ! [A_8] : m1_subset_1('#skF_4',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22153,c_19620])).

tff(c_22738,plain,(
    ! [A_1337,B_1338,C_1339,D_1340] :
      ( k2_partfun1(A_1337,B_1338,C_1339,D_1340) = k7_relat_1(C_1339,D_1340)
      | ~ m1_subset_1(C_1339,k1_zfmisc_1(k2_zfmisc_1(A_1337,B_1338)))
      | ~ v1_funct_1(C_1339) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_22745,plain,(
    ! [A_1337,B_1338,D_1340] :
      ( k2_partfun1(A_1337,B_1338,'#skF_4',D_1340) = k7_relat_1('#skF_4',D_1340)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22236,c_22738])).

tff(c_22754,plain,(
    ! [A_1337,B_1338,D_1340] : k2_partfun1(A_1337,B_1338,'#skF_4',D_1340) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_21815,c_22745])).

tff(c_21725,plain,(
    ! [A_1263] : r1_tarski('#skF_3',A_1263) ),
    inference(resolution,[status(thm)],[c_78,c_21697])).

tff(c_22152,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_21725,c_22111])).

tff(c_22218,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22153,c_22152])).

tff(c_21661,plain,(
    ! [A_1260] :
      ( r1_tarski(A_1260,'#skF_1')
      | ~ r1_tarski(A_1260,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_21371,c_21586])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_19643,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19610,c_19596])).

tff(c_19656,plain,(
    ! [A_1065,B_1066] :
      ( r1_tarski(A_1065,B_1066)
      | ~ m1_subset_1(A_1065,k1_zfmisc_1(B_1066)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_19663,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_19643,c_19656])).

tff(c_19664,plain,(
    ! [A_8] : r1_tarski('#skF_1',A_8) ),
    inference(resolution,[status(thm)],[c_19620,c_19656])).

tff(c_19722,plain,(
    ! [A_1078,C_1079,B_1080] :
      ( r1_tarski(A_1078,C_1079)
      | ~ r1_tarski(B_1080,C_1079)
      | ~ r1_tarski(A_1078,B_1080) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_19747,plain,(
    ! [A_1082,A_1083] :
      ( r1_tarski(A_1082,A_1083)
      | ~ r1_tarski(A_1082,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_19664,c_19722])).

tff(c_19761,plain,(
    ! [A_1083] : r1_tarski('#skF_4',A_1083) ),
    inference(resolution,[status(thm)],[c_19663,c_19747])).

tff(c_20130,plain,(
    ! [C_1119,A_1120,B_1121] :
      ( v4_relat_1(C_1119,A_1120)
      | ~ m1_subset_1(C_1119,k1_zfmisc_1(k2_zfmisc_1(A_1120,B_1121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_20147,plain,(
    ! [A_1122] : v4_relat_1('#skF_1',A_1122) ),
    inference(resolution,[status(thm)],[c_19620,c_20130])).

tff(c_20150,plain,(
    ! [A_1122] :
      ( k7_relat_1('#skF_1',A_1122) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20147,c_30])).

tff(c_20153,plain,(
    ! [A_1122] : k7_relat_1('#skF_1',A_1122) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19615,c_20150])).

tff(c_20672,plain,(
    ! [B_1160,A_1161] :
      ( k1_relat_1(k7_relat_1(B_1160,A_1161)) = A_1161
      | ~ r1_tarski(A_1161,k1_relat_1(B_1160))
      | ~ v1_relat_1(B_1160) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20715,plain,(
    ! [A_1161] :
      ( k1_relat_1(k7_relat_1('#skF_1',A_1161)) = A_1161
      | ~ r1_tarski(A_1161,'#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19589,c_20672])).

tff(c_20908,plain,(
    ! [A_1170] :
      ( A_1170 = '#skF_1'
      | ~ r1_tarski(A_1170,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19615,c_19589,c_20153,c_20715])).

tff(c_20936,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_19761,c_20908])).

tff(c_20964,plain,(
    ! [A_8] : m1_subset_1('#skF_4',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20936,c_19620])).

tff(c_21312,plain,(
    ! [A_1199,B_1200,C_1201,D_1202] :
      ( v1_funct_1(k2_partfun1(A_1199,B_1200,C_1201,D_1202))
      | ~ m1_subset_1(C_1201,k1_zfmisc_1(k2_zfmisc_1(A_1199,B_1200)))
      | ~ v1_funct_1(C_1201) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_21319,plain,(
    ! [A_1199,B_1200,D_1202] :
      ( v1_funct_1(k2_partfun1(A_1199,B_1200,'#skF_4',D_1202))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20964,c_21312])).

tff(c_21325,plain,(
    ! [A_1199,B_1200,D_1202] : v1_funct_1(k2_partfun1(A_1199,B_1200,'#skF_4',D_1202)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_21319])).

tff(c_19762,plain,(
    ! [A_1083] : r1_tarski('#skF_3',A_1083) ),
    inference(resolution,[status(thm)],[c_78,c_19747])).

tff(c_20793,plain,(
    ! [B_1164] :
      ( k1_relat_1(k7_relat_1(B_1164,'#skF_3')) = '#skF_3'
      | ~ v1_relat_1(B_1164) ) ),
    inference(resolution,[status(thm)],[c_19762,c_20672])).

tff(c_20825,plain,
    ( k1_relat_1('#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_20153,c_20793])).

tff(c_20836,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19615,c_19589,c_20825])).

tff(c_19622,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19595,c_19595,c_19595,c_19595,c_19595,c_74])).

tff(c_19623,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_19622])).

tff(c_20849,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20836,c_19623])).

tff(c_20942,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20936,c_20936,c_20936,c_20849])).

tff(c_21329,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21325,c_20942])).

tff(c_21330,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_19622])).

tff(c_21392,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21332,c_21330])).

tff(c_21393,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_21392])).

tff(c_21435,plain,(
    ~ r1_tarski(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_21393])).

tff(c_21676,plain,(
    ~ r1_tarski(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_21661,c_21435])).

tff(c_22596,plain,(
    ~ r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22218,c_22153,c_22153,c_21676])).

tff(c_22757,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22754,c_22596])).

tff(c_22761,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21724,c_22757])).

tff(c_22763,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_21392])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22811,plain,(
    r1_tarski(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_22763,c_16])).

tff(c_23079,plain,(
    ! [A_1376] : r1_tarski(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),A_1376) ),
    inference(resolution,[status(thm)],[c_22811,c_23054])).

tff(c_23727,plain,(
    k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_23079,c_23684])).

tff(c_24060,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23783,c_23732,c_23732,c_23732,c_23727])).

tff(c_22762,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_21392])).

tff(c_23757,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_3'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23732,c_23732,c_23732,c_22762])).

tff(c_24313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24087,c_24060,c_23783,c_23783,c_23757])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:56 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.38/4.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.47/4.51  
% 12.47/4.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.47/4.52  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.47/4.52  
% 12.47/4.52  %Foreground sorts:
% 12.47/4.52  
% 12.47/4.52  
% 12.47/4.52  %Background operators:
% 12.47/4.52  
% 12.47/4.52  
% 12.47/4.52  %Foreground operators:
% 12.47/4.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.47/4.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.47/4.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.47/4.52  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 12.47/4.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.47/4.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.47/4.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.47/4.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.47/4.52  tff('#skF_2', type, '#skF_2': $i).
% 12.47/4.52  tff('#skF_3', type, '#skF_3': $i).
% 12.47/4.52  tff('#skF_1', type, '#skF_1': $i).
% 12.47/4.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.47/4.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 12.47/4.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.47/4.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.47/4.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.47/4.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.47/4.52  tff('#skF_4', type, '#skF_4': $i).
% 12.47/4.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.47/4.52  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 12.47/4.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.47/4.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.47/4.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.47/4.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.47/4.52  
% 12.70/4.55  tff(f_176, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 12.70/4.55  tff(f_144, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 12.70/4.55  tff(f_138, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 12.70/4.55  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 12.70/4.55  tff(f_73, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 12.70/4.55  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 12.70/4.55  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 12.70/4.55  tff(f_96, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_relat_1)).
% 12.70/4.55  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 12.70/4.55  tff(f_32, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 12.70/4.55  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 12.70/4.55  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.70/4.55  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 12.70/4.55  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 12.70/4.55  tff(f_156, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 12.70/4.55  tff(f_112, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 12.70/4.55  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 12.70/4.55  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 12.70/4.55  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 12.70/4.55  tff(f_82, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 12.70/4.55  tff(c_84, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_176])).
% 12.70/4.55  tff(c_80, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_176])).
% 12.70/4.55  tff(c_16354, plain, (![A_946, B_947, C_948, D_949]: (k2_partfun1(A_946, B_947, C_948, D_949)=k7_relat_1(C_948, D_949) | ~m1_subset_1(C_948, k1_zfmisc_1(k2_zfmisc_1(A_946, B_947))) | ~v1_funct_1(C_948))), inference(cnfTransformation, [status(thm)], [f_144])).
% 12.70/4.55  tff(c_16370, plain, (![D_949]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_949)=k7_relat_1('#skF_4', D_949) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_80, c_16354])).
% 12.70/4.55  tff(c_16380, plain, (![D_949]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_949)=k7_relat_1('#skF_4', D_949))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_16370])).
% 12.70/4.55  tff(c_3932, plain, (![A_427, B_428, C_429, D_430]: (k2_partfun1(A_427, B_428, C_429, D_430)=k7_relat_1(C_429, D_430) | ~m1_subset_1(C_429, k1_zfmisc_1(k2_zfmisc_1(A_427, B_428))) | ~v1_funct_1(C_429))), inference(cnfTransformation, [status(thm)], [f_144])).
% 12.70/4.55  tff(c_3948, plain, (![D_430]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_430)=k7_relat_1('#skF_4', D_430) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_80, c_3932])).
% 12.70/4.55  tff(c_3958, plain, (![D_430]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_430)=k7_relat_1('#skF_4', D_430))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_3948])).
% 12.70/4.55  tff(c_4433, plain, (![A_454, B_455, C_456, D_457]: (m1_subset_1(k2_partfun1(A_454, B_455, C_456, D_457), k1_zfmisc_1(k2_zfmisc_1(A_454, B_455))) | ~m1_subset_1(C_456, k1_zfmisc_1(k2_zfmisc_1(A_454, B_455))) | ~v1_funct_1(C_456))), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.70/4.55  tff(c_4465, plain, (![D_430]: (m1_subset_1(k7_relat_1('#skF_4', D_430), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3958, c_4433])).
% 12.70/4.55  tff(c_4494, plain, (![D_459]: (m1_subset_1(k7_relat_1('#skF_4', D_459), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_4465])).
% 12.70/4.55  tff(c_42, plain, (![C_31, B_30, A_29]: (v5_relat_1(C_31, B_30) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.70/4.55  tff(c_4542, plain, (![D_459]: (v5_relat_1(k7_relat_1('#skF_4', D_459), '#skF_2'))), inference(resolution, [status(thm)], [c_4494, c_42])).
% 12.70/4.55  tff(c_28, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.70/4.55  tff(c_22, plain, (![B_16, A_14]: (v1_relat_1(B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_14)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.70/4.55  tff(c_4520, plain, (![D_459]: (v1_relat_1(k7_relat_1('#skF_4', D_459)) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_4494, c_22])).
% 12.70/4.55  tff(c_4545, plain, (![D_459]: (v1_relat_1(k7_relat_1('#skF_4', D_459)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4520])).
% 12.70/4.55  tff(c_44, plain, (![C_31, A_29, B_30]: (v4_relat_1(C_31, A_29) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.70/4.55  tff(c_4573, plain, (![D_462]: (v4_relat_1(k7_relat_1('#skF_4', D_462), '#skF_1'))), inference(resolution, [status(thm)], [c_4494, c_44])).
% 12.70/4.55  tff(c_30, plain, (![B_22, A_21]: (k7_relat_1(B_22, A_21)=B_22 | ~v4_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.70/4.55  tff(c_4576, plain, (![D_462]: (k7_relat_1(k7_relat_1('#skF_4', D_462), '#skF_1')=k7_relat_1('#skF_4', D_462) | ~v1_relat_1(k7_relat_1('#skF_4', D_462)))), inference(resolution, [status(thm)], [c_4573, c_30])).
% 12.70/4.55  tff(c_4581, plain, (![D_462]: (k7_relat_1(k7_relat_1('#skF_4', D_462), '#skF_1')=k7_relat_1('#skF_4', D_462))), inference(demodulation, [status(thm), theory('equality')], [c_4545, c_4576])).
% 12.70/4.55  tff(c_40, plain, (![B_28, A_27]: (r1_tarski(k2_relat_1(k7_relat_1(B_28, A_27)), k2_relat_1(B_28)) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_96])).
% 12.70/4.55  tff(c_26, plain, (![B_18, A_17]: (r1_tarski(k2_relat_1(B_18), A_17) | ~v5_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.70/4.55  tff(c_2115, plain, (![A_267, C_268, B_269]: (r1_tarski(A_267, C_268) | ~r1_tarski(B_269, C_268) | ~r1_tarski(A_267, B_269))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.70/4.55  tff(c_3987, plain, (![A_435, A_436, B_437]: (r1_tarski(A_435, A_436) | ~r1_tarski(A_435, k2_relat_1(B_437)) | ~v5_relat_1(B_437, A_436) | ~v1_relat_1(B_437))), inference(resolution, [status(thm)], [c_26, c_2115])).
% 12.70/4.55  tff(c_11365, plain, (![B_679, A_680, A_681]: (r1_tarski(k2_relat_1(k7_relat_1(B_679, A_680)), A_681) | ~v5_relat_1(B_679, A_681) | ~v1_relat_1(B_679))), inference(resolution, [status(thm)], [c_40, c_3987])).
% 12.70/4.55  tff(c_11515, plain, (![D_462, A_681]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', D_462)), A_681) | ~v5_relat_1(k7_relat_1('#skF_4', D_462), A_681) | ~v1_relat_1(k7_relat_1('#skF_4', D_462)))), inference(superposition, [status(thm), theory('equality')], [c_4581, c_11365])).
% 12.70/4.55  tff(c_11568, plain, (![D_462, A_681]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', D_462)), A_681) | ~v5_relat_1(k7_relat_1('#skF_4', D_462), A_681))), inference(demodulation, [status(thm), theory('equality')], [c_4545, c_11515])).
% 12.70/4.55  tff(c_3373, plain, (![A_381, B_382, C_383, D_384]: (v1_funct_1(k2_partfun1(A_381, B_382, C_383, D_384)) | ~m1_subset_1(C_383, k1_zfmisc_1(k2_zfmisc_1(A_381, B_382))) | ~v1_funct_1(C_383))), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.70/4.55  tff(c_3385, plain, (![D_384]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_384)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_80, c_3373])).
% 12.70/4.55  tff(c_3390, plain, (![D_384]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_384)))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_3385])).
% 12.70/4.55  tff(c_3959, plain, (![D_384]: (v1_funct_1(k7_relat_1('#skF_4', D_384)))), inference(demodulation, [status(thm), theory('equality')], [c_3958, c_3390])).
% 12.70/4.55  tff(c_1937, plain, (![B_238, A_239]: (v1_relat_1(B_238) | ~m1_subset_1(B_238, k1_zfmisc_1(A_239)) | ~v1_relat_1(A_239))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.70/4.55  tff(c_1946, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_80, c_1937])).
% 12.70/4.55  tff(c_1952, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1946])).
% 12.70/4.55  tff(c_4859, plain, (![D_474]: (k7_relat_1(k7_relat_1('#skF_4', D_474), '#skF_1')=k7_relat_1('#skF_4', D_474))), inference(demodulation, [status(thm), theory('equality')], [c_4545, c_4576])).
% 12.70/4.55  tff(c_36, plain, (![B_24, A_23]: (r1_tarski(k1_relat_1(k7_relat_1(B_24, A_23)), A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.70/4.55  tff(c_4886, plain, (![D_474]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_474)), '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_4', D_474)))), inference(superposition, [status(thm), theory('equality')], [c_4859, c_36])).
% 12.70/4.55  tff(c_4912, plain, (![D_475]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_475)), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4545, c_4886])).
% 12.70/4.55  tff(c_76, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_176])).
% 12.70/4.55  tff(c_99, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_76])).
% 12.70/4.55  tff(c_82, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 12.70/4.55  tff(c_2475, plain, (![A_302, B_303, C_304]: (k1_relset_1(A_302, B_303, C_304)=k1_relat_1(C_304) | ~m1_subset_1(C_304, k1_zfmisc_1(k2_zfmisc_1(A_302, B_303))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.70/4.55  tff(c_2496, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_2475])).
% 12.70/4.55  tff(c_4144, plain, (![B_439, A_440, C_441]: (k1_xboole_0=B_439 | k1_relset_1(A_440, B_439, C_441)=A_440 | ~v1_funct_2(C_441, A_440, B_439) | ~m1_subset_1(C_441, k1_zfmisc_1(k2_zfmisc_1(A_440, B_439))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 12.70/4.55  tff(c_4167, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_80, c_4144])).
% 12.70/4.55  tff(c_4178, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2496, c_4167])).
% 12.70/4.55  tff(c_4179, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_99, c_4178])).
% 12.70/4.55  tff(c_38, plain, (![B_26, A_25]: (k1_relat_1(k7_relat_1(B_26, A_25))=A_25 | ~r1_tarski(A_25, k1_relat_1(B_26)) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.70/4.55  tff(c_4202, plain, (![A_25]: (k1_relat_1(k7_relat_1('#skF_4', A_25))=A_25 | ~r1_tarski(A_25, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4179, c_38])).
% 12.70/4.55  tff(c_4668, plain, (![A_469]: (k1_relat_1(k7_relat_1('#skF_4', A_469))=A_469 | ~r1_tarski(A_469, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1952, c_4202])).
% 12.70/4.55  tff(c_4732, plain, (![A_469]: (r1_tarski(A_469, A_469) | ~v1_relat_1('#skF_4') | ~r1_tarski(A_469, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4668, c_36])).
% 12.70/4.55  tff(c_4778, plain, (![A_469]: (r1_tarski(A_469, A_469) | ~r1_tarski(A_469, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1952, c_4732])).
% 12.70/4.55  tff(c_5217, plain, (![D_495]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_495)), k1_relat_1(k7_relat_1('#skF_4', D_495))))), inference(resolution, [status(thm)], [c_4912, c_4778])).
% 12.70/4.55  tff(c_2133, plain, (![A_267, A_23, B_24]: (r1_tarski(A_267, A_23) | ~r1_tarski(A_267, k1_relat_1(k7_relat_1(B_24, A_23))) | ~v1_relat_1(B_24))), inference(resolution, [status(thm)], [c_36, c_2115])).
% 12.70/4.55  tff(c_5226, plain, (![D_495]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_495)), D_495) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_5217, c_2133])).
% 12.70/4.55  tff(c_5268, plain, (![D_495]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_495)), D_495))), inference(demodulation, [status(thm), theory('equality')], [c_1952, c_5226])).
% 12.70/4.55  tff(c_68, plain, (![B_51, A_50]: (m1_subset_1(B_51, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_51), A_50))) | ~r1_tarski(k2_relat_1(B_51), A_50) | ~v1_funct_1(B_51) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_156])).
% 12.70/4.55  tff(c_3827, plain, (![D_417, B_418, C_419, A_420]: (m1_subset_1(D_417, k1_zfmisc_1(k2_zfmisc_1(B_418, C_419))) | ~r1_tarski(k1_relat_1(D_417), B_418) | ~m1_subset_1(D_417, k1_zfmisc_1(k2_zfmisc_1(A_420, C_419))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 12.70/4.55  tff(c_14331, plain, (![B_760, B_761, A_762]: (m1_subset_1(B_760, k1_zfmisc_1(k2_zfmisc_1(B_761, A_762))) | ~r1_tarski(k1_relat_1(B_760), B_761) | ~r1_tarski(k2_relat_1(B_760), A_762) | ~v1_funct_1(B_760) | ~v1_relat_1(B_760))), inference(resolution, [status(thm)], [c_68, c_3827])).
% 12.70/4.55  tff(c_1896, plain, (![A_228, B_229, C_230, D_231]: (v1_funct_1(k2_partfun1(A_228, B_229, C_230, D_231)) | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_228, B_229))) | ~v1_funct_1(C_230))), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.70/4.55  tff(c_1908, plain, (![D_231]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_231)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_80, c_1896])).
% 12.70/4.55  tff(c_1913, plain, (![D_231]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_231)))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1908])).
% 12.70/4.55  tff(c_74, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_176])).
% 12.70/4.55  tff(c_149, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_74])).
% 12.70/4.55  tff(c_1916, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1913, c_149])).
% 12.70/4.55  tff(c_1917, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_74])).
% 12.70/4.55  tff(c_1919, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1917])).
% 12.70/4.55  tff(c_3961, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3958, c_1919])).
% 12.70/4.55  tff(c_14346, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~v1_funct_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_14331, c_3961])).
% 12.70/4.55  tff(c_14383, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4545, c_3959, c_5268, c_14346])).
% 12.70/4.55  tff(c_14397, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_11568, c_14383])).
% 12.70/4.55  tff(c_14422, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4542, c_14397])).
% 12.70/4.55  tff(c_14423, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_1917])).
% 12.70/4.55  tff(c_16393, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16380, c_14423])).
% 12.70/4.55  tff(c_14424, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_1917])).
% 12.70/4.55  tff(c_16392, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_16380, c_14424])).
% 12.70/4.55  tff(c_16761, plain, (![B_966, C_967, A_968]: (k1_xboole_0=B_966 | v1_funct_2(C_967, A_968, B_966) | k1_relset_1(A_968, B_966, C_967)!=A_968 | ~m1_subset_1(C_967, k1_zfmisc_1(k2_zfmisc_1(A_968, B_966))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 12.70/4.55  tff(c_16764, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_16392, c_16761])).
% 12.70/4.55  tff(c_16787, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_16393, c_99, c_16764])).
% 12.70/4.55  tff(c_17112, plain, (![A_976, B_977, C_978, D_979]: (m1_subset_1(k2_partfun1(A_976, B_977, C_978, D_979), k1_zfmisc_1(k2_zfmisc_1(A_976, B_977))) | ~m1_subset_1(C_978, k1_zfmisc_1(k2_zfmisc_1(A_976, B_977))) | ~v1_funct_1(C_978))), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.70/4.55  tff(c_17144, plain, (![D_949]: (m1_subset_1(k7_relat_1('#skF_4', D_949), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_16380, c_17112])).
% 12.70/4.55  tff(c_17168, plain, (![D_980]: (m1_subset_1(k7_relat_1('#skF_4', D_980), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_17144])).
% 12.70/4.55  tff(c_17194, plain, (![D_980]: (v1_relat_1(k7_relat_1('#skF_4', D_980)) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_17168, c_22])).
% 12.70/4.55  tff(c_17219, plain, (![D_980]: (v1_relat_1(k7_relat_1('#skF_4', D_980)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_17194])).
% 12.70/4.55  tff(c_14506, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_14424, c_22])).
% 12.70/4.55  tff(c_14513, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_14506])).
% 12.70/4.55  tff(c_16391, plain, (v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16380, c_14513])).
% 12.70/4.55  tff(c_14510, plain, (v4_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_14424, c_44])).
% 12.70/4.55  tff(c_16390, plain, (v4_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16380, c_14510])).
% 12.70/4.55  tff(c_16409, plain, (k7_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_3')=k7_relat_1('#skF_4', '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_16390, c_30])).
% 12.70/4.55  tff(c_16412, plain, (k7_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_3')=k7_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16391, c_16409])).
% 12.70/4.55  tff(c_78, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_176])).
% 12.70/4.55  tff(c_14442, plain, (![B_769, A_770]: (v1_relat_1(B_769) | ~m1_subset_1(B_769, k1_zfmisc_1(A_770)) | ~v1_relat_1(A_770))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.70/4.55  tff(c_14451, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_80, c_14442])).
% 12.70/4.55  tff(c_14457, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_14451])).
% 12.70/4.55  tff(c_15365, plain, (![A_863, B_864, C_865]: (k1_relset_1(A_863, B_864, C_865)=k1_relat_1(C_865) | ~m1_subset_1(C_865, k1_zfmisc_1(k2_zfmisc_1(A_863, B_864))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.70/4.55  tff(c_15390, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_15365])).
% 12.70/4.55  tff(c_16633, plain, (![B_959, A_960, C_961]: (k1_xboole_0=B_959 | k1_relset_1(A_960, B_959, C_961)=A_960 | ~v1_funct_2(C_961, A_960, B_959) | ~m1_subset_1(C_961, k1_zfmisc_1(k2_zfmisc_1(A_960, B_959))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 12.70/4.55  tff(c_16659, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_80, c_16633])).
% 12.70/4.55  tff(c_16672, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_15390, c_16659])).
% 12.70/4.55  tff(c_16673, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_99, c_16672])).
% 12.70/4.55  tff(c_16690, plain, (![A_25]: (k1_relat_1(k7_relat_1('#skF_4', A_25))=A_25 | ~r1_tarski(A_25, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_16673, c_38])).
% 12.70/4.55  tff(c_16698, plain, (![A_25]: (k1_relat_1(k7_relat_1('#skF_4', A_25))=A_25 | ~r1_tarski(A_25, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14457, c_16690])).
% 12.70/4.55  tff(c_14716, plain, (![A_804, C_805, B_806]: (r1_tarski(A_804, C_805) | ~r1_tarski(B_806, C_805) | ~r1_tarski(A_804, B_806))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.70/4.55  tff(c_14738, plain, (![A_807]: (r1_tarski(A_807, '#skF_1') | ~r1_tarski(A_807, '#skF_3'))), inference(resolution, [status(thm)], [c_78, c_14716])).
% 12.70/4.55  tff(c_14752, plain, (![B_24]: (r1_tarski(k1_relat_1(k7_relat_1(B_24, '#skF_3')), '#skF_1') | ~v1_relat_1(B_24))), inference(resolution, [status(thm)], [c_36, c_14738])).
% 12.70/4.55  tff(c_16526, plain, (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_16412, c_14752])).
% 12.70/4.55  tff(c_16546, plain, (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16391, c_16526])).
% 12.70/4.55  tff(c_16816, plain, (![A_971]: (k1_relat_1(k7_relat_1('#skF_4', A_971))=A_971 | ~r1_tarski(A_971, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14457, c_16690])).
% 12.70/4.55  tff(c_16886, plain, (![A_971]: (r1_tarski(A_971, A_971) | ~v1_relat_1('#skF_4') | ~r1_tarski(A_971, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_16816, c_36])).
% 12.70/4.55  tff(c_17015, plain, (![A_973]: (r1_tarski(A_973, A_973) | ~r1_tarski(A_973, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14457, c_16886])).
% 12.70/4.55  tff(c_17050, plain, (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), k1_relat_1(k7_relat_1('#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_16546, c_17015])).
% 12.70/4.55  tff(c_17635, plain, (r1_tarski('#skF_3', k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16698, c_17050])).
% 12.70/4.55  tff(c_17656, plain, (r1_tarski('#skF_3', k1_relat_1(k7_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_17635])).
% 12.70/4.55  tff(c_17675, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_3'))='#skF_3' | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_17656, c_38])).
% 12.70/4.55  tff(c_17697, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_17219, c_16412, c_17675])).
% 12.70/4.55  tff(c_46, plain, (![A_32, B_33, C_34]: (k1_relset_1(A_32, B_33, C_34)=k1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.70/4.55  tff(c_16497, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_16392, c_46])).
% 12.70/4.55  tff(c_19584, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_17697, c_16497])).
% 12.70/4.55  tff(c_19585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16787, c_19584])).
% 12.70/4.55  tff(c_19586, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_76])).
% 12.70/4.55  tff(c_12, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.70/4.55  tff(c_19610, plain, (![B_7]: (k2_zfmisc_1('#skF_1', B_7)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_19586, c_19586, c_12])).
% 12.70/4.55  tff(c_19587, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_76])).
% 12.70/4.55  tff(c_19595, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_19586, c_19587])).
% 12.70/4.55  tff(c_19596, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_19595, c_80])).
% 12.70/4.55  tff(c_21351, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_19610, c_19596])).
% 12.70/4.55  tff(c_21364, plain, (![A_1208, B_1209]: (r1_tarski(A_1208, B_1209) | ~m1_subset_1(A_1208, k1_zfmisc_1(B_1209)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.70/4.55  tff(c_21371, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_21351, c_21364])).
% 12.70/4.55  tff(c_14, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.70/4.55  tff(c_19620, plain, (![A_8]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_19586, c_14])).
% 12.70/4.55  tff(c_21372, plain, (![A_8]: (r1_tarski('#skF_1', A_8))), inference(resolution, [status(thm)], [c_19620, c_21364])).
% 12.70/4.55  tff(c_22888, plain, (![A_1360, C_1361, B_1362]: (r1_tarski(A_1360, C_1361) | ~r1_tarski(B_1362, C_1361) | ~r1_tarski(A_1360, B_1362))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.70/4.55  tff(c_23054, plain, (![A_1375, A_1376]: (r1_tarski(A_1375, A_1376) | ~r1_tarski(A_1375, '#skF_1'))), inference(resolution, [status(thm)], [c_21372, c_22888])).
% 12.70/4.55  tff(c_23083, plain, (![A_1376]: (r1_tarski('#skF_4', A_1376))), inference(resolution, [status(thm)], [c_21371, c_23054])).
% 12.70/4.55  tff(c_19611, plain, (![B_1058]: (k2_zfmisc_1('#skF_1', B_1058)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_19586, c_19586, c_12])).
% 12.70/4.55  tff(c_19615, plain, (v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_19611, c_28])).
% 12.70/4.55  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 12.70/4.55  tff(c_19589, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_19586, c_19586, c_34])).
% 12.70/4.55  tff(c_22818, plain, (![C_1345, A_1346, B_1347]: (v4_relat_1(C_1345, A_1346) | ~m1_subset_1(C_1345, k1_zfmisc_1(k2_zfmisc_1(A_1346, B_1347))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.70/4.55  tff(c_22834, plain, (![A_1346]: (v4_relat_1('#skF_1', A_1346))), inference(resolution, [status(thm)], [c_19620, c_22818])).
% 12.70/4.55  tff(c_22907, plain, (![B_1363, A_1364]: (k7_relat_1(B_1363, A_1364)=B_1363 | ~v4_relat_1(B_1363, A_1364) | ~v1_relat_1(B_1363))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.70/4.55  tff(c_22919, plain, (![A_1346]: (k7_relat_1('#skF_1', A_1346)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_22834, c_22907])).
% 12.70/4.55  tff(c_22929, plain, (![A_1346]: (k7_relat_1('#skF_1', A_1346)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_19615, c_22919])).
% 12.70/4.55  tff(c_23633, plain, (![B_1414, A_1415]: (k1_relat_1(k7_relat_1(B_1414, A_1415))=A_1415 | ~r1_tarski(A_1415, k1_relat_1(B_1414)) | ~v1_relat_1(B_1414))), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.70/4.55  tff(c_23672, plain, (![A_1415]: (k1_relat_1(k7_relat_1('#skF_1', A_1415))=A_1415 | ~r1_tarski(A_1415, '#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_19589, c_23633])).
% 12.70/4.55  tff(c_23684, plain, (![A_1416]: (A_1416='#skF_1' | ~r1_tarski(A_1416, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_19615, c_19589, c_22929, c_23672])).
% 12.70/4.55  tff(c_23732, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_23083, c_23684])).
% 12.70/4.55  tff(c_23769, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_23732, c_23732, c_19589])).
% 12.70/4.55  tff(c_23911, plain, (![A_1422]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_1422)))), inference(demodulation, [status(thm), theory('equality')], [c_23732, c_19620])).
% 12.70/4.55  tff(c_23915, plain, (![A_32, B_33]: (k1_relset_1(A_32, B_33, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_23911, c_46])).
% 12.70/4.55  tff(c_23933, plain, (![A_32, B_33]: (k1_relset_1(A_32, B_33, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_23769, c_23915])).
% 12.70/4.55  tff(c_23766, plain, (![A_8]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_23732, c_19620])).
% 12.70/4.55  tff(c_23773, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_23732, c_19586])).
% 12.70/4.55  tff(c_54, plain, (![C_41, B_40]: (v1_funct_2(C_41, k1_xboole_0, B_40) | k1_relset_1(k1_xboole_0, B_40, C_41)!=k1_xboole_0 | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_40))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 12.70/4.55  tff(c_88, plain, (![C_41, B_40]: (v1_funct_2(C_41, k1_xboole_0, B_40) | k1_relset_1(k1_xboole_0, B_40, C_41)!=k1_xboole_0 | ~m1_subset_1(C_41, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_54])).
% 12.70/4.55  tff(c_24078, plain, (![C_1440, B_1441]: (v1_funct_2(C_1440, '#skF_4', B_1441) | k1_relset_1('#skF_4', B_1441, C_1440)!='#skF_4' | ~m1_subset_1(C_1440, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_23773, c_23773, c_23773, c_23773, c_88])).
% 12.70/4.55  tff(c_24081, plain, (![B_1441]: (v1_funct_2('#skF_4', '#skF_4', B_1441) | k1_relset_1('#skF_4', B_1441, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_23766, c_24078])).
% 12.70/4.55  tff(c_24087, plain, (![B_1441]: (v1_funct_2('#skF_4', '#skF_4', B_1441))), inference(demodulation, [status(thm), theory('equality')], [c_23933, c_24081])).
% 12.70/4.55  tff(c_23084, plain, (![A_1376]: (r1_tarski('#skF_3', A_1376))), inference(resolution, [status(thm)], [c_78, c_23054])).
% 12.70/4.55  tff(c_23733, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_23084, c_23684])).
% 12.70/4.55  tff(c_23783, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_23732, c_23733])).
% 12.70/4.55  tff(c_21586, plain, (![A_1251, C_1252, B_1253]: (r1_tarski(A_1251, C_1252) | ~r1_tarski(B_1253, C_1252) | ~r1_tarski(A_1251, B_1253))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.70/4.55  tff(c_21697, plain, (![A_1262, A_1263]: (r1_tarski(A_1262, A_1263) | ~r1_tarski(A_1262, '#skF_1'))), inference(resolution, [status(thm)], [c_21372, c_21586])).
% 12.70/4.55  tff(c_21724, plain, (![A_1263]: (r1_tarski('#skF_4', A_1263))), inference(resolution, [status(thm)], [c_21371, c_21697])).
% 12.70/4.55  tff(c_21394, plain, (![B_1217, A_1218]: (v1_relat_1(B_1217) | ~m1_subset_1(B_1217, k1_zfmisc_1(A_1218)) | ~v1_relat_1(A_1218))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.70/4.55  tff(c_21400, plain, (v1_relat_1('#skF_4') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_21351, c_21394])).
% 12.70/4.55  tff(c_21407, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19615, c_21400])).
% 12.70/4.55  tff(c_10, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.70/4.55  tff(c_21332, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_19586, c_19586, c_10])).
% 12.70/4.55  tff(c_21505, plain, (![C_1235, A_1236, B_1237]: (v4_relat_1(C_1235, A_1236) | ~m1_subset_1(C_1235, k1_zfmisc_1(k2_zfmisc_1(A_1236, B_1237))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.70/4.55  tff(c_21523, plain, (![C_1239, A_1240]: (v4_relat_1(C_1239, A_1240) | ~m1_subset_1(C_1239, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_21332, c_21505])).
% 12.70/4.55  tff(c_21533, plain, (![A_1240]: (v4_relat_1('#skF_4', A_1240))), inference(resolution, [status(thm)], [c_21351, c_21523])).
% 12.70/4.55  tff(c_21802, plain, (![B_1266, A_1267]: (k7_relat_1(B_1266, A_1267)=B_1266 | ~v4_relat_1(B_1266, A_1267) | ~v1_relat_1(B_1266))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.70/4.55  tff(c_21808, plain, (![A_1240]: (k7_relat_1('#skF_4', A_1240)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_21533, c_21802])).
% 12.70/4.55  tff(c_21815, plain, (![A_1240]: (k7_relat_1('#skF_4', A_1240)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21407, c_21808])).
% 12.70/4.55  tff(c_21521, plain, (![A_1236]: (v4_relat_1('#skF_1', A_1236))), inference(resolution, [status(thm)], [c_19620, c_21505])).
% 12.70/4.55  tff(c_21811, plain, (![A_1236]: (k7_relat_1('#skF_1', A_1236)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_21521, c_21802])).
% 12.70/4.55  tff(c_21818, plain, (![A_1236]: (k7_relat_1('#skF_1', A_1236)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_19615, c_21811])).
% 12.70/4.55  tff(c_22069, plain, (![B_1284, A_1285]: (k1_relat_1(k7_relat_1(B_1284, A_1285))=A_1285 | ~r1_tarski(A_1285, k1_relat_1(B_1284)) | ~v1_relat_1(B_1284))), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.70/4.55  tff(c_22100, plain, (![A_1285]: (k1_relat_1(k7_relat_1('#skF_1', A_1285))=A_1285 | ~r1_tarski(A_1285, '#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_19589, c_22069])).
% 12.70/4.55  tff(c_22111, plain, (![A_1287]: (A_1287='#skF_1' | ~r1_tarski(A_1287, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_19615, c_19589, c_21818, c_22100])).
% 12.70/4.55  tff(c_22153, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_21724, c_22111])).
% 12.70/4.55  tff(c_22236, plain, (![A_8]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_22153, c_19620])).
% 12.70/4.55  tff(c_22738, plain, (![A_1337, B_1338, C_1339, D_1340]: (k2_partfun1(A_1337, B_1338, C_1339, D_1340)=k7_relat_1(C_1339, D_1340) | ~m1_subset_1(C_1339, k1_zfmisc_1(k2_zfmisc_1(A_1337, B_1338))) | ~v1_funct_1(C_1339))), inference(cnfTransformation, [status(thm)], [f_144])).
% 12.70/4.55  tff(c_22745, plain, (![A_1337, B_1338, D_1340]: (k2_partfun1(A_1337, B_1338, '#skF_4', D_1340)=k7_relat_1('#skF_4', D_1340) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_22236, c_22738])).
% 12.70/4.55  tff(c_22754, plain, (![A_1337, B_1338, D_1340]: (k2_partfun1(A_1337, B_1338, '#skF_4', D_1340)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_21815, c_22745])).
% 12.70/4.55  tff(c_21725, plain, (![A_1263]: (r1_tarski('#skF_3', A_1263))), inference(resolution, [status(thm)], [c_78, c_21697])).
% 12.70/4.55  tff(c_22152, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_21725, c_22111])).
% 12.70/4.55  tff(c_22218, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22153, c_22152])).
% 12.70/4.55  tff(c_21661, plain, (![A_1260]: (r1_tarski(A_1260, '#skF_1') | ~r1_tarski(A_1260, '#skF_4'))), inference(resolution, [status(thm)], [c_21371, c_21586])).
% 12.70/4.55  tff(c_18, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.70/4.55  tff(c_19643, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_19610, c_19596])).
% 12.70/4.55  tff(c_19656, plain, (![A_1065, B_1066]: (r1_tarski(A_1065, B_1066) | ~m1_subset_1(A_1065, k1_zfmisc_1(B_1066)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.70/4.55  tff(c_19663, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_19643, c_19656])).
% 12.70/4.55  tff(c_19664, plain, (![A_8]: (r1_tarski('#skF_1', A_8))), inference(resolution, [status(thm)], [c_19620, c_19656])).
% 12.70/4.55  tff(c_19722, plain, (![A_1078, C_1079, B_1080]: (r1_tarski(A_1078, C_1079) | ~r1_tarski(B_1080, C_1079) | ~r1_tarski(A_1078, B_1080))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.70/4.55  tff(c_19747, plain, (![A_1082, A_1083]: (r1_tarski(A_1082, A_1083) | ~r1_tarski(A_1082, '#skF_1'))), inference(resolution, [status(thm)], [c_19664, c_19722])).
% 12.70/4.55  tff(c_19761, plain, (![A_1083]: (r1_tarski('#skF_4', A_1083))), inference(resolution, [status(thm)], [c_19663, c_19747])).
% 12.70/4.55  tff(c_20130, plain, (![C_1119, A_1120, B_1121]: (v4_relat_1(C_1119, A_1120) | ~m1_subset_1(C_1119, k1_zfmisc_1(k2_zfmisc_1(A_1120, B_1121))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.70/4.55  tff(c_20147, plain, (![A_1122]: (v4_relat_1('#skF_1', A_1122))), inference(resolution, [status(thm)], [c_19620, c_20130])).
% 12.70/4.55  tff(c_20150, plain, (![A_1122]: (k7_relat_1('#skF_1', A_1122)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_20147, c_30])).
% 12.70/4.55  tff(c_20153, plain, (![A_1122]: (k7_relat_1('#skF_1', A_1122)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_19615, c_20150])).
% 12.70/4.55  tff(c_20672, plain, (![B_1160, A_1161]: (k1_relat_1(k7_relat_1(B_1160, A_1161))=A_1161 | ~r1_tarski(A_1161, k1_relat_1(B_1160)) | ~v1_relat_1(B_1160))), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.70/4.55  tff(c_20715, plain, (![A_1161]: (k1_relat_1(k7_relat_1('#skF_1', A_1161))=A_1161 | ~r1_tarski(A_1161, '#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_19589, c_20672])).
% 12.70/4.55  tff(c_20908, plain, (![A_1170]: (A_1170='#skF_1' | ~r1_tarski(A_1170, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_19615, c_19589, c_20153, c_20715])).
% 12.70/4.55  tff(c_20936, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_19761, c_20908])).
% 12.70/4.55  tff(c_20964, plain, (![A_8]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_20936, c_19620])).
% 12.70/4.55  tff(c_21312, plain, (![A_1199, B_1200, C_1201, D_1202]: (v1_funct_1(k2_partfun1(A_1199, B_1200, C_1201, D_1202)) | ~m1_subset_1(C_1201, k1_zfmisc_1(k2_zfmisc_1(A_1199, B_1200))) | ~v1_funct_1(C_1201))), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.70/4.55  tff(c_21319, plain, (![A_1199, B_1200, D_1202]: (v1_funct_1(k2_partfun1(A_1199, B_1200, '#skF_4', D_1202)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_20964, c_21312])).
% 12.70/4.55  tff(c_21325, plain, (![A_1199, B_1200, D_1202]: (v1_funct_1(k2_partfun1(A_1199, B_1200, '#skF_4', D_1202)))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_21319])).
% 12.70/4.55  tff(c_19762, plain, (![A_1083]: (r1_tarski('#skF_3', A_1083))), inference(resolution, [status(thm)], [c_78, c_19747])).
% 12.70/4.55  tff(c_20793, plain, (![B_1164]: (k1_relat_1(k7_relat_1(B_1164, '#skF_3'))='#skF_3' | ~v1_relat_1(B_1164))), inference(resolution, [status(thm)], [c_19762, c_20672])).
% 12.70/4.55  tff(c_20825, plain, (k1_relat_1('#skF_1')='#skF_3' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_20153, c_20793])).
% 12.70/4.55  tff(c_20836, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_19615, c_19589, c_20825])).
% 12.70/4.55  tff(c_19622, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_19595, c_19595, c_19595, c_19595, c_19595, c_74])).
% 12.70/4.55  tff(c_19623, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_19622])).
% 12.70/4.55  tff(c_20849, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20836, c_19623])).
% 12.70/4.55  tff(c_20942, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_20936, c_20936, c_20936, c_20849])).
% 12.70/4.55  tff(c_21329, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21325, c_20942])).
% 12.70/4.55  tff(c_21330, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(splitRight, [status(thm)], [c_19622])).
% 12.70/4.55  tff(c_21392, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_21332, c_21330])).
% 12.70/4.55  tff(c_21393, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_21392])).
% 12.70/4.55  tff(c_21435, plain, (~r1_tarski(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_18, c_21393])).
% 12.70/4.55  tff(c_21676, plain, (~r1_tarski(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_21661, c_21435])).
% 12.70/4.55  tff(c_22596, plain, (~r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22218, c_22153, c_22153, c_21676])).
% 12.70/4.55  tff(c_22757, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22754, c_22596])).
% 12.70/4.55  tff(c_22761, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21724, c_22757])).
% 12.70/4.55  tff(c_22763, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_21392])).
% 12.70/4.55  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.70/4.55  tff(c_22811, plain, (r1_tarski(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_22763, c_16])).
% 12.70/4.55  tff(c_23079, plain, (![A_1376]: (r1_tarski(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), A_1376))), inference(resolution, [status(thm)], [c_22811, c_23054])).
% 12.70/4.55  tff(c_23727, plain, (k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_23079, c_23684])).
% 12.70/4.55  tff(c_24060, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_23783, c_23732, c_23732, c_23732, c_23727])).
% 12.70/4.55  tff(c_22762, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_21392])).
% 12.70/4.55  tff(c_23757, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_3'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_23732, c_23732, c_23732, c_22762])).
% 12.70/4.55  tff(c_24313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24087, c_24060, c_23783, c_23783, c_23757])).
% 12.70/4.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.70/4.55  
% 12.70/4.55  Inference rules
% 12.70/4.55  ----------------------
% 12.70/4.55  #Ref     : 0
% 12.70/4.55  #Sup     : 5063
% 12.70/4.55  #Fact    : 0
% 12.70/4.55  #Define  : 0
% 12.70/4.55  #Split   : 43
% 12.70/4.55  #Chain   : 0
% 12.70/4.55  #Close   : 0
% 12.70/4.55  
% 12.70/4.55  Ordering : KBO
% 12.70/4.55  
% 12.70/4.55  Simplification rules
% 12.70/4.55  ----------------------
% 12.70/4.55  #Subsume      : 1337
% 12.70/4.55  #Demod        : 4295
% 12.70/4.55  #Tautology    : 1758
% 12.70/4.55  #SimpNegUnit  : 115
% 12.70/4.55  #BackRed      : 227
% 12.70/4.55  
% 12.70/4.55  #Partial instantiations: 0
% 12.70/4.55  #Strategies tried      : 1
% 12.70/4.55  
% 12.70/4.55  Timing (in seconds)
% 12.70/4.55  ----------------------
% 12.70/4.55  Preprocessing        : 0.38
% 12.70/4.55  Parsing              : 0.19
% 12.70/4.55  CNF conversion       : 0.03
% 12.70/4.55  Main loop            : 3.34
% 12.70/4.55  Inferencing          : 1.00
% 12.70/4.55  Reduction            : 1.25
% 12.70/4.55  Demodulation         : 0.88
% 12.70/4.56  BG Simplification    : 0.09
% 12.70/4.56  Subsumption          : 0.75
% 12.70/4.56  Abstraction          : 0.11
% 12.70/4.56  MUC search           : 0.00
% 12.70/4.56  Cooper               : 0.00
% 12.70/4.56  Total                : 3.81
% 12.70/4.56  Index Insertion      : 0.00
% 12.70/4.56  Index Deletion       : 0.00
% 12.70/4.56  Index Matching       : 0.00
% 12.70/4.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
