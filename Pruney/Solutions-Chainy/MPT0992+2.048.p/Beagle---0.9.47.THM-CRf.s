%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:38 EST 2020

% Result     : Theorem 52.42s
% Output     : CNFRefutation 52.52s
% Verified   : 
% Statistics : Number of formulae       :  270 (3601 expanded)
%              Number of leaves         :   43 (1119 expanded)
%              Depth                    :   13
%              Number of atoms          :  465 (10225 expanded)
%              Number of equality atoms :  132 (4269 expanded)
%              Maximal formula depth    :   11 (   4 average)
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

tff(f_167,negated_conjecture,(
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

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_121,axiom,(
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

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_135,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_129,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_147,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_75,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_50,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(c_76,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_78,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_2224,plain,(
    ! [C_254,A_255,B_256] :
      ( v1_relat_1(C_254)
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2241,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_2224])).

tff(c_74,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_97,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_80,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_207670,plain,(
    ! [A_2597,B_2598,C_2599] :
      ( k1_relset_1(A_2597,B_2598,C_2599) = k1_relat_1(C_2599)
      | ~ m1_subset_1(C_2599,k1_zfmisc_1(k2_zfmisc_1(A_2597,B_2598))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_207693,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_207670])).

tff(c_209398,plain,(
    ! [B_2728,A_2729,C_2730] :
      ( k1_xboole_0 = B_2728
      | k1_relset_1(A_2729,B_2728,C_2730) = A_2729
      | ~ v1_funct_2(C_2730,A_2729,B_2728)
      | ~ m1_subset_1(C_2730,k1_zfmisc_1(k2_zfmisc_1(A_2729,B_2728))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_209411,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_209398])).

tff(c_209428,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_207693,c_209411])).

tff(c_209429,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_209428])).

tff(c_34,plain,(
    ! [B_21,A_20] :
      ( k1_relat_1(k7_relat_1(B_21,A_20)) = A_20
      | ~ r1_tarski(A_20,k1_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_209446,plain,(
    ! [A_20] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_20)) = A_20
      | ~ r1_tarski(A_20,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209429,c_34])).

tff(c_209459,plain,(
    ! [A_20] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_20)) = A_20
      | ~ r1_tarski(A_20,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2241,c_209446])).

tff(c_82,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_209281,plain,(
    ! [A_2721,B_2722,C_2723,D_2724] :
      ( k2_partfun1(A_2721,B_2722,C_2723,D_2724) = k7_relat_1(C_2723,D_2724)
      | ~ m1_subset_1(C_2723,k1_zfmisc_1(k2_zfmisc_1(A_2721,B_2722)))
      | ~ v1_funct_1(C_2723) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_209290,plain,(
    ! [D_2724] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_2724) = k7_relat_1('#skF_4',D_2724)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_78,c_209281])).

tff(c_209305,plain,(
    ! [D_2724] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_2724) = k7_relat_1('#skF_4',D_2724) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_209290])).

tff(c_9674,plain,(
    ! [A_683,B_684,C_685,D_686] :
      ( k2_partfun1(A_683,B_684,C_685,D_686) = k7_relat_1(C_685,D_686)
      | ~ m1_subset_1(C_685,k1_zfmisc_1(k2_zfmisc_1(A_683,B_684)))
      | ~ v1_funct_1(C_685) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_9681,plain,(
    ! [D_686] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_686) = k7_relat_1('#skF_4',D_686)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_78,c_9674])).

tff(c_9693,plain,(
    ! [D_686] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_686) = k7_relat_1('#skF_4',D_686) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_9681])).

tff(c_10126,plain,(
    ! [A_702,B_703,C_704,D_705] :
      ( m1_subset_1(k2_partfun1(A_702,B_703,C_704,D_705),k1_zfmisc_1(k2_zfmisc_1(A_702,B_703)))
      | ~ m1_subset_1(C_704,k1_zfmisc_1(k2_zfmisc_1(A_702,B_703)))
      | ~ v1_funct_1(C_704) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_10156,plain,(
    ! [D_686] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_686),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9693,c_10126])).

tff(c_10236,plain,(
    ! [D_711] : m1_subset_1(k7_relat_1('#skF_4',D_711),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_10156])).

tff(c_40,plain,(
    ! [C_27,A_25,B_26] :
      ( v1_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_10286,plain,(
    ! [D_711] : v1_relat_1(k7_relat_1('#skF_4',D_711)) ),
    inference(resolution,[status(thm)],[c_10236,c_40])).

tff(c_38,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_24,A_23)),k2_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2503,plain,(
    ! [B_294,A_295] :
      ( v5_relat_1(B_294,A_295)
      | ~ r1_tarski(k2_relat_1(B_294),A_295)
      | ~ v1_relat_1(B_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2519,plain,(
    ! [B_24,A_23] :
      ( v5_relat_1(k7_relat_1(B_24,A_23),k2_relat_1(B_24))
      | ~ v1_relat_1(k7_relat_1(B_24,A_23))
      | ~ v1_relat_1(B_24) ) ),
    inference(resolution,[status(thm)],[c_38,c_2503])).

tff(c_2523,plain,(
    ! [C_297,B_298,A_299] :
      ( v5_relat_1(C_297,B_298)
      | ~ m1_subset_1(C_297,k1_zfmisc_1(k2_zfmisc_1(A_299,B_298))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2542,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_2523])).

tff(c_26,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v5_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2588,plain,(
    ! [B_308,A_309] :
      ( r1_tarski(k2_relat_1(B_308),A_309)
      | ~ v5_relat_1(B_308,A_309)
      | ~ v1_relat_1(B_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3796,plain,(
    ! [A_422,A_423,B_424] :
      ( r1_tarski(A_422,A_423)
      | ~ r1_tarski(A_422,k2_relat_1(B_424))
      | ~ v5_relat_1(B_424,A_423)
      | ~ v1_relat_1(B_424) ) ),
    inference(resolution,[status(thm)],[c_2588,c_4])).

tff(c_26917,plain,(
    ! [B_1245,A_1246,B_1247] :
      ( r1_tarski(k2_relat_1(B_1245),A_1246)
      | ~ v5_relat_1(B_1247,A_1246)
      | ~ v1_relat_1(B_1247)
      | ~ v5_relat_1(B_1245,k2_relat_1(B_1247))
      | ~ v1_relat_1(B_1245) ) ),
    inference(resolution,[status(thm)],[c_26,c_3796])).

tff(c_26987,plain,(
    ! [B_1245] :
      ( r1_tarski(k2_relat_1(B_1245),'#skF_2')
      | ~ v1_relat_1('#skF_4')
      | ~ v5_relat_1(B_1245,k2_relat_1('#skF_4'))
      | ~ v1_relat_1(B_1245) ) ),
    inference(resolution,[status(thm)],[c_2542,c_26917])).

tff(c_27062,plain,(
    ! [B_1248] :
      ( r1_tarski(k2_relat_1(B_1248),'#skF_2')
      | ~ v5_relat_1(B_1248,k2_relat_1('#skF_4'))
      | ~ v1_relat_1(B_1248) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2241,c_26987])).

tff(c_27122,plain,(
    ! [A_23] :
      ( r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_23)),'#skF_2')
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_23))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2519,c_27062])).

tff(c_27174,plain,(
    ! [A_23] : r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_23)),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2241,c_10286,c_27122])).

tff(c_4539,plain,(
    ! [A_460,B_461,C_462,D_463] :
      ( v1_funct_1(k2_partfun1(A_460,B_461,C_462,D_463))
      | ~ m1_subset_1(C_462,k1_zfmisc_1(k2_zfmisc_1(A_460,B_461)))
      | ~ v1_funct_1(C_462) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_4544,plain,(
    ! [D_463] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_463))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_78,c_4539])).

tff(c_4555,plain,(
    ! [D_463] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_463)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_4544])).

tff(c_9718,plain,(
    ! [D_463] : v1_funct_1(k7_relat_1('#skF_4',D_463)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9693,c_4555])).

tff(c_3088,plain,(
    ! [A_354,B_355,C_356] :
      ( k1_relset_1(A_354,B_355,C_356) = k1_relat_1(C_356)
      | ~ m1_subset_1(C_356,k1_zfmisc_1(k2_zfmisc_1(A_354,B_355))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3107,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_3088])).

tff(c_9771,plain,(
    ! [B_693,A_694,C_695] :
      ( k1_xboole_0 = B_693
      | k1_relset_1(A_694,B_693,C_695) = A_694
      | ~ v1_funct_2(C_695,A_694,B_693)
      | ~ m1_subset_1(C_695,k1_zfmisc_1(k2_zfmisc_1(A_694,B_693))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_9781,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_9771])).

tff(c_9796,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3107,c_9781])).

tff(c_9797,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_9796])).

tff(c_9814,plain,(
    ! [A_20] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_20)) = A_20
      | ~ r1_tarski(A_20,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9797,c_34])).

tff(c_9827,plain,(
    ! [A_20] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_20)) = A_20
      | ~ r1_tarski(A_20,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2241,c_9814])).

tff(c_9500,plain,(
    ! [B_671,A_672] :
      ( m1_subset_1(B_671,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_671),A_672)))
      | ~ r1_tarski(k2_relat_1(B_671),A_672)
      | ~ v1_funct_1(B_671)
      | ~ v1_relat_1(B_671) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10770,plain,(
    ! [B_734,A_735] :
      ( r1_tarski(B_734,k2_zfmisc_1(k1_relat_1(B_734),A_735))
      | ~ r1_tarski(k2_relat_1(B_734),A_735)
      | ~ v1_funct_1(B_734)
      | ~ v1_relat_1(B_734) ) ),
    inference(resolution,[status(thm)],[c_9500,c_18])).

tff(c_10811,plain,(
    ! [A_20,A_735] :
      ( r1_tarski(k7_relat_1('#skF_4',A_20),k2_zfmisc_1(A_20,A_735))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_20)),A_735)
      | ~ v1_funct_1(k7_relat_1('#skF_4',A_20))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_20))
      | ~ r1_tarski(A_20,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9827,c_10770])).

tff(c_206448,plain,(
    ! [A_2527,A_2528] :
      ( r1_tarski(k7_relat_1('#skF_4',A_2527),k2_zfmisc_1(A_2527,A_2528))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_2527)),A_2528)
      | ~ r1_tarski(A_2527,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10286,c_9718,c_10811])).

tff(c_206885,plain,(
    ! [A_2529] :
      ( r1_tarski(k7_relat_1('#skF_4',A_2529),k2_zfmisc_1(A_2529,'#skF_2'))
      | ~ r1_tarski(A_2529,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_27174,c_206448])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2201,plain,(
    ! [A_250,B_251,C_252,D_253] :
      ( v1_funct_1(k2_partfun1(A_250,B_251,C_252,D_253))
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_250,B_251)))
      | ~ v1_funct_1(C_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2206,plain,(
    ! [D_253] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_253))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_78,c_2201])).

tff(c_2217,plain,(
    ! [D_253] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_253)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2206])).

tff(c_72,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_203,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_2221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2217,c_203])).

tff(c_2222,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_2443,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2222])).

tff(c_2548,plain,(
    ~ r1_tarski(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_2443])).

tff(c_9719,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9693,c_2548])).

tff(c_206916,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_206885,c_9719])).

tff(c_207018,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_206916])).

tff(c_207020,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_2222])).

tff(c_207691,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_207020,c_207670])).

tff(c_209311,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209305,c_209305,c_207691])).

tff(c_207019,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2222])).

tff(c_209318,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_209305,c_207019])).

tff(c_209317,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209305,c_207020])).

tff(c_209577,plain,(
    ! [B_2731,C_2732,A_2733] :
      ( k1_xboole_0 = B_2731
      | v1_funct_2(C_2732,A_2733,B_2731)
      | k1_relset_1(A_2733,B_2731,C_2732) != A_2733
      | ~ m1_subset_1(C_2732,k1_zfmisc_1(k2_zfmisc_1(A_2733,B_2731))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_209580,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_209317,c_209577])).

tff(c_209603,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_209318,c_97,c_209580])).

tff(c_210071,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_209311,c_209603])).

tff(c_210078,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_209459,c_210071])).

tff(c_210082,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_210078])).

tff(c_210083,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_14,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_210108,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_1',B_8) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_210083,c_210083,c_14])).

tff(c_210084,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_210093,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_210083,c_210084])).

tff(c_210136,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210108,c_210093,c_78])).

tff(c_12,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_210118,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_210083,c_210083,c_12])).

tff(c_215673,plain,(
    ! [C_3209,A_3210,B_3211] :
      ( v1_relat_1(C_3209)
      | ~ m1_subset_1(C_3209,k1_zfmisc_1(k2_zfmisc_1(A_3210,B_3211))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_215689,plain,(
    ! [C_3212] :
      ( v1_relat_1(C_3212)
      | ~ m1_subset_1(C_3212,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210118,c_215673])).

tff(c_215706,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_210136,c_215689])).

tff(c_215655,plain,(
    ! [A_3207,B_3208] :
      ( r1_tarski(A_3207,B_3208)
      | ~ m1_subset_1(A_3207,k1_zfmisc_1(B_3208)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_215666,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_210136,c_215655])).

tff(c_6,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_210087,plain,(
    ! [A_4] : r1_tarski('#skF_1',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210083,c_6])).

tff(c_215810,plain,(
    ! [A_3235,C_3236,B_3237] :
      ( r1_tarski(A_3235,C_3236)
      | ~ r1_tarski(B_3237,C_3236)
      | ~ r1_tarski(A_3235,B_3237) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_215823,plain,(
    ! [A_3238,A_3239] :
      ( r1_tarski(A_3238,A_3239)
      | ~ r1_tarski(A_3238,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_210087,c_215810])).

tff(c_215834,plain,(
    ! [A_3239] : r1_tarski('#skF_4',A_3239) ),
    inference(resolution,[status(thm)],[c_215666,c_215823])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_210086,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_210083,c_210083,c_32])).

tff(c_212306,plain,(
    ! [A_2948] :
      ( k7_relat_1(A_2948,k1_relat_1(A_2948)) = A_2948
      | ~ v1_relat_1(A_2948) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_212315,plain,
    ( k7_relat_1('#skF_1','#skF_1') = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_210086,c_212306])).

tff(c_215598,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_212315])).

tff(c_16,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_210116,plain,(
    ! [A_9] : m1_subset_1('#skF_1',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210083,c_16])).

tff(c_215630,plain,(
    ! [C_3202,A_3203,B_3204] :
      ( v1_relat_1(C_3202)
      | ~ m1_subset_1(C_3202,k1_zfmisc_1(k2_zfmisc_1(A_3203,B_3204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_215640,plain,(
    v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_210116,c_215630])).

tff(c_215647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_215598,c_215640])).

tff(c_215649,plain,(
    v1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_212315])).

tff(c_215648,plain,(
    k7_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_212315])).

tff(c_217384,plain,(
    ! [C_3352,A_3353,B_3354] :
      ( k7_relat_1(k7_relat_1(C_3352,A_3353),B_3354) = k7_relat_1(C_3352,A_3353)
      | ~ r1_tarski(A_3353,B_3354)
      | ~ v1_relat_1(C_3352) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_217425,plain,(
    ! [B_3354] :
      ( k7_relat_1('#skF_1',B_3354) = k7_relat_1('#skF_1','#skF_1')
      | ~ r1_tarski('#skF_1',B_3354)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215648,c_217384])).

tff(c_217457,plain,(
    ! [B_3355] : k7_relat_1('#skF_1',B_3355) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_215649,c_210087,c_215648,c_217425])).

tff(c_216510,plain,(
    ! [B_3298,A_3299] :
      ( k1_relat_1(k7_relat_1(B_3298,A_3299)) = A_3299
      | ~ r1_tarski(A_3299,k1_relat_1(B_3298))
      | ~ v1_relat_1(B_3298) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_216547,plain,(
    ! [B_3298] :
      ( k1_relat_1(k7_relat_1(B_3298,'#skF_4')) = '#skF_4'
      | ~ v1_relat_1(B_3298) ) ),
    inference(resolution,[status(thm)],[c_215834,c_216510])).

tff(c_217470,plain,
    ( k1_relat_1('#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_217457,c_216547])).

tff(c_217498,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_215649,c_210086,c_217470])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_210085,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_210083,c_210083,c_30])).

tff(c_217556,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_217498,c_217498,c_210085])).

tff(c_217557,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_217498,c_217498,c_210086])).

tff(c_217676,plain,(
    ! [B_3356,A_3357] :
      ( v1_funct_2(B_3356,k1_relat_1(B_3356),A_3357)
      | ~ r1_tarski(k2_relat_1(B_3356),A_3357)
      | ~ v1_funct_1(B_3356)
      | ~ v1_relat_1(B_3356) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_217679,plain,(
    ! [A_3357] :
      ( v1_funct_2('#skF_4','#skF_4',A_3357)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_3357)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217557,c_217676])).

tff(c_217684,plain,(
    ! [A_3357] : v1_funct_2('#skF_4','#skF_4',A_3357) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215706,c_82,c_215834,c_217556,c_217679])).

tff(c_217439,plain,(
    ! [B_3354] : k7_relat_1('#skF_1',B_3354) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_215649,c_210087,c_215648,c_217425])).

tff(c_217512,plain,(
    ! [B_3354] : k7_relat_1('#skF_4',B_3354) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_217498,c_217498,c_217439])).

tff(c_217554,plain,(
    ! [A_9] : m1_subset_1('#skF_4',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217498,c_210116])).

tff(c_217982,plain,(
    ! [A_3388,B_3389,C_3390,D_3391] :
      ( k2_partfun1(A_3388,B_3389,C_3390,D_3391) = k7_relat_1(C_3390,D_3391)
      | ~ m1_subset_1(C_3390,k1_zfmisc_1(k2_zfmisc_1(A_3388,B_3389)))
      | ~ v1_funct_1(C_3390) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_217989,plain,(
    ! [A_3388,B_3389,D_3391] :
      ( k2_partfun1(A_3388,B_3389,'#skF_4',D_3391) = k7_relat_1('#skF_4',D_3391)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_217554,c_217982])).

tff(c_217998,plain,(
    ! [A_3388,B_3389,D_3391] : k2_partfun1(A_3388,B_3389,'#skF_4',D_3391) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_217512,c_217989])).

tff(c_215837,plain,(
    ! [A_3239] : r1_tarski('#skF_3',A_3239) ),
    inference(resolution,[status(thm)],[c_76,c_215823])).

tff(c_216545,plain,(
    ! [B_3298] :
      ( k1_relat_1(k7_relat_1(B_3298,'#skF_3')) = '#skF_3'
      | ~ v1_relat_1(B_3298) ) ),
    inference(resolution,[status(thm)],[c_215837,c_216510])).

tff(c_217474,plain,
    ( k1_relat_1('#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_217457,c_216545])).

tff(c_217500,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_215649,c_210086,c_217474])).

tff(c_217571,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_217498,c_217500])).

tff(c_212371,plain,(
    ! [A_2958,B_2959] :
      ( r1_tarski(A_2958,B_2959)
      | ~ m1_subset_1(A_2958,k1_zfmisc_1(B_2959)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_212378,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_210136,c_212371])).

tff(c_212567,plain,(
    ! [A_2991,C_2992,B_2993] :
      ( r1_tarski(A_2991,C_2992)
      | ~ r1_tarski(B_2993,C_2992)
      | ~ r1_tarski(A_2991,B_2993) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_212583,plain,(
    ! [A_2994,A_2995] :
      ( r1_tarski(A_2994,A_2995)
      | ~ r1_tarski(A_2994,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_210087,c_212567])).

tff(c_212594,plain,(
    ! [A_2995] : r1_tarski('#skF_4',A_2995) ),
    inference(resolution,[status(thm)],[c_212378,c_212583])).

tff(c_212390,plain,(
    ! [C_2962,A_2963,B_2964] :
      ( v1_relat_1(C_2962)
      | ~ m1_subset_1(C_2962,k1_zfmisc_1(k2_zfmisc_1(A_2963,B_2964))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_212418,plain,(
    ! [C_2967] :
      ( v1_relat_1(C_2967)
      | ~ m1_subset_1(C_2967,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210118,c_212390])).

tff(c_212431,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_210136,c_212418])).

tff(c_213776,plain,(
    ! [A_3089,B_3090,C_3091] :
      ( k1_relset_1(A_3089,B_3090,C_3091) = k1_relat_1(C_3091)
      | ~ m1_subset_1(C_3091,k1_zfmisc_1(k2_zfmisc_1(A_3089,B_3090))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_213864,plain,(
    ! [A_3099,C_3100] :
      ( k1_relset_1(A_3099,'#skF_1',C_3100) = k1_relat_1(C_3100)
      | ~ m1_subset_1(C_3100,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210118,c_213776])).

tff(c_213874,plain,(
    ! [A_3099] : k1_relset_1(A_3099,'#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_210136,c_213864])).

tff(c_210098,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_210093,c_80])).

tff(c_56,plain,(
    ! [B_35,C_36] :
      ( k1_relset_1(k1_xboole_0,B_35,C_36) = k1_xboole_0
      | ~ v1_funct_2(C_36,k1_xboole_0,B_35)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_85,plain,(
    ! [B_35,C_36] :
      ( k1_relset_1(k1_xboole_0,B_35,C_36) = k1_xboole_0
      | ~ v1_funct_2(C_36,k1_xboole_0,B_35)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_56])).

tff(c_214634,plain,(
    ! [B_3139,C_3140] :
      ( k1_relset_1('#skF_1',B_3139,C_3140) = '#skF_1'
      | ~ v1_funct_2(C_3140,'#skF_1',B_3139)
      | ~ m1_subset_1(C_3140,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210083,c_210083,c_210083,c_210083,c_85])).

tff(c_214641,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_4') = '#skF_1'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_210098,c_214634])).

tff(c_214651,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_210136,c_213874,c_214641])).

tff(c_36,plain,(
    ! [A_22] :
      ( k7_relat_1(A_22,k1_relat_1(A_22)) = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_214663,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_214651,c_36])).

tff(c_214671,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_212431,c_214663])).

tff(c_214834,plain,(
    ! [C_3146,A_3147,B_3148] :
      ( k7_relat_1(k7_relat_1(C_3146,A_3147),B_3148) = k7_relat_1(C_3146,A_3147)
      | ~ r1_tarski(A_3147,B_3148)
      | ~ v1_relat_1(C_3146) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_214880,plain,(
    ! [B_3148] :
      ( k7_relat_1('#skF_4',B_3148) = k7_relat_1('#skF_4','#skF_1')
      | ~ r1_tarski('#skF_1',B_3148)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214671,c_214834])).

tff(c_214897,plain,(
    ! [B_3148] : k7_relat_1('#skF_4',B_3148) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_212431,c_210087,c_214671,c_214880])).

tff(c_212319,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_212315])).

tff(c_212347,plain,(
    ! [C_2955,A_2956,B_2957] :
      ( v1_relat_1(C_2955)
      | ~ m1_subset_1(C_2955,k1_zfmisc_1(k2_zfmisc_1(A_2956,B_2957))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_212357,plain,(
    v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_210116,c_212347])).

tff(c_212364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_212319,c_212357])).

tff(c_212366,plain,(
    v1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_212315])).

tff(c_212365,plain,(
    k7_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_212315])).

tff(c_214883,plain,(
    ! [B_3148] :
      ( k7_relat_1('#skF_1',B_3148) = k7_relat_1('#skF_1','#skF_1')
      | ~ r1_tarski('#skF_1',B_3148)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212365,c_214834])).

tff(c_214919,plain,(
    ! [B_3149] : k7_relat_1('#skF_1',B_3149) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_212366,c_210087,c_212365,c_214883])).

tff(c_213216,plain,(
    ! [B_3052,A_3053] :
      ( k1_relat_1(k7_relat_1(B_3052,A_3053)) = A_3053
      | ~ r1_tarski(A_3053,k1_relat_1(B_3052))
      | ~ v1_relat_1(B_3052) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_213253,plain,(
    ! [B_3052] :
      ( k1_relat_1(k7_relat_1(B_3052,'#skF_4')) = '#skF_4'
      | ~ v1_relat_1(B_3052) ) ),
    inference(resolution,[status(thm)],[c_212594,c_213216])).

tff(c_214936,plain,
    ( k1_relat_1('#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_214919,c_213253])).

tff(c_214966,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_212366,c_210086,c_214936])).

tff(c_215025,plain,(
    ! [A_9] : m1_subset_1('#skF_4',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214966,c_210116])).

tff(c_215454,plain,(
    ! [A_3175,B_3176,C_3177,D_3178] :
      ( k2_partfun1(A_3175,B_3176,C_3177,D_3178) = k7_relat_1(C_3177,D_3178)
      | ~ m1_subset_1(C_3177,k1_zfmisc_1(k2_zfmisc_1(A_3175,B_3176)))
      | ~ v1_funct_1(C_3177) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_215461,plain,(
    ! [A_3175,B_3176,D_3178] :
      ( k2_partfun1(A_3175,B_3176,'#skF_4',D_3178) = k7_relat_1('#skF_4',D_3178)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_215025,c_215454])).

tff(c_215470,plain,(
    ! [A_3175,B_3176,D_3178] : k2_partfun1(A_3175,B_3176,'#skF_4',D_3178) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_214897,c_215461])).

tff(c_212597,plain,(
    ! [A_2995] : r1_tarski('#skF_3',A_2995) ),
    inference(resolution,[status(thm)],[c_76,c_212583])).

tff(c_213252,plain,(
    ! [B_3052] :
      ( k1_relat_1(k7_relat_1(B_3052,'#skF_3')) = '#skF_3'
      | ~ v1_relat_1(B_3052) ) ),
    inference(resolution,[status(thm)],[c_212597,c_213216])).

tff(c_214940,plain,
    ( k1_relat_1('#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_214919,c_213252])).

tff(c_214968,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_212366,c_210086,c_214940])).

tff(c_215043,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_214966,c_214968])).

tff(c_212381,plain,(
    ! [A_2960,B_2961] :
      ( m1_subset_1(A_2960,k1_zfmisc_1(B_2961))
      | ~ r1_tarski(A_2960,B_2961) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_210159,plain,(
    ! [A_2763] :
      ( k7_relat_1(A_2763,k1_relat_1(A_2763)) = A_2763
      | ~ v1_relat_1(A_2763) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_210168,plain,
    ( k7_relat_1('#skF_1','#skF_1') = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_210086,c_210159])).

tff(c_210171,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_210168])).

tff(c_210189,plain,(
    ! [C_2768,A_2769,B_2770] :
      ( v1_relat_1(C_2768)
      | ~ m1_subset_1(C_2768,k1_zfmisc_1(k2_zfmisc_1(A_2769,B_2770))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_210199,plain,(
    v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_210116,c_210189])).

tff(c_210206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_210171,c_210199])).

tff(c_210208,plain,(
    v1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_210168])).

tff(c_210207,plain,(
    k7_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_210168])).

tff(c_211754,plain,(
    ! [C_2915,A_2916,B_2917] :
      ( k7_relat_1(k7_relat_1(C_2915,A_2916),B_2917) = k7_relat_1(C_2915,A_2916)
      | ~ r1_tarski(A_2916,B_2917)
      | ~ v1_relat_1(C_2915) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_211788,plain,(
    ! [B_2917] :
      ( k7_relat_1('#skF_1',B_2917) = k7_relat_1('#skF_1','#skF_1')
      | ~ r1_tarski('#skF_1',B_2917)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210207,c_211754])).

tff(c_211818,plain,(
    ! [B_2918] : k7_relat_1('#skF_1',B_2918) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_210208,c_210087,c_210207,c_211788])).

tff(c_210149,plain,(
    ! [A_2761,B_2762] :
      ( r1_tarski(A_2761,B_2762)
      | ~ m1_subset_1(A_2761,k1_zfmisc_1(B_2762)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_210156,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_210136,c_210149])).

tff(c_210487,plain,(
    ! [A_2818,C_2819,B_2820] :
      ( r1_tarski(A_2818,C_2819)
      | ~ r1_tarski(B_2820,C_2819)
      | ~ r1_tarski(A_2818,B_2820) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_210516,plain,(
    ! [A_2824,A_2825] :
      ( r1_tarski(A_2824,A_2825)
      | ~ r1_tarski(A_2824,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_210087,c_210487])).

tff(c_210531,plain,(
    ! [A_2825] : r1_tarski('#skF_4',A_2825) ),
    inference(resolution,[status(thm)],[c_210156,c_210516])).

tff(c_210680,plain,(
    ! [B_2836,A_2837] :
      ( k1_relat_1(k7_relat_1(B_2836,A_2837)) = A_2837
      | ~ r1_tarski(A_2837,k1_relat_1(B_2836))
      | ~ v1_relat_1(B_2836) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_210706,plain,(
    ! [B_2836] :
      ( k1_relat_1(k7_relat_1(B_2836,'#skF_4')) = '#skF_4'
      | ~ v1_relat_1(B_2836) ) ),
    inference(resolution,[status(thm)],[c_210531,c_210680])).

tff(c_211827,plain,
    ( k1_relat_1('#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_211818,c_210706])).

tff(c_211853,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_210208,c_210086,c_211827])).

tff(c_211902,plain,(
    ! [A_9] : m1_subset_1('#skF_4',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211853,c_210116])).

tff(c_212179,plain,(
    ! [A_2927,B_2928,C_2929,D_2930] :
      ( v1_funct_1(k2_partfun1(A_2927,B_2928,C_2929,D_2930))
      | ~ m1_subset_1(C_2929,k1_zfmisc_1(k2_zfmisc_1(A_2927,B_2928)))
      | ~ v1_funct_1(C_2929) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_212184,plain,(
    ! [A_2927,B_2928,D_2930] :
      ( v1_funct_1(k2_partfun1(A_2927,B_2928,'#skF_4',D_2930))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_211902,c_212179])).

tff(c_212192,plain,(
    ! [A_2927,B_2928,D_2930] : v1_funct_1(k2_partfun1(A_2927,B_2928,'#skF_4',D_2930)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_212184])).

tff(c_210534,plain,(
    ! [A_2825] : r1_tarski('#skF_3',A_2825) ),
    inference(resolution,[status(thm)],[c_76,c_210516])).

tff(c_210705,plain,(
    ! [B_2836] :
      ( k1_relat_1(k7_relat_1(B_2836,'#skF_3')) = '#skF_3'
      | ~ v1_relat_1(B_2836) ) ),
    inference(resolution,[status(thm)],[c_210534,c_210680])).

tff(c_211831,plain,
    ( k1_relat_1('#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_211818,c_210705])).

tff(c_211855,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_210208,c_210086,c_211831])).

tff(c_211919,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_211853,c_211855])).

tff(c_210137,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210093,c_210093,c_210093,c_210118,c_210093,c_210093,c_72])).

tff(c_210138,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_210137])).

tff(c_211897,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211853,c_211853,c_210138])).

tff(c_212289,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211919,c_211897])).

tff(c_212293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_212192,c_212289])).

tff(c_212294,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_210137])).

tff(c_212318,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_212294])).

tff(c_212389,plain,(
    ~ r1_tarski(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_212381,c_212318])).

tff(c_215017,plain,(
    ~ r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_214966,c_214966,c_214966,c_212389])).

tff(c_215595,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_212594,c_215470,c_215043,c_215017])).

tff(c_215596,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_212294])).

tff(c_217546,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_3'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_217498,c_217498,c_217498,c_215596])).

tff(c_218142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_217684,c_217998,c_217571,c_217571,c_217546])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:25:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 52.42/39.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 52.52/39.38  
% 52.52/39.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 52.52/39.39  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 52.52/39.39  
% 52.52/39.39  %Foreground sorts:
% 52.52/39.39  
% 52.52/39.39  
% 52.52/39.39  %Background operators:
% 52.52/39.39  
% 52.52/39.39  
% 52.52/39.39  %Foreground operators:
% 52.52/39.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 52.52/39.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 52.52/39.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 52.52/39.39  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 52.52/39.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 52.52/39.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 52.52/39.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 52.52/39.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 52.52/39.39  tff('#skF_2', type, '#skF_2': $i).
% 52.52/39.39  tff('#skF_3', type, '#skF_3': $i).
% 52.52/39.39  tff('#skF_1', type, '#skF_1': $i).
% 52.52/39.39  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 52.52/39.39  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 52.52/39.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 52.52/39.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 52.52/39.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 52.52/39.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 52.52/39.39  tff('#skF_4', type, '#skF_4': $i).
% 52.52/39.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 52.52/39.39  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 52.52/39.39  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 52.52/39.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 52.52/39.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 52.52/39.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 52.52/39.39  
% 52.52/39.42  tff(f_167, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 52.52/39.42  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 52.52/39.42  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 52.52/39.42  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 52.52/39.42  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 52.52/39.42  tff(f_135, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 52.52/39.42  tff(f_129, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 52.52/39.42  tff(f_89, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_relat_1)).
% 52.52/39.42  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 52.52/39.42  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 52.52/39.42  tff(f_32, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 52.52/39.42  tff(f_147, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 52.52/39.42  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 52.52/39.42  tff(f_48, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 52.52/39.42  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 52.52/39.42  tff(f_75, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 52.52/39.42  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 52.52/39.42  tff(f_50, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 52.52/39.42  tff(f_72, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 52.52/39.42  tff(c_76, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_167])).
% 52.52/39.42  tff(c_78, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 52.52/39.42  tff(c_2224, plain, (![C_254, A_255, B_256]: (v1_relat_1(C_254) | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 52.52/39.42  tff(c_2241, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_2224])).
% 52.52/39.42  tff(c_74, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_167])).
% 52.52/39.42  tff(c_97, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_74])).
% 52.52/39.42  tff(c_80, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 52.52/39.42  tff(c_207670, plain, (![A_2597, B_2598, C_2599]: (k1_relset_1(A_2597, B_2598, C_2599)=k1_relat_1(C_2599) | ~m1_subset_1(C_2599, k1_zfmisc_1(k2_zfmisc_1(A_2597, B_2598))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 52.52/39.42  tff(c_207693, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_207670])).
% 52.52/39.42  tff(c_209398, plain, (![B_2728, A_2729, C_2730]: (k1_xboole_0=B_2728 | k1_relset_1(A_2729, B_2728, C_2730)=A_2729 | ~v1_funct_2(C_2730, A_2729, B_2728) | ~m1_subset_1(C_2730, k1_zfmisc_1(k2_zfmisc_1(A_2729, B_2728))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 52.52/39.42  tff(c_209411, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_78, c_209398])).
% 52.52/39.42  tff(c_209428, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_207693, c_209411])).
% 52.52/39.42  tff(c_209429, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_97, c_209428])).
% 52.52/39.42  tff(c_34, plain, (![B_21, A_20]: (k1_relat_1(k7_relat_1(B_21, A_20))=A_20 | ~r1_tarski(A_20, k1_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_81])).
% 52.52/39.42  tff(c_209446, plain, (![A_20]: (k1_relat_1(k7_relat_1('#skF_4', A_20))=A_20 | ~r1_tarski(A_20, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_209429, c_34])).
% 52.52/39.42  tff(c_209459, plain, (![A_20]: (k1_relat_1(k7_relat_1('#skF_4', A_20))=A_20 | ~r1_tarski(A_20, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2241, c_209446])).
% 52.52/39.42  tff(c_82, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 52.52/39.42  tff(c_209281, plain, (![A_2721, B_2722, C_2723, D_2724]: (k2_partfun1(A_2721, B_2722, C_2723, D_2724)=k7_relat_1(C_2723, D_2724) | ~m1_subset_1(C_2723, k1_zfmisc_1(k2_zfmisc_1(A_2721, B_2722))) | ~v1_funct_1(C_2723))), inference(cnfTransformation, [status(thm)], [f_135])).
% 52.52/39.42  tff(c_209290, plain, (![D_2724]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_2724)=k7_relat_1('#skF_4', D_2724) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_78, c_209281])).
% 52.52/39.42  tff(c_209305, plain, (![D_2724]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_2724)=k7_relat_1('#skF_4', D_2724))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_209290])).
% 52.52/39.42  tff(c_9674, plain, (![A_683, B_684, C_685, D_686]: (k2_partfun1(A_683, B_684, C_685, D_686)=k7_relat_1(C_685, D_686) | ~m1_subset_1(C_685, k1_zfmisc_1(k2_zfmisc_1(A_683, B_684))) | ~v1_funct_1(C_685))), inference(cnfTransformation, [status(thm)], [f_135])).
% 52.52/39.42  tff(c_9681, plain, (![D_686]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_686)=k7_relat_1('#skF_4', D_686) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_78, c_9674])).
% 52.52/39.42  tff(c_9693, plain, (![D_686]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_686)=k7_relat_1('#skF_4', D_686))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_9681])).
% 52.52/39.42  tff(c_10126, plain, (![A_702, B_703, C_704, D_705]: (m1_subset_1(k2_partfun1(A_702, B_703, C_704, D_705), k1_zfmisc_1(k2_zfmisc_1(A_702, B_703))) | ~m1_subset_1(C_704, k1_zfmisc_1(k2_zfmisc_1(A_702, B_703))) | ~v1_funct_1(C_704))), inference(cnfTransformation, [status(thm)], [f_129])).
% 52.52/39.42  tff(c_10156, plain, (![D_686]: (m1_subset_1(k7_relat_1('#skF_4', D_686), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_9693, c_10126])).
% 52.52/39.42  tff(c_10236, plain, (![D_711]: (m1_subset_1(k7_relat_1('#skF_4', D_711), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_10156])).
% 52.52/39.42  tff(c_40, plain, (![C_27, A_25, B_26]: (v1_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 52.52/39.42  tff(c_10286, plain, (![D_711]: (v1_relat_1(k7_relat_1('#skF_4', D_711)))), inference(resolution, [status(thm)], [c_10236, c_40])).
% 52.52/39.42  tff(c_38, plain, (![B_24, A_23]: (r1_tarski(k2_relat_1(k7_relat_1(B_24, A_23)), k2_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_89])).
% 52.52/39.42  tff(c_2503, plain, (![B_294, A_295]: (v5_relat_1(B_294, A_295) | ~r1_tarski(k2_relat_1(B_294), A_295) | ~v1_relat_1(B_294))), inference(cnfTransformation, [status(thm)], [f_66])).
% 52.52/39.42  tff(c_2519, plain, (![B_24, A_23]: (v5_relat_1(k7_relat_1(B_24, A_23), k2_relat_1(B_24)) | ~v1_relat_1(k7_relat_1(B_24, A_23)) | ~v1_relat_1(B_24))), inference(resolution, [status(thm)], [c_38, c_2503])).
% 52.52/39.42  tff(c_2523, plain, (![C_297, B_298, A_299]: (v5_relat_1(C_297, B_298) | ~m1_subset_1(C_297, k1_zfmisc_1(k2_zfmisc_1(A_299, B_298))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 52.52/39.42  tff(c_2542, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_78, c_2523])).
% 52.52/39.42  tff(c_26, plain, (![B_16, A_15]: (r1_tarski(k2_relat_1(B_16), A_15) | ~v5_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 52.52/39.42  tff(c_2588, plain, (![B_308, A_309]: (r1_tarski(k2_relat_1(B_308), A_309) | ~v5_relat_1(B_308, A_309) | ~v1_relat_1(B_308))), inference(cnfTransformation, [status(thm)], [f_66])).
% 52.52/39.42  tff(c_4, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 52.52/39.42  tff(c_3796, plain, (![A_422, A_423, B_424]: (r1_tarski(A_422, A_423) | ~r1_tarski(A_422, k2_relat_1(B_424)) | ~v5_relat_1(B_424, A_423) | ~v1_relat_1(B_424))), inference(resolution, [status(thm)], [c_2588, c_4])).
% 52.52/39.42  tff(c_26917, plain, (![B_1245, A_1246, B_1247]: (r1_tarski(k2_relat_1(B_1245), A_1246) | ~v5_relat_1(B_1247, A_1246) | ~v1_relat_1(B_1247) | ~v5_relat_1(B_1245, k2_relat_1(B_1247)) | ~v1_relat_1(B_1245))), inference(resolution, [status(thm)], [c_26, c_3796])).
% 52.52/39.42  tff(c_26987, plain, (![B_1245]: (r1_tarski(k2_relat_1(B_1245), '#skF_2') | ~v1_relat_1('#skF_4') | ~v5_relat_1(B_1245, k2_relat_1('#skF_4')) | ~v1_relat_1(B_1245))), inference(resolution, [status(thm)], [c_2542, c_26917])).
% 52.52/39.42  tff(c_27062, plain, (![B_1248]: (r1_tarski(k2_relat_1(B_1248), '#skF_2') | ~v5_relat_1(B_1248, k2_relat_1('#skF_4')) | ~v1_relat_1(B_1248))), inference(demodulation, [status(thm), theory('equality')], [c_2241, c_26987])).
% 52.52/39.42  tff(c_27122, plain, (![A_23]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_23)), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', A_23)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2519, c_27062])).
% 52.52/39.42  tff(c_27174, plain, (![A_23]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_23)), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2241, c_10286, c_27122])).
% 52.52/39.42  tff(c_4539, plain, (![A_460, B_461, C_462, D_463]: (v1_funct_1(k2_partfun1(A_460, B_461, C_462, D_463)) | ~m1_subset_1(C_462, k1_zfmisc_1(k2_zfmisc_1(A_460, B_461))) | ~v1_funct_1(C_462))), inference(cnfTransformation, [status(thm)], [f_129])).
% 52.52/39.42  tff(c_4544, plain, (![D_463]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_463)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_78, c_4539])).
% 52.52/39.42  tff(c_4555, plain, (![D_463]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_463)))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_4544])).
% 52.52/39.42  tff(c_9718, plain, (![D_463]: (v1_funct_1(k7_relat_1('#skF_4', D_463)))), inference(demodulation, [status(thm), theory('equality')], [c_9693, c_4555])).
% 52.52/39.42  tff(c_3088, plain, (![A_354, B_355, C_356]: (k1_relset_1(A_354, B_355, C_356)=k1_relat_1(C_356) | ~m1_subset_1(C_356, k1_zfmisc_1(k2_zfmisc_1(A_354, B_355))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 52.52/39.42  tff(c_3107, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_3088])).
% 52.52/39.42  tff(c_9771, plain, (![B_693, A_694, C_695]: (k1_xboole_0=B_693 | k1_relset_1(A_694, B_693, C_695)=A_694 | ~v1_funct_2(C_695, A_694, B_693) | ~m1_subset_1(C_695, k1_zfmisc_1(k2_zfmisc_1(A_694, B_693))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 52.52/39.42  tff(c_9781, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_78, c_9771])).
% 52.52/39.42  tff(c_9796, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_3107, c_9781])).
% 52.52/39.42  tff(c_9797, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_97, c_9796])).
% 52.52/39.42  tff(c_9814, plain, (![A_20]: (k1_relat_1(k7_relat_1('#skF_4', A_20))=A_20 | ~r1_tarski(A_20, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_9797, c_34])).
% 52.52/39.42  tff(c_9827, plain, (![A_20]: (k1_relat_1(k7_relat_1('#skF_4', A_20))=A_20 | ~r1_tarski(A_20, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2241, c_9814])).
% 52.52/39.42  tff(c_9500, plain, (![B_671, A_672]: (m1_subset_1(B_671, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_671), A_672))) | ~r1_tarski(k2_relat_1(B_671), A_672) | ~v1_funct_1(B_671) | ~v1_relat_1(B_671))), inference(cnfTransformation, [status(thm)], [f_147])).
% 52.52/39.42  tff(c_18, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 52.52/39.42  tff(c_10770, plain, (![B_734, A_735]: (r1_tarski(B_734, k2_zfmisc_1(k1_relat_1(B_734), A_735)) | ~r1_tarski(k2_relat_1(B_734), A_735) | ~v1_funct_1(B_734) | ~v1_relat_1(B_734))), inference(resolution, [status(thm)], [c_9500, c_18])).
% 52.52/39.42  tff(c_10811, plain, (![A_20, A_735]: (r1_tarski(k7_relat_1('#skF_4', A_20), k2_zfmisc_1(A_20, A_735)) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_20)), A_735) | ~v1_funct_1(k7_relat_1('#skF_4', A_20)) | ~v1_relat_1(k7_relat_1('#skF_4', A_20)) | ~r1_tarski(A_20, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_9827, c_10770])).
% 52.52/39.42  tff(c_206448, plain, (![A_2527, A_2528]: (r1_tarski(k7_relat_1('#skF_4', A_2527), k2_zfmisc_1(A_2527, A_2528)) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_2527)), A_2528) | ~r1_tarski(A_2527, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10286, c_9718, c_10811])).
% 52.52/39.42  tff(c_206885, plain, (![A_2529]: (r1_tarski(k7_relat_1('#skF_4', A_2529), k2_zfmisc_1(A_2529, '#skF_2')) | ~r1_tarski(A_2529, '#skF_1'))), inference(resolution, [status(thm)], [c_27174, c_206448])).
% 52.52/39.42  tff(c_20, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 52.52/39.42  tff(c_2201, plain, (![A_250, B_251, C_252, D_253]: (v1_funct_1(k2_partfun1(A_250, B_251, C_252, D_253)) | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(A_250, B_251))) | ~v1_funct_1(C_252))), inference(cnfTransformation, [status(thm)], [f_129])).
% 52.52/39.42  tff(c_2206, plain, (![D_253]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_253)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_78, c_2201])).
% 52.52/39.42  tff(c_2217, plain, (![D_253]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_253)))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2206])).
% 52.52/39.42  tff(c_72, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 52.52/39.42  tff(c_203, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_72])).
% 52.52/39.42  tff(c_2221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2217, c_203])).
% 52.52/39.42  tff(c_2222, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_72])).
% 52.52/39.42  tff(c_2443, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2222])).
% 52.52/39.42  tff(c_2548, plain, (~r1_tarski(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_2443])).
% 52.52/39.42  tff(c_9719, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_9693, c_2548])).
% 52.52/39.42  tff(c_206916, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_206885, c_9719])).
% 52.52/39.42  tff(c_207018, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_206916])).
% 52.52/39.42  tff(c_207020, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_2222])).
% 52.52/39.42  tff(c_207691, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_207020, c_207670])).
% 52.52/39.42  tff(c_209311, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_209305, c_209305, c_207691])).
% 52.52/39.42  tff(c_207019, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_2222])).
% 52.52/39.42  tff(c_209318, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_209305, c_207019])).
% 52.52/39.42  tff(c_209317, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_209305, c_207020])).
% 52.52/39.42  tff(c_209577, plain, (![B_2731, C_2732, A_2733]: (k1_xboole_0=B_2731 | v1_funct_2(C_2732, A_2733, B_2731) | k1_relset_1(A_2733, B_2731, C_2732)!=A_2733 | ~m1_subset_1(C_2732, k1_zfmisc_1(k2_zfmisc_1(A_2733, B_2731))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 52.52/39.42  tff(c_209580, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_209317, c_209577])).
% 52.52/39.42  tff(c_209603, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_209318, c_97, c_209580])).
% 52.52/39.42  tff(c_210071, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_209311, c_209603])).
% 52.52/39.42  tff(c_210078, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_209459, c_210071])).
% 52.52/39.42  tff(c_210082, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_210078])).
% 52.52/39.42  tff(c_210083, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_74])).
% 52.52/39.42  tff(c_14, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 52.52/39.42  tff(c_210108, plain, (![B_8]: (k2_zfmisc_1('#skF_1', B_8)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_210083, c_210083, c_14])).
% 52.52/39.42  tff(c_210084, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_74])).
% 52.52/39.42  tff(c_210093, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_210083, c_210084])).
% 52.52/39.42  tff(c_210136, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_210108, c_210093, c_78])).
% 52.52/39.42  tff(c_12, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 52.52/39.42  tff(c_210118, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_210083, c_210083, c_12])).
% 52.52/39.42  tff(c_215673, plain, (![C_3209, A_3210, B_3211]: (v1_relat_1(C_3209) | ~m1_subset_1(C_3209, k1_zfmisc_1(k2_zfmisc_1(A_3210, B_3211))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 52.52/39.42  tff(c_215689, plain, (![C_3212]: (v1_relat_1(C_3212) | ~m1_subset_1(C_3212, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_210118, c_215673])).
% 52.52/39.42  tff(c_215706, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_210136, c_215689])).
% 52.52/39.42  tff(c_215655, plain, (![A_3207, B_3208]: (r1_tarski(A_3207, B_3208) | ~m1_subset_1(A_3207, k1_zfmisc_1(B_3208)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 52.52/39.42  tff(c_215666, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_210136, c_215655])).
% 52.52/39.42  tff(c_6, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 52.52/39.42  tff(c_210087, plain, (![A_4]: (r1_tarski('#skF_1', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_210083, c_6])).
% 52.52/39.42  tff(c_215810, plain, (![A_3235, C_3236, B_3237]: (r1_tarski(A_3235, C_3236) | ~r1_tarski(B_3237, C_3236) | ~r1_tarski(A_3235, B_3237))), inference(cnfTransformation, [status(thm)], [f_32])).
% 52.52/39.42  tff(c_215823, plain, (![A_3238, A_3239]: (r1_tarski(A_3238, A_3239) | ~r1_tarski(A_3238, '#skF_1'))), inference(resolution, [status(thm)], [c_210087, c_215810])).
% 52.52/39.42  tff(c_215834, plain, (![A_3239]: (r1_tarski('#skF_4', A_3239))), inference(resolution, [status(thm)], [c_215666, c_215823])).
% 52.52/39.42  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 52.52/39.42  tff(c_210086, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_210083, c_210083, c_32])).
% 52.52/39.42  tff(c_212306, plain, (![A_2948]: (k7_relat_1(A_2948, k1_relat_1(A_2948))=A_2948 | ~v1_relat_1(A_2948))), inference(cnfTransformation, [status(thm)], [f_85])).
% 52.52/39.42  tff(c_212315, plain, (k7_relat_1('#skF_1', '#skF_1')='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_210086, c_212306])).
% 52.52/39.42  tff(c_215598, plain, (~v1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_212315])).
% 52.52/39.42  tff(c_16, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 52.52/39.42  tff(c_210116, plain, (![A_9]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_210083, c_16])).
% 52.52/39.42  tff(c_215630, plain, (![C_3202, A_3203, B_3204]: (v1_relat_1(C_3202) | ~m1_subset_1(C_3202, k1_zfmisc_1(k2_zfmisc_1(A_3203, B_3204))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 52.52/39.42  tff(c_215640, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_210116, c_215630])).
% 52.52/39.42  tff(c_215647, plain, $false, inference(negUnitSimplification, [status(thm)], [c_215598, c_215640])).
% 52.52/39.42  tff(c_215649, plain, (v1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_212315])).
% 52.52/39.42  tff(c_215648, plain, (k7_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_212315])).
% 52.52/39.42  tff(c_217384, plain, (![C_3352, A_3353, B_3354]: (k7_relat_1(k7_relat_1(C_3352, A_3353), B_3354)=k7_relat_1(C_3352, A_3353) | ~r1_tarski(A_3353, B_3354) | ~v1_relat_1(C_3352))), inference(cnfTransformation, [status(thm)], [f_72])).
% 52.52/39.42  tff(c_217425, plain, (![B_3354]: (k7_relat_1('#skF_1', B_3354)=k7_relat_1('#skF_1', '#skF_1') | ~r1_tarski('#skF_1', B_3354) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_215648, c_217384])).
% 52.52/39.42  tff(c_217457, plain, (![B_3355]: (k7_relat_1('#skF_1', B_3355)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_215649, c_210087, c_215648, c_217425])).
% 52.52/39.42  tff(c_216510, plain, (![B_3298, A_3299]: (k1_relat_1(k7_relat_1(B_3298, A_3299))=A_3299 | ~r1_tarski(A_3299, k1_relat_1(B_3298)) | ~v1_relat_1(B_3298))), inference(cnfTransformation, [status(thm)], [f_81])).
% 52.52/39.42  tff(c_216547, plain, (![B_3298]: (k1_relat_1(k7_relat_1(B_3298, '#skF_4'))='#skF_4' | ~v1_relat_1(B_3298))), inference(resolution, [status(thm)], [c_215834, c_216510])).
% 52.52/39.42  tff(c_217470, plain, (k1_relat_1('#skF_1')='#skF_4' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_217457, c_216547])).
% 52.52/39.42  tff(c_217498, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_215649, c_210086, c_217470])).
% 52.52/39.42  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 52.52/39.42  tff(c_210085, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_210083, c_210083, c_30])).
% 52.52/39.42  tff(c_217556, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_217498, c_217498, c_210085])).
% 52.52/39.42  tff(c_217557, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_217498, c_217498, c_210086])).
% 52.52/39.42  tff(c_217676, plain, (![B_3356, A_3357]: (v1_funct_2(B_3356, k1_relat_1(B_3356), A_3357) | ~r1_tarski(k2_relat_1(B_3356), A_3357) | ~v1_funct_1(B_3356) | ~v1_relat_1(B_3356))), inference(cnfTransformation, [status(thm)], [f_147])).
% 52.52/39.42  tff(c_217679, plain, (![A_3357]: (v1_funct_2('#skF_4', '#skF_4', A_3357) | ~r1_tarski(k2_relat_1('#skF_4'), A_3357) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_217557, c_217676])).
% 52.52/39.42  tff(c_217684, plain, (![A_3357]: (v1_funct_2('#skF_4', '#skF_4', A_3357))), inference(demodulation, [status(thm), theory('equality')], [c_215706, c_82, c_215834, c_217556, c_217679])).
% 52.52/39.42  tff(c_217439, plain, (![B_3354]: (k7_relat_1('#skF_1', B_3354)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_215649, c_210087, c_215648, c_217425])).
% 52.52/39.42  tff(c_217512, plain, (![B_3354]: (k7_relat_1('#skF_4', B_3354)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_217498, c_217498, c_217439])).
% 52.52/39.42  tff(c_217554, plain, (![A_9]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_217498, c_210116])).
% 52.52/39.42  tff(c_217982, plain, (![A_3388, B_3389, C_3390, D_3391]: (k2_partfun1(A_3388, B_3389, C_3390, D_3391)=k7_relat_1(C_3390, D_3391) | ~m1_subset_1(C_3390, k1_zfmisc_1(k2_zfmisc_1(A_3388, B_3389))) | ~v1_funct_1(C_3390))), inference(cnfTransformation, [status(thm)], [f_135])).
% 52.52/39.42  tff(c_217989, plain, (![A_3388, B_3389, D_3391]: (k2_partfun1(A_3388, B_3389, '#skF_4', D_3391)=k7_relat_1('#skF_4', D_3391) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_217554, c_217982])).
% 52.52/39.42  tff(c_217998, plain, (![A_3388, B_3389, D_3391]: (k2_partfun1(A_3388, B_3389, '#skF_4', D_3391)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_217512, c_217989])).
% 52.52/39.42  tff(c_215837, plain, (![A_3239]: (r1_tarski('#skF_3', A_3239))), inference(resolution, [status(thm)], [c_76, c_215823])).
% 52.52/39.42  tff(c_216545, plain, (![B_3298]: (k1_relat_1(k7_relat_1(B_3298, '#skF_3'))='#skF_3' | ~v1_relat_1(B_3298))), inference(resolution, [status(thm)], [c_215837, c_216510])).
% 52.52/39.42  tff(c_217474, plain, (k1_relat_1('#skF_1')='#skF_3' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_217457, c_216545])).
% 52.52/39.42  tff(c_217500, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_215649, c_210086, c_217474])).
% 52.52/39.42  tff(c_217571, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_217498, c_217500])).
% 52.52/39.42  tff(c_212371, plain, (![A_2958, B_2959]: (r1_tarski(A_2958, B_2959) | ~m1_subset_1(A_2958, k1_zfmisc_1(B_2959)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 52.52/39.42  tff(c_212378, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_210136, c_212371])).
% 52.52/39.42  tff(c_212567, plain, (![A_2991, C_2992, B_2993]: (r1_tarski(A_2991, C_2992) | ~r1_tarski(B_2993, C_2992) | ~r1_tarski(A_2991, B_2993))), inference(cnfTransformation, [status(thm)], [f_32])).
% 52.52/39.42  tff(c_212583, plain, (![A_2994, A_2995]: (r1_tarski(A_2994, A_2995) | ~r1_tarski(A_2994, '#skF_1'))), inference(resolution, [status(thm)], [c_210087, c_212567])).
% 52.52/39.42  tff(c_212594, plain, (![A_2995]: (r1_tarski('#skF_4', A_2995))), inference(resolution, [status(thm)], [c_212378, c_212583])).
% 52.52/39.42  tff(c_212390, plain, (![C_2962, A_2963, B_2964]: (v1_relat_1(C_2962) | ~m1_subset_1(C_2962, k1_zfmisc_1(k2_zfmisc_1(A_2963, B_2964))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 52.52/39.42  tff(c_212418, plain, (![C_2967]: (v1_relat_1(C_2967) | ~m1_subset_1(C_2967, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_210118, c_212390])).
% 52.52/39.42  tff(c_212431, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_210136, c_212418])).
% 52.52/39.42  tff(c_213776, plain, (![A_3089, B_3090, C_3091]: (k1_relset_1(A_3089, B_3090, C_3091)=k1_relat_1(C_3091) | ~m1_subset_1(C_3091, k1_zfmisc_1(k2_zfmisc_1(A_3089, B_3090))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 52.52/39.42  tff(c_213864, plain, (![A_3099, C_3100]: (k1_relset_1(A_3099, '#skF_1', C_3100)=k1_relat_1(C_3100) | ~m1_subset_1(C_3100, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_210118, c_213776])).
% 52.52/39.42  tff(c_213874, plain, (![A_3099]: (k1_relset_1(A_3099, '#skF_1', '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_210136, c_213864])).
% 52.52/39.42  tff(c_210098, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_210093, c_80])).
% 52.52/39.42  tff(c_56, plain, (![B_35, C_36]: (k1_relset_1(k1_xboole_0, B_35, C_36)=k1_xboole_0 | ~v1_funct_2(C_36, k1_xboole_0, B_35) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_35))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 52.52/39.42  tff(c_85, plain, (![B_35, C_36]: (k1_relset_1(k1_xboole_0, B_35, C_36)=k1_xboole_0 | ~v1_funct_2(C_36, k1_xboole_0, B_35) | ~m1_subset_1(C_36, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_56])).
% 52.52/39.42  tff(c_214634, plain, (![B_3139, C_3140]: (k1_relset_1('#skF_1', B_3139, C_3140)='#skF_1' | ~v1_funct_2(C_3140, '#skF_1', B_3139) | ~m1_subset_1(C_3140, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_210083, c_210083, c_210083, c_210083, c_85])).
% 52.52/39.42  tff(c_214641, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')='#skF_1' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_210098, c_214634])).
% 52.52/39.42  tff(c_214651, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_210136, c_213874, c_214641])).
% 52.52/39.42  tff(c_36, plain, (![A_22]: (k7_relat_1(A_22, k1_relat_1(A_22))=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_85])).
% 52.52/39.42  tff(c_214663, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_214651, c_36])).
% 52.52/39.42  tff(c_214671, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_212431, c_214663])).
% 52.52/39.42  tff(c_214834, plain, (![C_3146, A_3147, B_3148]: (k7_relat_1(k7_relat_1(C_3146, A_3147), B_3148)=k7_relat_1(C_3146, A_3147) | ~r1_tarski(A_3147, B_3148) | ~v1_relat_1(C_3146))), inference(cnfTransformation, [status(thm)], [f_72])).
% 52.52/39.42  tff(c_214880, plain, (![B_3148]: (k7_relat_1('#skF_4', B_3148)=k7_relat_1('#skF_4', '#skF_1') | ~r1_tarski('#skF_1', B_3148) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_214671, c_214834])).
% 52.52/39.42  tff(c_214897, plain, (![B_3148]: (k7_relat_1('#skF_4', B_3148)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_212431, c_210087, c_214671, c_214880])).
% 52.52/39.42  tff(c_212319, plain, (~v1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_212315])).
% 52.52/39.42  tff(c_212347, plain, (![C_2955, A_2956, B_2957]: (v1_relat_1(C_2955) | ~m1_subset_1(C_2955, k1_zfmisc_1(k2_zfmisc_1(A_2956, B_2957))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 52.52/39.42  tff(c_212357, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_210116, c_212347])).
% 52.52/39.42  tff(c_212364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_212319, c_212357])).
% 52.52/39.42  tff(c_212366, plain, (v1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_212315])).
% 52.52/39.42  tff(c_212365, plain, (k7_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_212315])).
% 52.52/39.42  tff(c_214883, plain, (![B_3148]: (k7_relat_1('#skF_1', B_3148)=k7_relat_1('#skF_1', '#skF_1') | ~r1_tarski('#skF_1', B_3148) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_212365, c_214834])).
% 52.52/39.42  tff(c_214919, plain, (![B_3149]: (k7_relat_1('#skF_1', B_3149)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_212366, c_210087, c_212365, c_214883])).
% 52.52/39.42  tff(c_213216, plain, (![B_3052, A_3053]: (k1_relat_1(k7_relat_1(B_3052, A_3053))=A_3053 | ~r1_tarski(A_3053, k1_relat_1(B_3052)) | ~v1_relat_1(B_3052))), inference(cnfTransformation, [status(thm)], [f_81])).
% 52.52/39.42  tff(c_213253, plain, (![B_3052]: (k1_relat_1(k7_relat_1(B_3052, '#skF_4'))='#skF_4' | ~v1_relat_1(B_3052))), inference(resolution, [status(thm)], [c_212594, c_213216])).
% 52.52/39.42  tff(c_214936, plain, (k1_relat_1('#skF_1')='#skF_4' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_214919, c_213253])).
% 52.52/39.42  tff(c_214966, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_212366, c_210086, c_214936])).
% 52.52/39.42  tff(c_215025, plain, (![A_9]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_214966, c_210116])).
% 52.52/39.42  tff(c_215454, plain, (![A_3175, B_3176, C_3177, D_3178]: (k2_partfun1(A_3175, B_3176, C_3177, D_3178)=k7_relat_1(C_3177, D_3178) | ~m1_subset_1(C_3177, k1_zfmisc_1(k2_zfmisc_1(A_3175, B_3176))) | ~v1_funct_1(C_3177))), inference(cnfTransformation, [status(thm)], [f_135])).
% 52.52/39.42  tff(c_215461, plain, (![A_3175, B_3176, D_3178]: (k2_partfun1(A_3175, B_3176, '#skF_4', D_3178)=k7_relat_1('#skF_4', D_3178) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_215025, c_215454])).
% 52.52/39.42  tff(c_215470, plain, (![A_3175, B_3176, D_3178]: (k2_partfun1(A_3175, B_3176, '#skF_4', D_3178)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_214897, c_215461])).
% 52.52/39.42  tff(c_212597, plain, (![A_2995]: (r1_tarski('#skF_3', A_2995))), inference(resolution, [status(thm)], [c_76, c_212583])).
% 52.52/39.42  tff(c_213252, plain, (![B_3052]: (k1_relat_1(k7_relat_1(B_3052, '#skF_3'))='#skF_3' | ~v1_relat_1(B_3052))), inference(resolution, [status(thm)], [c_212597, c_213216])).
% 52.52/39.42  tff(c_214940, plain, (k1_relat_1('#skF_1')='#skF_3' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_214919, c_213252])).
% 52.52/39.42  tff(c_214968, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_212366, c_210086, c_214940])).
% 52.52/39.42  tff(c_215043, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_214966, c_214968])).
% 52.52/39.42  tff(c_212381, plain, (![A_2960, B_2961]: (m1_subset_1(A_2960, k1_zfmisc_1(B_2961)) | ~r1_tarski(A_2960, B_2961))), inference(cnfTransformation, [status(thm)], [f_54])).
% 52.52/39.42  tff(c_210159, plain, (![A_2763]: (k7_relat_1(A_2763, k1_relat_1(A_2763))=A_2763 | ~v1_relat_1(A_2763))), inference(cnfTransformation, [status(thm)], [f_85])).
% 52.52/39.42  tff(c_210168, plain, (k7_relat_1('#skF_1', '#skF_1')='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_210086, c_210159])).
% 52.52/39.42  tff(c_210171, plain, (~v1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_210168])).
% 52.52/39.42  tff(c_210189, plain, (![C_2768, A_2769, B_2770]: (v1_relat_1(C_2768) | ~m1_subset_1(C_2768, k1_zfmisc_1(k2_zfmisc_1(A_2769, B_2770))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 52.52/39.42  tff(c_210199, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_210116, c_210189])).
% 52.52/39.42  tff(c_210206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_210171, c_210199])).
% 52.52/39.42  tff(c_210208, plain, (v1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_210168])).
% 52.52/39.42  tff(c_210207, plain, (k7_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_210168])).
% 52.52/39.42  tff(c_211754, plain, (![C_2915, A_2916, B_2917]: (k7_relat_1(k7_relat_1(C_2915, A_2916), B_2917)=k7_relat_1(C_2915, A_2916) | ~r1_tarski(A_2916, B_2917) | ~v1_relat_1(C_2915))), inference(cnfTransformation, [status(thm)], [f_72])).
% 52.52/39.42  tff(c_211788, plain, (![B_2917]: (k7_relat_1('#skF_1', B_2917)=k7_relat_1('#skF_1', '#skF_1') | ~r1_tarski('#skF_1', B_2917) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_210207, c_211754])).
% 52.52/39.42  tff(c_211818, plain, (![B_2918]: (k7_relat_1('#skF_1', B_2918)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_210208, c_210087, c_210207, c_211788])).
% 52.52/39.42  tff(c_210149, plain, (![A_2761, B_2762]: (r1_tarski(A_2761, B_2762) | ~m1_subset_1(A_2761, k1_zfmisc_1(B_2762)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 52.52/39.42  tff(c_210156, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_210136, c_210149])).
% 52.52/39.42  tff(c_210487, plain, (![A_2818, C_2819, B_2820]: (r1_tarski(A_2818, C_2819) | ~r1_tarski(B_2820, C_2819) | ~r1_tarski(A_2818, B_2820))), inference(cnfTransformation, [status(thm)], [f_32])).
% 52.52/39.42  tff(c_210516, plain, (![A_2824, A_2825]: (r1_tarski(A_2824, A_2825) | ~r1_tarski(A_2824, '#skF_1'))), inference(resolution, [status(thm)], [c_210087, c_210487])).
% 52.52/39.42  tff(c_210531, plain, (![A_2825]: (r1_tarski('#skF_4', A_2825))), inference(resolution, [status(thm)], [c_210156, c_210516])).
% 52.52/39.42  tff(c_210680, plain, (![B_2836, A_2837]: (k1_relat_1(k7_relat_1(B_2836, A_2837))=A_2837 | ~r1_tarski(A_2837, k1_relat_1(B_2836)) | ~v1_relat_1(B_2836))), inference(cnfTransformation, [status(thm)], [f_81])).
% 52.52/39.42  tff(c_210706, plain, (![B_2836]: (k1_relat_1(k7_relat_1(B_2836, '#skF_4'))='#skF_4' | ~v1_relat_1(B_2836))), inference(resolution, [status(thm)], [c_210531, c_210680])).
% 52.52/39.42  tff(c_211827, plain, (k1_relat_1('#skF_1')='#skF_4' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_211818, c_210706])).
% 52.52/39.42  tff(c_211853, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_210208, c_210086, c_211827])).
% 52.52/39.42  tff(c_211902, plain, (![A_9]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_211853, c_210116])).
% 52.52/39.42  tff(c_212179, plain, (![A_2927, B_2928, C_2929, D_2930]: (v1_funct_1(k2_partfun1(A_2927, B_2928, C_2929, D_2930)) | ~m1_subset_1(C_2929, k1_zfmisc_1(k2_zfmisc_1(A_2927, B_2928))) | ~v1_funct_1(C_2929))), inference(cnfTransformation, [status(thm)], [f_129])).
% 52.52/39.42  tff(c_212184, plain, (![A_2927, B_2928, D_2930]: (v1_funct_1(k2_partfun1(A_2927, B_2928, '#skF_4', D_2930)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_211902, c_212179])).
% 52.52/39.42  tff(c_212192, plain, (![A_2927, B_2928, D_2930]: (v1_funct_1(k2_partfun1(A_2927, B_2928, '#skF_4', D_2930)))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_212184])).
% 52.52/39.42  tff(c_210534, plain, (![A_2825]: (r1_tarski('#skF_3', A_2825))), inference(resolution, [status(thm)], [c_76, c_210516])).
% 52.52/39.42  tff(c_210705, plain, (![B_2836]: (k1_relat_1(k7_relat_1(B_2836, '#skF_3'))='#skF_3' | ~v1_relat_1(B_2836))), inference(resolution, [status(thm)], [c_210534, c_210680])).
% 52.52/39.42  tff(c_211831, plain, (k1_relat_1('#skF_1')='#skF_3' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_211818, c_210705])).
% 52.52/39.42  tff(c_211855, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_210208, c_210086, c_211831])).
% 52.52/39.42  tff(c_211919, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_211853, c_211855])).
% 52.52/39.42  tff(c_210137, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_210093, c_210093, c_210093, c_210118, c_210093, c_210093, c_72])).
% 52.52/39.42  tff(c_210138, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_210137])).
% 52.52/39.42  tff(c_211897, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_211853, c_211853, c_210138])).
% 52.52/39.42  tff(c_212289, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_211919, c_211897])).
% 52.52/39.42  tff(c_212293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_212192, c_212289])).
% 52.52/39.42  tff(c_212294, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_210137])).
% 52.52/39.42  tff(c_212318, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_212294])).
% 52.52/39.42  tff(c_212389, plain, (~r1_tarski(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_212381, c_212318])).
% 52.52/39.42  tff(c_215017, plain, (~r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_214966, c_214966, c_214966, c_212389])).
% 52.52/39.42  tff(c_215595, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_212594, c_215470, c_215043, c_215017])).
% 52.52/39.42  tff(c_215596, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_212294])).
% 52.52/39.42  tff(c_217546, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_3'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_217498, c_217498, c_217498, c_215596])).
% 52.52/39.42  tff(c_218142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_217684, c_217998, c_217571, c_217571, c_217546])).
% 52.52/39.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 52.52/39.42  
% 52.52/39.42  Inference rules
% 52.52/39.42  ----------------------
% 52.52/39.42  #Ref     : 0
% 52.52/39.42  #Sup     : 47507
% 52.52/39.42  #Fact    : 0
% 52.52/39.42  #Define  : 0
% 52.52/39.42  #Split   : 80
% 52.52/39.42  #Chain   : 0
% 52.52/39.42  #Close   : 0
% 52.52/39.42  
% 52.52/39.42  Ordering : KBO
% 52.52/39.42  
% 52.52/39.42  Simplification rules
% 52.52/39.42  ----------------------
% 52.52/39.42  #Subsume      : 17705
% 52.52/39.42  #Demod        : 87022
% 52.52/39.42  #Tautology    : 13707
% 52.52/39.42  #SimpNegUnit  : 625
% 52.52/39.42  #BackRed      : 447
% 52.52/39.42  
% 52.52/39.42  #Partial instantiations: 0
% 52.52/39.42  #Strategies tried      : 1
% 52.52/39.42  
% 52.52/39.42  Timing (in seconds)
% 52.52/39.42  ----------------------
% 52.77/39.42  Preprocessing        : 0.37
% 52.77/39.42  Parsing              : 0.19
% 52.77/39.42  CNF conversion       : 0.03
% 52.77/39.42  Main loop            : 38.22
% 52.77/39.42  Inferencing          : 5.31
% 52.77/39.42  Reduction            : 15.03
% 52.77/39.42  Demodulation         : 12.00
% 52.77/39.42  BG Simplification    : 0.51
% 52.77/39.42  Subsumption          : 15.19
% 52.77/39.42  Abstraction          : 1.01
% 52.77/39.42  MUC search           : 0.00
% 52.77/39.42  Cooper               : 0.00
% 52.77/39.42  Total                : 38.68
% 52.77/39.42  Index Insertion      : 0.00
% 52.77/39.42  Index Deletion       : 0.00
% 52.77/39.42  Index Matching       : 0.00
% 52.77/39.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
