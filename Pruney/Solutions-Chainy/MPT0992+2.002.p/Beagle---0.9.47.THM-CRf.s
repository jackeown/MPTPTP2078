%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:31 EST 2020

% Result     : Theorem 9.50s
% Output     : CNFRefutation 9.74s
% Verified   : 
% Statistics : Number of formulae       :  197 (2412 expanded)
%              Number of leaves         :   38 ( 758 expanded)
%              Depth                    :   15
%              Number of atoms          :  331 (7292 expanded)
%              Number of equality atoms :   92 (2746 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_144,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_98,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_124,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_70,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_133,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_146,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_133])).

tff(c_68,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_113,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_8036,plain,(
    ! [A_728,B_729,C_730] :
      ( k1_relset_1(A_728,B_729,C_730) = k1_relat_1(C_730)
      | ~ m1_subset_1(C_730,k1_zfmisc_1(k2_zfmisc_1(A_728,B_729))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8055,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_8036])).

tff(c_8890,plain,(
    ! [B_834,A_835,C_836] :
      ( k1_xboole_0 = B_834
      | k1_relset_1(A_835,B_834,C_836) = A_835
      | ~ v1_funct_2(C_836,A_835,B_834)
      | ~ m1_subset_1(C_836,k1_zfmisc_1(k2_zfmisc_1(A_835,B_834))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_8903,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_8890])).

tff(c_8917,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_8055,c_8903])).

tff(c_8918,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_8917])).

tff(c_30,plain,(
    ! [B_14,A_13] :
      ( k1_relat_1(k7_relat_1(B_14,A_13)) = A_13
      | ~ r1_tarski(A_13,k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8936,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8918,c_30])).

tff(c_8998,plain,(
    ! [A_839] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_839)) = A_839
      | ~ r1_tarski(A_839,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_8936])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_8717,plain,(
    ! [A_822,B_823,C_824,D_825] :
      ( k2_partfun1(A_822,B_823,C_824,D_825) = k7_relat_1(C_824,D_825)
      | ~ m1_subset_1(C_824,k1_zfmisc_1(k2_zfmisc_1(A_822,B_823)))
      | ~ v1_funct_1(C_824) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_8726,plain,(
    ! [D_825] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_825) = k7_relat_1('#skF_4',D_825)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_8717])).

tff(c_8738,plain,(
    ! [D_825] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_825) = k7_relat_1('#skF_4',D_825) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_8726])).

tff(c_1864,plain,(
    ! [A_281,B_282,C_283,D_284] :
      ( k2_partfun1(A_281,B_282,C_283,D_284) = k7_relat_1(C_283,D_284)
      | ~ m1_subset_1(C_283,k1_zfmisc_1(k2_zfmisc_1(A_281,B_282)))
      | ~ v1_funct_1(C_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1871,plain,(
    ! [D_284] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_284) = k7_relat_1('#skF_4',D_284)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_1864])).

tff(c_1880,plain,(
    ! [D_284] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_284) = k7_relat_1('#skF_4',D_284) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1871])).

tff(c_2063,plain,(
    ! [A_299,B_300,C_301,D_302] :
      ( m1_subset_1(k2_partfun1(A_299,B_300,C_301,D_302),k1_zfmisc_1(k2_zfmisc_1(A_299,B_300)))
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(A_299,B_300)))
      | ~ v1_funct_1(C_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2091,plain,(
    ! [D_284] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_284),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1880,c_2063])).

tff(c_2116,plain,(
    ! [D_304] : m1_subset_1(k7_relat_1('#skF_4',D_304),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_2091])).

tff(c_34,plain,(
    ! [C_18,A_16,B_17] :
      ( v1_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2157,plain,(
    ! [D_304] : v1_relat_1(k7_relat_1('#skF_4',D_304)) ),
    inference(resolution,[status(thm)],[c_2116,c_34])).

tff(c_36,plain,(
    ! [C_21,B_20,A_19] :
      ( v5_relat_1(C_21,B_20)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2156,plain,(
    ! [D_304] : v5_relat_1(k7_relat_1('#skF_4',D_304),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2116,c_36])).

tff(c_24,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1505,plain,(
    ! [A_232,B_233,C_234,D_235] :
      ( v1_funct_1(k2_partfun1(A_232,B_233,C_234,D_235))
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233)))
      | ~ v1_funct_1(C_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1510,plain,(
    ! [D_235] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_235))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_1505])).

tff(c_1518,plain,(
    ! [D_235] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_235)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1510])).

tff(c_1881,plain,(
    ! [D_235] : v1_funct_1(k7_relat_1('#skF_4',D_235)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1880,c_1518])).

tff(c_1315,plain,(
    ! [A_210,B_211,C_212] :
      ( k1_relset_1(A_210,B_211,C_212) = k1_relat_1(C_212)
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(A_210,B_211))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1330,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_1315])).

tff(c_1966,plain,(
    ! [B_295,A_296,C_297] :
      ( k1_xboole_0 = B_295
      | k1_relset_1(A_296,B_295,C_297) = A_296
      | ~ v1_funct_2(C_297,A_296,B_295)
      | ~ m1_subset_1(C_297,k1_zfmisc_1(k2_zfmisc_1(A_296,B_295))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1976,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_1966])).

tff(c_1987,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1330,c_1976])).

tff(c_1988,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_1987])).

tff(c_2006,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1988,c_30])).

tff(c_2186,plain,(
    ! [A_310] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_310)) = A_310
      | ~ r1_tarski(A_310,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_2006])).

tff(c_60,plain,(
    ! [B_37,A_36] :
      ( m1_subset_1(B_37,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_37),A_36)))
      | ~ r1_tarski(k2_relat_1(B_37),A_36)
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2198,plain,(
    ! [A_310,A_36] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_310),k1_zfmisc_1(k2_zfmisc_1(A_310,A_36)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_310)),A_36)
      | ~ v1_funct_1(k7_relat_1('#skF_4',A_310))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_310))
      | ~ r1_tarski(A_310,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2186,c_60])).

tff(c_7671,plain,(
    ! [A_693,A_694] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_693),k1_zfmisc_1(k2_zfmisc_1(A_693,A_694)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_693)),A_694)
      | ~ r1_tarski(A_693,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2157,c_1881,c_2198])).

tff(c_847,plain,(
    ! [A_146,B_147,C_148,D_149] :
      ( v1_funct_1(k2_partfun1(A_146,B_147,C_148,D_149))
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147)))
      | ~ v1_funct_1(C_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_852,plain,(
    ! [D_149] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_149))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_847])).

tff(c_860,plain,(
    ! [D_149] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_149)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_852])).

tff(c_66,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_147,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_863,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_860,c_147])).

tff(c_864,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_984,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_864])).

tff(c_1883,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1880,c_984])).

tff(c_7690,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_7671,c_1883])).

tff(c_7738,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_7690])).

tff(c_7757,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_7738])).

tff(c_7761,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2157,c_2156,c_7757])).

tff(c_7763,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_864])).

tff(c_8053,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_7763,c_8036])).

tff(c_8742,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8738,c_8738,c_8053])).

tff(c_7762,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_864])).

tff(c_8748,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8738,c_7762])).

tff(c_8747,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8738,c_7763])).

tff(c_48,plain,(
    ! [B_26,C_27,A_25] :
      ( k1_xboole_0 = B_26
      | v1_funct_2(C_27,A_25,B_26)
      | k1_relset_1(A_25,B_26,C_27) != A_25
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_8807,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_8747,c_48])).

tff(c_8829,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_8748,c_113,c_8807])).

tff(c_8845,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8742,c_8829])).

tff(c_9007,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8998,c_8845])).

tff(c_9052,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_9007])).

tff(c_9053,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9058,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9053,c_10])).

tff(c_14,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_9057,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9053,c_9053,c_14])).

tff(c_9054,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_9064,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9053,c_9054])).

tff(c_9085,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9057,c_9064,c_72])).

tff(c_9111,plain,(
    ! [A_849,B_850] :
      ( r1_tarski(A_849,B_850)
      | ~ m1_subset_1(A_849,k1_zfmisc_1(B_850)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_9119,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_9085,c_9111])).

tff(c_13040,plain,(
    ! [B_1307,A_1308] :
      ( B_1307 = A_1308
      | ~ r1_tarski(B_1307,A_1308)
      | ~ r1_tarski(A_1308,B_1307) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_13042,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_9119,c_13040])).

tff(c_13051,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9058,c_13042])).

tff(c_9065,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9064,c_74])).

tff(c_13077,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13051,c_13051,c_9065])).

tff(c_13048,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_13040])).

tff(c_13059,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9058,c_13048])).

tff(c_13069,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13051,c_13059])).

tff(c_10310,plain,(
    ! [B_1008,A_1009] :
      ( B_1008 = A_1009
      | ~ r1_tarski(B_1008,A_1009)
      | ~ r1_tarski(A_1009,B_1008) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10312,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_9119,c_10310])).

tff(c_10321,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9058,c_10312])).

tff(c_10350,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10321,c_9085])).

tff(c_16,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_9056,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9053,c_9053,c_16])).

tff(c_10347,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10321,c_10321,c_9056])).

tff(c_10514,plain,(
    ! [C_1022,B_1023,A_1024] :
      ( v5_relat_1(C_1022,B_1023)
      | ~ m1_subset_1(C_1022,k1_zfmisc_1(k2_zfmisc_1(A_1024,B_1023))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_10538,plain,(
    ! [C_1027,B_1028] :
      ( v5_relat_1(C_1027,B_1028)
      | ~ m1_subset_1(C_1027,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10347,c_10514])).

tff(c_10544,plain,(
    ! [B_1028] : v5_relat_1('#skF_4',B_1028) ),
    inference(resolution,[status(thm)],[c_10350,c_10538])).

tff(c_28,plain,(
    ! [A_12] : k7_relat_1(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_9055,plain,(
    ! [A_12] : k7_relat_1('#skF_1',A_12) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9053,c_9053,c_28])).

tff(c_10351,plain,(
    ! [A_12] : k7_relat_1('#skF_4',A_12) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10321,c_10321,c_9055])).

tff(c_10352,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10321,c_10321,c_9057])).

tff(c_11380,plain,(
    ! [A_1145,B_1146,C_1147,D_1148] :
      ( k2_partfun1(A_1145,B_1146,C_1147,D_1148) = k7_relat_1(C_1147,D_1148)
      | ~ m1_subset_1(C_1147,k1_zfmisc_1(k2_zfmisc_1(A_1145,B_1146)))
      | ~ v1_funct_1(C_1147) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_12953,plain,(
    ! [A_1295,C_1296,D_1297] :
      ( k2_partfun1(A_1295,'#skF_4',C_1296,D_1297) = k7_relat_1(C_1296,D_1297)
      | ~ m1_subset_1(C_1296,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_1296) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10352,c_11380])).

tff(c_12957,plain,(
    ! [A_1295,D_1297] :
      ( k2_partfun1(A_1295,'#skF_4','#skF_4',D_1297) = k7_relat_1('#skF_4',D_1297)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10350,c_12953])).

tff(c_12964,plain,(
    ! [A_1295,D_1297] : k2_partfun1(A_1295,'#skF_4','#skF_4',D_1297) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_10351,c_12957])).

tff(c_11793,plain,(
    ! [A_1180,B_1181,C_1182,D_1183] :
      ( m1_subset_1(k2_partfun1(A_1180,B_1181,C_1182,D_1183),k1_zfmisc_1(k2_zfmisc_1(A_1180,B_1181)))
      | ~ m1_subset_1(C_1182,k1_zfmisc_1(k2_zfmisc_1(A_1180,B_1181)))
      | ~ v1_funct_1(C_1182) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_12059,plain,(
    ! [A_1202,B_1203,C_1204,D_1205] :
      ( v1_relat_1(k2_partfun1(A_1202,B_1203,C_1204,D_1205))
      | ~ m1_subset_1(C_1204,k1_zfmisc_1(k2_zfmisc_1(A_1202,B_1203)))
      | ~ v1_funct_1(C_1204) ) ),
    inference(resolution,[status(thm)],[c_11793,c_34])).

tff(c_12074,plain,(
    ! [B_1206,C_1207,D_1208] :
      ( v1_relat_1(k2_partfun1('#skF_4',B_1206,C_1207,D_1208))
      | ~ m1_subset_1(C_1207,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_1207) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10347,c_12059])).

tff(c_12078,plain,(
    ! [B_1206,D_1208] :
      ( v1_relat_1(k2_partfun1('#skF_4',B_1206,'#skF_4',D_1208))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10350,c_12074])).

tff(c_12085,plain,(
    ! [B_1206,D_1208] : v1_relat_1(k2_partfun1('#skF_4',B_1206,'#skF_4',D_1208)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_12078])).

tff(c_11094,plain,(
    ! [A_1108,B_1109,C_1110,D_1111] :
      ( v1_funct_1(k2_partfun1(A_1108,B_1109,C_1110,D_1111))
      | ~ m1_subset_1(C_1110,k1_zfmisc_1(k2_zfmisc_1(A_1108,B_1109)))
      | ~ v1_funct_1(C_1110) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_11368,plain,(
    ! [B_1140,C_1141,D_1142] :
      ( v1_funct_1(k2_partfun1('#skF_4',B_1140,C_1141,D_1142))
      | ~ m1_subset_1(C_1141,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_1141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10347,c_11094])).

tff(c_11370,plain,(
    ! [B_1140,D_1142] :
      ( v1_funct_1(k2_partfun1('#skF_4',B_1140,'#skF_4',D_1142))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10350,c_11368])).

tff(c_11376,plain,(
    ! [B_1140,D_1142] : v1_funct_1(k2_partfun1('#skF_4',B_1140,'#skF_4',D_1142)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_11370])).

tff(c_11305,plain,(
    ! [B_1135,A_1136] :
      ( m1_subset_1(B_1135,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1135),A_1136)))
      | ~ r1_tarski(k2_relat_1(B_1135),A_1136)
      | ~ v1_funct_1(B_1135)
      | ~ v1_relat_1(B_1135) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_11423,plain,(
    ! [B_1163] :
      ( m1_subset_1(B_1163,k1_zfmisc_1('#skF_4'))
      | ~ r1_tarski(k2_relat_1(B_1163),'#skF_4')
      | ~ v1_funct_1(B_1163)
      | ~ v1_relat_1(B_1163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10352,c_11305])).

tff(c_11434,plain,(
    ! [B_1164] :
      ( m1_subset_1(B_1164,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(B_1164)
      | ~ v5_relat_1(B_1164,'#skF_4')
      | ~ v1_relat_1(B_1164) ) ),
    inference(resolution,[status(thm)],[c_24,c_11423])).

tff(c_10318,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_10310])).

tff(c_10329,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9058,c_10318])).

tff(c_9162,plain,(
    ! [B_856,A_857] :
      ( B_856 = A_857
      | ~ r1_tarski(B_856,A_857)
      | ~ r1_tarski(A_857,B_856) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_9164,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_9119,c_9162])).

tff(c_9173,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9058,c_9164])).

tff(c_9197,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9173,c_9085])).

tff(c_9194,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9173,c_9173,c_9056])).

tff(c_9934,plain,(
    ! [A_954,B_955,C_956,D_957] :
      ( v1_funct_1(k2_partfun1(A_954,B_955,C_956,D_957))
      | ~ m1_subset_1(C_956,k1_zfmisc_1(k2_zfmisc_1(A_954,B_955)))
      | ~ v1_funct_1(C_956) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_10224,plain,(
    ! [B_996,C_997,D_998] :
      ( v1_funct_1(k2_partfun1('#skF_4',B_996,C_997,D_998))
      | ~ m1_subset_1(C_997,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_997) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9194,c_9934])).

tff(c_10226,plain,(
    ! [B_996,D_998] :
      ( v1_funct_1(k2_partfun1('#skF_4',B_996,'#skF_4',D_998))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_9197,c_10224])).

tff(c_10232,plain,(
    ! [B_996,D_998] : v1_funct_1(k2_partfun1('#skF_4',B_996,'#skF_4',D_998)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_10226])).

tff(c_9170,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_9162])).

tff(c_9181,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9058,c_9170])).

tff(c_9130,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9064,c_9064,c_9064,c_9057,c_9064,c_9064,c_66])).

tff(c_9131,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_9130])).

tff(c_9182,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9181,c_9131])).

tff(c_9340,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9173,c_9173,c_9173,c_9182])).

tff(c_10236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10232,c_9340])).

tff(c_10237,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_9130])).

tff(c_10239,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_10237])).

tff(c_10331,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10329,c_10239])).

tff(c_10570,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10321,c_10321,c_10321,c_10321,c_10331])).

tff(c_11447,plain,
    ( ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'))
    | ~ v5_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_11434,c_10570])).

tff(c_11465,plain,
    ( ~ v5_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11376,c_11447])).

tff(c_11620,plain,(
    ~ v1_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_11465])).

tff(c_12089,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12085,c_11620])).

tff(c_12090,plain,(
    ~ v5_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_11465])).

tff(c_12966,plain,(
    ~ v5_relat_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12964,c_12090])).

tff(c_12971,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10544,c_12966])).

tff(c_12973,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_10237])).

tff(c_13109,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13069,c_13051,c_13051,c_13051,c_12973])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_13113,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_13109,c_18])).

tff(c_13052,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_9058,c_13040])).

tff(c_13177,plain,(
    ! [A_3] :
      ( A_3 = '#skF_4'
      | ~ r1_tarski(A_3,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13051,c_13051,c_13052])).

tff(c_13215,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_13113,c_13177])).

tff(c_12972,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_10237])).

tff(c_13204,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13069,c_13069,c_13051,c_13051,c_13051,c_12972])).

tff(c_13245,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13215,c_13204])).

tff(c_13252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13077,c_13245])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:37:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.50/3.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.66/3.45  
% 9.66/3.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.66/3.45  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.66/3.45  
% 9.66/3.45  %Foreground sorts:
% 9.66/3.45  
% 9.66/3.45  
% 9.66/3.45  %Background operators:
% 9.66/3.45  
% 9.66/3.45  
% 9.66/3.45  %Foreground operators:
% 9.66/3.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.66/3.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.66/3.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.66/3.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.66/3.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.66/3.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.66/3.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.66/3.45  tff('#skF_2', type, '#skF_2': $i).
% 9.66/3.45  tff('#skF_3', type, '#skF_3': $i).
% 9.66/3.45  tff('#skF_1', type, '#skF_1': $i).
% 9.66/3.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.66/3.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.66/3.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.66/3.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.66/3.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.66/3.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.66/3.45  tff('#skF_4', type, '#skF_4': $i).
% 9.66/3.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.66/3.45  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 9.66/3.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.66/3.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.66/3.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.66/3.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.66/3.45  
% 9.74/3.48  tff(f_144, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 9.74/3.48  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.74/3.48  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.74/3.48  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.74/3.48  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 9.74/3.48  tff(f_112, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 9.74/3.48  tff(f_106, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 9.74/3.48  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.74/3.48  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 9.74/3.48  tff(f_124, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 9.74/3.48  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.74/3.48  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.74/3.48  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.74/3.48  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.74/3.48  tff(f_56, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 9.74/3.48  tff(c_70, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.74/3.48  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.74/3.48  tff(c_133, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.74/3.48  tff(c_146, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_133])).
% 9.74/3.48  tff(c_68, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.74/3.48  tff(c_113, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_68])).
% 9.74/3.48  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.74/3.48  tff(c_8036, plain, (![A_728, B_729, C_730]: (k1_relset_1(A_728, B_729, C_730)=k1_relat_1(C_730) | ~m1_subset_1(C_730, k1_zfmisc_1(k2_zfmisc_1(A_728, B_729))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.74/3.48  tff(c_8055, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_8036])).
% 9.74/3.48  tff(c_8890, plain, (![B_834, A_835, C_836]: (k1_xboole_0=B_834 | k1_relset_1(A_835, B_834, C_836)=A_835 | ~v1_funct_2(C_836, A_835, B_834) | ~m1_subset_1(C_836, k1_zfmisc_1(k2_zfmisc_1(A_835, B_834))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.74/3.48  tff(c_8903, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_8890])).
% 9.74/3.48  tff(c_8917, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_8055, c_8903])).
% 9.74/3.48  tff(c_8918, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_113, c_8917])).
% 9.74/3.48  tff(c_30, plain, (![B_14, A_13]: (k1_relat_1(k7_relat_1(B_14, A_13))=A_13 | ~r1_tarski(A_13, k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.74/3.48  tff(c_8936, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_4', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8918, c_30])).
% 9.74/3.48  tff(c_8998, plain, (![A_839]: (k1_relat_1(k7_relat_1('#skF_4', A_839))=A_839 | ~r1_tarski(A_839, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_8936])).
% 9.74/3.48  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.74/3.48  tff(c_8717, plain, (![A_822, B_823, C_824, D_825]: (k2_partfun1(A_822, B_823, C_824, D_825)=k7_relat_1(C_824, D_825) | ~m1_subset_1(C_824, k1_zfmisc_1(k2_zfmisc_1(A_822, B_823))) | ~v1_funct_1(C_824))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.74/3.48  tff(c_8726, plain, (![D_825]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_825)=k7_relat_1('#skF_4', D_825) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_8717])).
% 9.74/3.48  tff(c_8738, plain, (![D_825]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_825)=k7_relat_1('#skF_4', D_825))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_8726])).
% 9.74/3.48  tff(c_1864, plain, (![A_281, B_282, C_283, D_284]: (k2_partfun1(A_281, B_282, C_283, D_284)=k7_relat_1(C_283, D_284) | ~m1_subset_1(C_283, k1_zfmisc_1(k2_zfmisc_1(A_281, B_282))) | ~v1_funct_1(C_283))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.74/3.48  tff(c_1871, plain, (![D_284]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_284)=k7_relat_1('#skF_4', D_284) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_1864])).
% 9.74/3.48  tff(c_1880, plain, (![D_284]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_284)=k7_relat_1('#skF_4', D_284))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1871])).
% 9.74/3.48  tff(c_2063, plain, (![A_299, B_300, C_301, D_302]: (m1_subset_1(k2_partfun1(A_299, B_300, C_301, D_302), k1_zfmisc_1(k2_zfmisc_1(A_299, B_300))) | ~m1_subset_1(C_301, k1_zfmisc_1(k2_zfmisc_1(A_299, B_300))) | ~v1_funct_1(C_301))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.74/3.48  tff(c_2091, plain, (![D_284]: (m1_subset_1(k7_relat_1('#skF_4', D_284), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1880, c_2063])).
% 9.74/3.48  tff(c_2116, plain, (![D_304]: (m1_subset_1(k7_relat_1('#skF_4', D_304), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_2091])).
% 9.74/3.48  tff(c_34, plain, (![C_18, A_16, B_17]: (v1_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.74/3.48  tff(c_2157, plain, (![D_304]: (v1_relat_1(k7_relat_1('#skF_4', D_304)))), inference(resolution, [status(thm)], [c_2116, c_34])).
% 9.74/3.48  tff(c_36, plain, (![C_21, B_20, A_19]: (v5_relat_1(C_21, B_20) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.74/3.48  tff(c_2156, plain, (![D_304]: (v5_relat_1(k7_relat_1('#skF_4', D_304), '#skF_2'))), inference(resolution, [status(thm)], [c_2116, c_36])).
% 9.74/3.48  tff(c_24, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.74/3.48  tff(c_1505, plain, (![A_232, B_233, C_234, D_235]: (v1_funct_1(k2_partfun1(A_232, B_233, C_234, D_235)) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))) | ~v1_funct_1(C_234))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.74/3.48  tff(c_1510, plain, (![D_235]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_235)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_1505])).
% 9.74/3.48  tff(c_1518, plain, (![D_235]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_235)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1510])).
% 9.74/3.48  tff(c_1881, plain, (![D_235]: (v1_funct_1(k7_relat_1('#skF_4', D_235)))), inference(demodulation, [status(thm), theory('equality')], [c_1880, c_1518])).
% 9.74/3.48  tff(c_1315, plain, (![A_210, B_211, C_212]: (k1_relset_1(A_210, B_211, C_212)=k1_relat_1(C_212) | ~m1_subset_1(C_212, k1_zfmisc_1(k2_zfmisc_1(A_210, B_211))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.74/3.48  tff(c_1330, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_1315])).
% 9.74/3.48  tff(c_1966, plain, (![B_295, A_296, C_297]: (k1_xboole_0=B_295 | k1_relset_1(A_296, B_295, C_297)=A_296 | ~v1_funct_2(C_297, A_296, B_295) | ~m1_subset_1(C_297, k1_zfmisc_1(k2_zfmisc_1(A_296, B_295))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.74/3.48  tff(c_1976, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_1966])).
% 9.74/3.48  tff(c_1987, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1330, c_1976])).
% 9.74/3.48  tff(c_1988, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_113, c_1987])).
% 9.74/3.48  tff(c_2006, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_4', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1988, c_30])).
% 9.74/3.48  tff(c_2186, plain, (![A_310]: (k1_relat_1(k7_relat_1('#skF_4', A_310))=A_310 | ~r1_tarski(A_310, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_2006])).
% 9.74/3.48  tff(c_60, plain, (![B_37, A_36]: (m1_subset_1(B_37, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_37), A_36))) | ~r1_tarski(k2_relat_1(B_37), A_36) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.74/3.48  tff(c_2198, plain, (![A_310, A_36]: (m1_subset_1(k7_relat_1('#skF_4', A_310), k1_zfmisc_1(k2_zfmisc_1(A_310, A_36))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_310)), A_36) | ~v1_funct_1(k7_relat_1('#skF_4', A_310)) | ~v1_relat_1(k7_relat_1('#skF_4', A_310)) | ~r1_tarski(A_310, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2186, c_60])).
% 9.74/3.48  tff(c_7671, plain, (![A_693, A_694]: (m1_subset_1(k7_relat_1('#skF_4', A_693), k1_zfmisc_1(k2_zfmisc_1(A_693, A_694))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_693)), A_694) | ~r1_tarski(A_693, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2157, c_1881, c_2198])).
% 9.74/3.48  tff(c_847, plain, (![A_146, B_147, C_148, D_149]: (v1_funct_1(k2_partfun1(A_146, B_147, C_148, D_149)) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))) | ~v1_funct_1(C_148))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.74/3.48  tff(c_852, plain, (![D_149]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_149)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_847])).
% 9.74/3.48  tff(c_860, plain, (![D_149]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_149)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_852])).
% 9.74/3.48  tff(c_66, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.74/3.48  tff(c_147, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_66])).
% 9.74/3.48  tff(c_863, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_860, c_147])).
% 9.74/3.48  tff(c_864, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_66])).
% 9.74/3.48  tff(c_984, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_864])).
% 9.74/3.48  tff(c_1883, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1880, c_984])).
% 9.74/3.48  tff(c_7690, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_7671, c_1883])).
% 9.74/3.48  tff(c_7738, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_7690])).
% 9.74/3.48  tff(c_7757, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_7738])).
% 9.74/3.48  tff(c_7761, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2157, c_2156, c_7757])).
% 9.74/3.48  tff(c_7763, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_864])).
% 9.74/3.48  tff(c_8053, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_7763, c_8036])).
% 9.74/3.48  tff(c_8742, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8738, c_8738, c_8053])).
% 9.74/3.48  tff(c_7762, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_864])).
% 9.74/3.48  tff(c_8748, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8738, c_7762])).
% 9.74/3.48  tff(c_8747, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_8738, c_7763])).
% 9.74/3.48  tff(c_48, plain, (![B_26, C_27, A_25]: (k1_xboole_0=B_26 | v1_funct_2(C_27, A_25, B_26) | k1_relset_1(A_25, B_26, C_27)!=A_25 | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.74/3.48  tff(c_8807, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_8747, c_48])).
% 9.74/3.48  tff(c_8829, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_8748, c_113, c_8807])).
% 9.74/3.48  tff(c_8845, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8742, c_8829])).
% 9.74/3.48  tff(c_9007, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8998, c_8845])).
% 9.74/3.48  tff(c_9052, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_9007])).
% 9.74/3.48  tff(c_9053, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_68])).
% 9.74/3.48  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.74/3.48  tff(c_9058, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_9053, c_10])).
% 9.74/3.48  tff(c_14, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.74/3.48  tff(c_9057, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9053, c_9053, c_14])).
% 9.74/3.48  tff(c_9054, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_68])).
% 9.74/3.48  tff(c_9064, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9053, c_9054])).
% 9.74/3.48  tff(c_9085, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9057, c_9064, c_72])).
% 9.74/3.48  tff(c_9111, plain, (![A_849, B_850]: (r1_tarski(A_849, B_850) | ~m1_subset_1(A_849, k1_zfmisc_1(B_850)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.74/3.48  tff(c_9119, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_9085, c_9111])).
% 9.74/3.48  tff(c_13040, plain, (![B_1307, A_1308]: (B_1307=A_1308 | ~r1_tarski(B_1307, A_1308) | ~r1_tarski(A_1308, B_1307))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.74/3.48  tff(c_13042, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_9119, c_13040])).
% 9.74/3.48  tff(c_13051, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9058, c_13042])).
% 9.74/3.48  tff(c_9065, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9064, c_74])).
% 9.74/3.48  tff(c_13077, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13051, c_13051, c_9065])).
% 9.74/3.48  tff(c_13048, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_13040])).
% 9.74/3.48  tff(c_13059, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9058, c_13048])).
% 9.74/3.48  tff(c_13069, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13051, c_13059])).
% 9.74/3.48  tff(c_10310, plain, (![B_1008, A_1009]: (B_1008=A_1009 | ~r1_tarski(B_1008, A_1009) | ~r1_tarski(A_1009, B_1008))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.74/3.48  tff(c_10312, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_9119, c_10310])).
% 9.74/3.48  tff(c_10321, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9058, c_10312])).
% 9.74/3.48  tff(c_10350, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10321, c_9085])).
% 9.74/3.48  tff(c_16, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.74/3.48  tff(c_9056, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9053, c_9053, c_16])).
% 9.74/3.48  tff(c_10347, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10321, c_10321, c_9056])).
% 9.74/3.48  tff(c_10514, plain, (![C_1022, B_1023, A_1024]: (v5_relat_1(C_1022, B_1023) | ~m1_subset_1(C_1022, k1_zfmisc_1(k2_zfmisc_1(A_1024, B_1023))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.74/3.48  tff(c_10538, plain, (![C_1027, B_1028]: (v5_relat_1(C_1027, B_1028) | ~m1_subset_1(C_1027, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_10347, c_10514])).
% 9.74/3.48  tff(c_10544, plain, (![B_1028]: (v5_relat_1('#skF_4', B_1028))), inference(resolution, [status(thm)], [c_10350, c_10538])).
% 9.74/3.48  tff(c_28, plain, (![A_12]: (k7_relat_1(k1_xboole_0, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.74/3.48  tff(c_9055, plain, (![A_12]: (k7_relat_1('#skF_1', A_12)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9053, c_9053, c_28])).
% 9.74/3.48  tff(c_10351, plain, (![A_12]: (k7_relat_1('#skF_4', A_12)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10321, c_10321, c_9055])).
% 9.74/3.48  tff(c_10352, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10321, c_10321, c_9057])).
% 9.74/3.48  tff(c_11380, plain, (![A_1145, B_1146, C_1147, D_1148]: (k2_partfun1(A_1145, B_1146, C_1147, D_1148)=k7_relat_1(C_1147, D_1148) | ~m1_subset_1(C_1147, k1_zfmisc_1(k2_zfmisc_1(A_1145, B_1146))) | ~v1_funct_1(C_1147))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.74/3.48  tff(c_12953, plain, (![A_1295, C_1296, D_1297]: (k2_partfun1(A_1295, '#skF_4', C_1296, D_1297)=k7_relat_1(C_1296, D_1297) | ~m1_subset_1(C_1296, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_1296))), inference(superposition, [status(thm), theory('equality')], [c_10352, c_11380])).
% 9.74/3.48  tff(c_12957, plain, (![A_1295, D_1297]: (k2_partfun1(A_1295, '#skF_4', '#skF_4', D_1297)=k7_relat_1('#skF_4', D_1297) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_10350, c_12953])).
% 9.74/3.48  tff(c_12964, plain, (![A_1295, D_1297]: (k2_partfun1(A_1295, '#skF_4', '#skF_4', D_1297)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_10351, c_12957])).
% 9.74/3.48  tff(c_11793, plain, (![A_1180, B_1181, C_1182, D_1183]: (m1_subset_1(k2_partfun1(A_1180, B_1181, C_1182, D_1183), k1_zfmisc_1(k2_zfmisc_1(A_1180, B_1181))) | ~m1_subset_1(C_1182, k1_zfmisc_1(k2_zfmisc_1(A_1180, B_1181))) | ~v1_funct_1(C_1182))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.74/3.48  tff(c_12059, plain, (![A_1202, B_1203, C_1204, D_1205]: (v1_relat_1(k2_partfun1(A_1202, B_1203, C_1204, D_1205)) | ~m1_subset_1(C_1204, k1_zfmisc_1(k2_zfmisc_1(A_1202, B_1203))) | ~v1_funct_1(C_1204))), inference(resolution, [status(thm)], [c_11793, c_34])).
% 9.74/3.48  tff(c_12074, plain, (![B_1206, C_1207, D_1208]: (v1_relat_1(k2_partfun1('#skF_4', B_1206, C_1207, D_1208)) | ~m1_subset_1(C_1207, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_1207))), inference(superposition, [status(thm), theory('equality')], [c_10347, c_12059])).
% 9.74/3.48  tff(c_12078, plain, (![B_1206, D_1208]: (v1_relat_1(k2_partfun1('#skF_4', B_1206, '#skF_4', D_1208)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_10350, c_12074])).
% 9.74/3.48  tff(c_12085, plain, (![B_1206, D_1208]: (v1_relat_1(k2_partfun1('#skF_4', B_1206, '#skF_4', D_1208)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_12078])).
% 9.74/3.48  tff(c_11094, plain, (![A_1108, B_1109, C_1110, D_1111]: (v1_funct_1(k2_partfun1(A_1108, B_1109, C_1110, D_1111)) | ~m1_subset_1(C_1110, k1_zfmisc_1(k2_zfmisc_1(A_1108, B_1109))) | ~v1_funct_1(C_1110))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.74/3.48  tff(c_11368, plain, (![B_1140, C_1141, D_1142]: (v1_funct_1(k2_partfun1('#skF_4', B_1140, C_1141, D_1142)) | ~m1_subset_1(C_1141, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_1141))), inference(superposition, [status(thm), theory('equality')], [c_10347, c_11094])).
% 9.74/3.48  tff(c_11370, plain, (![B_1140, D_1142]: (v1_funct_1(k2_partfun1('#skF_4', B_1140, '#skF_4', D_1142)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_10350, c_11368])).
% 9.74/3.48  tff(c_11376, plain, (![B_1140, D_1142]: (v1_funct_1(k2_partfun1('#skF_4', B_1140, '#skF_4', D_1142)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_11370])).
% 9.74/3.48  tff(c_11305, plain, (![B_1135, A_1136]: (m1_subset_1(B_1135, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1135), A_1136))) | ~r1_tarski(k2_relat_1(B_1135), A_1136) | ~v1_funct_1(B_1135) | ~v1_relat_1(B_1135))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.74/3.48  tff(c_11423, plain, (![B_1163]: (m1_subset_1(B_1163, k1_zfmisc_1('#skF_4')) | ~r1_tarski(k2_relat_1(B_1163), '#skF_4') | ~v1_funct_1(B_1163) | ~v1_relat_1(B_1163))), inference(superposition, [status(thm), theory('equality')], [c_10352, c_11305])).
% 9.74/3.48  tff(c_11434, plain, (![B_1164]: (m1_subset_1(B_1164, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(B_1164) | ~v5_relat_1(B_1164, '#skF_4') | ~v1_relat_1(B_1164))), inference(resolution, [status(thm)], [c_24, c_11423])).
% 9.74/3.48  tff(c_10318, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_10310])).
% 9.74/3.48  tff(c_10329, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9058, c_10318])).
% 9.74/3.48  tff(c_9162, plain, (![B_856, A_857]: (B_856=A_857 | ~r1_tarski(B_856, A_857) | ~r1_tarski(A_857, B_856))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.74/3.48  tff(c_9164, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_9119, c_9162])).
% 9.74/3.48  tff(c_9173, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9058, c_9164])).
% 9.74/3.48  tff(c_9197, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9173, c_9085])).
% 9.74/3.48  tff(c_9194, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9173, c_9173, c_9056])).
% 9.74/3.48  tff(c_9934, plain, (![A_954, B_955, C_956, D_957]: (v1_funct_1(k2_partfun1(A_954, B_955, C_956, D_957)) | ~m1_subset_1(C_956, k1_zfmisc_1(k2_zfmisc_1(A_954, B_955))) | ~v1_funct_1(C_956))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.74/3.48  tff(c_10224, plain, (![B_996, C_997, D_998]: (v1_funct_1(k2_partfun1('#skF_4', B_996, C_997, D_998)) | ~m1_subset_1(C_997, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_997))), inference(superposition, [status(thm), theory('equality')], [c_9194, c_9934])).
% 9.74/3.48  tff(c_10226, plain, (![B_996, D_998]: (v1_funct_1(k2_partfun1('#skF_4', B_996, '#skF_4', D_998)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_9197, c_10224])).
% 9.74/3.48  tff(c_10232, plain, (![B_996, D_998]: (v1_funct_1(k2_partfun1('#skF_4', B_996, '#skF_4', D_998)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_10226])).
% 9.74/3.48  tff(c_9170, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_9162])).
% 9.74/3.48  tff(c_9181, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9058, c_9170])).
% 9.74/3.48  tff(c_9130, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_9064, c_9064, c_9064, c_9057, c_9064, c_9064, c_66])).
% 9.74/3.48  tff(c_9131, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_9130])).
% 9.74/3.48  tff(c_9182, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9181, c_9131])).
% 9.74/3.48  tff(c_9340, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9173, c_9173, c_9173, c_9182])).
% 9.74/3.48  tff(c_10236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10232, c_9340])).
% 9.74/3.48  tff(c_10237, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_9130])).
% 9.74/3.48  tff(c_10239, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_10237])).
% 9.74/3.48  tff(c_10331, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10329, c_10239])).
% 9.74/3.48  tff(c_10570, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10321, c_10321, c_10321, c_10321, c_10331])).
% 9.74/3.48  tff(c_11447, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')) | ~v5_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4') | ~v1_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_11434, c_10570])).
% 9.74/3.48  tff(c_11465, plain, (~v5_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4') | ~v1_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11376, c_11447])).
% 9.74/3.48  tff(c_11620, plain, (~v1_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(splitLeft, [status(thm)], [c_11465])).
% 9.74/3.48  tff(c_12089, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12085, c_11620])).
% 9.74/3.48  tff(c_12090, plain, (~v5_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_11465])).
% 9.74/3.48  tff(c_12966, plain, (~v5_relat_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12964, c_12090])).
% 9.74/3.48  tff(c_12971, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10544, c_12966])).
% 9.74/3.48  tff(c_12973, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_10237])).
% 9.74/3.48  tff(c_13109, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13069, c_13051, c_13051, c_13051, c_12973])).
% 9.74/3.48  tff(c_18, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.74/3.48  tff(c_13113, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_13109, c_18])).
% 9.74/3.48  tff(c_13052, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(resolution, [status(thm)], [c_9058, c_13040])).
% 9.74/3.48  tff(c_13177, plain, (![A_3]: (A_3='#skF_4' | ~r1_tarski(A_3, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13051, c_13051, c_13052])).
% 9.74/3.48  tff(c_13215, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_13113, c_13177])).
% 9.74/3.48  tff(c_12972, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_10237])).
% 9.74/3.48  tff(c_13204, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13069, c_13069, c_13051, c_13051, c_13051, c_12972])).
% 9.74/3.48  tff(c_13245, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13215, c_13204])).
% 9.74/3.48  tff(c_13252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13077, c_13245])).
% 9.74/3.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.74/3.48  
% 9.74/3.48  Inference rules
% 9.74/3.48  ----------------------
% 9.74/3.48  #Ref     : 0
% 9.74/3.48  #Sup     : 2810
% 9.74/3.48  #Fact    : 0
% 9.74/3.48  #Define  : 0
% 9.74/3.48  #Split   : 21
% 9.74/3.48  #Chain   : 0
% 9.74/3.48  #Close   : 0
% 9.74/3.48  
% 9.74/3.48  Ordering : KBO
% 9.74/3.48  
% 9.74/3.48  Simplification rules
% 9.74/3.48  ----------------------
% 9.74/3.48  #Subsume      : 311
% 9.74/3.48  #Demod        : 4063
% 9.74/3.48  #Tautology    : 1404
% 9.74/3.48  #SimpNegUnit  : 26
% 9.74/3.48  #BackRed      : 108
% 9.74/3.48  
% 9.74/3.48  #Partial instantiations: 0
% 9.74/3.48  #Strategies tried      : 1
% 9.74/3.48  
% 9.74/3.48  Timing (in seconds)
% 9.74/3.48  ----------------------
% 9.74/3.48  Preprocessing        : 0.40
% 9.74/3.48  Parsing              : 0.18
% 9.74/3.48  CNF conversion       : 0.04
% 9.74/3.48  Main loop            : 2.22
% 9.74/3.48  Inferencing          : 0.72
% 9.74/3.48  Reduction            : 0.85
% 9.74/3.48  Demodulation         : 0.63
% 9.74/3.48  BG Simplification    : 0.08
% 9.74/3.48  Subsumption          : 0.42
% 9.74/3.48  Abstraction          : 0.08
% 9.74/3.48  MUC search           : 0.00
% 9.74/3.48  Cooper               : 0.00
% 9.74/3.48  Total                : 2.69
% 9.74/3.48  Index Insertion      : 0.00
% 9.74/3.48  Index Deletion       : 0.00
% 9.74/3.48  Index Matching       : 0.00
% 9.74/3.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
