%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:37 EST 2020

% Result     : Theorem 7.56s
% Output     : CNFRefutation 7.56s
% Verified   : 
% Statistics : Number of formulae       :  164 (1988 expanded)
%              Number of leaves         :   39 ( 637 expanded)
%              Depth                    :   12
%              Number of atoms          :  269 (6332 expanded)
%              Number of equality atoms :   73 (2457 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_147,negated_conjecture,(
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

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_101,axiom,(
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

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_115,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_127,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(c_66,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_801,plain,(
    ! [C_162,A_163,B_164] :
      ( v1_relat_1(C_162)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_818,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_801])).

tff(c_64,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_85,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_5540,plain,(
    ! [A_691,B_692,C_693] :
      ( k1_relset_1(A_691,B_692,C_693) = k1_relat_1(C_693)
      | ~ m1_subset_1(C_693,k1_zfmisc_1(k2_zfmisc_1(A_691,B_692))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_5563,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_5540])).

tff(c_6393,plain,(
    ! [B_776,A_777,C_778] :
      ( k1_xboole_0 = B_776
      | k1_relset_1(A_777,B_776,C_778) = A_777
      | ~ v1_funct_2(C_778,A_777,B_776)
      | ~ m1_subset_1(C_778,k1_zfmisc_1(k2_zfmisc_1(A_777,B_776))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_6406,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_6393])).

tff(c_6424,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5563,c_6406])).

tff(c_6425,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_6424])).

tff(c_28,plain,(
    ! [B_19,A_18] :
      ( k1_relat_1(k7_relat_1(B_19,A_18)) = A_18
      | ~ r1_tarski(A_18,k1_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6439,plain,(
    ! [A_18] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_18)) = A_18
      | ~ r1_tarski(A_18,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6425,c_28])).

tff(c_6461,plain,(
    ! [A_780] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_780)) = A_780
      | ~ r1_tarski(A_780,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_818,c_6439])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_6233,plain,(
    ! [A_764,B_765,C_766,D_767] :
      ( k2_partfun1(A_764,B_765,C_766,D_767) = k7_relat_1(C_766,D_767)
      | ~ m1_subset_1(C_766,k1_zfmisc_1(k2_zfmisc_1(A_764,B_765)))
      | ~ v1_funct_1(C_766) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_6242,plain,(
    ! [D_767] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_767) = k7_relat_1('#skF_4',D_767)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_6233])).

tff(c_6257,plain,(
    ! [D_767] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_767) = k7_relat_1('#skF_4',D_767) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6242])).

tff(c_1680,plain,(
    ! [A_301,B_302,C_303,D_304] :
      ( k2_partfun1(A_301,B_302,C_303,D_304) = k7_relat_1(C_303,D_304)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(A_301,B_302)))
      | ~ v1_funct_1(C_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1687,plain,(
    ! [D_304] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_304) = k7_relat_1('#skF_4',D_304)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_1680])).

tff(c_1699,plain,(
    ! [D_304] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_304) = k7_relat_1('#skF_4',D_304) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1687])).

tff(c_2166,plain,(
    ! [A_336,B_337,C_338,D_339] :
      ( m1_subset_1(k2_partfun1(A_336,B_337,C_338,D_339),k1_zfmisc_1(k2_zfmisc_1(A_336,B_337)))
      | ~ m1_subset_1(C_338,k1_zfmisc_1(k2_zfmisc_1(A_336,B_337)))
      | ~ v1_funct_1(C_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2196,plain,(
    ! [D_304] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_304),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1699,c_2166])).

tff(c_2217,plain,(
    ! [D_340] : m1_subset_1(k7_relat_1('#skF_4',D_340),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_2196])).

tff(c_32,plain,(
    ! [C_25,B_24,A_23] :
      ( v5_relat_1(C_25,B_24)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2260,plain,(
    ! [D_340] : v5_relat_1(k7_relat_1('#skF_4',D_340),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2217,c_32])).

tff(c_30,plain,(
    ! [C_22,A_20,B_21] :
      ( v1_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2261,plain,(
    ! [D_340] : v1_relat_1(k7_relat_1('#skF_4',D_340)) ),
    inference(resolution,[status(thm)],[c_2217,c_30])).

tff(c_20,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v5_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1502,plain,(
    ! [A_267,B_268,C_269,D_270] :
      ( v1_funct_1(k2_partfun1(A_267,B_268,C_269,D_270))
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1(A_267,B_268)))
      | ~ v1_funct_1(C_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1507,plain,(
    ! [D_270] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_270))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_1502])).

tff(c_1518,plain,(
    ! [D_270] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_270)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1507])).

tff(c_1702,plain,(
    ! [D_270] : v1_funct_1(k7_relat_1('#skF_4',D_270)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1699,c_1518])).

tff(c_1205,plain,(
    ! [A_228,B_229,C_230] :
      ( k1_relset_1(A_228,B_229,C_230) = k1_relat_1(C_230)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_228,B_229))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1224,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_1205])).

tff(c_1859,plain,(
    ! [B_315,A_316,C_317] :
      ( k1_xboole_0 = B_315
      | k1_relset_1(A_316,B_315,C_317) = A_316
      | ~ v1_funct_2(C_317,A_316,B_315)
      | ~ m1_subset_1(C_317,k1_zfmisc_1(k2_zfmisc_1(A_316,B_315))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1869,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_1859])).

tff(c_1884,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1224,c_1869])).

tff(c_1885,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_1884])).

tff(c_1901,plain,(
    ! [A_18] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_18)) = A_18
      | ~ r1_tarski(A_18,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1885,c_28])).

tff(c_1909,plain,(
    ! [A_18] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_18)) = A_18
      | ~ r1_tarski(A_18,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_818,c_1901])).

tff(c_1590,plain,(
    ! [B_291,A_292] :
      ( m1_subset_1(B_291,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_291),A_292)))
      | ~ r1_tarski(k2_relat_1(B_291),A_292)
      | ~ v1_funct_1(B_291)
      | ~ v1_relat_1(B_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2483,plain,(
    ! [B_381,A_382] :
      ( r1_tarski(B_381,k2_zfmisc_1(k1_relat_1(B_381),A_382))
      | ~ r1_tarski(k2_relat_1(B_381),A_382)
      | ~ v1_funct_1(B_381)
      | ~ v1_relat_1(B_381) ) ),
    inference(resolution,[status(thm)],[c_1590,c_12])).

tff(c_2529,plain,(
    ! [A_18,A_382] :
      ( r1_tarski(k7_relat_1('#skF_4',A_18),k2_zfmisc_1(A_18,A_382))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_18)),A_382)
      | ~ v1_funct_1(k7_relat_1('#skF_4',A_18))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_18))
      | ~ r1_tarski(A_18,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1909,c_2483])).

tff(c_3478,plain,(
    ! [A_503,A_504] :
      ( r1_tarski(k7_relat_1('#skF_4',A_503),k2_zfmisc_1(A_503,A_504))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_503)),A_504)
      | ~ r1_tarski(A_503,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2261,c_1702,c_2529])).

tff(c_3484,plain,(
    ! [A_503,A_10] :
      ( r1_tarski(k7_relat_1('#skF_4',A_503),k2_zfmisc_1(A_503,A_10))
      | ~ r1_tarski(A_503,'#skF_1')
      | ~ v5_relat_1(k7_relat_1('#skF_4',A_503),A_10)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_503)) ) ),
    inference(resolution,[status(thm)],[c_20,c_3478])).

tff(c_5027,plain,(
    ! [A_618,A_619] :
      ( r1_tarski(k7_relat_1('#skF_4',A_618),k2_zfmisc_1(A_618,A_619))
      | ~ r1_tarski(A_618,'#skF_1')
      | ~ v5_relat_1(k7_relat_1('#skF_4',A_618),A_619) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2261,c_3484])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_754,plain,(
    ! [A_153,B_154,C_155,D_156] :
      ( v1_funct_1(k2_partfun1(A_153,B_154,C_155,D_156))
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154)))
      | ~ v1_funct_1(C_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_759,plain,(
    ! [D_156] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_156))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_754])).

tff(c_770,plain,(
    ! [D_156] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_156)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_759])).

tff(c_62,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_150,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_774,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_770,c_150])).

tff(c_775,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_833,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_775])).

tff(c_914,plain,(
    ~ r1_tarski(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_833])).

tff(c_1703,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1699,c_914])).

tff(c_5042,plain,
    ( ~ r1_tarski('#skF_3','#skF_1')
    | ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_5027,c_1703])).

tff(c_5075,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2260,c_66,c_5042])).

tff(c_5077,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_775])).

tff(c_5561,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_5077,c_5540])).

tff(c_6262,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6257,c_6257,c_5561])).

tff(c_5076,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_775])).

tff(c_6269,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6257,c_5076])).

tff(c_6268,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6257,c_5077])).

tff(c_44,plain,(
    ! [B_30,C_31,A_29] :
      ( k1_xboole_0 = B_30
      | v1_funct_2(C_31,A_29,B_30)
      | k1_relset_1(A_29,B_30,C_31) != A_29
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_6330,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_6268,c_44])).

tff(c_6354,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_6269,c_85,c_6330])).

tff(c_6388,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6262,c_6354])).

tff(c_6467,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6461,c_6388])).

tff(c_6492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_6467])).

tff(c_6493,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6495,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6493,c_6493,c_6])).

tff(c_6494,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_6500,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6493,c_6494])).

tff(c_6543,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6495,c_6500,c_68])).

tff(c_6583,plain,(
    ! [A_795,B_796] :
      ( r1_tarski(A_795,B_796)
      | ~ m1_subset_1(A_795,k1_zfmisc_1(B_796)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6594,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_6543,c_6583])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6537,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ r1_tarski(A_1,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6493,c_6493,c_2])).

tff(c_6599,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6594,c_6537])).

tff(c_6501,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6500,c_70])).

tff(c_7338,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6599,c_6599,c_6501])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6516,plain,(
    ! [A_4] : m1_subset_1('#skF_1',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6493,c_10])).

tff(c_6595,plain,(
    ! [A_4] : r1_tarski('#skF_1',A_4) ),
    inference(resolution,[status(thm)],[c_6516,c_6583])).

tff(c_7364,plain,(
    ! [A_4] : r1_tarski('#skF_4',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6599,c_6595])).

tff(c_6513,plain,(
    ! [A_782,B_783] : v1_relat_1(k2_zfmisc_1(A_782,B_783)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6515,plain,(
    v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6495,c_6513])).

tff(c_6557,plain,(
    ! [B_790,A_791] :
      ( r1_tarski(k7_relat_1(B_790,A_791),B_790)
      | ~ v1_relat_1(B_790) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6561,plain,(
    ! [A_791] :
      ( k7_relat_1('#skF_1',A_791) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6557,c_6537])).

tff(c_6564,plain,(
    ! [A_791] : k7_relat_1('#skF_1',A_791) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6515,c_6561])).

tff(c_7329,plain,(
    ! [A_791] : k7_relat_1('#skF_4',A_791) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6599,c_6599,c_6564])).

tff(c_7337,plain,(
    ! [A_4] : m1_subset_1('#skF_4',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6599,c_6516])).

tff(c_8277,plain,(
    ! [A_1053,B_1054,C_1055,D_1056] :
      ( k2_partfun1(A_1053,B_1054,C_1055,D_1056) = k7_relat_1(C_1055,D_1056)
      | ~ m1_subset_1(C_1055,k1_zfmisc_1(k2_zfmisc_1(A_1053,B_1054)))
      | ~ v1_funct_1(C_1055) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_8282,plain,(
    ! [A_1053,B_1054,D_1056] :
      ( k2_partfun1(A_1053,B_1054,'#skF_4',D_1056) = k7_relat_1('#skF_4',D_1056)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_7337,c_8277])).

tff(c_8293,plain,(
    ! [A_1053,B_1054,D_1056] : k2_partfun1(A_1053,B_1054,'#skF_4',D_1056) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_7329,c_8282])).

tff(c_6611,plain,(
    ! [A_4] : m1_subset_1('#skF_4',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6599,c_6516])).

tff(c_7308,plain,(
    ! [A_903,B_904,C_905,D_906] :
      ( v1_funct_1(k2_partfun1(A_903,B_904,C_905,D_906))
      | ~ m1_subset_1(C_905,k1_zfmisc_1(k2_zfmisc_1(A_903,B_904)))
      | ~ v1_funct_1(C_905) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_7311,plain,(
    ! [A_903,B_904,D_906] :
      ( v1_funct_1(k2_partfun1(A_903,B_904,'#skF_4',D_906))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6611,c_7308])).

tff(c_7321,plain,(
    ! [A_903,B_904,D_906] : v1_funct_1(k2_partfun1(A_903,B_904,'#skF_4',D_906)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_7311])).

tff(c_6538,plain,(
    ! [A_786] :
      ( A_786 = '#skF_1'
      | ~ r1_tarski(A_786,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6493,c_6493,c_2])).

tff(c_6542,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_66,c_6538])).

tff(c_6600,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6542,c_6500,c_6542,c_6542,c_6500,c_6500,c_6542,c_6495,c_6500,c_6500,c_62])).

tff(c_6601,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_6600])).

tff(c_6735,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6599,c_6599,c_6599,c_6601])).

tff(c_7325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7321,c_6735])).

tff(c_7326,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_6600])).

tff(c_7462,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6599,c_6599,c_6599,c_6599,c_6599,c_6599,c_6599,c_6599,c_6599,c_7326])).

tff(c_7463,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_7462])).

tff(c_7547,plain,(
    ~ r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_7463])).

tff(c_8296,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8293,c_7547])).

tff(c_8301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7364,c_8296])).

tff(c_8303,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7462])).

tff(c_8468,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_8303,c_12])).

tff(c_7334,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ r1_tarski(A_1,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6599,c_6599,c_6537])).

tff(c_8478,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8468,c_7334])).

tff(c_8302,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_7462])).

tff(c_8482,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8478,c_8302])).

tff(c_8489,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7338,c_8482])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:01:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.56/2.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.56/2.68  
% 7.56/2.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.56/2.69  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.56/2.69  
% 7.56/2.69  %Foreground sorts:
% 7.56/2.69  
% 7.56/2.69  
% 7.56/2.69  %Background operators:
% 7.56/2.69  
% 7.56/2.69  
% 7.56/2.69  %Foreground operators:
% 7.56/2.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.56/2.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.56/2.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.56/2.69  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.56/2.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.56/2.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.56/2.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.56/2.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.56/2.69  tff('#skF_2', type, '#skF_2': $i).
% 7.56/2.69  tff('#skF_3', type, '#skF_3': $i).
% 7.56/2.69  tff('#skF_1', type, '#skF_1': $i).
% 7.56/2.69  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.56/2.69  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.56/2.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.56/2.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.56/2.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.56/2.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.56/2.69  tff('#skF_4', type, '#skF_4': $i).
% 7.56/2.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.56/2.69  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.56/2.69  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.56/2.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.56/2.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.56/2.69  
% 7.56/2.71  tff(f_147, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 7.56/2.71  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.56/2.71  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.56/2.71  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.56/2.71  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 7.56/2.71  tff(f_115, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 7.56/2.71  tff(f_109, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 7.56/2.71  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.56/2.71  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 7.56/2.71  tff(f_127, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 7.56/2.71  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.56/2.71  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.56/2.71  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 7.56/2.71  tff(f_37, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 7.56/2.71  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.56/2.71  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 7.56/2.71  tff(c_66, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.56/2.71  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.56/2.71  tff(c_801, plain, (![C_162, A_163, B_164]: (v1_relat_1(C_162) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.56/2.71  tff(c_818, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_801])).
% 7.56/2.71  tff(c_64, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.56/2.71  tff(c_85, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_64])).
% 7.56/2.71  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.56/2.71  tff(c_5540, plain, (![A_691, B_692, C_693]: (k1_relset_1(A_691, B_692, C_693)=k1_relat_1(C_693) | ~m1_subset_1(C_693, k1_zfmisc_1(k2_zfmisc_1(A_691, B_692))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.56/2.71  tff(c_5563, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_5540])).
% 7.56/2.71  tff(c_6393, plain, (![B_776, A_777, C_778]: (k1_xboole_0=B_776 | k1_relset_1(A_777, B_776, C_778)=A_777 | ~v1_funct_2(C_778, A_777, B_776) | ~m1_subset_1(C_778, k1_zfmisc_1(k2_zfmisc_1(A_777, B_776))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.56/2.71  tff(c_6406, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_6393])).
% 7.56/2.71  tff(c_6424, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_5563, c_6406])).
% 7.56/2.71  tff(c_6425, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_85, c_6424])).
% 7.56/2.71  tff(c_28, plain, (![B_19, A_18]: (k1_relat_1(k7_relat_1(B_19, A_18))=A_18 | ~r1_tarski(A_18, k1_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.56/2.71  tff(c_6439, plain, (![A_18]: (k1_relat_1(k7_relat_1('#skF_4', A_18))=A_18 | ~r1_tarski(A_18, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6425, c_28])).
% 7.56/2.71  tff(c_6461, plain, (![A_780]: (k1_relat_1(k7_relat_1('#skF_4', A_780))=A_780 | ~r1_tarski(A_780, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_818, c_6439])).
% 7.56/2.71  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.56/2.71  tff(c_6233, plain, (![A_764, B_765, C_766, D_767]: (k2_partfun1(A_764, B_765, C_766, D_767)=k7_relat_1(C_766, D_767) | ~m1_subset_1(C_766, k1_zfmisc_1(k2_zfmisc_1(A_764, B_765))) | ~v1_funct_1(C_766))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.56/2.71  tff(c_6242, plain, (![D_767]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_767)=k7_relat_1('#skF_4', D_767) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_6233])).
% 7.56/2.71  tff(c_6257, plain, (![D_767]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_767)=k7_relat_1('#skF_4', D_767))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_6242])).
% 7.56/2.71  tff(c_1680, plain, (![A_301, B_302, C_303, D_304]: (k2_partfun1(A_301, B_302, C_303, D_304)=k7_relat_1(C_303, D_304) | ~m1_subset_1(C_303, k1_zfmisc_1(k2_zfmisc_1(A_301, B_302))) | ~v1_funct_1(C_303))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.56/2.71  tff(c_1687, plain, (![D_304]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_304)=k7_relat_1('#skF_4', D_304) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_1680])).
% 7.56/2.71  tff(c_1699, plain, (![D_304]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_304)=k7_relat_1('#skF_4', D_304))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1687])).
% 7.56/2.71  tff(c_2166, plain, (![A_336, B_337, C_338, D_339]: (m1_subset_1(k2_partfun1(A_336, B_337, C_338, D_339), k1_zfmisc_1(k2_zfmisc_1(A_336, B_337))) | ~m1_subset_1(C_338, k1_zfmisc_1(k2_zfmisc_1(A_336, B_337))) | ~v1_funct_1(C_338))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.56/2.71  tff(c_2196, plain, (![D_304]: (m1_subset_1(k7_relat_1('#skF_4', D_304), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1699, c_2166])).
% 7.56/2.71  tff(c_2217, plain, (![D_340]: (m1_subset_1(k7_relat_1('#skF_4', D_340), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_2196])).
% 7.56/2.71  tff(c_32, plain, (![C_25, B_24, A_23]: (v5_relat_1(C_25, B_24) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.56/2.71  tff(c_2260, plain, (![D_340]: (v5_relat_1(k7_relat_1('#skF_4', D_340), '#skF_2'))), inference(resolution, [status(thm)], [c_2217, c_32])).
% 7.56/2.71  tff(c_30, plain, (![C_22, A_20, B_21]: (v1_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.56/2.71  tff(c_2261, plain, (![D_340]: (v1_relat_1(k7_relat_1('#skF_4', D_340)))), inference(resolution, [status(thm)], [c_2217, c_30])).
% 7.56/2.71  tff(c_20, plain, (![B_11, A_10]: (r1_tarski(k2_relat_1(B_11), A_10) | ~v5_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.56/2.71  tff(c_1502, plain, (![A_267, B_268, C_269, D_270]: (v1_funct_1(k2_partfun1(A_267, B_268, C_269, D_270)) | ~m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1(A_267, B_268))) | ~v1_funct_1(C_269))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.56/2.71  tff(c_1507, plain, (![D_270]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_270)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_1502])).
% 7.56/2.71  tff(c_1518, plain, (![D_270]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_270)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1507])).
% 7.56/2.71  tff(c_1702, plain, (![D_270]: (v1_funct_1(k7_relat_1('#skF_4', D_270)))), inference(demodulation, [status(thm), theory('equality')], [c_1699, c_1518])).
% 7.56/2.71  tff(c_1205, plain, (![A_228, B_229, C_230]: (k1_relset_1(A_228, B_229, C_230)=k1_relat_1(C_230) | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_228, B_229))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.56/2.71  tff(c_1224, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_1205])).
% 7.56/2.71  tff(c_1859, plain, (![B_315, A_316, C_317]: (k1_xboole_0=B_315 | k1_relset_1(A_316, B_315, C_317)=A_316 | ~v1_funct_2(C_317, A_316, B_315) | ~m1_subset_1(C_317, k1_zfmisc_1(k2_zfmisc_1(A_316, B_315))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.56/2.71  tff(c_1869, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_1859])).
% 7.56/2.71  tff(c_1884, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1224, c_1869])).
% 7.56/2.71  tff(c_1885, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_85, c_1884])).
% 7.56/2.71  tff(c_1901, plain, (![A_18]: (k1_relat_1(k7_relat_1('#skF_4', A_18))=A_18 | ~r1_tarski(A_18, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1885, c_28])).
% 7.56/2.71  tff(c_1909, plain, (![A_18]: (k1_relat_1(k7_relat_1('#skF_4', A_18))=A_18 | ~r1_tarski(A_18, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_818, c_1901])).
% 7.56/2.71  tff(c_1590, plain, (![B_291, A_292]: (m1_subset_1(B_291, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_291), A_292))) | ~r1_tarski(k2_relat_1(B_291), A_292) | ~v1_funct_1(B_291) | ~v1_relat_1(B_291))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.56/2.71  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.56/2.71  tff(c_2483, plain, (![B_381, A_382]: (r1_tarski(B_381, k2_zfmisc_1(k1_relat_1(B_381), A_382)) | ~r1_tarski(k2_relat_1(B_381), A_382) | ~v1_funct_1(B_381) | ~v1_relat_1(B_381))), inference(resolution, [status(thm)], [c_1590, c_12])).
% 7.56/2.71  tff(c_2529, plain, (![A_18, A_382]: (r1_tarski(k7_relat_1('#skF_4', A_18), k2_zfmisc_1(A_18, A_382)) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_18)), A_382) | ~v1_funct_1(k7_relat_1('#skF_4', A_18)) | ~v1_relat_1(k7_relat_1('#skF_4', A_18)) | ~r1_tarski(A_18, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1909, c_2483])).
% 7.56/2.71  tff(c_3478, plain, (![A_503, A_504]: (r1_tarski(k7_relat_1('#skF_4', A_503), k2_zfmisc_1(A_503, A_504)) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_503)), A_504) | ~r1_tarski(A_503, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2261, c_1702, c_2529])).
% 7.56/2.71  tff(c_3484, plain, (![A_503, A_10]: (r1_tarski(k7_relat_1('#skF_4', A_503), k2_zfmisc_1(A_503, A_10)) | ~r1_tarski(A_503, '#skF_1') | ~v5_relat_1(k7_relat_1('#skF_4', A_503), A_10) | ~v1_relat_1(k7_relat_1('#skF_4', A_503)))), inference(resolution, [status(thm)], [c_20, c_3478])).
% 7.56/2.71  tff(c_5027, plain, (![A_618, A_619]: (r1_tarski(k7_relat_1('#skF_4', A_618), k2_zfmisc_1(A_618, A_619)) | ~r1_tarski(A_618, '#skF_1') | ~v5_relat_1(k7_relat_1('#skF_4', A_618), A_619))), inference(demodulation, [status(thm), theory('equality')], [c_2261, c_3484])).
% 7.56/2.71  tff(c_14, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.56/2.71  tff(c_754, plain, (![A_153, B_154, C_155, D_156]: (v1_funct_1(k2_partfun1(A_153, B_154, C_155, D_156)) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))) | ~v1_funct_1(C_155))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.56/2.71  tff(c_759, plain, (![D_156]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_156)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_754])).
% 7.56/2.71  tff(c_770, plain, (![D_156]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_156)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_759])).
% 7.56/2.71  tff(c_62, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.56/2.71  tff(c_150, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_62])).
% 7.56/2.71  tff(c_774, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_770, c_150])).
% 7.56/2.71  tff(c_775, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_62])).
% 7.56/2.71  tff(c_833, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_775])).
% 7.56/2.71  tff(c_914, plain, (~r1_tarski(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_14, c_833])).
% 7.56/2.71  tff(c_1703, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1699, c_914])).
% 7.56/2.71  tff(c_5042, plain, (~r1_tarski('#skF_3', '#skF_1') | ~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_5027, c_1703])).
% 7.56/2.71  tff(c_5075, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2260, c_66, c_5042])).
% 7.56/2.71  tff(c_5077, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_775])).
% 7.56/2.71  tff(c_5561, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_5077, c_5540])).
% 7.56/2.71  tff(c_6262, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6257, c_6257, c_5561])).
% 7.56/2.71  tff(c_5076, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_775])).
% 7.56/2.71  tff(c_6269, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6257, c_5076])).
% 7.56/2.71  tff(c_6268, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6257, c_5077])).
% 7.56/2.71  tff(c_44, plain, (![B_30, C_31, A_29]: (k1_xboole_0=B_30 | v1_funct_2(C_31, A_29, B_30) | k1_relset_1(A_29, B_30, C_31)!=A_29 | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.56/2.71  tff(c_6330, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_6268, c_44])).
% 7.56/2.71  tff(c_6354, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_6269, c_85, c_6330])).
% 7.56/2.71  tff(c_6388, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6262, c_6354])).
% 7.56/2.71  tff(c_6467, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6461, c_6388])).
% 7.56/2.71  tff(c_6492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_6467])).
% 7.56/2.71  tff(c_6493, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_64])).
% 7.56/2.71  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.56/2.71  tff(c_6495, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6493, c_6493, c_6])).
% 7.56/2.71  tff(c_6494, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_64])).
% 7.56/2.71  tff(c_6500, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6493, c_6494])).
% 7.56/2.71  tff(c_6543, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6495, c_6500, c_68])).
% 7.56/2.71  tff(c_6583, plain, (![A_795, B_796]: (r1_tarski(A_795, B_796) | ~m1_subset_1(A_795, k1_zfmisc_1(B_796)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.56/2.71  tff(c_6594, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_6543, c_6583])).
% 7.56/2.71  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.56/2.71  tff(c_6537, plain, (![A_1]: (A_1='#skF_1' | ~r1_tarski(A_1, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6493, c_6493, c_2])).
% 7.56/2.71  tff(c_6599, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_6594, c_6537])).
% 7.56/2.71  tff(c_6501, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6500, c_70])).
% 7.56/2.71  tff(c_7338, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6599, c_6599, c_6501])).
% 7.56/2.71  tff(c_10, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.56/2.71  tff(c_6516, plain, (![A_4]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_6493, c_10])).
% 7.56/2.71  tff(c_6595, plain, (![A_4]: (r1_tarski('#skF_1', A_4))), inference(resolution, [status(thm)], [c_6516, c_6583])).
% 7.56/2.71  tff(c_7364, plain, (![A_4]: (r1_tarski('#skF_4', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_6599, c_6595])).
% 7.56/2.71  tff(c_6513, plain, (![A_782, B_783]: (v1_relat_1(k2_zfmisc_1(A_782, B_783)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.56/2.71  tff(c_6515, plain, (v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6495, c_6513])).
% 7.56/2.71  tff(c_6557, plain, (![B_790, A_791]: (r1_tarski(k7_relat_1(B_790, A_791), B_790) | ~v1_relat_1(B_790))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.56/2.71  tff(c_6561, plain, (![A_791]: (k7_relat_1('#skF_1', A_791)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_6557, c_6537])).
% 7.56/2.71  tff(c_6564, plain, (![A_791]: (k7_relat_1('#skF_1', A_791)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6515, c_6561])).
% 7.56/2.71  tff(c_7329, plain, (![A_791]: (k7_relat_1('#skF_4', A_791)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6599, c_6599, c_6564])).
% 7.56/2.71  tff(c_7337, plain, (![A_4]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_6599, c_6516])).
% 7.56/2.71  tff(c_8277, plain, (![A_1053, B_1054, C_1055, D_1056]: (k2_partfun1(A_1053, B_1054, C_1055, D_1056)=k7_relat_1(C_1055, D_1056) | ~m1_subset_1(C_1055, k1_zfmisc_1(k2_zfmisc_1(A_1053, B_1054))) | ~v1_funct_1(C_1055))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.56/2.71  tff(c_8282, plain, (![A_1053, B_1054, D_1056]: (k2_partfun1(A_1053, B_1054, '#skF_4', D_1056)=k7_relat_1('#skF_4', D_1056) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_7337, c_8277])).
% 7.56/2.71  tff(c_8293, plain, (![A_1053, B_1054, D_1056]: (k2_partfun1(A_1053, B_1054, '#skF_4', D_1056)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_7329, c_8282])).
% 7.56/2.71  tff(c_6611, plain, (![A_4]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_6599, c_6516])).
% 7.56/2.71  tff(c_7308, plain, (![A_903, B_904, C_905, D_906]: (v1_funct_1(k2_partfun1(A_903, B_904, C_905, D_906)) | ~m1_subset_1(C_905, k1_zfmisc_1(k2_zfmisc_1(A_903, B_904))) | ~v1_funct_1(C_905))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.56/2.71  tff(c_7311, plain, (![A_903, B_904, D_906]: (v1_funct_1(k2_partfun1(A_903, B_904, '#skF_4', D_906)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_6611, c_7308])).
% 7.56/2.71  tff(c_7321, plain, (![A_903, B_904, D_906]: (v1_funct_1(k2_partfun1(A_903, B_904, '#skF_4', D_906)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_7311])).
% 7.56/2.71  tff(c_6538, plain, (![A_786]: (A_786='#skF_1' | ~r1_tarski(A_786, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6493, c_6493, c_2])).
% 7.56/2.71  tff(c_6542, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_66, c_6538])).
% 7.56/2.71  tff(c_6600, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6542, c_6500, c_6542, c_6542, c_6500, c_6500, c_6542, c_6495, c_6500, c_6500, c_62])).
% 7.56/2.71  tff(c_6601, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_6600])).
% 7.56/2.71  tff(c_6735, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6599, c_6599, c_6599, c_6601])).
% 7.56/2.71  tff(c_7325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7321, c_6735])).
% 7.56/2.71  tff(c_7326, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_6600])).
% 7.56/2.71  tff(c_7462, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6599, c_6599, c_6599, c_6599, c_6599, c_6599, c_6599, c_6599, c_6599, c_7326])).
% 7.56/2.71  tff(c_7463, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_7462])).
% 7.56/2.71  tff(c_7547, plain, (~r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_14, c_7463])).
% 7.56/2.71  tff(c_8296, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8293, c_7547])).
% 7.56/2.71  tff(c_8301, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7364, c_8296])).
% 7.56/2.71  tff(c_8303, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_7462])).
% 7.56/2.71  tff(c_8468, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_8303, c_12])).
% 7.56/2.71  tff(c_7334, plain, (![A_1]: (A_1='#skF_4' | ~r1_tarski(A_1, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6599, c_6599, c_6537])).
% 7.56/2.71  tff(c_8478, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_8468, c_7334])).
% 7.56/2.71  tff(c_8302, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_7462])).
% 7.56/2.71  tff(c_8482, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8478, c_8302])).
% 7.56/2.71  tff(c_8489, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7338, c_8482])).
% 7.56/2.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.56/2.71  
% 7.56/2.71  Inference rules
% 7.56/2.71  ----------------------
% 7.56/2.71  #Ref     : 0
% 7.56/2.71  #Sup     : 1775
% 7.56/2.71  #Fact    : 0
% 7.56/2.71  #Define  : 0
% 7.56/2.71  #Split   : 10
% 7.56/2.71  #Chain   : 0
% 7.56/2.71  #Close   : 0
% 7.56/2.71  
% 7.56/2.71  Ordering : KBO
% 7.56/2.71  
% 7.56/2.71  Simplification rules
% 7.56/2.71  ----------------------
% 7.56/2.71  #Subsume      : 311
% 7.56/2.71  #Demod        : 2131
% 7.56/2.71  #Tautology    : 704
% 7.56/2.71  #SimpNegUnit  : 19
% 7.56/2.71  #BackRed      : 63
% 7.56/2.71  
% 7.56/2.71  #Partial instantiations: 0
% 7.56/2.71  #Strategies tried      : 1
% 7.56/2.71  
% 7.56/2.71  Timing (in seconds)
% 7.56/2.71  ----------------------
% 7.56/2.71  Preprocessing        : 0.33
% 7.56/2.71  Parsing              : 0.17
% 7.56/2.71  CNF conversion       : 0.02
% 7.56/2.71  Main loop            : 1.47
% 7.56/2.71  Inferencing          : 0.51
% 7.56/2.71  Reduction            : 0.54
% 7.56/2.71  Demodulation         : 0.39
% 7.56/2.71  BG Simplification    : 0.05
% 7.56/2.72  Subsumption          : 0.26
% 7.56/2.72  Abstraction          : 0.06
% 7.56/2.72  MUC search           : 0.00
% 7.56/2.72  Cooper               : 0.00
% 7.56/2.72  Total                : 1.85
% 7.56/2.72  Index Insertion      : 0.00
% 7.79/2.72  Index Deletion       : 0.00
% 7.79/2.72  Index Matching       : 0.00
% 7.79/2.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
