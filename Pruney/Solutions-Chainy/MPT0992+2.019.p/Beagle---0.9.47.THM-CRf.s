%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:34 EST 2020

% Result     : Theorem 36.60s
% Output     : CNFRefutation 36.98s
% Verified   : 
% Statistics : Number of formulae       :  234 (2982 expanded)
%              Number of leaves         :   43 ( 976 expanded)
%              Depth                    :   21
%              Number of atoms          :  414 (9563 expanded)
%              Number of equality atoms :  102 (2875 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_159,negated_conjecture,(
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

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_113,axiom,(
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

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_127,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_121,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_139,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_64,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_74,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_130123,plain,(
    ! [C_2204,A_2205,B_2206] :
      ( v1_relat_1(C_2204)
      | ~ m1_subset_1(C_2204,k1_zfmisc_1(k2_zfmisc_1(A_2205,B_2206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_130135,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_130123])).

tff(c_72,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_117,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_78,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_130519,plain,(
    ! [A_2249,B_2250,C_2251] :
      ( k1_relset_1(A_2249,B_2250,C_2251) = k1_relat_1(C_2251)
      | ~ m1_subset_1(C_2251,k1_zfmisc_1(k2_zfmisc_1(A_2249,B_2250))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_130537,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_130519])).

tff(c_130937,plain,(
    ! [B_2301,A_2302,C_2303] :
      ( k1_xboole_0 = B_2301
      | k1_relset_1(A_2302,B_2301,C_2303) = A_2302
      | ~ v1_funct_2(C_2303,A_2302,B_2301)
      | ~ m1_subset_1(C_2303,k1_zfmisc_1(k2_zfmisc_1(A_2302,B_2301))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_130946,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_130937])).

tff(c_130963,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_130537,c_130946])).

tff(c_130964,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_130963])).

tff(c_32,plain,(
    ! [B_18,A_17] :
      ( k1_relat_1(k7_relat_1(B_18,A_17)) = A_17
      | ~ r1_tarski(A_17,k1_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_130981,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130964,c_32])).

tff(c_131037,plain,(
    ! [A_2306] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_2306)) = A_2306
      | ~ r1_tarski(A_2306,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130135,c_130981])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_130793,plain,(
    ! [A_2287,B_2288,C_2289,D_2290] :
      ( k2_partfun1(A_2287,B_2288,C_2289,D_2290) = k7_relat_1(C_2289,D_2290)
      | ~ m1_subset_1(C_2289,k1_zfmisc_1(k2_zfmisc_1(A_2287,B_2288)))
      | ~ v1_funct_1(C_2289) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_130799,plain,(
    ! [D_2290] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_2290) = k7_relat_1('#skF_4',D_2290)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_130793])).

tff(c_130813,plain,(
    ! [D_2290] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_2290) = k7_relat_1('#skF_4',D_2290) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_130799])).

tff(c_2273,plain,(
    ! [A_291,B_292,C_293,D_294] :
      ( k2_partfun1(A_291,B_292,C_293,D_294) = k7_relat_1(C_293,D_294)
      | ~ m1_subset_1(C_293,k1_zfmisc_1(k2_zfmisc_1(A_291,B_292)))
      | ~ v1_funct_1(C_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2277,plain,(
    ! [D_294] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_294) = k7_relat_1('#skF_4',D_294)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_2273])).

tff(c_2288,plain,(
    ! [D_294] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_294) = k7_relat_1('#skF_4',D_294) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2277])).

tff(c_2069,plain,(
    ! [A_263,B_264,C_265,D_266] :
      ( v1_funct_1(k2_partfun1(A_263,B_264,C_265,D_266))
      | ~ m1_subset_1(C_265,k1_zfmisc_1(k2_zfmisc_1(A_263,B_264)))
      | ~ v1_funct_1(C_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2071,plain,(
    ! [D_266] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_266))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_2069])).

tff(c_2081,plain,(
    ! [D_266] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_266)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2071])).

tff(c_2292,plain,(
    ! [D_266] : v1_funct_1(k7_relat_1('#skF_4',D_266)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2288,c_2081])).

tff(c_2614,plain,(
    ! [A_316,B_317,C_318,D_319] :
      ( m1_subset_1(k2_partfun1(A_316,B_317,C_318,D_319),k1_zfmisc_1(k2_zfmisc_1(A_316,B_317)))
      | ~ m1_subset_1(C_318,k1_zfmisc_1(k2_zfmisc_1(A_316,B_317)))
      | ~ v1_funct_1(C_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2647,plain,(
    ! [D_294] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_294),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2288,c_2614])).

tff(c_2667,plain,(
    ! [D_294] : m1_subset_1(k7_relat_1('#skF_4',D_294),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_2647])).

tff(c_2683,plain,(
    ! [D_321] : m1_subset_1(k7_relat_1('#skF_4',D_321),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_2647])).

tff(c_62,plain,(
    ! [A_40,B_41,C_42,D_43] :
      ( k2_partfun1(A_40,B_41,C_42,D_43) = k7_relat_1(C_42,D_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | ~ v1_funct_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2691,plain,(
    ! [D_321,D_43] :
      ( k2_partfun1('#skF_1','#skF_2',k7_relat_1('#skF_4',D_321),D_43) = k7_relat_1(k7_relat_1('#skF_4',D_321),D_43)
      | ~ v1_funct_1(k7_relat_1('#skF_4',D_321)) ) ),
    inference(resolution,[status(thm)],[c_2683,c_62])).

tff(c_3581,plain,(
    ! [D_414,D_415] : k2_partfun1('#skF_1','#skF_2',k7_relat_1('#skF_4',D_414),D_415) = k7_relat_1(k7_relat_1('#skF_4',D_414),D_415) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2292,c_2691])).

tff(c_58,plain,(
    ! [A_36,B_37,C_38,D_39] :
      ( m1_subset_1(k2_partfun1(A_36,B_37,C_38,D_39),k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_3587,plain,(
    ! [D_414,D_415] :
      ( m1_subset_1(k7_relat_1(k7_relat_1('#skF_4',D_414),D_415),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1(k7_relat_1('#skF_4',D_414),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1(k7_relat_1('#skF_4',D_414)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3581,c_58])).

tff(c_3666,plain,(
    ! [D_422,D_423] : m1_subset_1(k7_relat_1(k7_relat_1('#skF_4',D_422),D_423),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2292,c_2667,c_3587])).

tff(c_38,plain,(
    ! [C_25,B_24,A_23] :
      ( v5_relat_1(C_25,B_24)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3731,plain,(
    ! [D_422,D_423] : v5_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_422),D_423),'#skF_2') ),
    inference(resolution,[status(thm)],[c_3666,c_38])).

tff(c_2725,plain,(
    ! [D_321,D_43] : k2_partfun1('#skF_1','#skF_2',k7_relat_1('#skF_4',D_321),D_43) = k7_relat_1(k7_relat_1('#skF_4',D_321),D_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2292,c_2691])).

tff(c_36,plain,(
    ! [C_22,A_20,B_21] :
      ( v1_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2994,plain,(
    ! [A_341,B_342,C_343,D_344] :
      ( v1_relat_1(k2_partfun1(A_341,B_342,C_343,D_344))
      | ~ m1_subset_1(C_343,k1_zfmisc_1(k2_zfmisc_1(A_341,B_342)))
      | ~ v1_funct_1(C_343) ) ),
    inference(resolution,[status(thm)],[c_2614,c_36])).

tff(c_2996,plain,(
    ! [D_294,D_344] :
      ( v1_relat_1(k2_partfun1('#skF_1','#skF_2',k7_relat_1('#skF_4',D_294),D_344))
      | ~ v1_funct_1(k7_relat_1('#skF_4',D_294)) ) ),
    inference(resolution,[status(thm)],[c_2667,c_2994])).

tff(c_3014,plain,(
    ! [D_294,D_344] : v1_relat_1(k2_partfun1('#skF_1','#skF_2',k7_relat_1('#skF_4',D_294),D_344)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2292,c_2996])).

tff(c_3579,plain,(
    ! [D_294,D_344] : v1_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_294),D_344)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2725,c_3014])).

tff(c_2734,plain,(
    ! [D_321] : v1_relat_1(k7_relat_1('#skF_4',D_321)) ),
    inference(resolution,[status(thm)],[c_2683,c_36])).

tff(c_34,plain,(
    ! [A_19] :
      ( k7_relat_1(A_19,k1_relat_1(A_19)) = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_60,plain,(
    ! [A_36,B_37,C_38,D_39] :
      ( v1_funct_1(k2_partfun1(A_36,B_37,C_38,D_39))
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2693,plain,(
    ! [D_321,D_39] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2',k7_relat_1('#skF_4',D_321),D_39))
      | ~ v1_funct_1(k7_relat_1('#skF_4',D_321)) ) ),
    inference(resolution,[status(thm)],[c_2683,c_60])).

tff(c_2728,plain,(
    ! [D_321,D_39] : v1_funct_1(k2_partfun1('#skF_1','#skF_2',k7_relat_1('#skF_4',D_321),D_39)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2292,c_2693])).

tff(c_3580,plain,(
    ! [D_321,D_39] : v1_funct_1(k7_relat_1(k7_relat_1('#skF_4',D_321),D_39)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2725,c_2728])).

tff(c_10042,plain,(
    ! [B_656,C_658,D_655,A_659,D_657] :
      ( k2_partfun1(A_659,B_656,k2_partfun1(A_659,B_656,C_658,D_657),D_655) = k7_relat_1(k2_partfun1(A_659,B_656,C_658,D_657),D_655)
      | ~ v1_funct_1(k2_partfun1(A_659,B_656,C_658,D_657))
      | ~ m1_subset_1(C_658,k1_zfmisc_1(k2_zfmisc_1(A_659,B_656)))
      | ~ v1_funct_1(C_658) ) ),
    inference(resolution,[status(thm)],[c_2614,c_62])).

tff(c_10058,plain,(
    ! [D_321,D_43,D_655] :
      ( k2_partfun1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2',k7_relat_1('#skF_4',D_321),D_43),D_655) = k7_relat_1(k2_partfun1('#skF_1','#skF_2',k7_relat_1('#skF_4',D_321),D_43),D_655)
      | ~ v1_funct_1(k7_relat_1(k7_relat_1('#skF_4',D_321),D_43))
      | ~ m1_subset_1(k7_relat_1('#skF_4',D_321),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1(k7_relat_1('#skF_4',D_321)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2725,c_10042])).

tff(c_14013,plain,(
    ! [D_731,D_732,D_733] : k2_partfun1('#skF_1','#skF_2',k7_relat_1(k7_relat_1('#skF_4',D_731),D_732),D_733) = k7_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_731),D_732),D_733) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2292,c_2667,c_3580,c_2725,c_2725,c_10058])).

tff(c_14069,plain,(
    ! [D_731,D_733] :
      ( k7_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_731),k1_relat_1(k7_relat_1('#skF_4',D_731))),D_733) = k2_partfun1('#skF_1','#skF_2',k7_relat_1('#skF_4',D_731),D_733)
      | ~ v1_relat_1(k7_relat_1('#skF_4',D_731)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_14013])).

tff(c_20894,plain,(
    ! [D_876,D_877] : k7_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_876),k1_relat_1(k7_relat_1('#skF_4',D_876))),D_877) = k7_relat_1(k7_relat_1('#skF_4',D_876),D_877) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2734,c_2725,c_14069])).

tff(c_10,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_64,plain,(
    ! [B_45,A_44] :
      ( m1_subset_1(B_45,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_45),A_44)))
      | ~ r1_tarski(k2_relat_1(B_45),A_44)
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_6492,plain,(
    ! [B_567,A_568,D_569] :
      ( k2_partfun1(k1_relat_1(B_567),A_568,B_567,D_569) = k7_relat_1(B_567,D_569)
      | ~ r1_tarski(k2_relat_1(B_567),A_568)
      | ~ v1_funct_1(B_567)
      | ~ v1_relat_1(B_567) ) ),
    inference(resolution,[status(thm)],[c_64,c_2273])).

tff(c_6503,plain,(
    ! [B_567,D_569] :
      ( k2_partfun1(k1_relat_1(B_567),k2_relat_1(B_567),B_567,D_569) = k7_relat_1(B_567,D_569)
      | ~ v1_funct_1(B_567)
      | ~ v1_relat_1(B_567) ) ),
    inference(resolution,[status(thm)],[c_10,c_6492])).

tff(c_4128,plain,(
    ! [A_473,B_474,C_475,D_476] :
      ( v5_relat_1(k2_partfun1(A_473,B_474,C_475,D_476),B_474)
      | ~ m1_subset_1(C_475,k1_zfmisc_1(k2_zfmisc_1(A_473,B_474)))
      | ~ v1_funct_1(C_475) ) ),
    inference(resolution,[status(thm)],[c_2614,c_38])).

tff(c_10690,plain,(
    ! [B_676,A_677,D_678] :
      ( v5_relat_1(k2_partfun1(k1_relat_1(B_676),A_677,B_676,D_678),A_677)
      | ~ r1_tarski(k2_relat_1(B_676),A_677)
      | ~ v1_funct_1(B_676)
      | ~ v1_relat_1(B_676) ) ),
    inference(resolution,[status(thm)],[c_64,c_4128])).

tff(c_10756,plain,(
    ! [B_567,D_569] :
      ( v5_relat_1(k7_relat_1(B_567,D_569),k2_relat_1(B_567))
      | ~ r1_tarski(k2_relat_1(B_567),k2_relat_1(B_567))
      | ~ v1_funct_1(B_567)
      | ~ v1_relat_1(B_567)
      | ~ v1_funct_1(B_567)
      | ~ v1_relat_1(B_567) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6503,c_10690])).

tff(c_10811,plain,(
    ! [B_567,D_569] :
      ( v5_relat_1(k7_relat_1(B_567,D_569),k2_relat_1(B_567))
      | ~ v1_funct_1(B_567)
      | ~ v1_relat_1(B_567) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10756])).

tff(c_20984,plain,(
    ! [D_876,D_877] :
      ( v5_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_876),D_877),k2_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_876),k1_relat_1(k7_relat_1('#skF_4',D_876)))))
      | ~ v1_funct_1(k7_relat_1(k7_relat_1('#skF_4',D_876),k1_relat_1(k7_relat_1('#skF_4',D_876))))
      | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_876),k1_relat_1(k7_relat_1('#skF_4',D_876)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20894,c_10811])).

tff(c_23667,plain,(
    ! [D_908,D_909] : v5_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_908),D_909),k2_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_908),k1_relat_1(k7_relat_1('#skF_4',D_908))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3579,c_3580,c_20984])).

tff(c_23779,plain,(
    ! [D_908,D_909] :
      ( v5_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_908),D_909),k2_relat_1(k7_relat_1('#skF_4',D_908)))
      | ~ v1_relat_1(k7_relat_1('#skF_4',D_908)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_23667])).

tff(c_23823,plain,(
    ! [D_908,D_909] : v5_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_908),D_909),k2_relat_1(k7_relat_1('#skF_4',D_908))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2734,c_23779])).

tff(c_23768,plain,(
    ! [D_908] :
      ( v5_relat_1(k7_relat_1('#skF_4',D_908),k2_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_908),k1_relat_1(k7_relat_1('#skF_4',D_908)))))
      | ~ v1_relat_1(k7_relat_1('#skF_4',D_908)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_23667])).

tff(c_25783,plain,(
    ! [D_946] : v5_relat_1(k7_relat_1('#skF_4',D_946),k2_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_946),k1_relat_1(k7_relat_1('#skF_4',D_946))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2734,c_23768])).

tff(c_26,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_839,plain,(
    ! [B_154,A_155] :
      ( r1_tarski(k2_relat_1(B_154),A_155)
      | ~ v5_relat_1(B_154,A_155)
      | ~ v1_relat_1(B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2096,plain,(
    ! [B_272,A_273] :
      ( k2_relat_1(B_272) = A_273
      | ~ r1_tarski(A_273,k2_relat_1(B_272))
      | ~ v5_relat_1(B_272,A_273)
      | ~ v1_relat_1(B_272) ) ),
    inference(resolution,[status(thm)],[c_839,c_6])).

tff(c_2118,plain,(
    ! [B_272,B_12] :
      ( k2_relat_1(B_272) = k2_relat_1(B_12)
      | ~ v5_relat_1(B_272,k2_relat_1(B_12))
      | ~ v1_relat_1(B_272)
      | ~ v5_relat_1(B_12,k2_relat_1(B_272))
      | ~ v1_relat_1(B_12) ) ),
    inference(resolution,[status(thm)],[c_26,c_2096])).

tff(c_25788,plain,(
    ! [D_946] :
      ( k2_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_946),k1_relat_1(k7_relat_1('#skF_4',D_946)))) = k2_relat_1(k7_relat_1('#skF_4',D_946))
      | ~ v1_relat_1(k7_relat_1('#skF_4',D_946))
      | ~ v5_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_946),k1_relat_1(k7_relat_1('#skF_4',D_946))),k2_relat_1(k7_relat_1('#skF_4',D_946)))
      | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_946),k1_relat_1(k7_relat_1('#skF_4',D_946)))) ) ),
    inference(resolution,[status(thm)],[c_25783,c_2118])).

tff(c_25902,plain,(
    ! [D_947] : k2_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_947),k1_relat_1(k7_relat_1('#skF_4',D_947)))) = k2_relat_1(k7_relat_1('#skF_4',D_947)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3579,c_23823,c_2734,c_25788])).

tff(c_25968,plain,(
    ! [D_947,A_11] :
      ( r1_tarski(k2_relat_1(k7_relat_1('#skF_4',D_947)),A_11)
      | ~ v5_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_947),k1_relat_1(k7_relat_1('#skF_4',D_947))),A_11)
      | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_947),k1_relat_1(k7_relat_1('#skF_4',D_947)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25902,c_26])).

tff(c_80014,plain,(
    ! [D_1693,A_1694] :
      ( r1_tarski(k2_relat_1(k7_relat_1('#skF_4',D_1693)),A_1694)
      | ~ v5_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_1693),k1_relat_1(k7_relat_1('#skF_4',D_1693))),A_1694) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3579,c_25968])).

tff(c_80154,plain,(
    ! [D_422] : r1_tarski(k2_relat_1(k7_relat_1('#skF_4',D_422)),'#skF_2') ),
    inference(resolution,[status(thm)],[c_3731,c_80014])).

tff(c_674,plain,(
    ! [C_128,A_129,B_130] :
      ( v1_relat_1(C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_686,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_674])).

tff(c_961,plain,(
    ! [A_170,B_171,C_172] :
      ( k1_relset_1(A_170,B_171,C_172) = k1_relat_1(C_172)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_975,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_961])).

tff(c_2310,plain,(
    ! [B_297,A_298,C_299] :
      ( k1_xboole_0 = B_297
      | k1_relset_1(A_298,B_297,C_299) = A_298
      | ~ v1_funct_2(C_299,A_298,B_297)
      | ~ m1_subset_1(C_299,k1_zfmisc_1(k2_zfmisc_1(A_298,B_297))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2316,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_2310])).

tff(c_2330,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_975,c_2316])).

tff(c_2331,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_2330])).

tff(c_2351,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2331,c_32])).

tff(c_2462,plain,(
    ! [A_308] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_308)) = A_308
      | ~ r1_tarski(A_308,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_686,c_2351])).

tff(c_2471,plain,(
    ! [A_308,A_44] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_308),k1_zfmisc_1(k2_zfmisc_1(A_308,A_44)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_308)),A_44)
      | ~ v1_funct_1(k7_relat_1('#skF_4',A_308))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_308))
      | ~ r1_tarski(A_308,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2462,c_64])).

tff(c_2514,plain,(
    ! [A_308,A_44] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_308),k1_zfmisc_1(k2_zfmisc_1(A_308,A_44)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_308)),A_44)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_308))
      | ~ r1_tarski(A_308,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2292,c_2471])).

tff(c_129988,plain,(
    ! [A_2202,A_2203] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_2202),k1_zfmisc_1(k2_zfmisc_1(A_2202,A_2203)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_2202)),A_2203)
      | ~ r1_tarski(A_2202,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2734,c_2514])).

tff(c_654,plain,(
    ! [A_124,B_125,C_126,D_127] :
      ( v1_funct_1(k2_partfun1(A_124,B_125,C_126,D_127))
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ v1_funct_1(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_656,plain,(
    ! [D_127] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_127))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_654])).

tff(c_666,plain,(
    ! [D_127] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_127)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_656])).

tff(c_70,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_142,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_670,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_666,c_142])).

tff(c_671,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_673,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_671])).

tff(c_2293,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2288,c_673])).

tff(c_130032,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_129988,c_2293])).

tff(c_130120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_80154,c_130032])).

tff(c_130122,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_671])).

tff(c_130536,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_130122,c_130519])).

tff(c_130817,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130813,c_130813,c_130536])).

tff(c_130121,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_671])).

tff(c_130823,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130813,c_130121])).

tff(c_130822,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130813,c_130122])).

tff(c_52,plain,(
    ! [B_34,C_35,A_33] :
      ( k1_xboole_0 = B_34
      | v1_funct_2(C_35,A_33,B_34)
      | k1_relset_1(A_33,B_34,C_35) != A_33
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_130866,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_130822,c_52])).

tff(c_130890,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_130823,c_117,c_130866])).

tff(c_130932,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130817,c_130890])).

tff(c_131043,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_131037,c_130932])).

tff(c_131089,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_131043])).

tff(c_131090,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_16,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_131094,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131090,c_131090,c_16])).

tff(c_131091,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_131101,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131090,c_131091])).

tff(c_131121,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131094,c_131101,c_76])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_131096,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131090,c_2])).

tff(c_18,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_131092,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131090,c_131090,c_18])).

tff(c_132812,plain,(
    ! [C_2505,A_2506,B_2507] :
      ( v1_xboole_0(C_2505)
      | ~ m1_subset_1(C_2505,k1_zfmisc_1(k2_zfmisc_1(A_2506,B_2507)))
      | ~ v1_xboole_0(A_2506) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_132815,plain,(
    ! [C_2505] :
      ( v1_xboole_0(C_2505)
      | ~ m1_subset_1(C_2505,k1_zfmisc_1('#skF_1'))
      | ~ v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131092,c_132812])).

tff(c_132827,plain,(
    ! [C_2508] :
      ( v1_xboole_0(C_2508)
      | ~ m1_subset_1(C_2508,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131096,c_132815])).

tff(c_132841,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_131121,c_132827])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_131093,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131090,c_4])).

tff(c_132845,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_132841,c_131093])).

tff(c_131102,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131101,c_78])).

tff(c_132871,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132845,c_132845,c_131102])).

tff(c_132065,plain,(
    ! [C_2429,A_2430,B_2431] :
      ( v1_xboole_0(C_2429)
      | ~ m1_subset_1(C_2429,k1_zfmisc_1(k2_zfmisc_1(A_2430,B_2431)))
      | ~ v1_xboole_0(A_2430) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_132068,plain,(
    ! [C_2429] :
      ( v1_xboole_0(C_2429)
      | ~ m1_subset_1(C_2429,k1_zfmisc_1('#skF_1'))
      | ~ v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131092,c_132065])).

tff(c_132080,plain,(
    ! [C_2432] :
      ( v1_xboole_0(C_2432)
      | ~ m1_subset_1(C_2432,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131096,c_132068])).

tff(c_132090,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_131121,c_132080])).

tff(c_132094,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_132090,c_131093])).

tff(c_20,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_131122,plain,(
    ! [A_7] : m1_subset_1('#skF_1',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131090,c_20])).

tff(c_132116,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132094,c_131122])).

tff(c_131798,plain,(
    ! [C_2392,A_2393,B_2394] :
      ( v1_relat_1(C_2392)
      | ~ m1_subset_1(C_2392,k1_zfmisc_1(k2_zfmisc_1(A_2393,B_2394))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_131807,plain,(
    v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_131122,c_131798])).

tff(c_131139,plain,(
    ! [A_2312,B_2313] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_2312,B_2313)),A_2312) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_131145,plain,(
    ! [A_5] : r1_tarski(k1_relat_1('#skF_1'),A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_131094,c_131139])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_131095,plain,(
    ! [A_4] : r1_tarski('#skF_1',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131090,c_12])).

tff(c_131831,plain,(
    ! [B_2398,A_2399] :
      ( B_2398 = A_2399
      | ~ r1_tarski(B_2398,A_2399)
      | ~ r1_tarski(A_2399,B_2398) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_131859,plain,(
    ! [A_2400] :
      ( A_2400 = '#skF_1'
      | ~ r1_tarski(A_2400,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_131095,c_131831])).

tff(c_131876,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_131145,c_131859])).

tff(c_131888,plain,
    ( k7_relat_1('#skF_1','#skF_1') = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_131876,c_34])).

tff(c_131892,plain,(
    k7_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131807,c_131888])).

tff(c_132107,plain,(
    k7_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132094,c_132094,c_132094,c_131892])).

tff(c_132638,plain,(
    ! [A_2484,B_2485,C_2486,D_2487] :
      ( k2_partfun1(A_2484,B_2485,C_2486,D_2487) = k7_relat_1(C_2486,D_2487)
      | ~ m1_subset_1(C_2486,k1_zfmisc_1(k2_zfmisc_1(A_2484,B_2485)))
      | ~ v1_funct_1(C_2486) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_132643,plain,(
    ! [A_2484,B_2485,D_2487] :
      ( k2_partfun1(A_2484,B_2485,'#skF_4',D_2487) = k7_relat_1('#skF_4',D_2487)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_132116,c_132638])).

tff(c_132651,plain,(
    ! [A_2484,B_2485,D_2487] : k2_partfun1(A_2484,B_2485,'#skF_4',D_2487) = k7_relat_1('#skF_4',D_2487) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_132643])).

tff(c_131841,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_131831])).

tff(c_131851,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131095,c_131841])).

tff(c_131412,plain,(
    ! [C_2355,A_2356,B_2357] :
      ( v1_xboole_0(C_2355)
      | ~ m1_subset_1(C_2355,k1_zfmisc_1(k2_zfmisc_1(A_2356,B_2357)))
      | ~ v1_xboole_0(A_2356) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_131415,plain,(
    ! [C_2355] :
      ( v1_xboole_0(C_2355)
      | ~ m1_subset_1(C_2355,k1_zfmisc_1('#skF_1'))
      | ~ v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131092,c_131412])).

tff(c_131427,plain,(
    ! [C_2358] :
      ( v1_xboole_0(C_2358)
      | ~ m1_subset_1(C_2358,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131096,c_131415])).

tff(c_131437,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_131121,c_131427])).

tff(c_131441,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_131437,c_131093])).

tff(c_131462,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131441,c_131122])).

tff(c_131782,plain,(
    ! [A_2388,B_2389,C_2390,D_2391] :
      ( v1_funct_1(k2_partfun1(A_2388,B_2389,C_2390,D_2391))
      | ~ m1_subset_1(C_2390,k1_zfmisc_1(k2_zfmisc_1(A_2388,B_2389)))
      | ~ v1_funct_1(C_2390) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_131785,plain,(
    ! [A_2388,B_2389,D_2391] :
      ( v1_funct_1(k2_partfun1(A_2388,B_2389,'#skF_4',D_2391))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_131462,c_131782])).

tff(c_131792,plain,(
    ! [A_2388,B_2389,D_2391] : v1_funct_1(k2_partfun1(A_2388,B_2389,'#skF_4',D_2391)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_131785])).

tff(c_131186,plain,(
    ! [B_2323,A_2324] :
      ( B_2323 = A_2324
      | ~ r1_tarski(B_2323,A_2324)
      | ~ r1_tarski(A_2324,B_2323) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_131196,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_131186])).

tff(c_131206,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131095,c_131196])).

tff(c_131163,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131101,c_131101,c_131101,c_131094,c_131101,c_131101,c_70])).

tff(c_131164,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_131163])).

tff(c_131207,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131206,c_131164])).

tff(c_131454,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131441,c_131441,c_131441,c_131207])).

tff(c_131795,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131792,c_131454])).

tff(c_131796,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_131163])).

tff(c_131927,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131851,c_131851,c_131851,c_131796])).

tff(c_131928,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_131927])).

tff(c_132099,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132094,c_132094,c_132094,c_132094,c_131928])).

tff(c_132653,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132651,c_132099])).

tff(c_132656,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132116,c_132107,c_132653])).

tff(c_132658,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_131927])).

tff(c_132838,plain,(
    v1_xboole_0(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_132658,c_132827])).

tff(c_133094,plain,(
    v1_xboole_0(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132845,c_132845,c_132845,c_132838])).

tff(c_132874,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132845,c_131093])).

tff(c_133098,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_133094,c_132874])).

tff(c_132657,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_131927])).

tff(c_132848,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132845,c_132845,c_132845,c_132845,c_132845,c_132657])).

tff(c_133153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132871,c_133098,c_132848])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:21:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 36.60/25.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.60/25.62  
% 36.60/25.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.60/25.62  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 36.60/25.62  
% 36.60/25.62  %Foreground sorts:
% 36.60/25.62  
% 36.60/25.62  
% 36.60/25.62  %Background operators:
% 36.60/25.62  
% 36.60/25.62  
% 36.60/25.62  %Foreground operators:
% 36.60/25.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 36.60/25.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 36.60/25.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 36.60/25.62  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 36.60/25.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 36.60/25.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 36.60/25.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 36.60/25.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 36.60/25.62  tff('#skF_2', type, '#skF_2': $i).
% 36.60/25.62  tff('#skF_3', type, '#skF_3': $i).
% 36.60/25.62  tff('#skF_1', type, '#skF_1': $i).
% 36.60/25.62  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 36.60/25.62  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 36.60/25.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 36.60/25.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 36.60/25.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 36.60/25.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 36.60/25.62  tff('#skF_4', type, '#skF_4': $i).
% 36.60/25.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 36.60/25.62  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 36.60/25.62  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 36.60/25.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 36.60/25.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 36.60/25.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 36.60/25.62  
% 36.98/25.65  tff(f_159, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 36.98/25.65  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 36.98/25.65  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 36.98/25.65  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 36.98/25.65  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 36.98/25.65  tff(f_127, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 36.98/25.65  tff(f_121, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 36.98/25.65  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 36.98/25.65  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 36.98/25.65  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 36.98/25.65  tff(f_139, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 36.98/25.65  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 36.98/25.65  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 36.98/25.65  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 36.98/25.65  tff(f_91, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 36.98/25.65  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 36.98/25.65  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 36.98/25.65  tff(f_64, axiom, (![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_relat_1)).
% 36.98/25.65  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 36.98/25.65  tff(c_74, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 36.98/25.65  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_159])).
% 36.98/25.65  tff(c_130123, plain, (![C_2204, A_2205, B_2206]: (v1_relat_1(C_2204) | ~m1_subset_1(C_2204, k1_zfmisc_1(k2_zfmisc_1(A_2205, B_2206))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 36.98/25.65  tff(c_130135, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_130123])).
% 36.98/25.65  tff(c_72, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_159])).
% 36.98/25.65  tff(c_117, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_72])).
% 36.98/25.65  tff(c_78, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 36.98/25.65  tff(c_130519, plain, (![A_2249, B_2250, C_2251]: (k1_relset_1(A_2249, B_2250, C_2251)=k1_relat_1(C_2251) | ~m1_subset_1(C_2251, k1_zfmisc_1(k2_zfmisc_1(A_2249, B_2250))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 36.98/25.65  tff(c_130537, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_130519])).
% 36.98/25.65  tff(c_130937, plain, (![B_2301, A_2302, C_2303]: (k1_xboole_0=B_2301 | k1_relset_1(A_2302, B_2301, C_2303)=A_2302 | ~v1_funct_2(C_2303, A_2302, B_2301) | ~m1_subset_1(C_2303, k1_zfmisc_1(k2_zfmisc_1(A_2302, B_2301))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 36.98/25.65  tff(c_130946, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_76, c_130937])).
% 36.98/25.65  tff(c_130963, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_130537, c_130946])).
% 36.98/25.65  tff(c_130964, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_117, c_130963])).
% 36.98/25.65  tff(c_32, plain, (![B_18, A_17]: (k1_relat_1(k7_relat_1(B_18, A_17))=A_17 | ~r1_tarski(A_17, k1_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_70])).
% 36.98/25.65  tff(c_130981, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_130964, c_32])).
% 36.98/25.65  tff(c_131037, plain, (![A_2306]: (k1_relat_1(k7_relat_1('#skF_4', A_2306))=A_2306 | ~r1_tarski(A_2306, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_130135, c_130981])).
% 36.98/25.65  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_159])).
% 36.98/25.65  tff(c_130793, plain, (![A_2287, B_2288, C_2289, D_2290]: (k2_partfun1(A_2287, B_2288, C_2289, D_2290)=k7_relat_1(C_2289, D_2290) | ~m1_subset_1(C_2289, k1_zfmisc_1(k2_zfmisc_1(A_2287, B_2288))) | ~v1_funct_1(C_2289))), inference(cnfTransformation, [status(thm)], [f_127])).
% 36.98/25.65  tff(c_130799, plain, (![D_2290]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_2290)=k7_relat_1('#skF_4', D_2290) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_130793])).
% 36.98/25.65  tff(c_130813, plain, (![D_2290]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_2290)=k7_relat_1('#skF_4', D_2290))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_130799])).
% 36.98/25.65  tff(c_2273, plain, (![A_291, B_292, C_293, D_294]: (k2_partfun1(A_291, B_292, C_293, D_294)=k7_relat_1(C_293, D_294) | ~m1_subset_1(C_293, k1_zfmisc_1(k2_zfmisc_1(A_291, B_292))) | ~v1_funct_1(C_293))), inference(cnfTransformation, [status(thm)], [f_127])).
% 36.98/25.65  tff(c_2277, plain, (![D_294]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_294)=k7_relat_1('#skF_4', D_294) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_2273])).
% 36.98/25.65  tff(c_2288, plain, (![D_294]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_294)=k7_relat_1('#skF_4', D_294))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2277])).
% 36.98/25.65  tff(c_2069, plain, (![A_263, B_264, C_265, D_266]: (v1_funct_1(k2_partfun1(A_263, B_264, C_265, D_266)) | ~m1_subset_1(C_265, k1_zfmisc_1(k2_zfmisc_1(A_263, B_264))) | ~v1_funct_1(C_265))), inference(cnfTransformation, [status(thm)], [f_121])).
% 36.98/25.65  tff(c_2071, plain, (![D_266]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_266)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_2069])).
% 36.98/25.65  tff(c_2081, plain, (![D_266]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_266)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2071])).
% 36.98/25.65  tff(c_2292, plain, (![D_266]: (v1_funct_1(k7_relat_1('#skF_4', D_266)))), inference(demodulation, [status(thm), theory('equality')], [c_2288, c_2081])).
% 36.98/25.65  tff(c_2614, plain, (![A_316, B_317, C_318, D_319]: (m1_subset_1(k2_partfun1(A_316, B_317, C_318, D_319), k1_zfmisc_1(k2_zfmisc_1(A_316, B_317))) | ~m1_subset_1(C_318, k1_zfmisc_1(k2_zfmisc_1(A_316, B_317))) | ~v1_funct_1(C_318))), inference(cnfTransformation, [status(thm)], [f_121])).
% 36.98/25.65  tff(c_2647, plain, (![D_294]: (m1_subset_1(k7_relat_1('#skF_4', D_294), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2288, c_2614])).
% 36.98/25.65  tff(c_2667, plain, (![D_294]: (m1_subset_1(k7_relat_1('#skF_4', D_294), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_2647])).
% 36.98/25.65  tff(c_2683, plain, (![D_321]: (m1_subset_1(k7_relat_1('#skF_4', D_321), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_2647])).
% 36.98/25.65  tff(c_62, plain, (![A_40, B_41, C_42, D_43]: (k2_partfun1(A_40, B_41, C_42, D_43)=k7_relat_1(C_42, D_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))) | ~v1_funct_1(C_42))), inference(cnfTransformation, [status(thm)], [f_127])).
% 36.98/25.65  tff(c_2691, plain, (![D_321, D_43]: (k2_partfun1('#skF_1', '#skF_2', k7_relat_1('#skF_4', D_321), D_43)=k7_relat_1(k7_relat_1('#skF_4', D_321), D_43) | ~v1_funct_1(k7_relat_1('#skF_4', D_321)))), inference(resolution, [status(thm)], [c_2683, c_62])).
% 36.98/25.65  tff(c_3581, plain, (![D_414, D_415]: (k2_partfun1('#skF_1', '#skF_2', k7_relat_1('#skF_4', D_414), D_415)=k7_relat_1(k7_relat_1('#skF_4', D_414), D_415))), inference(demodulation, [status(thm), theory('equality')], [c_2292, c_2691])).
% 36.98/25.65  tff(c_58, plain, (![A_36, B_37, C_38, D_39]: (m1_subset_1(k2_partfun1(A_36, B_37, C_38, D_39), k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_1(C_38))), inference(cnfTransformation, [status(thm)], [f_121])).
% 36.98/25.65  tff(c_3587, plain, (![D_414, D_415]: (m1_subset_1(k7_relat_1(k7_relat_1('#skF_4', D_414), D_415), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k7_relat_1('#skF_4', D_414), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1(k7_relat_1('#skF_4', D_414)))), inference(superposition, [status(thm), theory('equality')], [c_3581, c_58])).
% 36.98/25.65  tff(c_3666, plain, (![D_422, D_423]: (m1_subset_1(k7_relat_1(k7_relat_1('#skF_4', D_422), D_423), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_2292, c_2667, c_3587])).
% 36.98/25.65  tff(c_38, plain, (![C_25, B_24, A_23]: (v5_relat_1(C_25, B_24) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 36.98/25.65  tff(c_3731, plain, (![D_422, D_423]: (v5_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_422), D_423), '#skF_2'))), inference(resolution, [status(thm)], [c_3666, c_38])).
% 36.98/25.65  tff(c_2725, plain, (![D_321, D_43]: (k2_partfun1('#skF_1', '#skF_2', k7_relat_1('#skF_4', D_321), D_43)=k7_relat_1(k7_relat_1('#skF_4', D_321), D_43))), inference(demodulation, [status(thm), theory('equality')], [c_2292, c_2691])).
% 36.98/25.65  tff(c_36, plain, (![C_22, A_20, B_21]: (v1_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 36.98/25.65  tff(c_2994, plain, (![A_341, B_342, C_343, D_344]: (v1_relat_1(k2_partfun1(A_341, B_342, C_343, D_344)) | ~m1_subset_1(C_343, k1_zfmisc_1(k2_zfmisc_1(A_341, B_342))) | ~v1_funct_1(C_343))), inference(resolution, [status(thm)], [c_2614, c_36])).
% 36.98/25.65  tff(c_2996, plain, (![D_294, D_344]: (v1_relat_1(k2_partfun1('#skF_1', '#skF_2', k7_relat_1('#skF_4', D_294), D_344)) | ~v1_funct_1(k7_relat_1('#skF_4', D_294)))), inference(resolution, [status(thm)], [c_2667, c_2994])).
% 36.98/25.65  tff(c_3014, plain, (![D_294, D_344]: (v1_relat_1(k2_partfun1('#skF_1', '#skF_2', k7_relat_1('#skF_4', D_294), D_344)))), inference(demodulation, [status(thm), theory('equality')], [c_2292, c_2996])).
% 36.98/25.65  tff(c_3579, plain, (![D_294, D_344]: (v1_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_294), D_344)))), inference(demodulation, [status(thm), theory('equality')], [c_2725, c_3014])).
% 36.98/25.65  tff(c_2734, plain, (![D_321]: (v1_relat_1(k7_relat_1('#skF_4', D_321)))), inference(resolution, [status(thm)], [c_2683, c_36])).
% 36.98/25.65  tff(c_34, plain, (![A_19]: (k7_relat_1(A_19, k1_relat_1(A_19))=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_74])).
% 36.98/25.65  tff(c_60, plain, (![A_36, B_37, C_38, D_39]: (v1_funct_1(k2_partfun1(A_36, B_37, C_38, D_39)) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_1(C_38))), inference(cnfTransformation, [status(thm)], [f_121])).
% 36.98/25.65  tff(c_2693, plain, (![D_321, D_39]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', k7_relat_1('#skF_4', D_321), D_39)) | ~v1_funct_1(k7_relat_1('#skF_4', D_321)))), inference(resolution, [status(thm)], [c_2683, c_60])).
% 36.98/25.65  tff(c_2728, plain, (![D_321, D_39]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', k7_relat_1('#skF_4', D_321), D_39)))), inference(demodulation, [status(thm), theory('equality')], [c_2292, c_2693])).
% 36.98/25.65  tff(c_3580, plain, (![D_321, D_39]: (v1_funct_1(k7_relat_1(k7_relat_1('#skF_4', D_321), D_39)))), inference(demodulation, [status(thm), theory('equality')], [c_2725, c_2728])).
% 36.98/25.65  tff(c_10042, plain, (![B_656, C_658, D_655, A_659, D_657]: (k2_partfun1(A_659, B_656, k2_partfun1(A_659, B_656, C_658, D_657), D_655)=k7_relat_1(k2_partfun1(A_659, B_656, C_658, D_657), D_655) | ~v1_funct_1(k2_partfun1(A_659, B_656, C_658, D_657)) | ~m1_subset_1(C_658, k1_zfmisc_1(k2_zfmisc_1(A_659, B_656))) | ~v1_funct_1(C_658))), inference(resolution, [status(thm)], [c_2614, c_62])).
% 36.98/25.65  tff(c_10058, plain, (![D_321, D_43, D_655]: (k2_partfun1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', k7_relat_1('#skF_4', D_321), D_43), D_655)=k7_relat_1(k2_partfun1('#skF_1', '#skF_2', k7_relat_1('#skF_4', D_321), D_43), D_655) | ~v1_funct_1(k7_relat_1(k7_relat_1('#skF_4', D_321), D_43)) | ~m1_subset_1(k7_relat_1('#skF_4', D_321), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1(k7_relat_1('#skF_4', D_321)))), inference(superposition, [status(thm), theory('equality')], [c_2725, c_10042])).
% 36.98/25.65  tff(c_14013, plain, (![D_731, D_732, D_733]: (k2_partfun1('#skF_1', '#skF_2', k7_relat_1(k7_relat_1('#skF_4', D_731), D_732), D_733)=k7_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_731), D_732), D_733))), inference(demodulation, [status(thm), theory('equality')], [c_2292, c_2667, c_3580, c_2725, c_2725, c_10058])).
% 36.98/25.65  tff(c_14069, plain, (![D_731, D_733]: (k7_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_731), k1_relat_1(k7_relat_1('#skF_4', D_731))), D_733)=k2_partfun1('#skF_1', '#skF_2', k7_relat_1('#skF_4', D_731), D_733) | ~v1_relat_1(k7_relat_1('#skF_4', D_731)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_14013])).
% 36.98/25.65  tff(c_20894, plain, (![D_876, D_877]: (k7_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_876), k1_relat_1(k7_relat_1('#skF_4', D_876))), D_877)=k7_relat_1(k7_relat_1('#skF_4', D_876), D_877))), inference(demodulation, [status(thm), theory('equality')], [c_2734, c_2725, c_14069])).
% 36.98/25.65  tff(c_10, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 36.98/25.65  tff(c_64, plain, (![B_45, A_44]: (m1_subset_1(B_45, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_45), A_44))) | ~r1_tarski(k2_relat_1(B_45), A_44) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_139])).
% 36.98/25.65  tff(c_6492, plain, (![B_567, A_568, D_569]: (k2_partfun1(k1_relat_1(B_567), A_568, B_567, D_569)=k7_relat_1(B_567, D_569) | ~r1_tarski(k2_relat_1(B_567), A_568) | ~v1_funct_1(B_567) | ~v1_relat_1(B_567))), inference(resolution, [status(thm)], [c_64, c_2273])).
% 36.98/25.65  tff(c_6503, plain, (![B_567, D_569]: (k2_partfun1(k1_relat_1(B_567), k2_relat_1(B_567), B_567, D_569)=k7_relat_1(B_567, D_569) | ~v1_funct_1(B_567) | ~v1_relat_1(B_567))), inference(resolution, [status(thm)], [c_10, c_6492])).
% 36.98/25.65  tff(c_4128, plain, (![A_473, B_474, C_475, D_476]: (v5_relat_1(k2_partfun1(A_473, B_474, C_475, D_476), B_474) | ~m1_subset_1(C_475, k1_zfmisc_1(k2_zfmisc_1(A_473, B_474))) | ~v1_funct_1(C_475))), inference(resolution, [status(thm)], [c_2614, c_38])).
% 36.98/25.65  tff(c_10690, plain, (![B_676, A_677, D_678]: (v5_relat_1(k2_partfun1(k1_relat_1(B_676), A_677, B_676, D_678), A_677) | ~r1_tarski(k2_relat_1(B_676), A_677) | ~v1_funct_1(B_676) | ~v1_relat_1(B_676))), inference(resolution, [status(thm)], [c_64, c_4128])).
% 36.98/25.65  tff(c_10756, plain, (![B_567, D_569]: (v5_relat_1(k7_relat_1(B_567, D_569), k2_relat_1(B_567)) | ~r1_tarski(k2_relat_1(B_567), k2_relat_1(B_567)) | ~v1_funct_1(B_567) | ~v1_relat_1(B_567) | ~v1_funct_1(B_567) | ~v1_relat_1(B_567))), inference(superposition, [status(thm), theory('equality')], [c_6503, c_10690])).
% 36.98/25.65  tff(c_10811, plain, (![B_567, D_569]: (v5_relat_1(k7_relat_1(B_567, D_569), k2_relat_1(B_567)) | ~v1_funct_1(B_567) | ~v1_relat_1(B_567))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10756])).
% 36.98/25.65  tff(c_20984, plain, (![D_876, D_877]: (v5_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_876), D_877), k2_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_876), k1_relat_1(k7_relat_1('#skF_4', D_876))))) | ~v1_funct_1(k7_relat_1(k7_relat_1('#skF_4', D_876), k1_relat_1(k7_relat_1('#skF_4', D_876)))) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_876), k1_relat_1(k7_relat_1('#skF_4', D_876)))))), inference(superposition, [status(thm), theory('equality')], [c_20894, c_10811])).
% 36.98/25.65  tff(c_23667, plain, (![D_908, D_909]: (v5_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_908), D_909), k2_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_908), k1_relat_1(k7_relat_1('#skF_4', D_908))))))), inference(demodulation, [status(thm), theory('equality')], [c_3579, c_3580, c_20984])).
% 36.98/25.65  tff(c_23779, plain, (![D_908, D_909]: (v5_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_908), D_909), k2_relat_1(k7_relat_1('#skF_4', D_908))) | ~v1_relat_1(k7_relat_1('#skF_4', D_908)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_23667])).
% 36.98/25.65  tff(c_23823, plain, (![D_908, D_909]: (v5_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_908), D_909), k2_relat_1(k7_relat_1('#skF_4', D_908))))), inference(demodulation, [status(thm), theory('equality')], [c_2734, c_23779])).
% 36.98/25.65  tff(c_23768, plain, (![D_908]: (v5_relat_1(k7_relat_1('#skF_4', D_908), k2_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_908), k1_relat_1(k7_relat_1('#skF_4', D_908))))) | ~v1_relat_1(k7_relat_1('#skF_4', D_908)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_23667])).
% 36.98/25.65  tff(c_25783, plain, (![D_946]: (v5_relat_1(k7_relat_1('#skF_4', D_946), k2_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_946), k1_relat_1(k7_relat_1('#skF_4', D_946))))))), inference(demodulation, [status(thm), theory('equality')], [c_2734, c_23768])).
% 36.98/25.65  tff(c_26, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(B_12), A_11) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 36.98/25.65  tff(c_839, plain, (![B_154, A_155]: (r1_tarski(k2_relat_1(B_154), A_155) | ~v5_relat_1(B_154, A_155) | ~v1_relat_1(B_154))), inference(cnfTransformation, [status(thm)], [f_58])).
% 36.98/25.65  tff(c_6, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 36.98/25.65  tff(c_2096, plain, (![B_272, A_273]: (k2_relat_1(B_272)=A_273 | ~r1_tarski(A_273, k2_relat_1(B_272)) | ~v5_relat_1(B_272, A_273) | ~v1_relat_1(B_272))), inference(resolution, [status(thm)], [c_839, c_6])).
% 36.98/25.65  tff(c_2118, plain, (![B_272, B_12]: (k2_relat_1(B_272)=k2_relat_1(B_12) | ~v5_relat_1(B_272, k2_relat_1(B_12)) | ~v1_relat_1(B_272) | ~v5_relat_1(B_12, k2_relat_1(B_272)) | ~v1_relat_1(B_12))), inference(resolution, [status(thm)], [c_26, c_2096])).
% 36.98/25.65  tff(c_25788, plain, (![D_946]: (k2_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_946), k1_relat_1(k7_relat_1('#skF_4', D_946))))=k2_relat_1(k7_relat_1('#skF_4', D_946)) | ~v1_relat_1(k7_relat_1('#skF_4', D_946)) | ~v5_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_946), k1_relat_1(k7_relat_1('#skF_4', D_946))), k2_relat_1(k7_relat_1('#skF_4', D_946))) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_946), k1_relat_1(k7_relat_1('#skF_4', D_946)))))), inference(resolution, [status(thm)], [c_25783, c_2118])).
% 36.98/25.65  tff(c_25902, plain, (![D_947]: (k2_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_947), k1_relat_1(k7_relat_1('#skF_4', D_947))))=k2_relat_1(k7_relat_1('#skF_4', D_947)))), inference(demodulation, [status(thm), theory('equality')], [c_3579, c_23823, c_2734, c_25788])).
% 36.98/25.65  tff(c_25968, plain, (![D_947, A_11]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', D_947)), A_11) | ~v5_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_947), k1_relat_1(k7_relat_1('#skF_4', D_947))), A_11) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_947), k1_relat_1(k7_relat_1('#skF_4', D_947)))))), inference(superposition, [status(thm), theory('equality')], [c_25902, c_26])).
% 36.98/25.65  tff(c_80014, plain, (![D_1693, A_1694]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', D_1693)), A_1694) | ~v5_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_1693), k1_relat_1(k7_relat_1('#skF_4', D_1693))), A_1694))), inference(demodulation, [status(thm), theory('equality')], [c_3579, c_25968])).
% 36.98/25.65  tff(c_80154, plain, (![D_422]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', D_422)), '#skF_2'))), inference(resolution, [status(thm)], [c_3731, c_80014])).
% 36.98/25.65  tff(c_674, plain, (![C_128, A_129, B_130]: (v1_relat_1(C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 36.98/25.65  tff(c_686, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_674])).
% 36.98/25.65  tff(c_961, plain, (![A_170, B_171, C_172]: (k1_relset_1(A_170, B_171, C_172)=k1_relat_1(C_172) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 36.98/25.65  tff(c_975, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_961])).
% 36.98/25.65  tff(c_2310, plain, (![B_297, A_298, C_299]: (k1_xboole_0=B_297 | k1_relset_1(A_298, B_297, C_299)=A_298 | ~v1_funct_2(C_299, A_298, B_297) | ~m1_subset_1(C_299, k1_zfmisc_1(k2_zfmisc_1(A_298, B_297))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 36.98/25.65  tff(c_2316, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_76, c_2310])).
% 36.98/25.65  tff(c_2330, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_975, c_2316])).
% 36.98/25.65  tff(c_2331, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_117, c_2330])).
% 36.98/25.65  tff(c_2351, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2331, c_32])).
% 36.98/25.65  tff(c_2462, plain, (![A_308]: (k1_relat_1(k7_relat_1('#skF_4', A_308))=A_308 | ~r1_tarski(A_308, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_686, c_2351])).
% 36.98/25.65  tff(c_2471, plain, (![A_308, A_44]: (m1_subset_1(k7_relat_1('#skF_4', A_308), k1_zfmisc_1(k2_zfmisc_1(A_308, A_44))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_308)), A_44) | ~v1_funct_1(k7_relat_1('#skF_4', A_308)) | ~v1_relat_1(k7_relat_1('#skF_4', A_308)) | ~r1_tarski(A_308, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2462, c_64])).
% 36.98/25.65  tff(c_2514, plain, (![A_308, A_44]: (m1_subset_1(k7_relat_1('#skF_4', A_308), k1_zfmisc_1(k2_zfmisc_1(A_308, A_44))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_308)), A_44) | ~v1_relat_1(k7_relat_1('#skF_4', A_308)) | ~r1_tarski(A_308, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2292, c_2471])).
% 36.98/25.65  tff(c_129988, plain, (![A_2202, A_2203]: (m1_subset_1(k7_relat_1('#skF_4', A_2202), k1_zfmisc_1(k2_zfmisc_1(A_2202, A_2203))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_2202)), A_2203) | ~r1_tarski(A_2202, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2734, c_2514])).
% 36.98/25.65  tff(c_654, plain, (![A_124, B_125, C_126, D_127]: (v1_funct_1(k2_partfun1(A_124, B_125, C_126, D_127)) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~v1_funct_1(C_126))), inference(cnfTransformation, [status(thm)], [f_121])).
% 36.98/25.65  tff(c_656, plain, (![D_127]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_127)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_654])).
% 36.98/25.65  tff(c_666, plain, (![D_127]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_127)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_656])).
% 36.98/25.65  tff(c_70, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 36.98/25.65  tff(c_142, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_70])).
% 36.98/25.65  tff(c_670, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_666, c_142])).
% 36.98/25.65  tff(c_671, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_70])).
% 36.98/25.65  tff(c_673, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_671])).
% 36.98/25.65  tff(c_2293, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2288, c_673])).
% 36.98/25.65  tff(c_130032, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_129988, c_2293])).
% 36.98/25.65  tff(c_130120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_80154, c_130032])).
% 36.98/25.65  tff(c_130122, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_671])).
% 36.98/25.65  tff(c_130536, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_130122, c_130519])).
% 36.98/25.65  tff(c_130817, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_130813, c_130813, c_130536])).
% 36.98/25.65  tff(c_130121, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_671])).
% 36.98/25.65  tff(c_130823, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_130813, c_130121])).
% 36.98/25.65  tff(c_130822, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_130813, c_130122])).
% 36.98/25.65  tff(c_52, plain, (![B_34, C_35, A_33]: (k1_xboole_0=B_34 | v1_funct_2(C_35, A_33, B_34) | k1_relset_1(A_33, B_34, C_35)!=A_33 | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 36.98/25.65  tff(c_130866, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_130822, c_52])).
% 36.98/25.65  tff(c_130890, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_130823, c_117, c_130866])).
% 36.98/25.65  tff(c_130932, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_130817, c_130890])).
% 36.98/25.65  tff(c_131043, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_131037, c_130932])).
% 36.98/25.65  tff(c_131089, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_131043])).
% 36.98/25.65  tff(c_131090, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_72])).
% 36.98/25.65  tff(c_16, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 36.98/25.65  tff(c_131094, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_131090, c_131090, c_16])).
% 36.98/25.65  tff(c_131091, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_72])).
% 36.98/25.65  tff(c_131101, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_131090, c_131091])).
% 36.98/25.65  tff(c_131121, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_131094, c_131101, c_76])).
% 36.98/25.65  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 36.98/25.65  tff(c_131096, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_131090, c_2])).
% 36.98/25.65  tff(c_18, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 36.98/25.65  tff(c_131092, plain, (![B_6]: (k2_zfmisc_1('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_131090, c_131090, c_18])).
% 36.98/25.65  tff(c_132812, plain, (![C_2505, A_2506, B_2507]: (v1_xboole_0(C_2505) | ~m1_subset_1(C_2505, k1_zfmisc_1(k2_zfmisc_1(A_2506, B_2507))) | ~v1_xboole_0(A_2506))), inference(cnfTransformation, [status(thm)], [f_91])).
% 36.98/25.65  tff(c_132815, plain, (![C_2505]: (v1_xboole_0(C_2505) | ~m1_subset_1(C_2505, k1_zfmisc_1('#skF_1')) | ~v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_131092, c_132812])).
% 36.98/25.65  tff(c_132827, plain, (![C_2508]: (v1_xboole_0(C_2508) | ~m1_subset_1(C_2508, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_131096, c_132815])).
% 36.98/25.65  tff(c_132841, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_131121, c_132827])).
% 36.98/25.65  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 36.98/25.65  tff(c_131093, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_131090, c_4])).
% 36.98/25.65  tff(c_132845, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_132841, c_131093])).
% 36.98/25.65  tff(c_131102, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_131101, c_78])).
% 36.98/25.65  tff(c_132871, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_132845, c_132845, c_131102])).
% 36.98/25.65  tff(c_132065, plain, (![C_2429, A_2430, B_2431]: (v1_xboole_0(C_2429) | ~m1_subset_1(C_2429, k1_zfmisc_1(k2_zfmisc_1(A_2430, B_2431))) | ~v1_xboole_0(A_2430))), inference(cnfTransformation, [status(thm)], [f_91])).
% 36.98/25.65  tff(c_132068, plain, (![C_2429]: (v1_xboole_0(C_2429) | ~m1_subset_1(C_2429, k1_zfmisc_1('#skF_1')) | ~v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_131092, c_132065])).
% 36.98/25.65  tff(c_132080, plain, (![C_2432]: (v1_xboole_0(C_2432) | ~m1_subset_1(C_2432, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_131096, c_132068])).
% 36.98/25.65  tff(c_132090, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_131121, c_132080])).
% 36.98/25.65  tff(c_132094, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_132090, c_131093])).
% 36.98/25.65  tff(c_20, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 36.98/25.65  tff(c_131122, plain, (![A_7]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_131090, c_20])).
% 36.98/25.65  tff(c_132116, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_132094, c_131122])).
% 36.98/25.65  tff(c_131798, plain, (![C_2392, A_2393, B_2394]: (v1_relat_1(C_2392) | ~m1_subset_1(C_2392, k1_zfmisc_1(k2_zfmisc_1(A_2393, B_2394))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 36.98/25.65  tff(c_131807, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_131122, c_131798])).
% 36.98/25.65  tff(c_131139, plain, (![A_2312, B_2313]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_2312, B_2313)), A_2312))), inference(cnfTransformation, [status(thm)], [f_64])).
% 36.98/25.65  tff(c_131145, plain, (![A_5]: (r1_tarski(k1_relat_1('#skF_1'), A_5))), inference(superposition, [status(thm), theory('equality')], [c_131094, c_131139])).
% 36.98/25.65  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 36.98/25.65  tff(c_131095, plain, (![A_4]: (r1_tarski('#skF_1', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_131090, c_12])).
% 36.98/25.65  tff(c_131831, plain, (![B_2398, A_2399]: (B_2398=A_2399 | ~r1_tarski(B_2398, A_2399) | ~r1_tarski(A_2399, B_2398))), inference(cnfTransformation, [status(thm)], [f_36])).
% 36.98/25.65  tff(c_131859, plain, (![A_2400]: (A_2400='#skF_1' | ~r1_tarski(A_2400, '#skF_1'))), inference(resolution, [status(thm)], [c_131095, c_131831])).
% 36.98/25.65  tff(c_131876, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_131145, c_131859])).
% 36.98/25.65  tff(c_131888, plain, (k7_relat_1('#skF_1', '#skF_1')='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_131876, c_34])).
% 36.98/25.65  tff(c_131892, plain, (k7_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_131807, c_131888])).
% 36.98/25.65  tff(c_132107, plain, (k7_relat_1('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_132094, c_132094, c_132094, c_131892])).
% 36.98/25.65  tff(c_132638, plain, (![A_2484, B_2485, C_2486, D_2487]: (k2_partfun1(A_2484, B_2485, C_2486, D_2487)=k7_relat_1(C_2486, D_2487) | ~m1_subset_1(C_2486, k1_zfmisc_1(k2_zfmisc_1(A_2484, B_2485))) | ~v1_funct_1(C_2486))), inference(cnfTransformation, [status(thm)], [f_127])).
% 36.98/25.65  tff(c_132643, plain, (![A_2484, B_2485, D_2487]: (k2_partfun1(A_2484, B_2485, '#skF_4', D_2487)=k7_relat_1('#skF_4', D_2487) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_132116, c_132638])).
% 36.98/25.65  tff(c_132651, plain, (![A_2484, B_2485, D_2487]: (k2_partfun1(A_2484, B_2485, '#skF_4', D_2487)=k7_relat_1('#skF_4', D_2487))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_132643])).
% 36.98/25.65  tff(c_131841, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_131831])).
% 36.98/25.65  tff(c_131851, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_131095, c_131841])).
% 36.98/25.65  tff(c_131412, plain, (![C_2355, A_2356, B_2357]: (v1_xboole_0(C_2355) | ~m1_subset_1(C_2355, k1_zfmisc_1(k2_zfmisc_1(A_2356, B_2357))) | ~v1_xboole_0(A_2356))), inference(cnfTransformation, [status(thm)], [f_91])).
% 36.98/25.65  tff(c_131415, plain, (![C_2355]: (v1_xboole_0(C_2355) | ~m1_subset_1(C_2355, k1_zfmisc_1('#skF_1')) | ~v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_131092, c_131412])).
% 36.98/25.65  tff(c_131427, plain, (![C_2358]: (v1_xboole_0(C_2358) | ~m1_subset_1(C_2358, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_131096, c_131415])).
% 36.98/25.65  tff(c_131437, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_131121, c_131427])).
% 36.98/25.65  tff(c_131441, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_131437, c_131093])).
% 36.98/25.65  tff(c_131462, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_131441, c_131122])).
% 36.98/25.65  tff(c_131782, plain, (![A_2388, B_2389, C_2390, D_2391]: (v1_funct_1(k2_partfun1(A_2388, B_2389, C_2390, D_2391)) | ~m1_subset_1(C_2390, k1_zfmisc_1(k2_zfmisc_1(A_2388, B_2389))) | ~v1_funct_1(C_2390))), inference(cnfTransformation, [status(thm)], [f_121])).
% 36.98/25.65  tff(c_131785, plain, (![A_2388, B_2389, D_2391]: (v1_funct_1(k2_partfun1(A_2388, B_2389, '#skF_4', D_2391)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_131462, c_131782])).
% 36.98/25.65  tff(c_131792, plain, (![A_2388, B_2389, D_2391]: (v1_funct_1(k2_partfun1(A_2388, B_2389, '#skF_4', D_2391)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_131785])).
% 36.98/25.65  tff(c_131186, plain, (![B_2323, A_2324]: (B_2323=A_2324 | ~r1_tarski(B_2323, A_2324) | ~r1_tarski(A_2324, B_2323))), inference(cnfTransformation, [status(thm)], [f_36])).
% 36.98/25.65  tff(c_131196, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_131186])).
% 36.98/25.65  tff(c_131206, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_131095, c_131196])).
% 36.98/25.65  tff(c_131163, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_131101, c_131101, c_131101, c_131094, c_131101, c_131101, c_70])).
% 36.98/25.65  tff(c_131164, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_131163])).
% 36.98/25.65  tff(c_131207, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_131206, c_131164])).
% 36.98/25.65  tff(c_131454, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_131441, c_131441, c_131441, c_131207])).
% 36.98/25.65  tff(c_131795, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131792, c_131454])).
% 36.98/25.65  tff(c_131796, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_131163])).
% 36.98/25.65  tff(c_131927, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_131851, c_131851, c_131851, c_131796])).
% 36.98/25.65  tff(c_131928, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_131927])).
% 36.98/25.65  tff(c_132099, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_132094, c_132094, c_132094, c_132094, c_131928])).
% 36.98/25.65  tff(c_132653, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_132651, c_132099])).
% 36.98/25.65  tff(c_132656, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132116, c_132107, c_132653])).
% 36.98/25.65  tff(c_132658, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_131927])).
% 36.98/25.65  tff(c_132838, plain, (v1_xboole_0(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_132658, c_132827])).
% 36.98/25.65  tff(c_133094, plain, (v1_xboole_0(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_132845, c_132845, c_132845, c_132838])).
% 36.98/25.65  tff(c_132874, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_132845, c_131093])).
% 36.98/25.65  tff(c_133098, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_133094, c_132874])).
% 36.98/25.65  tff(c_132657, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_131927])).
% 36.98/25.65  tff(c_132848, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_132845, c_132845, c_132845, c_132845, c_132845, c_132657])).
% 36.98/25.65  tff(c_133153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132871, c_133098, c_132848])).
% 36.98/25.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.98/25.65  
% 36.98/25.65  Inference rules
% 36.98/25.65  ----------------------
% 36.98/25.65  #Ref     : 0
% 36.98/25.65  #Sup     : 27805
% 36.98/25.65  #Fact    : 0
% 36.98/25.65  #Define  : 0
% 36.98/25.65  #Split   : 33
% 36.98/25.65  #Chain   : 0
% 36.98/25.65  #Close   : 0
% 36.98/25.65  
% 36.98/25.65  Ordering : KBO
% 36.98/25.65  
% 36.98/25.65  Simplification rules
% 36.98/25.65  ----------------------
% 36.98/25.65  #Subsume      : 9183
% 36.98/25.65  #Demod        : 65611
% 36.98/25.65  #Tautology    : 8846
% 36.98/25.65  #SimpNegUnit  : 790
% 36.98/25.65  #BackRed      : 200
% 36.98/25.65  
% 36.98/25.65  #Partial instantiations: 0
% 36.98/25.65  #Strategies tried      : 1
% 36.98/25.65  
% 36.98/25.65  Timing (in seconds)
% 36.98/25.65  ----------------------
% 36.98/25.65  Preprocessing        : 0.35
% 36.98/25.65  Parsing              : 0.18
% 36.98/25.65  CNF conversion       : 0.02
% 36.98/25.65  Main loop            : 24.41
% 36.98/25.65  Inferencing          : 4.00
% 36.98/25.65  Reduction            : 11.25
% 36.98/25.65  Demodulation         : 9.43
% 36.98/25.65  BG Simplification    : 0.38
% 36.98/25.65  Subsumption          : 7.49
% 36.98/25.65  Abstraction          : 0.75
% 36.98/25.65  MUC search           : 0.00
% 36.98/25.65  Cooper               : 0.00
% 36.98/25.65  Total                : 24.84
% 36.98/25.65  Index Insertion      : 0.00
% 36.98/25.65  Index Deletion       : 0.00
% 36.98/25.65  Index Matching       : 0.00
% 36.98/25.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
