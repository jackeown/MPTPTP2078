%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:24 EST 2020

% Result     : Theorem 7.04s
% Output     : CNFRefutation 7.04s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 469 expanded)
%              Number of leaves         :   41 ( 169 expanded)
%              Depth                    :   17
%              Number of atoms          :  225 ( 929 expanded)
%              Number of equality atoms :   43 ( 147 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_5549,plain,(
    ! [A_602,B_603,C_604] :
      ( k2_relset_1(A_602,B_603,C_604) = k2_relat_1(C_604)
      | ~ m1_subset_1(C_604,k1_zfmisc_1(k2_zfmisc_1(A_602,B_603))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_5586,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_5549])).

tff(c_50,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_5589,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5586,c_50])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_57,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_194,plain,(
    ! [C_83,A_84,B_85] :
      ( v1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_219,plain,(
    ! [A_84,B_85] : v1_relat_1(k2_zfmisc_1(A_84,B_85)) ),
    inference(resolution,[status(thm)],[c_57,c_194])).

tff(c_2026,plain,(
    ! [C_317,A_318,B_319] :
      ( v4_relat_1(C_317,A_318)
      | ~ m1_subset_1(C_317,k1_zfmisc_1(k2_zfmisc_1(A_318,B_319))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2062,plain,(
    ! [A_322,B_323] : v4_relat_1(k2_zfmisc_1(A_322,B_323),A_322) ),
    inference(resolution,[status(thm)],[c_57,c_2026])).

tff(c_28,plain,(
    ! [B_23,A_22] :
      ( k7_relat_1(B_23,A_22) = B_23
      | ~ v4_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2065,plain,(
    ! [A_322,B_323] :
      ( k7_relat_1(k2_zfmisc_1(A_322,B_323),A_322) = k2_zfmisc_1(A_322,B_323)
      | ~ v1_relat_1(k2_zfmisc_1(A_322,B_323)) ) ),
    inference(resolution,[status(thm)],[c_2062,c_28])).

tff(c_2068,plain,(
    ! [A_322,B_323] : k7_relat_1(k2_zfmisc_1(A_322,B_323),A_322) = k2_zfmisc_1(A_322,B_323) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_2065])).

tff(c_26,plain,(
    ! [A_21] :
      ( v1_xboole_0(k2_relat_1(A_21))
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_86,plain,(
    ! [A_64,B_65] :
      ( v1_xboole_0(k2_zfmisc_1(A_64,B_65))
      | ~ v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_100,plain,(
    ! [A_68,B_69] :
      ( k2_zfmisc_1(A_68,B_69) = k1_xboole_0
      | ~ v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_86,c_6])).

tff(c_158,plain,(
    ! [A_79,B_80] :
      ( k2_zfmisc_1(k2_relat_1(A_79),B_80) = k1_xboole_0
      | ~ v1_xboole_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_26,c_100])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( v1_xboole_0(k2_zfmisc_1(A_6,B_7))
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_164,plain,(
    ! [A_79] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k2_relat_1(A_79))
      | ~ v1_xboole_0(A_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_8])).

tff(c_1922,plain,(
    ! [A_302] :
      ( ~ v1_xboole_0(k2_relat_1(A_302))
      | ~ v1_xboole_0(A_302) ) ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_1932,plain,(
    ! [A_21] : ~ v1_xboole_0(A_21) ),
    inference(resolution,[status(thm)],[c_26,c_1922])).

tff(c_1936,plain,(
    ! [A_1] : r2_hidden('#skF_1'(A_1),A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_1932,c_4])).

tff(c_2085,plain,(
    ! [A_332,B_333,C_334] :
      ( r2_hidden(A_332,B_333)
      | ~ r2_hidden(A_332,k1_relat_1(k7_relat_1(C_334,B_333)))
      | ~ v1_relat_1(C_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2215,plain,(
    ! [C_348,B_349] :
      ( r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_348,B_349))),B_349)
      | ~ v1_relat_1(C_348) ) ),
    inference(resolution,[status(thm)],[c_1936,c_2085])).

tff(c_2237,plain,(
    ! [A_322,B_323] :
      ( r2_hidden('#skF_1'(k1_relat_1(k2_zfmisc_1(A_322,B_323))),A_322)
      | ~ v1_relat_1(k2_zfmisc_1(A_322,B_323)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2068,c_2215])).

tff(c_2250,plain,(
    ! [A_350,B_351] : r2_hidden('#skF_1'(k1_relat_1(k2_zfmisc_1(A_350,B_351))),A_350) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_2237])).

tff(c_218,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_194])).

tff(c_2048,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_2026])).

tff(c_2053,plain,
    ( k7_relat_1('#skF_5','#skF_4') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2048,c_28])).

tff(c_2056,plain,(
    k7_relat_1('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_2053])).

tff(c_2088,plain,(
    ! [A_332] :
      ( r2_hidden(A_332,'#skF_4')
      | ~ r2_hidden(A_332,k1_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2056,c_2085])).

tff(c_2098,plain,(
    ! [A_332] :
      ( r2_hidden(A_332,'#skF_4')
      | ~ r2_hidden(A_332,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_2088])).

tff(c_2307,plain,(
    ! [B_355] : r2_hidden('#skF_1'(k1_relat_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_355))),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2250,c_2098])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,B_13)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2311,plain,(
    ! [B_355] : m1_subset_1('#skF_1'(k1_relat_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_355))),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2307,c_16])).

tff(c_2336,plain,(
    ! [A_360,B_361,C_362] :
      ( k1_relset_1(A_360,B_361,C_362) = k1_relat_1(C_362)
      | ~ m1_subset_1(C_362,k1_zfmisc_1(k2_zfmisc_1(A_360,B_361))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2363,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_2336])).

tff(c_48,plain,(
    ! [D_54] :
      ( ~ r2_hidden(D_54,k1_relset_1('#skF_4','#skF_3','#skF_5'))
      | ~ m1_subset_1(D_54,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2273,plain,(
    ! [B_351] : ~ m1_subset_1('#skF_1'(k1_relat_1(k2_zfmisc_1(k1_relset_1('#skF_4','#skF_3','#skF_5'),B_351))),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2250,c_48])).

tff(c_2366,plain,(
    ! [B_351] : ~ m1_subset_1('#skF_1'(k1_relat_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_351))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2363,c_2273])).

tff(c_2373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2311,c_2366])).

tff(c_2374,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_127,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(A_74,B_75)
      | ~ m1_subset_1(A_74,k1_zfmisc_1(B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_148,plain,(
    ! [A_9] : r1_tarski(A_9,A_9) ),
    inference(resolution,[status(thm)],[c_57,c_127])).

tff(c_94,plain,(
    ! [A_64,B_65] :
      ( k2_zfmisc_1(A_64,B_65) = k1_xboole_0
      | ~ v1_xboole_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_86,c_6])).

tff(c_2383,plain,(
    ! [B_65] : k2_zfmisc_1(k1_xboole_0,B_65) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2374,c_94])).

tff(c_5172,plain,(
    ! [C_579,A_580,B_581] :
      ( v4_relat_1(C_579,A_580)
      | ~ m1_subset_1(C_579,k1_zfmisc_1(k2_zfmisc_1(A_580,B_581))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_5203,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_5172])).

tff(c_5208,plain,
    ( k7_relat_1('#skF_5','#skF_4') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_5203,c_28])).

tff(c_5211,plain,(
    k7_relat_1('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_5208])).

tff(c_5242,plain,(
    ! [A_584,B_585,C_586] :
      ( r2_hidden(A_584,B_585)
      | ~ r2_hidden(A_584,k1_relat_1(k7_relat_1(C_586,B_585)))
      | ~ v1_relat_1(C_586) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_5248,plain,(
    ! [A_584] :
      ( r2_hidden(A_584,'#skF_4')
      | ~ r2_hidden(A_584,k1_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5211,c_5242])).

tff(c_5335,plain,(
    ! [A_590] :
      ( r2_hidden(A_590,'#skF_4')
      | ~ r2_hidden(A_590,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_5248])).

tff(c_5345,plain,
    ( r2_hidden('#skF_1'(k1_relat_1('#skF_5')),'#skF_4')
    | v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_5335])).

tff(c_5499,plain,(
    v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_5345])).

tff(c_5510,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5499,c_6])).

tff(c_5849,plain,(
    ! [D_620,B_621,C_622,A_623] :
      ( m1_subset_1(D_620,k1_zfmisc_1(k2_zfmisc_1(B_621,C_622)))
      | ~ r1_tarski(k1_relat_1(D_620),B_621)
      | ~ m1_subset_1(D_620,k1_zfmisc_1(k2_zfmisc_1(A_623,C_622))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_5866,plain,(
    ! [B_621] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(B_621,'#skF_3')))
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_621) ) ),
    inference(resolution,[status(thm)],[c_52,c_5849])).

tff(c_5989,plain,(
    ! [B_634] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(B_634,'#skF_3')))
      | ~ r1_tarski(k1_xboole_0,B_634) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5510,c_5866])).

tff(c_6019,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2383,c_5989])).

tff(c_6037,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_6019])).

tff(c_24,plain,(
    ! [C_20,B_19,A_18] :
      ( ~ v1_xboole_0(C_20)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(C_20))
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6042,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_18,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6037,c_24])).

tff(c_6065,plain,(
    ! [A_635] : ~ r2_hidden(A_635,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2374,c_6042])).

tff(c_6075,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_6065])).

tff(c_71,plain,(
    ! [A_61] :
      ( v1_xboole_0(k2_relat_1(A_61))
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_75,plain,(
    ! [A_61] :
      ( k2_relat_1(A_61) = k1_xboole_0
      | ~ v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_71,c_6])).

tff(c_6083,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6075,c_75])).

tff(c_6092,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5589,c_6083])).

tff(c_6093,plain,(
    r2_hidden('#skF_1'(k1_relat_1('#skF_5')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_5345])).

tff(c_6141,plain,(
    m1_subset_1('#skF_1'(k1_relat_1('#skF_5')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_6093,c_16])).

tff(c_6258,plain,(
    ! [A_645,B_646,C_647] :
      ( k1_relset_1(A_645,B_646,C_647) = k1_relat_1(C_647)
      | ~ m1_subset_1(C_647,k1_zfmisc_1(k2_zfmisc_1(A_645,B_646))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6294,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_6258])).

tff(c_150,plain,(
    ! [D_76] :
      ( ~ r2_hidden(D_76,k1_relset_1('#skF_4','#skF_3','#skF_5'))
      | ~ m1_subset_1(D_76,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_155,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_4','#skF_3','#skF_5')),'#skF_4')
    | v1_xboole_0(k1_relset_1('#skF_4','#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_150])).

tff(c_725,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_4','#skF_3','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_155])).

tff(c_6299,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6294,c_725])).

tff(c_6303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6141,c_6299])).

tff(c_6304,plain,(
    v1_xboole_0(k1_relset_1('#skF_4','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_6316,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6304,c_6])).

tff(c_6317,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6316,c_6304])).

tff(c_9256,plain,(
    ! [A_851,B_852,C_853] :
      ( k1_relset_1(A_851,B_852,C_853) = k1_relat_1(C_853)
      | ~ m1_subset_1(C_853,k1_zfmisc_1(k2_zfmisc_1(A_851,B_852))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_9277,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_9256])).

tff(c_9291,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6316,c_9277])).

tff(c_8674,plain,(
    ! [A_823,B_824,C_825] :
      ( k2_relset_1(A_823,B_824,C_825) = k2_relat_1(C_825)
      | ~ m1_subset_1(C_825,k1_zfmisc_1(k2_zfmisc_1(A_823,B_824))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_8711,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_8674])).

tff(c_8714,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8711,c_50])).

tff(c_6337,plain,(
    ! [B_65] : k2_zfmisc_1(k1_xboole_0,B_65) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6317,c_94])).

tff(c_7788,plain,(
    ! [C_752,A_753,B_754] :
      ( v4_relat_1(C_752,A_753)
      | ~ m1_subset_1(C_752,k1_zfmisc_1(k2_zfmisc_1(A_753,B_754))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_7816,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_7788])).

tff(c_7852,plain,(
    ! [B_759,A_760] :
      ( k7_relat_1(B_759,A_760) = B_759
      | ~ v4_relat_1(B_759,A_760)
      | ~ v1_relat_1(B_759) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_7864,plain,
    ( k7_relat_1('#skF_5','#skF_4') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_7816,c_7852])).

tff(c_7876,plain,(
    k7_relat_1('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_7864])).

tff(c_8264,plain,(
    ! [A_790,B_791,C_792] :
      ( r2_hidden(A_790,B_791)
      | ~ r2_hidden(A_790,k1_relat_1(k7_relat_1(C_792,B_791)))
      | ~ v1_relat_1(C_792) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8273,plain,(
    ! [A_790] :
      ( r2_hidden(A_790,'#skF_4')
      | ~ r2_hidden(A_790,k1_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7876,c_8264])).

tff(c_8320,plain,(
    ! [A_794] :
      ( r2_hidden(A_794,'#skF_4')
      | ~ r2_hidden(A_794,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_8273])).

tff(c_8330,plain,
    ( r2_hidden('#skF_1'(k1_relat_1('#skF_5')),'#skF_4')
    | v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_8320])).

tff(c_8394,plain,(
    v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_8330])).

tff(c_8409,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8394,c_6])).

tff(c_9005,plain,(
    ! [D_841,B_842,C_843,A_844] :
      ( m1_subset_1(D_841,k1_zfmisc_1(k2_zfmisc_1(B_842,C_843)))
      | ~ r1_tarski(k1_relat_1(D_841),B_842)
      | ~ m1_subset_1(D_841,k1_zfmisc_1(k2_zfmisc_1(A_844,C_843))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_9024,plain,(
    ! [B_842] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(B_842,'#skF_3')))
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_842) ) ),
    inference(resolution,[status(thm)],[c_52,c_9005])).

tff(c_9137,plain,(
    ! [B_848] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(B_848,'#skF_3')))
      | ~ r1_tarski(k1_xboole_0,B_848) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8409,c_9024])).

tff(c_9171,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6337,c_9137])).

tff(c_9189,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_9171])).

tff(c_9200,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_18,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_9189,c_24])).

tff(c_9226,plain,(
    ! [A_850] : ~ r2_hidden(A_850,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6317,c_9200])).

tff(c_9236,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_9226])).

tff(c_9244,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9236,c_75])).

tff(c_9253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8714,c_9244])).

tff(c_9255,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_8330])).

tff(c_9300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6317,c_9291,c_9255])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:46:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.04/2.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.04/2.61  
% 7.04/2.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.04/2.61  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 7.04/2.61  
% 7.04/2.61  %Foreground sorts:
% 7.04/2.61  
% 7.04/2.61  
% 7.04/2.61  %Background operators:
% 7.04/2.61  
% 7.04/2.61  
% 7.04/2.61  %Foreground operators:
% 7.04/2.61  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.04/2.61  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.04/2.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.04/2.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.04/2.61  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.04/2.61  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.04/2.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.04/2.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.04/2.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.04/2.61  tff('#skF_5', type, '#skF_5': $i).
% 7.04/2.61  tff('#skF_3', type, '#skF_3': $i).
% 7.04/2.61  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.04/2.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.04/2.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.04/2.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.04/2.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.04/2.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.04/2.61  tff('#skF_4', type, '#skF_4': $i).
% 7.04/2.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.04/2.61  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.04/2.61  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 7.04/2.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.04/2.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.04/2.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.04/2.61  
% 7.04/2.64  tff(f_130, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 7.04/2.64  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.04/2.64  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.04/2.64  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 7.04/2.64  tff(f_43, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 7.04/2.64  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.04/2.64  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.04/2.64  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 7.04/2.64  tff(f_71, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 7.04/2.64  tff(f_39, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 7.04/2.64  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 7.04/2.64  tff(f_85, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 7.04/2.64  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 7.04/2.64  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.04/2.64  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.04/2.64  tff(f_109, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 7.04/2.64  tff(f_67, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 7.04/2.64  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.04/2.64  tff(c_5549, plain, (![A_602, B_603, C_604]: (k2_relset_1(A_602, B_603, C_604)=k2_relat_1(C_604) | ~m1_subset_1(C_604, k1_zfmisc_1(k2_zfmisc_1(A_602, B_603))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.04/2.64  tff(c_5586, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_5549])).
% 7.04/2.64  tff(c_50, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.04/2.64  tff(c_5589, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5586, c_50])).
% 7.04/2.64  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.04/2.64  tff(c_10, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.04/2.64  tff(c_12, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.04/2.64  tff(c_57, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 7.04/2.64  tff(c_194, plain, (![C_83, A_84, B_85]: (v1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.04/2.64  tff(c_219, plain, (![A_84, B_85]: (v1_relat_1(k2_zfmisc_1(A_84, B_85)))), inference(resolution, [status(thm)], [c_57, c_194])).
% 7.04/2.64  tff(c_2026, plain, (![C_317, A_318, B_319]: (v4_relat_1(C_317, A_318) | ~m1_subset_1(C_317, k1_zfmisc_1(k2_zfmisc_1(A_318, B_319))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.04/2.64  tff(c_2062, plain, (![A_322, B_323]: (v4_relat_1(k2_zfmisc_1(A_322, B_323), A_322))), inference(resolution, [status(thm)], [c_57, c_2026])).
% 7.04/2.64  tff(c_28, plain, (![B_23, A_22]: (k7_relat_1(B_23, A_22)=B_23 | ~v4_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.04/2.64  tff(c_2065, plain, (![A_322, B_323]: (k7_relat_1(k2_zfmisc_1(A_322, B_323), A_322)=k2_zfmisc_1(A_322, B_323) | ~v1_relat_1(k2_zfmisc_1(A_322, B_323)))), inference(resolution, [status(thm)], [c_2062, c_28])).
% 7.04/2.64  tff(c_2068, plain, (![A_322, B_323]: (k7_relat_1(k2_zfmisc_1(A_322, B_323), A_322)=k2_zfmisc_1(A_322, B_323))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_2065])).
% 7.04/2.64  tff(c_26, plain, (![A_21]: (v1_xboole_0(k2_relat_1(A_21)) | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.04/2.64  tff(c_86, plain, (![A_64, B_65]: (v1_xboole_0(k2_zfmisc_1(A_64, B_65)) | ~v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.04/2.64  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.04/2.64  tff(c_100, plain, (![A_68, B_69]: (k2_zfmisc_1(A_68, B_69)=k1_xboole_0 | ~v1_xboole_0(A_68))), inference(resolution, [status(thm)], [c_86, c_6])).
% 7.04/2.64  tff(c_158, plain, (![A_79, B_80]: (k2_zfmisc_1(k2_relat_1(A_79), B_80)=k1_xboole_0 | ~v1_xboole_0(A_79))), inference(resolution, [status(thm)], [c_26, c_100])).
% 7.04/2.64  tff(c_8, plain, (![A_6, B_7]: (v1_xboole_0(k2_zfmisc_1(A_6, B_7)) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.04/2.64  tff(c_164, plain, (![A_79]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k2_relat_1(A_79)) | ~v1_xboole_0(A_79))), inference(superposition, [status(thm), theory('equality')], [c_158, c_8])).
% 7.04/2.64  tff(c_1922, plain, (![A_302]: (~v1_xboole_0(k2_relat_1(A_302)) | ~v1_xboole_0(A_302))), inference(splitLeft, [status(thm)], [c_164])).
% 7.04/2.64  tff(c_1932, plain, (![A_21]: (~v1_xboole_0(A_21))), inference(resolution, [status(thm)], [c_26, c_1922])).
% 7.04/2.64  tff(c_1936, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1))), inference(negUnitSimplification, [status(thm)], [c_1932, c_4])).
% 7.04/2.64  tff(c_2085, plain, (![A_332, B_333, C_334]: (r2_hidden(A_332, B_333) | ~r2_hidden(A_332, k1_relat_1(k7_relat_1(C_334, B_333))) | ~v1_relat_1(C_334))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.04/2.64  tff(c_2215, plain, (![C_348, B_349]: (r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_348, B_349))), B_349) | ~v1_relat_1(C_348))), inference(resolution, [status(thm)], [c_1936, c_2085])).
% 7.04/2.64  tff(c_2237, plain, (![A_322, B_323]: (r2_hidden('#skF_1'(k1_relat_1(k2_zfmisc_1(A_322, B_323))), A_322) | ~v1_relat_1(k2_zfmisc_1(A_322, B_323)))), inference(superposition, [status(thm), theory('equality')], [c_2068, c_2215])).
% 7.04/2.64  tff(c_2250, plain, (![A_350, B_351]: (r2_hidden('#skF_1'(k1_relat_1(k2_zfmisc_1(A_350, B_351))), A_350))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_2237])).
% 7.04/2.64  tff(c_218, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_194])).
% 7.04/2.64  tff(c_2048, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_2026])).
% 7.04/2.64  tff(c_2053, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2048, c_28])).
% 7.04/2.64  tff(c_2056, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_218, c_2053])).
% 7.04/2.64  tff(c_2088, plain, (![A_332]: (r2_hidden(A_332, '#skF_4') | ~r2_hidden(A_332, k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2056, c_2085])).
% 7.04/2.64  tff(c_2098, plain, (![A_332]: (r2_hidden(A_332, '#skF_4') | ~r2_hidden(A_332, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_2088])).
% 7.04/2.64  tff(c_2307, plain, (![B_355]: (r2_hidden('#skF_1'(k1_relat_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_355))), '#skF_4'))), inference(resolution, [status(thm)], [c_2250, c_2098])).
% 7.04/2.64  tff(c_16, plain, (![A_12, B_13]: (m1_subset_1(A_12, B_13) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.04/2.64  tff(c_2311, plain, (![B_355]: (m1_subset_1('#skF_1'(k1_relat_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_355))), '#skF_4'))), inference(resolution, [status(thm)], [c_2307, c_16])).
% 7.04/2.64  tff(c_2336, plain, (![A_360, B_361, C_362]: (k1_relset_1(A_360, B_361, C_362)=k1_relat_1(C_362) | ~m1_subset_1(C_362, k1_zfmisc_1(k2_zfmisc_1(A_360, B_361))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.04/2.64  tff(c_2363, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_2336])).
% 7.04/2.64  tff(c_48, plain, (![D_54]: (~r2_hidden(D_54, k1_relset_1('#skF_4', '#skF_3', '#skF_5')) | ~m1_subset_1(D_54, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.04/2.64  tff(c_2273, plain, (![B_351]: (~m1_subset_1('#skF_1'(k1_relat_1(k2_zfmisc_1(k1_relset_1('#skF_4', '#skF_3', '#skF_5'), B_351))), '#skF_4'))), inference(resolution, [status(thm)], [c_2250, c_48])).
% 7.04/2.64  tff(c_2366, plain, (![B_351]: (~m1_subset_1('#skF_1'(k1_relat_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_351))), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2363, c_2273])).
% 7.04/2.64  tff(c_2373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2311, c_2366])).
% 7.04/2.64  tff(c_2374, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_164])).
% 7.04/2.64  tff(c_127, plain, (![A_74, B_75]: (r1_tarski(A_74, B_75) | ~m1_subset_1(A_74, k1_zfmisc_1(B_75)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.04/2.64  tff(c_148, plain, (![A_9]: (r1_tarski(A_9, A_9))), inference(resolution, [status(thm)], [c_57, c_127])).
% 7.04/2.64  tff(c_94, plain, (![A_64, B_65]: (k2_zfmisc_1(A_64, B_65)=k1_xboole_0 | ~v1_xboole_0(A_64))), inference(resolution, [status(thm)], [c_86, c_6])).
% 7.04/2.64  tff(c_2383, plain, (![B_65]: (k2_zfmisc_1(k1_xboole_0, B_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2374, c_94])).
% 7.04/2.64  tff(c_5172, plain, (![C_579, A_580, B_581]: (v4_relat_1(C_579, A_580) | ~m1_subset_1(C_579, k1_zfmisc_1(k2_zfmisc_1(A_580, B_581))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.04/2.64  tff(c_5203, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_5172])).
% 7.04/2.64  tff(c_5208, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_5203, c_28])).
% 7.04/2.64  tff(c_5211, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_218, c_5208])).
% 7.04/2.64  tff(c_5242, plain, (![A_584, B_585, C_586]: (r2_hidden(A_584, B_585) | ~r2_hidden(A_584, k1_relat_1(k7_relat_1(C_586, B_585))) | ~v1_relat_1(C_586))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.04/2.64  tff(c_5248, plain, (![A_584]: (r2_hidden(A_584, '#skF_4') | ~r2_hidden(A_584, k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5211, c_5242])).
% 7.04/2.64  tff(c_5335, plain, (![A_590]: (r2_hidden(A_590, '#skF_4') | ~r2_hidden(A_590, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_5248])).
% 7.04/2.64  tff(c_5345, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_5')), '#skF_4') | v1_xboole_0(k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_4, c_5335])).
% 7.04/2.64  tff(c_5499, plain, (v1_xboole_0(k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_5345])).
% 7.04/2.64  tff(c_5510, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_5499, c_6])).
% 7.04/2.64  tff(c_5849, plain, (![D_620, B_621, C_622, A_623]: (m1_subset_1(D_620, k1_zfmisc_1(k2_zfmisc_1(B_621, C_622))) | ~r1_tarski(k1_relat_1(D_620), B_621) | ~m1_subset_1(D_620, k1_zfmisc_1(k2_zfmisc_1(A_623, C_622))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.04/2.64  tff(c_5866, plain, (![B_621]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(B_621, '#skF_3'))) | ~r1_tarski(k1_relat_1('#skF_5'), B_621))), inference(resolution, [status(thm)], [c_52, c_5849])).
% 7.04/2.64  tff(c_5989, plain, (![B_634]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(B_634, '#skF_3'))) | ~r1_tarski(k1_xboole_0, B_634))), inference(demodulation, [status(thm), theory('equality')], [c_5510, c_5866])).
% 7.04/2.64  tff(c_6019, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2383, c_5989])).
% 7.04/2.64  tff(c_6037, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_6019])).
% 7.04/2.64  tff(c_24, plain, (![C_20, B_19, A_18]: (~v1_xboole_0(C_20) | ~m1_subset_1(B_19, k1_zfmisc_1(C_20)) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.04/2.64  tff(c_6042, plain, (![A_18]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_18, '#skF_5'))), inference(resolution, [status(thm)], [c_6037, c_24])).
% 7.04/2.64  tff(c_6065, plain, (![A_635]: (~r2_hidden(A_635, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2374, c_6042])).
% 7.04/2.64  tff(c_6075, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_6065])).
% 7.04/2.64  tff(c_71, plain, (![A_61]: (v1_xboole_0(k2_relat_1(A_61)) | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.04/2.64  tff(c_75, plain, (![A_61]: (k2_relat_1(A_61)=k1_xboole_0 | ~v1_xboole_0(A_61))), inference(resolution, [status(thm)], [c_71, c_6])).
% 7.04/2.64  tff(c_6083, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_6075, c_75])).
% 7.04/2.64  tff(c_6092, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5589, c_6083])).
% 7.04/2.64  tff(c_6093, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_5')), '#skF_4')), inference(splitRight, [status(thm)], [c_5345])).
% 7.04/2.64  tff(c_6141, plain, (m1_subset_1('#skF_1'(k1_relat_1('#skF_5')), '#skF_4')), inference(resolution, [status(thm)], [c_6093, c_16])).
% 7.04/2.64  tff(c_6258, plain, (![A_645, B_646, C_647]: (k1_relset_1(A_645, B_646, C_647)=k1_relat_1(C_647) | ~m1_subset_1(C_647, k1_zfmisc_1(k2_zfmisc_1(A_645, B_646))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.04/2.64  tff(c_6294, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_6258])).
% 7.04/2.64  tff(c_150, plain, (![D_76]: (~r2_hidden(D_76, k1_relset_1('#skF_4', '#skF_3', '#skF_5')) | ~m1_subset_1(D_76, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.04/2.64  tff(c_155, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_4', '#skF_3', '#skF_5')), '#skF_4') | v1_xboole_0(k1_relset_1('#skF_4', '#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_4, c_150])).
% 7.04/2.64  tff(c_725, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_4', '#skF_3', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_155])).
% 7.04/2.64  tff(c_6299, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6294, c_725])).
% 7.04/2.64  tff(c_6303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6141, c_6299])).
% 7.04/2.64  tff(c_6304, plain, (v1_xboole_0(k1_relset_1('#skF_4', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_155])).
% 7.04/2.64  tff(c_6316, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_6304, c_6])).
% 7.04/2.64  tff(c_6317, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6316, c_6304])).
% 7.04/2.64  tff(c_9256, plain, (![A_851, B_852, C_853]: (k1_relset_1(A_851, B_852, C_853)=k1_relat_1(C_853) | ~m1_subset_1(C_853, k1_zfmisc_1(k2_zfmisc_1(A_851, B_852))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.04/2.64  tff(c_9277, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_9256])).
% 7.04/2.64  tff(c_9291, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6316, c_9277])).
% 7.04/2.64  tff(c_8674, plain, (![A_823, B_824, C_825]: (k2_relset_1(A_823, B_824, C_825)=k2_relat_1(C_825) | ~m1_subset_1(C_825, k1_zfmisc_1(k2_zfmisc_1(A_823, B_824))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.04/2.64  tff(c_8711, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_8674])).
% 7.04/2.64  tff(c_8714, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8711, c_50])).
% 7.04/2.64  tff(c_6337, plain, (![B_65]: (k2_zfmisc_1(k1_xboole_0, B_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6317, c_94])).
% 7.04/2.64  tff(c_7788, plain, (![C_752, A_753, B_754]: (v4_relat_1(C_752, A_753) | ~m1_subset_1(C_752, k1_zfmisc_1(k2_zfmisc_1(A_753, B_754))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.04/2.64  tff(c_7816, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_7788])).
% 7.04/2.64  tff(c_7852, plain, (![B_759, A_760]: (k7_relat_1(B_759, A_760)=B_759 | ~v4_relat_1(B_759, A_760) | ~v1_relat_1(B_759))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.04/2.64  tff(c_7864, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_7816, c_7852])).
% 7.04/2.64  tff(c_7876, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_218, c_7864])).
% 7.04/2.64  tff(c_8264, plain, (![A_790, B_791, C_792]: (r2_hidden(A_790, B_791) | ~r2_hidden(A_790, k1_relat_1(k7_relat_1(C_792, B_791))) | ~v1_relat_1(C_792))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.04/2.64  tff(c_8273, plain, (![A_790]: (r2_hidden(A_790, '#skF_4') | ~r2_hidden(A_790, k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7876, c_8264])).
% 7.04/2.64  tff(c_8320, plain, (![A_794]: (r2_hidden(A_794, '#skF_4') | ~r2_hidden(A_794, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_8273])).
% 7.04/2.64  tff(c_8330, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_5')), '#skF_4') | v1_xboole_0(k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_4, c_8320])).
% 7.04/2.64  tff(c_8394, plain, (v1_xboole_0(k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_8330])).
% 7.04/2.64  tff(c_8409, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_8394, c_6])).
% 7.04/2.64  tff(c_9005, plain, (![D_841, B_842, C_843, A_844]: (m1_subset_1(D_841, k1_zfmisc_1(k2_zfmisc_1(B_842, C_843))) | ~r1_tarski(k1_relat_1(D_841), B_842) | ~m1_subset_1(D_841, k1_zfmisc_1(k2_zfmisc_1(A_844, C_843))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.04/2.64  tff(c_9024, plain, (![B_842]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(B_842, '#skF_3'))) | ~r1_tarski(k1_relat_1('#skF_5'), B_842))), inference(resolution, [status(thm)], [c_52, c_9005])).
% 7.04/2.64  tff(c_9137, plain, (![B_848]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(B_848, '#skF_3'))) | ~r1_tarski(k1_xboole_0, B_848))), inference(demodulation, [status(thm), theory('equality')], [c_8409, c_9024])).
% 7.04/2.64  tff(c_9171, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6337, c_9137])).
% 7.04/2.64  tff(c_9189, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_9171])).
% 7.04/2.64  tff(c_9200, plain, (![A_18]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_18, '#skF_5'))), inference(resolution, [status(thm)], [c_9189, c_24])).
% 7.04/2.64  tff(c_9226, plain, (![A_850]: (~r2_hidden(A_850, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6317, c_9200])).
% 7.04/2.64  tff(c_9236, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_9226])).
% 7.04/2.64  tff(c_9244, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_9236, c_75])).
% 7.04/2.64  tff(c_9253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8714, c_9244])).
% 7.04/2.64  tff(c_9255, plain, (~v1_xboole_0(k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_8330])).
% 7.04/2.64  tff(c_9300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6317, c_9291, c_9255])).
% 7.04/2.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.04/2.64  
% 7.04/2.64  Inference rules
% 7.04/2.64  ----------------------
% 7.04/2.64  #Ref     : 0
% 7.04/2.64  #Sup     : 1930
% 7.04/2.64  #Fact    : 0
% 7.04/2.64  #Define  : 0
% 7.04/2.64  #Split   : 20
% 7.04/2.64  #Chain   : 0
% 7.04/2.64  #Close   : 0
% 7.04/2.64  
% 7.04/2.64  Ordering : KBO
% 7.04/2.64  
% 7.04/2.64  Simplification rules
% 7.04/2.64  ----------------------
% 7.04/2.64  #Subsume      : 308
% 7.04/2.64  #Demod        : 1240
% 7.04/2.64  #Tautology    : 798
% 7.04/2.64  #SimpNegUnit  : 100
% 7.04/2.64  #BackRed      : 110
% 7.04/2.64  
% 7.04/2.64  #Partial instantiations: 0
% 7.04/2.64  #Strategies tried      : 1
% 7.04/2.64  
% 7.04/2.64  Timing (in seconds)
% 7.04/2.64  ----------------------
% 7.04/2.65  Preprocessing        : 0.35
% 7.04/2.65  Parsing              : 0.18
% 7.04/2.65  CNF conversion       : 0.03
% 7.04/2.65  Main loop            : 1.51
% 7.04/2.65  Inferencing          : 0.54
% 7.04/2.65  Reduction            : 0.50
% 7.04/2.65  Demodulation         : 0.34
% 7.04/2.65  BG Simplification    : 0.05
% 7.04/2.65  Subsumption          : 0.28
% 7.04/2.65  Abstraction          : 0.08
% 7.04/2.65  MUC search           : 0.00
% 7.04/2.65  Cooper               : 0.00
% 7.04/2.65  Total                : 1.91
% 7.04/2.65  Index Insertion      : 0.00
% 7.04/2.65  Index Deletion       : 0.00
% 7.04/2.65  Index Matching       : 0.00
% 7.04/2.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
