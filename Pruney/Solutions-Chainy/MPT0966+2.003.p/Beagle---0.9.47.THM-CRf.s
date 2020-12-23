%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:07 EST 2020

% Result     : Theorem 12.66s
% Output     : CNFRefutation 12.98s
% Verified   : 
% Statistics : Number of formulae       :  506 (8362 expanded)
%              Number of leaves         :   35 (2671 expanded)
%              Depth                    :   25
%              Number of atoms          :  966 (23699 expanded)
%              Number of equality atoms :  297 (7418 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(k2_relset_1(A,B,D),C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_62,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_106,axiom,(
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

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_125,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_138,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_125])).

tff(c_33758,plain,(
    ! [C_4460,A_4461,B_4462] :
      ( v4_relat_1(C_4460,A_4461)
      | ~ m1_subset_1(C_4460,k1_zfmisc_1(k2_zfmisc_1(A_4461,B_4462))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_33773,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_33758])).

tff(c_22,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k1_relat_1(B_11),A_10)
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_34048,plain,(
    ! [A_4514,B_4515,C_4516] :
      ( k2_relset_1(A_4514,B_4515,C_4516) = k2_relat_1(C_4516)
      | ~ m1_subset_1(C_4516,k1_zfmisc_1(k2_zfmisc_1(A_4514,B_4515))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34063,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_34048])).

tff(c_58,plain,(
    r1_tarski(k2_relset_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_34065,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34063,c_58])).

tff(c_34119,plain,(
    ! [C_4524,A_4525,B_4526] :
      ( m1_subset_1(C_4524,k1_zfmisc_1(k2_zfmisc_1(A_4525,B_4526)))
      | ~ r1_tarski(k2_relat_1(C_4524),B_4526)
      | ~ r1_tarski(k1_relat_1(C_4524),A_4525)
      | ~ v1_relat_1(C_4524) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3335,plain,(
    ! [C_270,B_271,A_272] :
      ( v5_relat_1(C_270,B_271)
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(A_272,B_271))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3365,plain,(
    ! [C_278,B_279] :
      ( v5_relat_1(C_278,B_279)
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_3335])).

tff(c_3369,plain,(
    ! [A_5,B_279] :
      ( v5_relat_1(A_5,B_279)
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_3365])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3590,plain,(
    ! [A_316,B_317,C_318] :
      ( k1_relset_1(A_316,B_317,C_318) = k1_relat_1(C_318)
      | ~ m1_subset_1(C_318,k1_zfmisc_1(k2_zfmisc_1(A_316,B_317))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3605,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_3590])).

tff(c_8460,plain,(
    ! [B_1869,A_1870,C_1871] :
      ( k1_xboole_0 = B_1869
      | k1_relset_1(A_1870,B_1869,C_1871) = A_1870
      | ~ v1_funct_2(C_1871,A_1870,B_1869)
      | ~ m1_subset_1(C_1871,k1_zfmisc_1(k2_zfmisc_1(A_1870,B_1869))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_8470,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_8460])).

tff(c_8481,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3605,c_8470])).

tff(c_8482,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_8481])).

tff(c_3640,plain,(
    ! [A_325,B_326,C_327] :
      ( k2_relset_1(A_325,B_326,C_327) = k2_relat_1(C_327)
      | ~ m1_subset_1(C_327,k1_zfmisc_1(k2_zfmisc_1(A_325,B_326))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3655,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_3640])).

tff(c_3658,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3655,c_58])).

tff(c_3732,plain,(
    ! [C_338,A_339,B_340] :
      ( m1_subset_1(C_338,k1_zfmisc_1(k2_zfmisc_1(A_339,B_340)))
      | ~ r1_tarski(k2_relat_1(C_338),B_340)
      | ~ r1_tarski(k1_relat_1(C_338),A_339)
      | ~ v1_relat_1(C_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10814,plain,(
    ! [C_2040,A_2041,B_2042] :
      ( r1_tarski(C_2040,k2_zfmisc_1(A_2041,B_2042))
      | ~ r1_tarski(k2_relat_1(C_2040),B_2042)
      | ~ r1_tarski(k1_relat_1(C_2040),A_2041)
      | ~ v1_relat_1(C_2040) ) ),
    inference(resolution,[status(thm)],[c_3732,c_14])).

tff(c_10820,plain,(
    ! [A_2041] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_2041,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_2041)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3658,c_10814])).

tff(c_10835,plain,(
    ! [A_2043] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_2043,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_2043) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_8482,c_10820])).

tff(c_3604,plain,(
    ! [A_316,B_317,A_5] :
      ( k1_relset_1(A_316,B_317,A_5) = k1_relat_1(A_5)
      | ~ r1_tarski(A_5,k2_zfmisc_1(A_316,B_317)) ) ),
    inference(resolution,[status(thm)],[c_16,c_3590])).

tff(c_10841,plain,(
    ! [A_2043] :
      ( k1_relset_1(A_2043,'#skF_3','#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',A_2043) ) ),
    inference(resolution,[status(thm)],[c_10835,c_3604])).

tff(c_10873,plain,(
    ! [A_2044] :
      ( k1_relset_1(A_2044,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_2044) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8482,c_10841])).

tff(c_10878,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_10873])).

tff(c_10832,plain,(
    ! [A_2041] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_2041,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_2041) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_8482,c_10820])).

tff(c_11500,plain,(
    ! [B_2083,A_2084,A_2085] :
      ( k1_xboole_0 = B_2083
      | k1_relset_1(A_2084,B_2083,A_2085) = A_2084
      | ~ v1_funct_2(A_2085,A_2084,B_2083)
      | ~ r1_tarski(A_2085,k2_zfmisc_1(A_2084,B_2083)) ) ),
    inference(resolution,[status(thm)],[c_16,c_8460])).

tff(c_11533,plain,(
    ! [A_2041] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1(A_2041,'#skF_3','#skF_4') = A_2041
      | ~ v1_funct_2('#skF_4',A_2041,'#skF_3')
      | ~ r1_tarski('#skF_1',A_2041) ) ),
    inference(resolution,[status(thm)],[c_10832,c_11500])).

tff(c_11690,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_11533])).

tff(c_75,plain,(
    ! [B_37] : k2_zfmisc_1(k1_xboole_0,B_37) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_79,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_28])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3396,plain,(
    ! [C_287,A_288,B_289] :
      ( v4_relat_1(C_287,A_288)
      | ~ m1_subset_1(C_287,k1_zfmisc_1(k2_zfmisc_1(A_288,B_289))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3421,plain,(
    ! [A_295,A_296,B_297] :
      ( v4_relat_1(A_295,A_296)
      | ~ r1_tarski(A_295,k2_zfmisc_1(A_296,B_297)) ) ),
    inference(resolution,[status(thm)],[c_16,c_3396])).

tff(c_3438,plain,(
    ! [A_298,B_299] : v4_relat_1(k2_zfmisc_1(A_298,B_299),A_298) ),
    inference(resolution,[status(thm)],[c_6,c_3421])).

tff(c_3441,plain,(
    ! [A_3] : v4_relat_1(k1_xboole_0,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_3438])).

tff(c_3942,plain,(
    ! [B_365,A_366,C_367] :
      ( k1_xboole_0 = B_365
      | k1_relset_1(A_366,B_365,C_367) = A_366
      | ~ v1_funct_2(C_367,A_366,B_365)
      | ~ m1_subset_1(C_367,k1_zfmisc_1(k2_zfmisc_1(A_366,B_365))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3952,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_3942])).

tff(c_3963,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3605,c_3952])).

tff(c_3964,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3963])).

tff(c_4977,plain,(
    ! [C_442,A_443,B_444] :
      ( r1_tarski(C_442,k2_zfmisc_1(A_443,B_444))
      | ~ r1_tarski(k2_relat_1(C_442),B_444)
      | ~ r1_tarski(k1_relat_1(C_442),A_443)
      | ~ v1_relat_1(C_442) ) ),
    inference(resolution,[status(thm)],[c_3732,c_14])).

tff(c_4979,plain,(
    ! [A_443] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_443,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_443)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3658,c_4977])).

tff(c_5029,plain,(
    ! [A_445] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_445,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_445) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_3964,c_4979])).

tff(c_5032,plain,(
    ! [A_445] :
      ( k1_relset_1(A_445,'#skF_3','#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',A_445) ) ),
    inference(resolution,[status(thm)],[c_5029,c_3604])).

tff(c_5273,plain,(
    ! [A_449] :
      ( k1_relset_1(A_449,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_449) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3964,c_5032])).

tff(c_5278,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_5273])).

tff(c_4987,plain,(
    ! [A_443] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_443,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_443) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_3964,c_4979])).

tff(c_5433,plain,(
    ! [B_459,A_460,A_461] :
      ( k1_xboole_0 = B_459
      | k1_relset_1(A_460,B_459,A_461) = A_460
      | ~ v1_funct_2(A_461,A_460,B_459)
      | ~ r1_tarski(A_461,k2_zfmisc_1(A_460,B_459)) ) ),
    inference(resolution,[status(thm)],[c_16,c_3942])).

tff(c_5458,plain,(
    ! [A_443] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1(A_443,'#skF_3','#skF_4') = A_443
      | ~ v1_funct_2('#skF_4',A_443,'#skF_3')
      | ~ r1_tarski('#skF_1',A_443) ) ),
    inference(resolution,[status(thm)],[c_4987,c_5433])).

tff(c_5659,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5458])).

tff(c_3414,plain,(
    ! [C_291,A_292] :
      ( v4_relat_1(C_291,A_292)
      | ~ m1_subset_1(C_291,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_3396])).

tff(c_3418,plain,(
    ! [A_5,A_292] :
      ( v4_relat_1(A_5,A_292)
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_3414])).

tff(c_3480,plain,(
    ! [B_304,A_305] :
      ( r1_tarski(k1_relat_1(B_304),A_305)
      | ~ v4_relat_1(B_304,A_305)
      | ~ v1_relat_1(B_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_137,plain,(
    ! [A_5,A_46,B_47] :
      ( v1_relat_1(A_5)
      | ~ r1_tarski(A_5,k2_zfmisc_1(A_46,B_47)) ) ),
    inference(resolution,[status(thm)],[c_16,c_125])).

tff(c_3555,plain,(
    ! [B_310,A_311,B_312] :
      ( v1_relat_1(k1_relat_1(B_310))
      | ~ v4_relat_1(B_310,k2_zfmisc_1(A_311,B_312))
      | ~ v1_relat_1(B_310) ) ),
    inference(resolution,[status(thm)],[c_3480,c_137])).

tff(c_3578,plain,(
    ! [A_5] :
      ( v1_relat_1(k1_relat_1(A_5))
      | ~ v1_relat_1(A_5)
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_3418,c_3555])).

tff(c_3970,plain,
    ( v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3964,c_3578])).

tff(c_3986,plain,
    ( v1_relat_1('#skF_1')
    | ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_3970])).

tff(c_4000,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3986])).

tff(c_5721,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5659,c_4000])).

tff(c_5757,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5659,c_5659,c_10])).

tff(c_5835,plain,(
    ! [A_443] :
      ( r1_tarski('#skF_4','#skF_3')
      | ~ r1_tarski('#skF_1',A_443) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5757,c_4987])).

tff(c_5961,plain,(
    ! [A_486] : ~ r1_tarski('#skF_1',A_486) ),
    inference(negUnitSimplification,[status(thm)],[c_5721,c_5835])).

tff(c_5966,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_5961])).

tff(c_5968,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5458])).

tff(c_3870,plain,(
    ! [B_354,C_355,A_356] :
      ( k1_xboole_0 = B_354
      | v1_funct_2(C_355,A_356,B_354)
      | k1_relset_1(A_356,B_354,C_355) != A_356
      | ~ m1_subset_1(C_355,k1_zfmisc_1(k2_zfmisc_1(A_356,B_354))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_5587,plain,(
    ! [B_471,A_472,A_473] :
      ( k1_xboole_0 = B_471
      | v1_funct_2(A_472,A_473,B_471)
      | k1_relset_1(A_473,B_471,A_472) != A_473
      | ~ r1_tarski(A_472,k2_zfmisc_1(A_473,B_471)) ) ),
    inference(resolution,[status(thm)],[c_16,c_3870])).

tff(c_5612,plain,(
    ! [A_443] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2('#skF_4',A_443,'#skF_3')
      | k1_relset_1(A_443,'#skF_3','#skF_4') != A_443
      | ~ r1_tarski('#skF_1',A_443) ) ),
    inference(resolution,[status(thm)],[c_4987,c_5587])).

tff(c_5970,plain,(
    ! [A_487] :
      ( v1_funct_2('#skF_4',A_487,'#skF_3')
      | k1_relset_1(A_487,'#skF_3','#skF_4') != A_487
      | ~ r1_tarski('#skF_1',A_487) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5968,c_5612])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_54,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_66,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_54])).

tff(c_152,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_5976,plain,
    ( k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_5970,c_152])).

tff(c_5981,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5278,c_5976])).

tff(c_5983,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_3986])).

tff(c_3976,plain,(
    ! [A_10] :
      ( r1_tarski('#skF_1',A_10)
      | ~ v4_relat_1('#skF_4',A_10)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3964,c_22])).

tff(c_6071,plain,(
    ! [A_494] :
      ( r1_tarski('#skF_1',A_494)
      | ~ v4_relat_1('#skF_4',A_494) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_3976])).

tff(c_6078,plain,(
    ! [A_292] :
      ( r1_tarski('#skF_1',A_292)
      | ~ r1_tarski('#skF_4',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_3418,c_6071])).

tff(c_6098,plain,(
    ! [A_495] : r1_tarski('#skF_1',A_495) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5983,c_6078])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6212,plain,(
    ! [A_502] :
      ( A_502 = '#skF_1'
      | ~ r1_tarski(A_502,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6098,c_2])).

tff(c_6515,plain,(
    ! [B_522] :
      ( k1_relat_1(B_522) = '#skF_1'
      | ~ v4_relat_1(B_522,'#skF_1')
      | ~ v1_relat_1(B_522) ) ),
    inference(resolution,[status(thm)],[c_22,c_6212])).

tff(c_6527,plain,
    ( k1_relat_1(k1_xboole_0) = '#skF_1'
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3441,c_6515])).

tff(c_6544,plain,(
    k1_relat_1(k1_xboole_0) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_6527])).

tff(c_42,plain,(
    ! [A_31] :
      ( v1_funct_2(k1_xboole_0,A_31,k1_xboole_0)
      | k1_xboole_0 = A_31
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_31,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_70,plain,(
    ! [A_31] :
      ( v1_funct_2(k1_xboole_0,A_31,k1_xboole_0)
      | k1_xboole_0 = A_31
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_42])).

tff(c_3513,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_3516,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_3513])).

tff(c_3520,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3516])).

tff(c_3522,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_3724,plain,(
    ! [B_336,C_337] :
      ( k1_relset_1(k1_xboole_0,B_336,C_337) = k1_relat_1(C_337)
      | ~ m1_subset_1(C_337,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_3590])).

tff(c_3730,plain,(
    ! [B_336] : k1_relset_1(k1_xboole_0,B_336,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3522,c_3724])).

tff(c_46,plain,(
    ! [C_33,B_32] :
      ( v1_funct_2(C_33,k1_xboole_0,B_32)
      | k1_relset_1(k1_xboole_0,B_32,C_33) != k1_xboole_0
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3694,plain,(
    ! [C_331,B_332] :
      ( v1_funct_2(C_331,k1_xboole_0,B_332)
      | k1_relset_1(k1_xboole_0,B_332,C_331) != k1_xboole_0
      | ~ m1_subset_1(C_331,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_46])).

tff(c_3700,plain,(
    ! [B_332] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_332)
      | k1_relset_1(k1_xboole_0,B_332,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3522,c_3694])).

tff(c_3769,plain,(
    ! [B_332] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_332)
      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3730,c_3700])).

tff(c_3785,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3769])).

tff(c_6612,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6544,c_3785])).

tff(c_6089,plain,(
    ! [A_292] : r1_tarski('#skF_1',A_292) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5983,c_6078])).

tff(c_3372,plain,(
    ! [A_282,B_283,A_284] :
      ( v5_relat_1(A_282,B_283)
      | ~ r1_tarski(A_282,k2_zfmisc_1(A_284,B_283)) ) ),
    inference(resolution,[status(thm)],[c_16,c_3335])).

tff(c_3389,plain,(
    ! [A_285,B_286] : v5_relat_1(k2_zfmisc_1(A_285,B_286),B_286) ),
    inference(resolution,[status(thm)],[c_6,c_3372])).

tff(c_3395,plain,(
    ! [B_4] : v5_relat_1(k1_xboole_0,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_3389])).

tff(c_3445,plain,(
    ! [B_300,A_301] :
      ( r1_tarski(k2_relat_1(B_300),A_301)
      | ~ v5_relat_1(B_300,A_301)
      | ~ v1_relat_1(B_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6281,plain,(
    ! [B_510,A_511] :
      ( k2_relat_1(B_510) = A_511
      | ~ r1_tarski(A_511,k2_relat_1(B_510))
      | ~ v5_relat_1(B_510,A_511)
      | ~ v1_relat_1(B_510) ) ),
    inference(resolution,[status(thm)],[c_3445,c_2])).

tff(c_6305,plain,(
    ! [B_512] :
      ( k2_relat_1(B_512) = '#skF_1'
      | ~ v5_relat_1(B_512,'#skF_1')
      | ~ v1_relat_1(B_512) ) ),
    inference(resolution,[status(thm)],[c_6089,c_6281])).

tff(c_6313,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_1'
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3395,c_6305])).

tff(c_6327,plain,(
    k2_relat_1(k1_xboole_0) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_6313])).

tff(c_7540,plain,(
    ! [C_568,A_569,B_570] :
      ( r1_tarski(C_568,k2_zfmisc_1(A_569,B_570))
      | ~ r1_tarski(k2_relat_1(C_568),B_570)
      | ~ r1_tarski(k1_relat_1(C_568),A_569)
      | ~ v1_relat_1(C_568) ) ),
    inference(resolution,[status(thm)],[c_3732,c_14])).

tff(c_7548,plain,(
    ! [A_569,B_570] :
      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(A_569,B_570))
      | ~ r1_tarski('#skF_1',B_570)
      | ~ r1_tarski(k1_relat_1(k1_xboole_0),A_569)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6327,c_7540])).

tff(c_7563,plain,(
    ! [A_569,B_570] : r1_tarski(k1_xboole_0,k2_zfmisc_1(A_569,B_570)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_6089,c_6544,c_6089,c_7548])).

tff(c_3437,plain,(
    ! [A_296,B_297] : v4_relat_1(k2_zfmisc_1(A_296,B_297),A_296) ),
    inference(resolution,[status(thm)],[c_6,c_3421])).

tff(c_6531,plain,(
    ! [B_297] :
      ( k1_relat_1(k2_zfmisc_1('#skF_1',B_297)) = '#skF_1'
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1',B_297)) ) ),
    inference(resolution,[status(thm)],[c_3437,c_6515])).

tff(c_6547,plain,(
    ! [B_297] : k1_relat_1(k2_zfmisc_1('#skF_1',B_297)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6531])).

tff(c_7134,plain,(
    ! [C_550,B_551] :
      ( m1_subset_1(C_550,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_550),B_551)
      | ~ r1_tarski(k1_relat_1(C_550),k1_xboole_0)
      | ~ v1_relat_1(C_550) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_3732])).

tff(c_7509,plain,(
    ! [C_567] :
      ( m1_subset_1(C_567,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(C_567),k1_xboole_0)
      | ~ v1_relat_1(C_567) ) ),
    inference(resolution,[status(thm)],[c_6,c_7134])).

tff(c_7515,plain,(
    ! [B_297] :
      ( m1_subset_1(k2_zfmisc_1('#skF_1',B_297),k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_1',k1_xboole_0)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1',B_297)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6547,c_7509])).

tff(c_7735,plain,(
    ! [B_584] : m1_subset_1(k2_zfmisc_1('#skF_1',B_584),k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6089,c_7515])).

tff(c_7831,plain,(
    ! [B_590] : r1_tarski(k2_zfmisc_1('#skF_1',B_590),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_7735,c_14])).

tff(c_7853,plain,(
    ! [B_590] :
      ( k2_zfmisc_1('#skF_1',B_590) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1('#skF_1',B_590)) ) ),
    inference(resolution,[status(thm)],[c_7831,c_2])).

tff(c_7895,plain,(
    ! [B_591] : k2_zfmisc_1('#skF_1',B_591) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7563,c_7853])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_7977,plain,(
    ! [B_591] :
      ( k1_xboole_0 = B_591
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7895,c_8])).

tff(c_8015,plain,(
    ! [B_592] : k1_xboole_0 = B_592 ),
    inference(negUnitSimplification,[status(thm)],[c_6612,c_7977])).

tff(c_6549,plain,(
    ! [A_523] :
      ( k2_relat_1(A_523) = '#skF_1'
      | ~ v1_relat_1(A_523)
      | ~ r1_tarski(A_523,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_3369,c_6305])).

tff(c_6556,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_5983,c_6549])).

tff(c_6574,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_6556])).

tff(c_7544,plain,(
    ! [A_569,B_570] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_569,B_570))
      | ~ r1_tarski('#skF_1',B_570)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_569)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6574,c_7540])).

tff(c_7610,plain,(
    ! [A_573,B_574] : r1_tarski('#skF_4',k2_zfmisc_1(A_573,B_574)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_6089,c_3964,c_6089,c_7544])).

tff(c_7613,plain,(
    ! [A_573,B_574] : k1_relset_1(A_573,B_574,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_7610,c_3604])).

tff(c_7636,plain,(
    ! [A_573,B_574] : k1_relset_1(A_573,B_574,'#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3964,c_7613])).

tff(c_8031,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_8015,c_7636])).

tff(c_8457,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6612,c_8031])).

tff(c_8459,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3769])).

tff(c_8527,plain,(
    ! [A_10] :
      ( r1_tarski(k1_xboole_0,A_10)
      | ~ v4_relat_1(k1_xboole_0,A_10)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8459,c_22])).

tff(c_8541,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_3441,c_8527])).

tff(c_11746,plain,(
    ! [A_10] : r1_tarski('#skF_3',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11690,c_8541])).

tff(c_112,plain,(
    ! [B_43,A_44] :
      ( B_43 = A_44
      | ~ r1_tarski(B_43,A_44)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_120,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_58,c_112])).

tff(c_3370,plain,(
    ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_3656,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3655,c_3370])).

tff(c_11832,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11746,c_3656])).

tff(c_11834,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_11533])).

tff(c_8667,plain,(
    ! [B_1879,C_1880,A_1881] :
      ( k1_xboole_0 = B_1879
      | v1_funct_2(C_1880,A_1881,B_1879)
      | k1_relset_1(A_1881,B_1879,C_1880) != A_1881
      | ~ m1_subset_1(C_1880,k1_zfmisc_1(k2_zfmisc_1(A_1881,B_1879))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_12248,plain,(
    ! [B_2102,A_2103,A_2104] :
      ( k1_xboole_0 = B_2102
      | v1_funct_2(A_2103,A_2104,B_2102)
      | k1_relset_1(A_2104,B_2102,A_2103) != A_2104
      | ~ r1_tarski(A_2103,k2_zfmisc_1(A_2104,B_2102)) ) ),
    inference(resolution,[status(thm)],[c_16,c_8667])).

tff(c_12254,plain,(
    ! [A_2041] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2('#skF_4',A_2041,'#skF_3')
      | k1_relset_1(A_2041,'#skF_3','#skF_4') != A_2041
      | ~ r1_tarski('#skF_1',A_2041) ) ),
    inference(resolution,[status(thm)],[c_10832,c_12248])).

tff(c_12325,plain,(
    ! [A_2107] :
      ( v1_funct_2('#skF_4',A_2107,'#skF_3')
      | k1_relset_1(A_2107,'#skF_3','#skF_4') != A_2107
      | ~ r1_tarski('#skF_1',A_2107) ) ),
    inference(negUnitSimplification,[status(thm)],[c_11834,c_12254])).

tff(c_12334,plain,
    ( k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_12325,c_152])).

tff(c_12340,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10878,c_12334])).

tff(c_12341,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_16865,plain,(
    ! [A_2390,B_2391,C_2392] :
      ( k2_relset_1(A_2390,B_2391,C_2392) = k2_relat_1(C_2392)
      | ~ m1_subset_1(C_2392,k1_zfmisc_1(k2_zfmisc_1(A_2390,B_2391))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_16872,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_16865])).

tff(c_16881,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12341,c_16872])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v5_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16888,plain,(
    ! [A_12] :
      ( r1_tarski('#skF_3',A_12)
      | ~ v5_relat_1('#skF_4',A_12)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16881,c_26])).

tff(c_16906,plain,(
    ! [A_2393] :
      ( r1_tarski('#skF_3',A_2393)
      | ~ v5_relat_1('#skF_4',A_2393) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_16888])).

tff(c_16923,plain,(
    ! [B_279] :
      ( r1_tarski('#skF_3',B_279)
      | ~ r1_tarski('#skF_4',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_3369,c_16906])).

tff(c_16942,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_16923])).

tff(c_16817,plain,(
    ! [A_2385,B_2386,C_2387] :
      ( k1_relset_1(A_2385,B_2386,C_2387) = k1_relat_1(C_2387)
      | ~ m1_subset_1(C_2387,k1_zfmisc_1(k2_zfmisc_1(A_2385,B_2386))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_16832,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_16817])).

tff(c_17106,plain,(
    ! [B_2420,A_2421,C_2422] :
      ( k1_xboole_0 = B_2420
      | k1_relset_1(A_2421,B_2420,C_2422) = A_2421
      | ~ v1_funct_2(C_2422,A_2421,B_2420)
      | ~ m1_subset_1(C_2422,k1_zfmisc_1(k2_zfmisc_1(A_2421,B_2420))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_17116,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_17106])).

tff(c_17127,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_16832,c_17116])).

tff(c_17128,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_17127])).

tff(c_16979,plain,(
    ! [C_2402,A_2403,B_2404] :
      ( m1_subset_1(C_2402,k1_zfmisc_1(k2_zfmisc_1(A_2403,B_2404)))
      | ~ r1_tarski(k2_relat_1(C_2402),B_2404)
      | ~ r1_tarski(k1_relat_1(C_2402),A_2403)
      | ~ v1_relat_1(C_2402) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_17838,plain,(
    ! [C_2487,A_2488] :
      ( m1_subset_1(C_2487,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_2487),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_2487),A_2488)
      | ~ v1_relat_1(C_2487) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_16979])).

tff(c_17840,plain,(
    ! [A_2488] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_2488)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16881,c_17838])).

tff(c_17845,plain,(
    ! [A_2488] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski('#skF_1',A_2488) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_17128,c_17840])).

tff(c_17867,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_17845])).

tff(c_3357,plain,(
    ! [B_274,A_275] :
      ( v5_relat_1(B_274,A_275)
      | ~ r1_tarski(k2_relat_1(B_274),A_275)
      | ~ v1_relat_1(B_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3362,plain,(
    ! [B_274] :
      ( v5_relat_1(B_274,k2_relat_1(B_274))
      | ~ v1_relat_1(B_274) ) ),
    inference(resolution,[status(thm)],[c_6,c_3357])).

tff(c_16891,plain,
    ( v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_16881,c_3362])).

tff(c_16902,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_16891])).

tff(c_36,plain,(
    ! [A_22,B_23,C_24] :
      ( k1_relset_1(A_22,B_23,C_24) = k1_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_18687,plain,(
    ! [A_2519,B_2520,C_2521] :
      ( k1_relset_1(A_2519,B_2520,C_2521) = k1_relat_1(C_2521)
      | ~ r1_tarski(k2_relat_1(C_2521),B_2520)
      | ~ r1_tarski(k1_relat_1(C_2521),A_2519)
      | ~ v1_relat_1(C_2521) ) ),
    inference(resolution,[status(thm)],[c_16979,c_36])).

tff(c_18691,plain,(
    ! [A_2519,B_2520] :
      ( k1_relset_1(A_2519,B_2520,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_3',B_2520)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_2519)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16881,c_18687])).

tff(c_18762,plain,(
    ! [A_2523,B_2524] :
      ( k1_relset_1(A_2523,B_2524,'#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_3',B_2524)
      | ~ r1_tarski('#skF_1',A_2523) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_17128,c_17128,c_18691])).

tff(c_19623,plain,(
    ! [A_2550] :
      ( k1_relset_1(A_2550,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_2550) ) ),
    inference(resolution,[status(thm)],[c_6,c_18762])).

tff(c_19628,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_19623])).

tff(c_40,plain,(
    ! [C_30,A_28,B_29] :
      ( m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ r1_tarski(k2_relat_1(C_30),B_29)
      | ~ r1_tarski(k1_relat_1(C_30),A_28)
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_17228,plain,(
    ! [B_2430,C_2431,A_2432] :
      ( k1_xboole_0 = B_2430
      | v1_funct_2(C_2431,A_2432,B_2430)
      | k1_relset_1(A_2432,B_2430,C_2431) != A_2432
      | ~ m1_subset_1(C_2431,k1_zfmisc_1(k2_zfmisc_1(A_2432,B_2430))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_19723,plain,(
    ! [B_2553,C_2554,A_2555] :
      ( k1_xboole_0 = B_2553
      | v1_funct_2(C_2554,A_2555,B_2553)
      | k1_relset_1(A_2555,B_2553,C_2554) != A_2555
      | ~ r1_tarski(k2_relat_1(C_2554),B_2553)
      | ~ r1_tarski(k1_relat_1(C_2554),A_2555)
      | ~ v1_relat_1(C_2554) ) ),
    inference(resolution,[status(thm)],[c_40,c_17228])).

tff(c_19735,plain,(
    ! [B_2553,A_2555] :
      ( k1_xboole_0 = B_2553
      | v1_funct_2('#skF_4',A_2555,B_2553)
      | k1_relset_1(A_2555,B_2553,'#skF_4') != A_2555
      | ~ r1_tarski('#skF_3',B_2553)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_2555)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16881,c_19723])).

tff(c_19855,plain,(
    ! [B_2557,A_2558] :
      ( k1_xboole_0 = B_2557
      | v1_funct_2('#skF_4',A_2558,B_2557)
      | k1_relset_1(A_2558,B_2557,'#skF_4') != A_2558
      | ~ r1_tarski('#skF_3',B_2557)
      | ~ r1_tarski('#skF_1',A_2558) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_17128,c_19735])).

tff(c_19866,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_19855,c_152])).

tff(c_19874,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_19628,c_19866])).

tff(c_12460,plain,(
    ! [B_2131,A_2132] :
      ( r1_tarski(k2_relat_1(B_2131),A_2132)
      | ~ v5_relat_1(B_2131,A_2132)
      | ~ v1_relat_1(B_2131) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12377,plain,(
    ! [C_2115,A_2116,B_2117] :
      ( v4_relat_1(C_2115,A_2116)
      | ~ m1_subset_1(C_2115,k1_zfmisc_1(k2_zfmisc_1(A_2116,B_2117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12391,plain,(
    ! [A_5,A_2116,B_2117] :
      ( v4_relat_1(A_5,A_2116)
      | ~ r1_tarski(A_5,k2_zfmisc_1(A_2116,B_2117)) ) ),
    inference(resolution,[status(thm)],[c_16,c_12377])).

tff(c_17766,plain,(
    ! [B_2482,A_2483,B_2484] :
      ( v4_relat_1(k2_relat_1(B_2482),A_2483)
      | ~ v5_relat_1(B_2482,k2_zfmisc_1(A_2483,B_2484))
      | ~ v1_relat_1(B_2482) ) ),
    inference(resolution,[status(thm)],[c_12460,c_12391])).

tff(c_17952,plain,(
    ! [B_2497] :
      ( v4_relat_1(k2_relat_1(B_2497),k1_xboole_0)
      | ~ v5_relat_1(B_2497,k1_xboole_0)
      | ~ v1_relat_1(B_2497) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_17766])).

tff(c_17957,plain,
    ( v4_relat_1('#skF_3',k1_xboole_0)
    | ~ v5_relat_1('#skF_4',k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_16881,c_17952])).

tff(c_17962,plain,
    ( v4_relat_1('#skF_3',k1_xboole_0)
    | ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_17957])).

tff(c_17963,plain,(
    ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_17962])).

tff(c_19937,plain,(
    ~ v5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19874,c_17963])).

tff(c_20006,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16902,c_19937])).

tff(c_20008,plain,(
    v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_17962])).

tff(c_16900,plain,(
    ! [A_12] :
      ( r1_tarski('#skF_3',A_12)
      | ~ v5_relat_1('#skF_4',A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_16888])).

tff(c_20021,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20008,c_16900])).

tff(c_20029,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17867,c_20021])).

tff(c_20030,plain,(
    ! [A_2488] :
      ( ~ r1_tarski('#skF_1',A_2488)
      | m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_17845])).

tff(c_20089,plain,(
    ! [A_2563] : ~ r1_tarski('#skF_1',A_2563) ),
    inference(splitLeft,[status(thm)],[c_20030])).

tff(c_20094,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_20089])).

tff(c_20095,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_20030])).

tff(c_20118,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20095,c_14])).

tff(c_20138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16942,c_20118])).

tff(c_20140,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_16923])).

tff(c_12396,plain,(
    ! [C_2119,A_2120] :
      ( v4_relat_1(C_2119,A_2120)
      | ~ m1_subset_1(C_2119,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_12377])).

tff(c_12400,plain,(
    ! [A_5,A_2120] :
      ( v4_relat_1(A_5,A_2120)
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_12396])).

tff(c_20145,plain,(
    ! [B_2564] : r1_tarski('#skF_3',B_2564) ),
    inference(splitRight,[status(thm)],[c_16923])).

tff(c_20207,plain,(
    ! [B_2570] :
      ( B_2570 = '#skF_3'
      | ~ r1_tarski(B_2570,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20145,c_2])).

tff(c_20372,plain,(
    ! [B_2575] :
      ( k1_relat_1(B_2575) = '#skF_3'
      | ~ v4_relat_1(B_2575,'#skF_3')
      | ~ v1_relat_1(B_2575) ) ),
    inference(resolution,[status(thm)],[c_22,c_20207])).

tff(c_20555,plain,(
    ! [A_2584] :
      ( k1_relat_1(A_2584) = '#skF_3'
      | ~ v1_relat_1(A_2584)
      | ~ r1_tarski(A_2584,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12400,c_20372])).

tff(c_20558,plain,
    ( k1_relat_1('#skF_4') = '#skF_3'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20140,c_20555])).

tff(c_20577,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_20558])).

tff(c_20586,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20577,c_16832])).

tff(c_21077,plain,(
    ! [B_2620,A_2621,C_2622] :
      ( k1_xboole_0 = B_2620
      | k1_relset_1(A_2621,B_2620,C_2622) = A_2621
      | ~ v1_funct_2(C_2622,A_2621,B_2620)
      | ~ m1_subset_1(C_2622,k1_zfmisc_1(k2_zfmisc_1(A_2621,B_2620))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_21087,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_21077])).

tff(c_21098,plain,
    ( k1_xboole_0 = '#skF_2'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_20586,c_21087])).

tff(c_21099,plain,(
    '#skF_3' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_21098])).

tff(c_20139,plain,(
    ! [B_279] : r1_tarski('#skF_3',B_279) ),
    inference(splitRight,[status(thm)],[c_16923])).

tff(c_21129,plain,(
    ! [B_279] : r1_tarski('#skF_1',B_279) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21099,c_20139])).

tff(c_12402,plain,(
    ! [A_2123,A_2124,B_2125] :
      ( v4_relat_1(A_2123,A_2124)
      | ~ r1_tarski(A_2123,k2_zfmisc_1(A_2124,B_2125)) ) ),
    inference(resolution,[status(thm)],[c_16,c_12377])).

tff(c_12451,plain,(
    ! [A_2128,B_2129] : v4_relat_1(k2_zfmisc_1(A_2128,B_2129),A_2128) ),
    inference(resolution,[status(thm)],[c_6,c_12402])).

tff(c_12454,plain,(
    ! [A_3] : v4_relat_1(k1_xboole_0,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_12451])).

tff(c_20380,plain,
    ( k1_relat_1(k1_xboole_0) = '#skF_3'
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12454,c_20372])).

tff(c_20394,plain,(
    k1_relat_1(k1_xboole_0) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_20380])).

tff(c_12494,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_12497,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_12494])).

tff(c_12501,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12497])).

tff(c_12503,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_21068,plain,(
    ! [B_2618,C_2619] :
      ( k1_relset_1(k1_xboole_0,B_2618,C_2619) = k1_relat_1(C_2619)
      | ~ m1_subset_1(C_2619,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_16817])).

tff(c_21070,plain,(
    ! [B_2618] : k1_relset_1(k1_xboole_0,B_2618,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12503,c_21068])).

tff(c_21075,plain,(
    ! [B_2618] : k1_relset_1(k1_xboole_0,B_2618,k1_xboole_0) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20394,c_21070])).

tff(c_21411,plain,(
    ! [B_2618] : k1_relset_1(k1_xboole_0,B_2618,k1_xboole_0) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21099,c_21075])).

tff(c_20516,plain,(
    ! [C_2581,B_2582] :
      ( v1_funct_2(C_2581,k1_xboole_0,B_2582)
      | k1_relset_1(k1_xboole_0,B_2582,C_2581) != k1_xboole_0
      | ~ m1_subset_1(C_2581,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_46])).

tff(c_20522,plain,(
    ! [B_2582] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_2582)
      | k1_relset_1(k1_xboole_0,B_2582,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12503,c_20516])).

tff(c_21412,plain,(
    ! [B_2582] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_2582)
      | k1_xboole_0 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21411,c_20522])).

tff(c_21744,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_21412])).

tff(c_12418,plain,(
    ! [A_2124,B_2125] : v4_relat_1(k2_zfmisc_1(A_2124,B_2125),A_2124) ),
    inference(resolution,[status(thm)],[c_6,c_12402])).

tff(c_20384,plain,(
    ! [B_2125] :
      ( k1_relat_1(k2_zfmisc_1('#skF_3',B_2125)) = '#skF_3'
      | ~ v1_relat_1(k2_zfmisc_1('#skF_3',B_2125)) ) ),
    inference(resolution,[status(thm)],[c_12418,c_20372])).

tff(c_20397,plain,(
    ! [B_2125] : k1_relat_1(k2_zfmisc_1('#skF_3',B_2125)) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_20384])).

tff(c_21118,plain,(
    ! [B_2125] : k1_relat_1(k2_zfmisc_1('#skF_1',B_2125)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21099,c_21099,c_20397])).

tff(c_20672,plain,(
    ! [C_2590,A_2591,B_2592] :
      ( m1_subset_1(C_2590,k1_zfmisc_1(k2_zfmisc_1(A_2591,B_2592)))
      | ~ r1_tarski(k2_relat_1(C_2590),B_2592)
      | ~ r1_tarski(k1_relat_1(C_2590),A_2591)
      | ~ v1_relat_1(C_2590) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_22017,plain,(
    ! [C_2666,B_2667] :
      ( m1_subset_1(C_2666,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_2666),B_2667)
      | ~ r1_tarski(k1_relat_1(C_2666),k1_xboole_0)
      | ~ v1_relat_1(C_2666) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_20672])).

tff(c_22544,plain,(
    ! [C_2700] :
      ( m1_subset_1(C_2700,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(C_2700),k1_xboole_0)
      | ~ v1_relat_1(C_2700) ) ),
    inference(resolution,[status(thm)],[c_6,c_22017])).

tff(c_22550,plain,(
    ! [B_2125] :
      ( m1_subset_1(k2_zfmisc_1('#skF_1',B_2125),k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_1',k1_xboole_0)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1',B_2125)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21118,c_22544])).

tff(c_22607,plain,(
    ! [B_2704] : m1_subset_1(k2_zfmisc_1('#skF_1',B_2704),k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_21129,c_22550])).

tff(c_22670,plain,(
    ! [B_2707] : r1_tarski(k2_zfmisc_1('#skF_1',B_2707),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22607,c_14])).

tff(c_21119,plain,(
    k1_relat_1(k1_xboole_0) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21099,c_20394])).

tff(c_12353,plain,(
    ! [A_2110,B_2111,A_2112] :
      ( v5_relat_1(A_2110,B_2111)
      | ~ r1_tarski(A_2110,k2_zfmisc_1(A_2112,B_2111)) ) ),
    inference(resolution,[status(thm)],[c_16,c_3335])).

tff(c_12370,plain,(
    ! [A_2113,B_2114] : v5_relat_1(k2_zfmisc_1(A_2113,B_2114),B_2114) ),
    inference(resolution,[status(thm)],[c_6,c_12353])).

tff(c_12376,plain,(
    ! [B_4] : v5_relat_1(k1_xboole_0,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_12370])).

tff(c_20251,plain,(
    ! [B_2571] :
      ( k2_relat_1(B_2571) = '#skF_3'
      | ~ v5_relat_1(B_2571,'#skF_3')
      | ~ v1_relat_1(B_2571) ) ),
    inference(resolution,[status(thm)],[c_26,c_20207])).

tff(c_20263,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_3'
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12376,c_20251])).

tff(c_20280,plain,(
    k2_relat_1(k1_xboole_0) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_20263])).

tff(c_21123,plain,(
    k2_relat_1(k1_xboole_0) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21099,c_20280])).

tff(c_22371,plain,(
    ! [C_2681,A_2682,B_2683] :
      ( r1_tarski(C_2681,k2_zfmisc_1(A_2682,B_2683))
      | ~ r1_tarski(k2_relat_1(C_2681),B_2683)
      | ~ r1_tarski(k1_relat_1(C_2681),A_2682)
      | ~ v1_relat_1(C_2681) ) ),
    inference(resolution,[status(thm)],[c_20672,c_14])).

tff(c_22379,plain,(
    ! [A_2682,B_2683] :
      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(A_2682,B_2683))
      | ~ r1_tarski('#skF_1',B_2683)
      | ~ r1_tarski(k1_relat_1(k1_xboole_0),A_2682)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21123,c_22371])).

tff(c_22403,plain,(
    ! [A_2684,B_2685] : r1_tarski(k1_xboole_0,k2_zfmisc_1(A_2684,B_2685)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_21129,c_21119,c_21129,c_22379])).

tff(c_22441,plain,(
    ! [A_2684,B_2685] :
      ( k2_zfmisc_1(A_2684,B_2685) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_2684,B_2685),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22403,c_2])).

tff(c_22806,plain,(
    ! [B_2709] : k2_zfmisc_1('#skF_1',B_2709) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22670,c_22441])).

tff(c_22876,plain,(
    ! [B_2709] :
      ( k1_xboole_0 = B_2709
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22806,c_8])).

tff(c_22912,plain,(
    ! [B_2710] : k1_xboole_0 = B_2710 ),
    inference(negUnitSimplification,[status(thm)],[c_21744,c_22876])).

tff(c_16831,plain,(
    ! [A_2385,B_2386,A_5] :
      ( k1_relset_1(A_2385,B_2386,A_5) = k1_relat_1(A_5)
      | ~ r1_tarski(A_5,k2_zfmisc_1(A_2385,B_2386)) ) ),
    inference(resolution,[status(thm)],[c_16,c_16817])).

tff(c_22409,plain,(
    ! [A_2684,B_2685] : k1_relset_1(A_2684,B_2685,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22403,c_16831])).

tff(c_22431,plain,(
    ! [A_2684,B_2685] : k1_relset_1(A_2684,B_2685,k1_xboole_0) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21119,c_22409])).

tff(c_22935,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_22912,c_22431])).

tff(c_23330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21744,c_22935])).

tff(c_23332,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_21412])).

tff(c_20189,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_20140,c_2])).

tff(c_20230,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_20189])).

tff(c_23354,plain,(
    ~ r1_tarski('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23332,c_20230])).

tff(c_23382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21129,c_23354])).

tff(c_23383,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_20189])).

tff(c_23404,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23383,c_74])).

tff(c_23392,plain,(
    ! [A_3] : v4_relat_1('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23383,c_12454])).

tff(c_23441,plain,(
    ! [B_3858] :
      ( k1_relat_1(B_3858) = '#skF_3'
      | ~ v4_relat_1(B_3858,'#skF_3')
      | ~ v1_relat_1(B_3858) ) ),
    inference(resolution,[status(thm)],[c_22,c_20207])).

tff(c_23445,plain,
    ( k1_relat_1('#skF_4') = '#skF_3'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_23392,c_23441])).

tff(c_23456,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_23445])).

tff(c_23463,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23456,c_16832])).

tff(c_52,plain,(
    ! [B_32,A_31,C_33] :
      ( k1_xboole_0 = B_32
      | k1_relset_1(A_31,B_32,C_33) = A_31
      | ~ v1_funct_2(C_33,A_31,B_32)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_23897,plain,(
    ! [B_3888,A_3889,C_3890] :
      ( B_3888 = '#skF_4'
      | k1_relset_1(A_3889,B_3888,C_3890) = A_3889
      | ~ v1_funct_2(C_3890,A_3889,B_3888)
      | ~ m1_subset_1(C_3890,k1_zfmisc_1(k2_zfmisc_1(A_3889,B_3888))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23383,c_52])).

tff(c_23913,plain,
    ( '#skF_2' = '#skF_4'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_23897])).

tff(c_23919,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_23463,c_23913])).

tff(c_23920,plain,(
    '#skF_3' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_23404,c_23919])).

tff(c_23935,plain,(
    ! [B_279] : r1_tarski('#skF_1',B_279) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23920,c_20139])).

tff(c_23453,plain,(
    ! [B_2125] :
      ( k1_relat_1(k2_zfmisc_1('#skF_3',B_2125)) = '#skF_3'
      | ~ v1_relat_1(k2_zfmisc_1('#skF_3',B_2125)) ) ),
    inference(resolution,[status(thm)],[c_12418,c_23441])).

tff(c_23462,plain,(
    ! [B_2125] : k1_relat_1(k2_zfmisc_1('#skF_3',B_2125)) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_23453])).

tff(c_23927,plain,(
    ! [B_2125] : k1_relat_1(k2_zfmisc_1('#skF_1',B_2125)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23920,c_23920,c_23462])).

tff(c_23403,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23383,c_23383,c_12])).

tff(c_23697,plain,(
    ! [C_3872,A_3873,B_3874] :
      ( m1_subset_1(C_3872,k1_zfmisc_1(k2_zfmisc_1(A_3873,B_3874)))
      | ~ r1_tarski(k2_relat_1(C_3872),B_3874)
      | ~ r1_tarski(k1_relat_1(C_3872),A_3873)
      | ~ v1_relat_1(C_3872) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_25153,plain,(
    ! [C_3975,A_3976,B_3977] :
      ( r1_tarski(C_3975,k2_zfmisc_1(A_3976,B_3977))
      | ~ r1_tarski(k2_relat_1(C_3975),B_3977)
      | ~ r1_tarski(k1_relat_1(C_3975),A_3976)
      | ~ v1_relat_1(C_3975) ) ),
    inference(resolution,[status(thm)],[c_23697,c_14])).

tff(c_26953,plain,(
    ! [C_4066,A_4067] :
      ( r1_tarski(C_4066,k2_zfmisc_1(A_4067,k2_relat_1(C_4066)))
      | ~ r1_tarski(k1_relat_1(C_4066),A_4067)
      | ~ v1_relat_1(C_4066) ) ),
    inference(resolution,[status(thm)],[c_6,c_25153])).

tff(c_27137,plain,(
    ! [C_4071] :
      ( r1_tarski(C_4071,'#skF_4')
      | ~ r1_tarski(k1_relat_1(C_4071),'#skF_4')
      | ~ v1_relat_1(C_4071) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23403,c_26953])).

tff(c_27152,plain,(
    ! [B_2125] :
      ( r1_tarski(k2_zfmisc_1('#skF_1',B_2125),'#skF_4')
      | ~ r1_tarski('#skF_1','#skF_4')
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1',B_2125)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23927,c_27137])).

tff(c_27172,plain,(
    ! [B_2125] : r1_tarski(k2_zfmisc_1('#skF_1',B_2125),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_23935,c_27152])).

tff(c_103,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_111,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_103])).

tff(c_119,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_111,c_112])).

tff(c_12395,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_27248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27172,c_12395])).

tff(c_27249,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_27252,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27249,c_60])).

tff(c_27269,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_27249,c_8])).

tff(c_27279,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_27269])).

tff(c_27293,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_27279])).

tff(c_27628,plain,(
    ! [A_4117,B_4118,C_4119] :
      ( k2_relset_1(A_4117,B_4118,C_4119) = k2_relat_1(C_4119)
      | ~ m1_subset_1(C_4119,k1_zfmisc_1(k2_zfmisc_1(A_4117,B_4118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_27662,plain,(
    ! [C_4125] :
      ( k2_relset_1('#skF_1','#skF_2',C_4125) = k2_relat_1(C_4125)
      | ~ m1_subset_1(C_4125,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27249,c_27628])).

tff(c_27665,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_27252,c_27662])).

tff(c_27671,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12341,c_27665])).

tff(c_27685,plain,(
    ! [A_12] :
      ( r1_tarski('#skF_3',A_12)
      | ~ v5_relat_1('#skF_4',A_12)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27671,c_26])).

tff(c_27707,plain,(
    ! [A_4126] :
      ( r1_tarski('#skF_3',A_4126)
      | ~ v5_relat_1('#skF_4',A_4126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_27685])).

tff(c_27731,plain,(
    ! [B_279] :
      ( r1_tarski('#skF_3',B_279)
      | ~ r1_tarski('#skF_4',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_3369,c_27707])).

tff(c_27787,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_27731])).

tff(c_27745,plain,(
    ! [A_4127,B_4128,C_4129] :
      ( k1_relset_1(A_4127,B_4128,C_4129) = k1_relat_1(C_4129)
      | ~ m1_subset_1(C_4129,k1_zfmisc_1(k2_zfmisc_1(A_4127,B_4128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_27773,plain,(
    ! [C_4131] :
      ( k1_relset_1('#skF_1','#skF_2',C_4131) = k1_relat_1(C_4131)
      | ~ m1_subset_1(C_4131,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27249,c_27745])).

tff(c_27781,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_27252,c_27773])).

tff(c_28151,plain,(
    ! [B_4173,A_4174,C_4175] :
      ( k1_xboole_0 = B_4173
      | k1_relset_1(A_4174,B_4173,C_4175) = A_4174
      | ~ v1_funct_2(C_4175,A_4174,B_4173)
      | ~ m1_subset_1(C_4175,k1_zfmisc_1(k2_zfmisc_1(A_4174,B_4173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_28157,plain,(
    ! [C_4175] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_4175) = '#skF_1'
      | ~ v1_funct_2(C_4175,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_4175,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27249,c_28151])).

tff(c_28247,plain,(
    ! [C_4184] :
      ( k1_relset_1('#skF_1','#skF_2',C_4184) = '#skF_1'
      | ~ v1_funct_2(C_4184,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_4184,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_28157])).

tff(c_28250,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_27252,c_28247])).

tff(c_28257,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_27781,c_28250])).

tff(c_27990,plain,(
    ! [C_4158,A_4159,B_4160] :
      ( m1_subset_1(C_4158,k1_zfmisc_1(k2_zfmisc_1(A_4159,B_4160)))
      | ~ r1_tarski(k2_relat_1(C_4158),B_4160)
      | ~ r1_tarski(k1_relat_1(C_4158),A_4159)
      | ~ v1_relat_1(C_4158) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_29621,plain,(
    ! [A_4273,B_4274,C_4275] :
      ( k1_relset_1(A_4273,B_4274,C_4275) = k1_relat_1(C_4275)
      | ~ r1_tarski(k2_relat_1(C_4275),B_4274)
      | ~ r1_tarski(k1_relat_1(C_4275),A_4273)
      | ~ v1_relat_1(C_4275) ) ),
    inference(resolution,[status(thm)],[c_27990,c_36])).

tff(c_29623,plain,(
    ! [A_4273,B_4274] :
      ( k1_relset_1(A_4273,B_4274,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_3',B_4274)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_4273)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27671,c_29621])).

tff(c_30002,plain,(
    ! [A_4292,B_4293] :
      ( k1_relset_1(A_4292,B_4293,'#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_3',B_4293)
      | ~ r1_tarski('#skF_1',A_4292) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_28257,c_28257,c_29623])).

tff(c_30054,plain,(
    ! [A_4300] :
      ( k1_relset_1(A_4300,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_4300) ) ),
    inference(resolution,[status(thm)],[c_6,c_30002])).

tff(c_30059,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_30054])).

tff(c_28329,plain,(
    ! [B_4186,C_4187,A_4188] :
      ( k1_xboole_0 = B_4186
      | v1_funct_2(C_4187,A_4188,B_4186)
      | k1_relset_1(A_4188,B_4186,C_4187) != A_4188
      | ~ m1_subset_1(C_4187,k1_zfmisc_1(k2_zfmisc_1(A_4188,B_4186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_30035,plain,(
    ! [B_4296,C_4297,A_4298] :
      ( k1_xboole_0 = B_4296
      | v1_funct_2(C_4297,A_4298,B_4296)
      | k1_relset_1(A_4298,B_4296,C_4297) != A_4298
      | ~ r1_tarski(k2_relat_1(C_4297),B_4296)
      | ~ r1_tarski(k1_relat_1(C_4297),A_4298)
      | ~ v1_relat_1(C_4297) ) ),
    inference(resolution,[status(thm)],[c_40,c_28329])).

tff(c_30037,plain,(
    ! [B_4296,A_4298] :
      ( k1_xboole_0 = B_4296
      | v1_funct_2('#skF_4',A_4298,B_4296)
      | k1_relset_1(A_4298,B_4296,'#skF_4') != A_4298
      | ~ r1_tarski('#skF_3',B_4296)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_4298)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27671,c_30035])).

tff(c_32106,plain,(
    ! [B_4343,A_4344] :
      ( k1_xboole_0 = B_4343
      | v1_funct_2('#skF_4',A_4344,B_4343)
      | k1_relset_1(A_4344,B_4343,'#skF_4') != A_4344
      | ~ r1_tarski('#skF_3',B_4343)
      | ~ r1_tarski('#skF_1',A_4344) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_28257,c_30037])).

tff(c_32125,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_32106,c_152])).

tff(c_32142,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_30059,c_32125])).

tff(c_24,plain,(
    ! [B_13,A_12] :
      ( v5_relat_1(B_13,A_12)
      | ~ r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_27691,plain,(
    ! [A_12] :
      ( v5_relat_1('#skF_4',A_12)
      | ~ r1_tarski('#skF_3',A_12)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27671,c_24])).

tff(c_27705,plain,(
    ! [A_12] :
      ( v5_relat_1('#skF_4',A_12)
      | ~ r1_tarski('#skF_3',A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_27691])).

tff(c_27370,plain,(
    ! [B_4085,A_4086] :
      ( r1_tarski(k2_relat_1(B_4085),A_4086)
      | ~ v5_relat_1(B_4085,A_4086)
      | ~ v1_relat_1(B_4085) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3349,plain,(
    ! [A_5,B_271,A_272] :
      ( v5_relat_1(A_5,B_271)
      | ~ r1_tarski(A_5,k2_zfmisc_1(A_272,B_271)) ) ),
    inference(resolution,[status(thm)],[c_16,c_3335])).

tff(c_28218,plain,(
    ! [B_4181,B_4182,A_4183] :
      ( v5_relat_1(k2_relat_1(B_4181),B_4182)
      | ~ v5_relat_1(B_4181,k2_zfmisc_1(A_4183,B_4182))
      | ~ v1_relat_1(B_4181) ) ),
    inference(resolution,[status(thm)],[c_27370,c_3349])).

tff(c_28677,plain,(
    ! [B_4211,B_4212] :
      ( v5_relat_1(k2_relat_1(B_4211),B_4212)
      | ~ v5_relat_1(B_4211,k1_xboole_0)
      | ~ v1_relat_1(B_4211) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_28218])).

tff(c_28689,plain,(
    ! [B_4212] :
      ( v5_relat_1('#skF_3',B_4212)
      | ~ v5_relat_1('#skF_4',k1_xboole_0)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27671,c_28677])).

tff(c_28694,plain,(
    ! [B_4212] :
      ( v5_relat_1('#skF_3',B_4212)
      | ~ v5_relat_1('#skF_4',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_28689])).

tff(c_28695,plain,(
    ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_28694])).

tff(c_28711,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_27705,c_28695])).

tff(c_32244,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32142,c_28711])).

tff(c_32303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_32244])).

tff(c_32305,plain,(
    v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_28694])).

tff(c_27701,plain,(
    ! [A_12] :
      ( r1_tarski('#skF_3',A_12)
      | ~ v5_relat_1('#skF_4',A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_27685])).

tff(c_32337,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32305,c_27701])).

tff(c_32422,plain,(
    ! [C_4351,A_4352] :
      ( m1_subset_1(C_4351,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_4351),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_4351),A_4352)
      | ~ v1_relat_1(C_4351) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_27990])).

tff(c_32424,plain,(
    ! [A_4352] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_4352)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27671,c_32422])).

tff(c_32429,plain,(
    ! [A_4352] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_1',A_4352) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_28257,c_32337,c_32424])).

tff(c_32448,plain,(
    ! [A_4355] : ~ r1_tarski('#skF_1',A_4355) ),
    inference(splitLeft,[status(thm)],[c_32429])).

tff(c_32453,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_32448])).

tff(c_32454,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_32429])).

tff(c_32477,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32454,c_14])).

tff(c_32497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27787,c_32477])).

tff(c_32499,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_27731])).

tff(c_32548,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_32499,c_2])).

tff(c_32556,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_27293,c_32548])).

tff(c_32498,plain,(
    ! [B_279] : r1_tarski('#skF_3',B_279) ),
    inference(splitRight,[status(thm)],[c_27731])).

tff(c_27414,plain,(
    ! [A_4089,A_4090,B_4091] :
      ( v4_relat_1(A_4089,A_4090)
      | ~ r1_tarski(A_4089,k2_zfmisc_1(A_4090,B_4091)) ) ),
    inference(resolution,[status(thm)],[c_16,c_12377])).

tff(c_27440,plain,(
    ! [A_4093,B_4094] : v4_relat_1(k2_zfmisc_1(A_4093,B_4094),A_4093) ),
    inference(resolution,[status(thm)],[c_6,c_27414])).

tff(c_27446,plain,(
    ! [A_3] : v4_relat_1(k1_xboole_0,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_27440])).

tff(c_32504,plain,(
    ! [B_4356] : r1_tarski('#skF_3',B_4356) ),
    inference(splitRight,[status(thm)],[c_27731])).

tff(c_32618,plain,(
    ! [B_4363] :
      ( B_4363 = '#skF_3'
      | ~ r1_tarski(B_4363,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32504,c_2])).

tff(c_32851,plain,(
    ! [B_4371] :
      ( k1_relat_1(B_4371) = '#skF_3'
      | ~ v4_relat_1(B_4371,'#skF_3')
      | ~ v1_relat_1(B_4371) ) ),
    inference(resolution,[status(thm)],[c_22,c_32618])).

tff(c_32859,plain,
    ( k1_relat_1(k1_xboole_0) = '#skF_3'
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_27446,c_32851])).

tff(c_32873,plain,(
    k1_relat_1(k1_xboole_0) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_32859])).

tff(c_32654,plain,(
    ! [B_4366] :
      ( k2_relat_1(B_4366) = '#skF_3'
      | ~ v5_relat_1(B_4366,'#skF_3')
      | ~ v1_relat_1(B_4366) ) ),
    inference(resolution,[status(thm)],[c_26,c_32618])).

tff(c_32666,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_3'
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12376,c_32654])).

tff(c_32683,plain,(
    k2_relat_1(k1_xboole_0) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_32666])).

tff(c_32878,plain,(
    ! [C_4372,A_4373,B_4374] :
      ( m1_subset_1(C_4372,k1_zfmisc_1(k2_zfmisc_1(A_4373,B_4374)))
      | ~ r1_tarski(k2_relat_1(C_4372),B_4374)
      | ~ r1_tarski(k1_relat_1(C_4372),A_4373)
      | ~ v1_relat_1(C_4372) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_32995,plain,(
    ! [C_4375] :
      ( m1_subset_1(C_4375,k1_zfmisc_1('#skF_4'))
      | ~ r1_tarski(k2_relat_1(C_4375),'#skF_2')
      | ~ r1_tarski(k1_relat_1(C_4375),'#skF_1')
      | ~ v1_relat_1(C_4375) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27249,c_32878])).

tff(c_33001,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),'#skF_1')
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32683,c_32995])).

tff(c_33015,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_32498,c_32873,c_32498,c_33001])).

tff(c_33041,plain,(
    r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_33015,c_14])).

tff(c_33058,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32556,c_33041])).

tff(c_33060,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_27279])).

tff(c_33059,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_27279])).

tff(c_33075,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33060,c_33059])).

tff(c_33069,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33059,c_33059,c_12])).

tff(c_33117,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33075,c_33075,c_33069])).

tff(c_33278,plain,(
    ! [A_4394,B_4395,C_4396] :
      ( k1_relset_1(A_4394,B_4395,C_4396) = k1_relat_1(C_4396)
      | ~ m1_subset_1(C_4396,k1_zfmisc_1(k2_zfmisc_1(A_4394,B_4395))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_33565,plain,(
    ! [B_4443,C_4444] :
      ( k1_relset_1('#skF_4',B_4443,C_4444) = k1_relat_1(C_4444)
      | ~ m1_subset_1(C_4444,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33117,c_33278])).

tff(c_33573,plain,(
    ! [B_4445] : k1_relset_1('#skF_4',B_4445,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_27252,c_33565])).

tff(c_33108,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33075,c_62])).

tff(c_50,plain,(
    ! [B_32,C_33] :
      ( k1_relset_1(k1_xboole_0,B_32,C_33) = k1_xboole_0
      | ~ v1_funct_2(C_33,k1_xboole_0,B_32)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_67,plain,(
    ! [B_32,C_33] :
      ( k1_relset_1(k1_xboole_0,B_32,C_33) = k1_xboole_0
      | ~ v1_funct_2(C_33,k1_xboole_0,B_32)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_50])).

tff(c_33547,plain,(
    ! [B_4440,C_4441] :
      ( k1_relset_1('#skF_4',B_4440,C_4441) = '#skF_4'
      | ~ v1_funct_2(C_4441,'#skF_4',B_4440)
      | ~ m1_subset_1(C_4441,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33060,c_33060,c_33060,c_33060,c_67])).

tff(c_33552,plain,
    ( k1_relset_1('#skF_4','#skF_2','#skF_4') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_33108,c_33547])).

tff(c_33559,plain,(
    k1_relset_1('#skF_4','#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27252,c_33552])).

tff(c_33577,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_33573,c_33559])).

tff(c_33571,plain,(
    ! [B_4443] : k1_relset_1('#skF_4',B_4443,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_27252,c_33565])).

tff(c_33584,plain,(
    ! [B_4443] : k1_relset_1('#skF_4',B_4443,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33577,c_33571])).

tff(c_68,plain,(
    ! [C_33,B_32] :
      ( v1_funct_2(C_33,k1_xboole_0,B_32)
      | k1_relset_1(k1_xboole_0,B_32,C_33) != k1_xboole_0
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_46])).

tff(c_33682,plain,(
    ! [C_4449,B_4450] :
      ( v1_funct_2(C_4449,'#skF_4',B_4450)
      | k1_relset_1('#skF_4',B_4450,C_4449) != '#skF_4'
      | ~ m1_subset_1(C_4449,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33060,c_33060,c_33060,c_33060,c_68])).

tff(c_33684,plain,(
    ! [B_4450] :
      ( v1_funct_2('#skF_4','#skF_4',B_4450)
      | k1_relset_1('#skF_4',B_4450,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_27252,c_33682])).

tff(c_33690,plain,(
    ! [B_4450] : v1_funct_2('#skF_4','#skF_4',B_4450) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33584,c_33684])).

tff(c_33107,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33075,c_152])).

tff(c_33695,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33690,c_33107])).

tff(c_33696,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_34137,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34119,c_33696])).

tff(c_34159,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_34065,c_34137])).

tff(c_34164,plain,
    ( ~ v4_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_34159])).

tff(c_34168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_33773,c_34164])).

tff(c_34169,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_34182,plain,(
    ! [B_4527] : k2_zfmisc_1('#skF_1',B_4527) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34169,c_34169,c_12])).

tff(c_34186,plain,(
    v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_34182,c_28])).

tff(c_34181,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34169,c_34169,c_12])).

tff(c_34170,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_34175,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34169,c_34170])).

tff(c_34210,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34181,c_34175,c_60])).

tff(c_34224,plain,(
    ! [B_4533,A_4534] :
      ( v1_relat_1(B_4533)
      | ~ m1_subset_1(B_4533,k1_zfmisc_1(A_4534))
      | ~ v1_relat_1(A_4534) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_34230,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_34210,c_34224])).

tff(c_34234,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34186,c_34230])).

tff(c_34191,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34169,c_34169,c_10])).

tff(c_34320,plain,(
    ! [C_4549,A_4550,B_4551] :
      ( v4_relat_1(C_4549,A_4550)
      | ~ m1_subset_1(C_4549,k1_zfmisc_1(k2_zfmisc_1(A_4550,B_4551))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_34333,plain,(
    ! [C_4552,A_4553] :
      ( v4_relat_1(C_4552,A_4553)
      | ~ m1_subset_1(C_4552,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34191,c_34320])).

tff(c_34340,plain,(
    ! [A_4553] : v4_relat_1('#skF_4',A_4553) ),
    inference(resolution,[status(thm)],[c_34210,c_34333])).

tff(c_34457,plain,(
    ! [A_4579,B_4580,C_4581] :
      ( k1_relset_1(A_4579,B_4580,C_4581) = k1_relat_1(C_4581)
      | ~ m1_subset_1(C_4581,k1_zfmisc_1(k2_zfmisc_1(A_4579,B_4580))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_34576,plain,(
    ! [A_4601,C_4602] :
      ( k1_relset_1(A_4601,'#skF_1',C_4602) = k1_relat_1(C_4602)
      | ~ m1_subset_1(C_4602,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34191,c_34457])).

tff(c_34586,plain,(
    ! [A_4601] : k1_relset_1(A_4601,'#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34210,c_34576])).

tff(c_34176,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34175,c_62])).

tff(c_34697,plain,(
    ! [B_4614,C_4615] :
      ( k1_relset_1('#skF_1',B_4614,C_4615) = '#skF_1'
      | ~ v1_funct_2(C_4615,'#skF_1',B_4614)
      | ~ m1_subset_1(C_4615,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34169,c_34169,c_34169,c_34169,c_67])).

tff(c_34702,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_4') = '#skF_1'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_34176,c_34697])).

tff(c_34709,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34210,c_34586,c_34702])).

tff(c_34717,plain,(
    ! [A_10] :
      ( r1_tarski('#skF_1',A_10)
      | ~ v4_relat_1('#skF_4',A_10)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34709,c_22])).

tff(c_34729,plain,(
    ! [A_10] : r1_tarski('#skF_1',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34234,c_34340,c_34717])).

tff(c_34214,plain,(
    ! [A_4529,B_4530] :
      ( r1_tarski(A_4529,B_4530)
      | ~ m1_subset_1(A_4529,k1_zfmisc_1(B_4530)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_34218,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_34210,c_34214])).

tff(c_34307,plain,(
    ! [B_4547,A_4548] :
      ( B_4547 = A_4548
      | ~ r1_tarski(B_4547,A_4548)
      | ~ r1_tarski(A_4548,B_4547) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34314,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_34218,c_34307])).

tff(c_34332,plain,(
    ~ r1_tarski('#skF_1','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_34314])).

tff(c_34737,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34729,c_34332])).

tff(c_34738,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_34314])).

tff(c_34746,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34738,c_34210])).

tff(c_34750,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34738,c_34738,c_34181])).

tff(c_34987,plain,(
    ! [A_4653,B_4654,C_4655] :
      ( k1_relset_1(A_4653,B_4654,C_4655) = k1_relat_1(C_4655)
      | ~ m1_subset_1(C_4655,k1_zfmisc_1(k2_zfmisc_1(A_4653,B_4654))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_35237,plain,(
    ! [B_4691,C_4692] :
      ( k1_relset_1('#skF_4',B_4691,C_4692) = k1_relat_1(C_4692)
      | ~ m1_subset_1(C_4692,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34750,c_34987])).

tff(c_35243,plain,(
    ! [B_4691] : k1_relset_1('#skF_4',B_4691,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34746,c_35237])).

tff(c_34752,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34738,c_34169])).

tff(c_35284,plain,(
    ! [C_4699,B_4700] :
      ( v1_funct_2(C_4699,'#skF_4',B_4700)
      | k1_relset_1('#skF_4',B_4700,C_4699) != '#skF_4'
      | ~ m1_subset_1(C_4699,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34752,c_34752,c_34752,c_34752,c_68])).

tff(c_35286,plain,(
    ! [B_4700] :
      ( v1_funct_2('#skF_4','#skF_4',B_4700)
      | k1_relset_1('#skF_4',B_4700,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_34746,c_35284])).

tff(c_35291,plain,(
    ! [B_4700] :
      ( v1_funct_2('#skF_4','#skF_4',B_4700)
      | k1_relat_1('#skF_4') != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35243,c_35286])).

tff(c_35307,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_35291])).

tff(c_34747,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34738,c_34738,c_34176])).

tff(c_35360,plain,(
    ! [B_4708,C_4709] :
      ( k1_relset_1('#skF_4',B_4708,C_4709) = '#skF_4'
      | ~ v1_funct_2(C_4709,'#skF_4',B_4708)
      | ~ m1_subset_1(C_4709,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34752,c_34752,c_34752,c_34752,c_67])).

tff(c_35365,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_4') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_34747,c_35360])).

tff(c_35373,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34746,c_35243,c_35365])).

tff(c_35375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35307,c_35373])).

tff(c_35376,plain,(
    ! [B_4700] : v1_funct_2('#skF_4','#skF_4',B_4700) ),
    inference(splitRight,[status(thm)],[c_35291])).

tff(c_34213,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34210,c_34181,c_66])).

tff(c_34744,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34738,c_34213])).

tff(c_35451,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35376,c_34744])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:49:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.66/5.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.98/5.14  
% 12.98/5.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.98/5.15  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.98/5.15  
% 12.98/5.15  %Foreground sorts:
% 12.98/5.15  
% 12.98/5.15  
% 12.98/5.15  %Background operators:
% 12.98/5.15  
% 12.98/5.15  
% 12.98/5.15  %Foreground operators:
% 12.98/5.15  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 12.98/5.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.98/5.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.98/5.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.98/5.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.98/5.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.98/5.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.98/5.15  tff('#skF_2', type, '#skF_2': $i).
% 12.98/5.15  tff('#skF_3', type, '#skF_3': $i).
% 12.98/5.15  tff('#skF_1', type, '#skF_1': $i).
% 12.98/5.15  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.98/5.15  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 12.98/5.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.98/5.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.98/5.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.98/5.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.98/5.15  tff('#skF_4', type, '#skF_4': $i).
% 12.98/5.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.98/5.15  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.98/5.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.98/5.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.98/5.15  
% 12.98/5.20  tff(f_126, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 12.98/5.20  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.98/5.20  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 12.98/5.20  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 12.98/5.20  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 12.98/5.20  tff(f_88, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 12.98/5.20  tff(f_62, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 12.98/5.20  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 12.98/5.20  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 12.98/5.20  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.98/5.20  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.98/5.20  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 12.98/5.20  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 12.98/5.20  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 12.98/5.20  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 12.98/5.20  tff(c_125, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.98/5.20  tff(c_138, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_125])).
% 12.98/5.20  tff(c_33758, plain, (![C_4460, A_4461, B_4462]: (v4_relat_1(C_4460, A_4461) | ~m1_subset_1(C_4460, k1_zfmisc_1(k2_zfmisc_1(A_4461, B_4462))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.98/5.20  tff(c_33773, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_33758])).
% 12.98/5.20  tff(c_22, plain, (![B_11, A_10]: (r1_tarski(k1_relat_1(B_11), A_10) | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.98/5.20  tff(c_34048, plain, (![A_4514, B_4515, C_4516]: (k2_relset_1(A_4514, B_4515, C_4516)=k2_relat_1(C_4516) | ~m1_subset_1(C_4516, k1_zfmisc_1(k2_zfmisc_1(A_4514, B_4515))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.98/5.20  tff(c_34063, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_34048])).
% 12.98/5.20  tff(c_58, plain, (r1_tarski(k2_relset_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 12.98/5.20  tff(c_34065, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34063, c_58])).
% 12.98/5.20  tff(c_34119, plain, (![C_4524, A_4525, B_4526]: (m1_subset_1(C_4524, k1_zfmisc_1(k2_zfmisc_1(A_4525, B_4526))) | ~r1_tarski(k2_relat_1(C_4524), B_4526) | ~r1_tarski(k1_relat_1(C_4524), A_4525) | ~v1_relat_1(C_4524))), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.98/5.20  tff(c_28, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.98/5.20  tff(c_56, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_126])).
% 12.98/5.20  tff(c_74, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_56])).
% 12.98/5.20  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 12.98/5.20  tff(c_16, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.98/5.20  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.98/5.20  tff(c_3335, plain, (![C_270, B_271, A_272]: (v5_relat_1(C_270, B_271) | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(A_272, B_271))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.98/5.20  tff(c_3365, plain, (![C_278, B_279]: (v5_relat_1(C_278, B_279) | ~m1_subset_1(C_278, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_3335])).
% 12.98/5.20  tff(c_3369, plain, (![A_5, B_279]: (v5_relat_1(A_5, B_279) | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_3365])).
% 12.98/5.20  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.98/5.20  tff(c_3590, plain, (![A_316, B_317, C_318]: (k1_relset_1(A_316, B_317, C_318)=k1_relat_1(C_318) | ~m1_subset_1(C_318, k1_zfmisc_1(k2_zfmisc_1(A_316, B_317))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.98/5.20  tff(c_3605, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_3590])).
% 12.98/5.20  tff(c_8460, plain, (![B_1869, A_1870, C_1871]: (k1_xboole_0=B_1869 | k1_relset_1(A_1870, B_1869, C_1871)=A_1870 | ~v1_funct_2(C_1871, A_1870, B_1869) | ~m1_subset_1(C_1871, k1_zfmisc_1(k2_zfmisc_1(A_1870, B_1869))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.98/5.20  tff(c_8470, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_8460])).
% 12.98/5.20  tff(c_8481, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_3605, c_8470])).
% 12.98/5.20  tff(c_8482, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_74, c_8481])).
% 12.98/5.20  tff(c_3640, plain, (![A_325, B_326, C_327]: (k2_relset_1(A_325, B_326, C_327)=k2_relat_1(C_327) | ~m1_subset_1(C_327, k1_zfmisc_1(k2_zfmisc_1(A_325, B_326))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.98/5.20  tff(c_3655, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_3640])).
% 12.98/5.20  tff(c_3658, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3655, c_58])).
% 12.98/5.20  tff(c_3732, plain, (![C_338, A_339, B_340]: (m1_subset_1(C_338, k1_zfmisc_1(k2_zfmisc_1(A_339, B_340))) | ~r1_tarski(k2_relat_1(C_338), B_340) | ~r1_tarski(k1_relat_1(C_338), A_339) | ~v1_relat_1(C_338))), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.98/5.20  tff(c_14, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.98/5.20  tff(c_10814, plain, (![C_2040, A_2041, B_2042]: (r1_tarski(C_2040, k2_zfmisc_1(A_2041, B_2042)) | ~r1_tarski(k2_relat_1(C_2040), B_2042) | ~r1_tarski(k1_relat_1(C_2040), A_2041) | ~v1_relat_1(C_2040))), inference(resolution, [status(thm)], [c_3732, c_14])).
% 12.98/5.20  tff(c_10820, plain, (![A_2041]: (r1_tarski('#skF_4', k2_zfmisc_1(A_2041, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_2041) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_3658, c_10814])).
% 12.98/5.20  tff(c_10835, plain, (![A_2043]: (r1_tarski('#skF_4', k2_zfmisc_1(A_2043, '#skF_3')) | ~r1_tarski('#skF_1', A_2043))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_8482, c_10820])).
% 12.98/5.20  tff(c_3604, plain, (![A_316, B_317, A_5]: (k1_relset_1(A_316, B_317, A_5)=k1_relat_1(A_5) | ~r1_tarski(A_5, k2_zfmisc_1(A_316, B_317)))), inference(resolution, [status(thm)], [c_16, c_3590])).
% 12.98/5.20  tff(c_10841, plain, (![A_2043]: (k1_relset_1(A_2043, '#skF_3', '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_1', A_2043))), inference(resolution, [status(thm)], [c_10835, c_3604])).
% 12.98/5.20  tff(c_10873, plain, (![A_2044]: (k1_relset_1(A_2044, '#skF_3', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_2044))), inference(demodulation, [status(thm), theory('equality')], [c_8482, c_10841])).
% 12.98/5.20  tff(c_10878, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_6, c_10873])).
% 12.98/5.20  tff(c_10832, plain, (![A_2041]: (r1_tarski('#skF_4', k2_zfmisc_1(A_2041, '#skF_3')) | ~r1_tarski('#skF_1', A_2041))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_8482, c_10820])).
% 12.98/5.20  tff(c_11500, plain, (![B_2083, A_2084, A_2085]: (k1_xboole_0=B_2083 | k1_relset_1(A_2084, B_2083, A_2085)=A_2084 | ~v1_funct_2(A_2085, A_2084, B_2083) | ~r1_tarski(A_2085, k2_zfmisc_1(A_2084, B_2083)))), inference(resolution, [status(thm)], [c_16, c_8460])).
% 12.98/5.20  tff(c_11533, plain, (![A_2041]: (k1_xboole_0='#skF_3' | k1_relset_1(A_2041, '#skF_3', '#skF_4')=A_2041 | ~v1_funct_2('#skF_4', A_2041, '#skF_3') | ~r1_tarski('#skF_1', A_2041))), inference(resolution, [status(thm)], [c_10832, c_11500])).
% 12.98/5.20  tff(c_11690, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_11533])).
% 12.98/5.20  tff(c_75, plain, (![B_37]: (k2_zfmisc_1(k1_xboole_0, B_37)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.98/5.20  tff(c_79, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_75, c_28])).
% 12.98/5.20  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.98/5.20  tff(c_3396, plain, (![C_287, A_288, B_289]: (v4_relat_1(C_287, A_288) | ~m1_subset_1(C_287, k1_zfmisc_1(k2_zfmisc_1(A_288, B_289))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.98/5.20  tff(c_3421, plain, (![A_295, A_296, B_297]: (v4_relat_1(A_295, A_296) | ~r1_tarski(A_295, k2_zfmisc_1(A_296, B_297)))), inference(resolution, [status(thm)], [c_16, c_3396])).
% 12.98/5.20  tff(c_3438, plain, (![A_298, B_299]: (v4_relat_1(k2_zfmisc_1(A_298, B_299), A_298))), inference(resolution, [status(thm)], [c_6, c_3421])).
% 12.98/5.20  tff(c_3441, plain, (![A_3]: (v4_relat_1(k1_xboole_0, A_3))), inference(superposition, [status(thm), theory('equality')], [c_10, c_3438])).
% 12.98/5.20  tff(c_3942, plain, (![B_365, A_366, C_367]: (k1_xboole_0=B_365 | k1_relset_1(A_366, B_365, C_367)=A_366 | ~v1_funct_2(C_367, A_366, B_365) | ~m1_subset_1(C_367, k1_zfmisc_1(k2_zfmisc_1(A_366, B_365))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.98/5.20  tff(c_3952, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_3942])).
% 12.98/5.20  tff(c_3963, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_3605, c_3952])).
% 12.98/5.20  tff(c_3964, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_74, c_3963])).
% 12.98/5.20  tff(c_4977, plain, (![C_442, A_443, B_444]: (r1_tarski(C_442, k2_zfmisc_1(A_443, B_444)) | ~r1_tarski(k2_relat_1(C_442), B_444) | ~r1_tarski(k1_relat_1(C_442), A_443) | ~v1_relat_1(C_442))), inference(resolution, [status(thm)], [c_3732, c_14])).
% 12.98/5.20  tff(c_4979, plain, (![A_443]: (r1_tarski('#skF_4', k2_zfmisc_1(A_443, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_443) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_3658, c_4977])).
% 12.98/5.20  tff(c_5029, plain, (![A_445]: (r1_tarski('#skF_4', k2_zfmisc_1(A_445, '#skF_3')) | ~r1_tarski('#skF_1', A_445))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_3964, c_4979])).
% 12.98/5.20  tff(c_5032, plain, (![A_445]: (k1_relset_1(A_445, '#skF_3', '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_1', A_445))), inference(resolution, [status(thm)], [c_5029, c_3604])).
% 12.98/5.20  tff(c_5273, plain, (![A_449]: (k1_relset_1(A_449, '#skF_3', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_449))), inference(demodulation, [status(thm), theory('equality')], [c_3964, c_5032])).
% 12.98/5.20  tff(c_5278, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_6, c_5273])).
% 12.98/5.20  tff(c_4987, plain, (![A_443]: (r1_tarski('#skF_4', k2_zfmisc_1(A_443, '#skF_3')) | ~r1_tarski('#skF_1', A_443))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_3964, c_4979])).
% 12.98/5.20  tff(c_5433, plain, (![B_459, A_460, A_461]: (k1_xboole_0=B_459 | k1_relset_1(A_460, B_459, A_461)=A_460 | ~v1_funct_2(A_461, A_460, B_459) | ~r1_tarski(A_461, k2_zfmisc_1(A_460, B_459)))), inference(resolution, [status(thm)], [c_16, c_3942])).
% 12.98/5.20  tff(c_5458, plain, (![A_443]: (k1_xboole_0='#skF_3' | k1_relset_1(A_443, '#skF_3', '#skF_4')=A_443 | ~v1_funct_2('#skF_4', A_443, '#skF_3') | ~r1_tarski('#skF_1', A_443))), inference(resolution, [status(thm)], [c_4987, c_5433])).
% 12.98/5.20  tff(c_5659, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_5458])).
% 12.98/5.20  tff(c_3414, plain, (![C_291, A_292]: (v4_relat_1(C_291, A_292) | ~m1_subset_1(C_291, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_3396])).
% 12.98/5.20  tff(c_3418, plain, (![A_5, A_292]: (v4_relat_1(A_5, A_292) | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_3414])).
% 12.98/5.20  tff(c_3480, plain, (![B_304, A_305]: (r1_tarski(k1_relat_1(B_304), A_305) | ~v4_relat_1(B_304, A_305) | ~v1_relat_1(B_304))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.98/5.20  tff(c_137, plain, (![A_5, A_46, B_47]: (v1_relat_1(A_5) | ~r1_tarski(A_5, k2_zfmisc_1(A_46, B_47)))), inference(resolution, [status(thm)], [c_16, c_125])).
% 12.98/5.20  tff(c_3555, plain, (![B_310, A_311, B_312]: (v1_relat_1(k1_relat_1(B_310)) | ~v4_relat_1(B_310, k2_zfmisc_1(A_311, B_312)) | ~v1_relat_1(B_310))), inference(resolution, [status(thm)], [c_3480, c_137])).
% 12.98/5.20  tff(c_3578, plain, (![A_5]: (v1_relat_1(k1_relat_1(A_5)) | ~v1_relat_1(A_5) | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_3418, c_3555])).
% 12.98/5.20  tff(c_3970, plain, (v1_relat_1('#skF_1') | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3964, c_3578])).
% 12.98/5.20  tff(c_3986, plain, (v1_relat_1('#skF_1') | ~r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_138, c_3970])).
% 12.98/5.20  tff(c_4000, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3986])).
% 12.98/5.20  tff(c_5721, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5659, c_4000])).
% 12.98/5.20  tff(c_5757, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5659, c_5659, c_10])).
% 12.98/5.20  tff(c_5835, plain, (![A_443]: (r1_tarski('#skF_4', '#skF_3') | ~r1_tarski('#skF_1', A_443))), inference(demodulation, [status(thm), theory('equality')], [c_5757, c_4987])).
% 12.98/5.20  tff(c_5961, plain, (![A_486]: (~r1_tarski('#skF_1', A_486))), inference(negUnitSimplification, [status(thm)], [c_5721, c_5835])).
% 12.98/5.20  tff(c_5966, plain, $false, inference(resolution, [status(thm)], [c_6, c_5961])).
% 12.98/5.20  tff(c_5968, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_5458])).
% 12.98/5.20  tff(c_3870, plain, (![B_354, C_355, A_356]: (k1_xboole_0=B_354 | v1_funct_2(C_355, A_356, B_354) | k1_relset_1(A_356, B_354, C_355)!=A_356 | ~m1_subset_1(C_355, k1_zfmisc_1(k2_zfmisc_1(A_356, B_354))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.98/5.20  tff(c_5587, plain, (![B_471, A_472, A_473]: (k1_xboole_0=B_471 | v1_funct_2(A_472, A_473, B_471) | k1_relset_1(A_473, B_471, A_472)!=A_473 | ~r1_tarski(A_472, k2_zfmisc_1(A_473, B_471)))), inference(resolution, [status(thm)], [c_16, c_3870])).
% 12.98/5.20  tff(c_5612, plain, (![A_443]: (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', A_443, '#skF_3') | k1_relset_1(A_443, '#skF_3', '#skF_4')!=A_443 | ~r1_tarski('#skF_1', A_443))), inference(resolution, [status(thm)], [c_4987, c_5587])).
% 12.98/5.20  tff(c_5970, plain, (![A_487]: (v1_funct_2('#skF_4', A_487, '#skF_3') | k1_relset_1(A_487, '#skF_3', '#skF_4')!=A_487 | ~r1_tarski('#skF_1', A_487))), inference(negUnitSimplification, [status(thm)], [c_5968, c_5612])).
% 12.98/5.20  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 12.98/5.20  tff(c_54, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 12.98/5.20  tff(c_66, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_54])).
% 12.98/5.20  tff(c_152, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_66])).
% 12.98/5.20  tff(c_5976, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_5970, c_152])).
% 12.98/5.20  tff(c_5981, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_5278, c_5976])).
% 12.98/5.20  tff(c_5983, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_3986])).
% 12.98/5.20  tff(c_3976, plain, (![A_10]: (r1_tarski('#skF_1', A_10) | ~v4_relat_1('#skF_4', A_10) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3964, c_22])).
% 12.98/5.20  tff(c_6071, plain, (![A_494]: (r1_tarski('#skF_1', A_494) | ~v4_relat_1('#skF_4', A_494))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_3976])).
% 12.98/5.20  tff(c_6078, plain, (![A_292]: (r1_tarski('#skF_1', A_292) | ~r1_tarski('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_3418, c_6071])).
% 12.98/5.20  tff(c_6098, plain, (![A_495]: (r1_tarski('#skF_1', A_495))), inference(demodulation, [status(thm), theory('equality')], [c_5983, c_6078])).
% 12.98/5.20  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.98/5.20  tff(c_6212, plain, (![A_502]: (A_502='#skF_1' | ~r1_tarski(A_502, '#skF_1'))), inference(resolution, [status(thm)], [c_6098, c_2])).
% 12.98/5.20  tff(c_6515, plain, (![B_522]: (k1_relat_1(B_522)='#skF_1' | ~v4_relat_1(B_522, '#skF_1') | ~v1_relat_1(B_522))), inference(resolution, [status(thm)], [c_22, c_6212])).
% 12.98/5.20  tff(c_6527, plain, (k1_relat_1(k1_xboole_0)='#skF_1' | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_3441, c_6515])).
% 12.98/5.20  tff(c_6544, plain, (k1_relat_1(k1_xboole_0)='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_79, c_6527])).
% 12.98/5.20  tff(c_42, plain, (![A_31]: (v1_funct_2(k1_xboole_0, A_31, k1_xboole_0) | k1_xboole_0=A_31 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_31, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.98/5.20  tff(c_70, plain, (![A_31]: (v1_funct_2(k1_xboole_0, A_31, k1_xboole_0) | k1_xboole_0=A_31 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_42])).
% 12.98/5.20  tff(c_3513, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_70])).
% 12.98/5.20  tff(c_3516, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_3513])).
% 12.98/5.20  tff(c_3520, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3516])).
% 12.98/5.20  tff(c_3522, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_70])).
% 12.98/5.20  tff(c_3724, plain, (![B_336, C_337]: (k1_relset_1(k1_xboole_0, B_336, C_337)=k1_relat_1(C_337) | ~m1_subset_1(C_337, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_3590])).
% 12.98/5.20  tff(c_3730, plain, (![B_336]: (k1_relset_1(k1_xboole_0, B_336, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_3522, c_3724])).
% 12.98/5.20  tff(c_46, plain, (![C_33, B_32]: (v1_funct_2(C_33, k1_xboole_0, B_32) | k1_relset_1(k1_xboole_0, B_32, C_33)!=k1_xboole_0 | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_32))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.98/5.20  tff(c_3694, plain, (![C_331, B_332]: (v1_funct_2(C_331, k1_xboole_0, B_332) | k1_relset_1(k1_xboole_0, B_332, C_331)!=k1_xboole_0 | ~m1_subset_1(C_331, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_46])).
% 12.98/5.20  tff(c_3700, plain, (![B_332]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_332) | k1_relset_1(k1_xboole_0, B_332, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_3522, c_3694])).
% 12.98/5.20  tff(c_3769, plain, (![B_332]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_332) | k1_relat_1(k1_xboole_0)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3730, c_3700])).
% 12.98/5.20  tff(c_3785, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3769])).
% 12.98/5.20  tff(c_6612, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6544, c_3785])).
% 12.98/5.20  tff(c_6089, plain, (![A_292]: (r1_tarski('#skF_1', A_292))), inference(demodulation, [status(thm), theory('equality')], [c_5983, c_6078])).
% 12.98/5.20  tff(c_3372, plain, (![A_282, B_283, A_284]: (v5_relat_1(A_282, B_283) | ~r1_tarski(A_282, k2_zfmisc_1(A_284, B_283)))), inference(resolution, [status(thm)], [c_16, c_3335])).
% 12.98/5.20  tff(c_3389, plain, (![A_285, B_286]: (v5_relat_1(k2_zfmisc_1(A_285, B_286), B_286))), inference(resolution, [status(thm)], [c_6, c_3372])).
% 12.98/5.20  tff(c_3395, plain, (![B_4]: (v5_relat_1(k1_xboole_0, B_4))), inference(superposition, [status(thm), theory('equality')], [c_12, c_3389])).
% 12.98/5.20  tff(c_3445, plain, (![B_300, A_301]: (r1_tarski(k2_relat_1(B_300), A_301) | ~v5_relat_1(B_300, A_301) | ~v1_relat_1(B_300))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.98/5.20  tff(c_6281, plain, (![B_510, A_511]: (k2_relat_1(B_510)=A_511 | ~r1_tarski(A_511, k2_relat_1(B_510)) | ~v5_relat_1(B_510, A_511) | ~v1_relat_1(B_510))), inference(resolution, [status(thm)], [c_3445, c_2])).
% 12.98/5.20  tff(c_6305, plain, (![B_512]: (k2_relat_1(B_512)='#skF_1' | ~v5_relat_1(B_512, '#skF_1') | ~v1_relat_1(B_512))), inference(resolution, [status(thm)], [c_6089, c_6281])).
% 12.98/5.20  tff(c_6313, plain, (k2_relat_1(k1_xboole_0)='#skF_1' | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_3395, c_6305])).
% 12.98/5.20  tff(c_6327, plain, (k2_relat_1(k1_xboole_0)='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_79, c_6313])).
% 12.98/5.20  tff(c_7540, plain, (![C_568, A_569, B_570]: (r1_tarski(C_568, k2_zfmisc_1(A_569, B_570)) | ~r1_tarski(k2_relat_1(C_568), B_570) | ~r1_tarski(k1_relat_1(C_568), A_569) | ~v1_relat_1(C_568))), inference(resolution, [status(thm)], [c_3732, c_14])).
% 12.98/5.20  tff(c_7548, plain, (![A_569, B_570]: (r1_tarski(k1_xboole_0, k2_zfmisc_1(A_569, B_570)) | ~r1_tarski('#skF_1', B_570) | ~r1_tarski(k1_relat_1(k1_xboole_0), A_569) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6327, c_7540])).
% 12.98/5.20  tff(c_7563, plain, (![A_569, B_570]: (r1_tarski(k1_xboole_0, k2_zfmisc_1(A_569, B_570)))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_6089, c_6544, c_6089, c_7548])).
% 12.98/5.20  tff(c_3437, plain, (![A_296, B_297]: (v4_relat_1(k2_zfmisc_1(A_296, B_297), A_296))), inference(resolution, [status(thm)], [c_6, c_3421])).
% 12.98/5.20  tff(c_6531, plain, (![B_297]: (k1_relat_1(k2_zfmisc_1('#skF_1', B_297))='#skF_1' | ~v1_relat_1(k2_zfmisc_1('#skF_1', B_297)))), inference(resolution, [status(thm)], [c_3437, c_6515])).
% 12.98/5.20  tff(c_6547, plain, (![B_297]: (k1_relat_1(k2_zfmisc_1('#skF_1', B_297))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_6531])).
% 12.98/5.20  tff(c_7134, plain, (![C_550, B_551]: (m1_subset_1(C_550, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_550), B_551) | ~r1_tarski(k1_relat_1(C_550), k1_xboole_0) | ~v1_relat_1(C_550))), inference(superposition, [status(thm), theory('equality')], [c_12, c_3732])).
% 12.98/5.20  tff(c_7509, plain, (![C_567]: (m1_subset_1(C_567, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(C_567), k1_xboole_0) | ~v1_relat_1(C_567))), inference(resolution, [status(thm)], [c_6, c_7134])).
% 12.98/5.20  tff(c_7515, plain, (![B_297]: (m1_subset_1(k2_zfmisc_1('#skF_1', B_297), k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_1', k1_xboole_0) | ~v1_relat_1(k2_zfmisc_1('#skF_1', B_297)))), inference(superposition, [status(thm), theory('equality')], [c_6547, c_7509])).
% 12.98/5.20  tff(c_7735, plain, (![B_584]: (m1_subset_1(k2_zfmisc_1('#skF_1', B_584), k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_6089, c_7515])).
% 12.98/5.20  tff(c_7831, plain, (![B_590]: (r1_tarski(k2_zfmisc_1('#skF_1', B_590), k1_xboole_0))), inference(resolution, [status(thm)], [c_7735, c_14])).
% 12.98/5.20  tff(c_7853, plain, (![B_590]: (k2_zfmisc_1('#skF_1', B_590)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k2_zfmisc_1('#skF_1', B_590)))), inference(resolution, [status(thm)], [c_7831, c_2])).
% 12.98/5.20  tff(c_7895, plain, (![B_591]: (k2_zfmisc_1('#skF_1', B_591)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7563, c_7853])).
% 12.98/5.20  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.98/5.20  tff(c_7977, plain, (![B_591]: (k1_xboole_0=B_591 | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7895, c_8])).
% 12.98/5.20  tff(c_8015, plain, (![B_592]: (k1_xboole_0=B_592)), inference(negUnitSimplification, [status(thm)], [c_6612, c_7977])).
% 12.98/5.20  tff(c_6549, plain, (![A_523]: (k2_relat_1(A_523)='#skF_1' | ~v1_relat_1(A_523) | ~r1_tarski(A_523, k1_xboole_0))), inference(resolution, [status(thm)], [c_3369, c_6305])).
% 12.98/5.20  tff(c_6556, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_5983, c_6549])).
% 12.98/5.20  tff(c_6574, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_138, c_6556])).
% 12.98/5.20  tff(c_7544, plain, (![A_569, B_570]: (r1_tarski('#skF_4', k2_zfmisc_1(A_569, B_570)) | ~r1_tarski('#skF_1', B_570) | ~r1_tarski(k1_relat_1('#skF_4'), A_569) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6574, c_7540])).
% 12.98/5.20  tff(c_7610, plain, (![A_573, B_574]: (r1_tarski('#skF_4', k2_zfmisc_1(A_573, B_574)))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_6089, c_3964, c_6089, c_7544])).
% 12.98/5.20  tff(c_7613, plain, (![A_573, B_574]: (k1_relset_1(A_573, B_574, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_7610, c_3604])).
% 12.98/5.20  tff(c_7636, plain, (![A_573, B_574]: (k1_relset_1(A_573, B_574, '#skF_4')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3964, c_7613])).
% 12.98/5.20  tff(c_8031, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_8015, c_7636])).
% 12.98/5.20  tff(c_8457, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6612, c_8031])).
% 12.98/5.20  tff(c_8459, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_3769])).
% 12.98/5.20  tff(c_8527, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10) | ~v4_relat_1(k1_xboole_0, A_10) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8459, c_22])).
% 12.98/5.20  tff(c_8541, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_3441, c_8527])).
% 12.98/5.20  tff(c_11746, plain, (![A_10]: (r1_tarski('#skF_3', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_11690, c_8541])).
% 12.98/5.20  tff(c_112, plain, (![B_43, A_44]: (B_43=A_44 | ~r1_tarski(B_43, A_44) | ~r1_tarski(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.98/5.20  tff(c_120, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_112])).
% 12.98/5.20  tff(c_3370, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_120])).
% 12.98/5.20  tff(c_3656, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3655, c_3370])).
% 12.98/5.20  tff(c_11832, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11746, c_3656])).
% 12.98/5.20  tff(c_11834, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_11533])).
% 12.98/5.20  tff(c_8667, plain, (![B_1879, C_1880, A_1881]: (k1_xboole_0=B_1879 | v1_funct_2(C_1880, A_1881, B_1879) | k1_relset_1(A_1881, B_1879, C_1880)!=A_1881 | ~m1_subset_1(C_1880, k1_zfmisc_1(k2_zfmisc_1(A_1881, B_1879))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.98/5.20  tff(c_12248, plain, (![B_2102, A_2103, A_2104]: (k1_xboole_0=B_2102 | v1_funct_2(A_2103, A_2104, B_2102) | k1_relset_1(A_2104, B_2102, A_2103)!=A_2104 | ~r1_tarski(A_2103, k2_zfmisc_1(A_2104, B_2102)))), inference(resolution, [status(thm)], [c_16, c_8667])).
% 12.98/5.20  tff(c_12254, plain, (![A_2041]: (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', A_2041, '#skF_3') | k1_relset_1(A_2041, '#skF_3', '#skF_4')!=A_2041 | ~r1_tarski('#skF_1', A_2041))), inference(resolution, [status(thm)], [c_10832, c_12248])).
% 12.98/5.20  tff(c_12325, plain, (![A_2107]: (v1_funct_2('#skF_4', A_2107, '#skF_3') | k1_relset_1(A_2107, '#skF_3', '#skF_4')!=A_2107 | ~r1_tarski('#skF_1', A_2107))), inference(negUnitSimplification, [status(thm)], [c_11834, c_12254])).
% 12.98/5.20  tff(c_12334, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_12325, c_152])).
% 12.98/5.20  tff(c_12340, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_10878, c_12334])).
% 12.98/5.20  tff(c_12341, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_120])).
% 12.98/5.20  tff(c_16865, plain, (![A_2390, B_2391, C_2392]: (k2_relset_1(A_2390, B_2391, C_2392)=k2_relat_1(C_2392) | ~m1_subset_1(C_2392, k1_zfmisc_1(k2_zfmisc_1(A_2390, B_2391))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.98/5.20  tff(c_16872, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_16865])).
% 12.98/5.20  tff(c_16881, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12341, c_16872])).
% 12.98/5.20  tff(c_26, plain, (![B_13, A_12]: (r1_tarski(k2_relat_1(B_13), A_12) | ~v5_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.98/5.20  tff(c_16888, plain, (![A_12]: (r1_tarski('#skF_3', A_12) | ~v5_relat_1('#skF_4', A_12) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_16881, c_26])).
% 12.98/5.20  tff(c_16906, plain, (![A_2393]: (r1_tarski('#skF_3', A_2393) | ~v5_relat_1('#skF_4', A_2393))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_16888])).
% 12.98/5.20  tff(c_16923, plain, (![B_279]: (r1_tarski('#skF_3', B_279) | ~r1_tarski('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_3369, c_16906])).
% 12.98/5.20  tff(c_16942, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_16923])).
% 12.98/5.20  tff(c_16817, plain, (![A_2385, B_2386, C_2387]: (k1_relset_1(A_2385, B_2386, C_2387)=k1_relat_1(C_2387) | ~m1_subset_1(C_2387, k1_zfmisc_1(k2_zfmisc_1(A_2385, B_2386))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.98/5.20  tff(c_16832, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_16817])).
% 12.98/5.20  tff(c_17106, plain, (![B_2420, A_2421, C_2422]: (k1_xboole_0=B_2420 | k1_relset_1(A_2421, B_2420, C_2422)=A_2421 | ~v1_funct_2(C_2422, A_2421, B_2420) | ~m1_subset_1(C_2422, k1_zfmisc_1(k2_zfmisc_1(A_2421, B_2420))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.98/5.20  tff(c_17116, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_17106])).
% 12.98/5.20  tff(c_17127, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_16832, c_17116])).
% 12.98/5.20  tff(c_17128, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_74, c_17127])).
% 12.98/5.20  tff(c_16979, plain, (![C_2402, A_2403, B_2404]: (m1_subset_1(C_2402, k1_zfmisc_1(k2_zfmisc_1(A_2403, B_2404))) | ~r1_tarski(k2_relat_1(C_2402), B_2404) | ~r1_tarski(k1_relat_1(C_2402), A_2403) | ~v1_relat_1(C_2402))), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.98/5.20  tff(c_17838, plain, (![C_2487, A_2488]: (m1_subset_1(C_2487, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_2487), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_2487), A_2488) | ~v1_relat_1(C_2487))), inference(superposition, [status(thm), theory('equality')], [c_10, c_16979])).
% 12.98/5.20  tff(c_17840, plain, (![A_2488]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_4'), A_2488) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_16881, c_17838])).
% 12.98/5.20  tff(c_17845, plain, (![A_2488]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_1', A_2488))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_17128, c_17840])).
% 12.98/5.20  tff(c_17867, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_17845])).
% 12.98/5.20  tff(c_3357, plain, (![B_274, A_275]: (v5_relat_1(B_274, A_275) | ~r1_tarski(k2_relat_1(B_274), A_275) | ~v1_relat_1(B_274))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.98/5.20  tff(c_3362, plain, (![B_274]: (v5_relat_1(B_274, k2_relat_1(B_274)) | ~v1_relat_1(B_274))), inference(resolution, [status(thm)], [c_6, c_3357])).
% 12.98/5.20  tff(c_16891, plain, (v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_16881, c_3362])).
% 12.98/5.20  tff(c_16902, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_16891])).
% 12.98/5.20  tff(c_36, plain, (![A_22, B_23, C_24]: (k1_relset_1(A_22, B_23, C_24)=k1_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.98/5.20  tff(c_18687, plain, (![A_2519, B_2520, C_2521]: (k1_relset_1(A_2519, B_2520, C_2521)=k1_relat_1(C_2521) | ~r1_tarski(k2_relat_1(C_2521), B_2520) | ~r1_tarski(k1_relat_1(C_2521), A_2519) | ~v1_relat_1(C_2521))), inference(resolution, [status(thm)], [c_16979, c_36])).
% 12.98/5.20  tff(c_18691, plain, (![A_2519, B_2520]: (k1_relset_1(A_2519, B_2520, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_3', B_2520) | ~r1_tarski(k1_relat_1('#skF_4'), A_2519) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_16881, c_18687])).
% 12.98/5.20  tff(c_18762, plain, (![A_2523, B_2524]: (k1_relset_1(A_2523, B_2524, '#skF_4')='#skF_1' | ~r1_tarski('#skF_3', B_2524) | ~r1_tarski('#skF_1', A_2523))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_17128, c_17128, c_18691])).
% 12.98/5.20  tff(c_19623, plain, (![A_2550]: (k1_relset_1(A_2550, '#skF_3', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_2550))), inference(resolution, [status(thm)], [c_6, c_18762])).
% 12.98/5.20  tff(c_19628, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_6, c_19623])).
% 12.98/5.20  tff(c_40, plain, (![C_30, A_28, B_29]: (m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~r1_tarski(k2_relat_1(C_30), B_29) | ~r1_tarski(k1_relat_1(C_30), A_28) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.98/5.20  tff(c_17228, plain, (![B_2430, C_2431, A_2432]: (k1_xboole_0=B_2430 | v1_funct_2(C_2431, A_2432, B_2430) | k1_relset_1(A_2432, B_2430, C_2431)!=A_2432 | ~m1_subset_1(C_2431, k1_zfmisc_1(k2_zfmisc_1(A_2432, B_2430))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.98/5.20  tff(c_19723, plain, (![B_2553, C_2554, A_2555]: (k1_xboole_0=B_2553 | v1_funct_2(C_2554, A_2555, B_2553) | k1_relset_1(A_2555, B_2553, C_2554)!=A_2555 | ~r1_tarski(k2_relat_1(C_2554), B_2553) | ~r1_tarski(k1_relat_1(C_2554), A_2555) | ~v1_relat_1(C_2554))), inference(resolution, [status(thm)], [c_40, c_17228])).
% 12.98/5.20  tff(c_19735, plain, (![B_2553, A_2555]: (k1_xboole_0=B_2553 | v1_funct_2('#skF_4', A_2555, B_2553) | k1_relset_1(A_2555, B_2553, '#skF_4')!=A_2555 | ~r1_tarski('#skF_3', B_2553) | ~r1_tarski(k1_relat_1('#skF_4'), A_2555) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_16881, c_19723])).
% 12.98/5.20  tff(c_19855, plain, (![B_2557, A_2558]: (k1_xboole_0=B_2557 | v1_funct_2('#skF_4', A_2558, B_2557) | k1_relset_1(A_2558, B_2557, '#skF_4')!=A_2558 | ~r1_tarski('#skF_3', B_2557) | ~r1_tarski('#skF_1', A_2558))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_17128, c_19735])).
% 12.98/5.20  tff(c_19866, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_19855, c_152])).
% 12.98/5.20  tff(c_19874, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_19628, c_19866])).
% 12.98/5.20  tff(c_12460, plain, (![B_2131, A_2132]: (r1_tarski(k2_relat_1(B_2131), A_2132) | ~v5_relat_1(B_2131, A_2132) | ~v1_relat_1(B_2131))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.98/5.20  tff(c_12377, plain, (![C_2115, A_2116, B_2117]: (v4_relat_1(C_2115, A_2116) | ~m1_subset_1(C_2115, k1_zfmisc_1(k2_zfmisc_1(A_2116, B_2117))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.98/5.20  tff(c_12391, plain, (![A_5, A_2116, B_2117]: (v4_relat_1(A_5, A_2116) | ~r1_tarski(A_5, k2_zfmisc_1(A_2116, B_2117)))), inference(resolution, [status(thm)], [c_16, c_12377])).
% 12.98/5.20  tff(c_17766, plain, (![B_2482, A_2483, B_2484]: (v4_relat_1(k2_relat_1(B_2482), A_2483) | ~v5_relat_1(B_2482, k2_zfmisc_1(A_2483, B_2484)) | ~v1_relat_1(B_2482))), inference(resolution, [status(thm)], [c_12460, c_12391])).
% 12.98/5.20  tff(c_17952, plain, (![B_2497]: (v4_relat_1(k2_relat_1(B_2497), k1_xboole_0) | ~v5_relat_1(B_2497, k1_xboole_0) | ~v1_relat_1(B_2497))), inference(superposition, [status(thm), theory('equality')], [c_12, c_17766])).
% 12.98/5.20  tff(c_17957, plain, (v4_relat_1('#skF_3', k1_xboole_0) | ~v5_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_16881, c_17952])).
% 12.98/5.20  tff(c_17962, plain, (v4_relat_1('#skF_3', k1_xboole_0) | ~v5_relat_1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_138, c_17957])).
% 12.98/5.20  tff(c_17963, plain, (~v5_relat_1('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_17962])).
% 12.98/5.20  tff(c_19937, plain, (~v5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19874, c_17963])).
% 12.98/5.20  tff(c_20006, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16902, c_19937])).
% 12.98/5.20  tff(c_20008, plain, (v5_relat_1('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_17962])).
% 12.98/5.20  tff(c_16900, plain, (![A_12]: (r1_tarski('#skF_3', A_12) | ~v5_relat_1('#skF_4', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_16888])).
% 12.98/5.20  tff(c_20021, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_20008, c_16900])).
% 12.98/5.20  tff(c_20029, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17867, c_20021])).
% 12.98/5.20  tff(c_20030, plain, (![A_2488]: (~r1_tarski('#skF_1', A_2488) | m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_17845])).
% 12.98/5.20  tff(c_20089, plain, (![A_2563]: (~r1_tarski('#skF_1', A_2563))), inference(splitLeft, [status(thm)], [c_20030])).
% 12.98/5.20  tff(c_20094, plain, $false, inference(resolution, [status(thm)], [c_6, c_20089])).
% 12.98/5.20  tff(c_20095, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_20030])).
% 12.98/5.20  tff(c_20118, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_20095, c_14])).
% 12.98/5.20  tff(c_20138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16942, c_20118])).
% 12.98/5.20  tff(c_20140, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_16923])).
% 12.98/5.20  tff(c_12396, plain, (![C_2119, A_2120]: (v4_relat_1(C_2119, A_2120) | ~m1_subset_1(C_2119, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_12377])).
% 12.98/5.20  tff(c_12400, plain, (![A_5, A_2120]: (v4_relat_1(A_5, A_2120) | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_12396])).
% 12.98/5.20  tff(c_20145, plain, (![B_2564]: (r1_tarski('#skF_3', B_2564))), inference(splitRight, [status(thm)], [c_16923])).
% 12.98/5.20  tff(c_20207, plain, (![B_2570]: (B_2570='#skF_3' | ~r1_tarski(B_2570, '#skF_3'))), inference(resolution, [status(thm)], [c_20145, c_2])).
% 12.98/5.20  tff(c_20372, plain, (![B_2575]: (k1_relat_1(B_2575)='#skF_3' | ~v4_relat_1(B_2575, '#skF_3') | ~v1_relat_1(B_2575))), inference(resolution, [status(thm)], [c_22, c_20207])).
% 12.98/5.20  tff(c_20555, plain, (![A_2584]: (k1_relat_1(A_2584)='#skF_3' | ~v1_relat_1(A_2584) | ~r1_tarski(A_2584, k1_xboole_0))), inference(resolution, [status(thm)], [c_12400, c_20372])).
% 12.98/5.20  tff(c_20558, plain, (k1_relat_1('#skF_4')='#skF_3' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20140, c_20555])).
% 12.98/5.20  tff(c_20577, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_138, c_20558])).
% 12.98/5.20  tff(c_20586, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20577, c_16832])).
% 12.98/5.20  tff(c_21077, plain, (![B_2620, A_2621, C_2622]: (k1_xboole_0=B_2620 | k1_relset_1(A_2621, B_2620, C_2622)=A_2621 | ~v1_funct_2(C_2622, A_2621, B_2620) | ~m1_subset_1(C_2622, k1_zfmisc_1(k2_zfmisc_1(A_2621, B_2620))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.98/5.20  tff(c_21087, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_21077])).
% 12.98/5.20  tff(c_21098, plain, (k1_xboole_0='#skF_2' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_20586, c_21087])).
% 12.98/5.20  tff(c_21099, plain, ('#skF_3'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_74, c_21098])).
% 12.98/5.20  tff(c_20139, plain, (![B_279]: (r1_tarski('#skF_3', B_279))), inference(splitRight, [status(thm)], [c_16923])).
% 12.98/5.20  tff(c_21129, plain, (![B_279]: (r1_tarski('#skF_1', B_279))), inference(demodulation, [status(thm), theory('equality')], [c_21099, c_20139])).
% 12.98/5.20  tff(c_12402, plain, (![A_2123, A_2124, B_2125]: (v4_relat_1(A_2123, A_2124) | ~r1_tarski(A_2123, k2_zfmisc_1(A_2124, B_2125)))), inference(resolution, [status(thm)], [c_16, c_12377])).
% 12.98/5.20  tff(c_12451, plain, (![A_2128, B_2129]: (v4_relat_1(k2_zfmisc_1(A_2128, B_2129), A_2128))), inference(resolution, [status(thm)], [c_6, c_12402])).
% 12.98/5.20  tff(c_12454, plain, (![A_3]: (v4_relat_1(k1_xboole_0, A_3))), inference(superposition, [status(thm), theory('equality')], [c_10, c_12451])).
% 12.98/5.20  tff(c_20380, plain, (k1_relat_1(k1_xboole_0)='#skF_3' | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_12454, c_20372])).
% 12.98/5.20  tff(c_20394, plain, (k1_relat_1(k1_xboole_0)='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_79, c_20380])).
% 12.98/5.20  tff(c_12494, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_70])).
% 12.98/5.20  tff(c_12497, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_12494])).
% 12.98/5.20  tff(c_12501, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_12497])).
% 12.98/5.20  tff(c_12503, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_70])).
% 12.98/5.20  tff(c_21068, plain, (![B_2618, C_2619]: (k1_relset_1(k1_xboole_0, B_2618, C_2619)=k1_relat_1(C_2619) | ~m1_subset_1(C_2619, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_16817])).
% 12.98/5.20  tff(c_21070, plain, (![B_2618]: (k1_relset_1(k1_xboole_0, B_2618, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_12503, c_21068])).
% 12.98/5.20  tff(c_21075, plain, (![B_2618]: (k1_relset_1(k1_xboole_0, B_2618, k1_xboole_0)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20394, c_21070])).
% 12.98/5.20  tff(c_21411, plain, (![B_2618]: (k1_relset_1(k1_xboole_0, B_2618, k1_xboole_0)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_21099, c_21075])).
% 12.98/5.20  tff(c_20516, plain, (![C_2581, B_2582]: (v1_funct_2(C_2581, k1_xboole_0, B_2582) | k1_relset_1(k1_xboole_0, B_2582, C_2581)!=k1_xboole_0 | ~m1_subset_1(C_2581, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_46])).
% 12.98/5.20  tff(c_20522, plain, (![B_2582]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_2582) | k1_relset_1(k1_xboole_0, B_2582, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12503, c_20516])).
% 12.98/5.20  tff(c_21412, plain, (![B_2582]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_2582) | k1_xboole_0!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_21411, c_20522])).
% 12.98/5.20  tff(c_21744, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_21412])).
% 12.98/5.20  tff(c_12418, plain, (![A_2124, B_2125]: (v4_relat_1(k2_zfmisc_1(A_2124, B_2125), A_2124))), inference(resolution, [status(thm)], [c_6, c_12402])).
% 12.98/5.20  tff(c_20384, plain, (![B_2125]: (k1_relat_1(k2_zfmisc_1('#skF_3', B_2125))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_3', B_2125)))), inference(resolution, [status(thm)], [c_12418, c_20372])).
% 12.98/5.20  tff(c_20397, plain, (![B_2125]: (k1_relat_1(k2_zfmisc_1('#skF_3', B_2125))='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_20384])).
% 12.98/5.20  tff(c_21118, plain, (![B_2125]: (k1_relat_1(k2_zfmisc_1('#skF_1', B_2125))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_21099, c_21099, c_20397])).
% 12.98/5.20  tff(c_20672, plain, (![C_2590, A_2591, B_2592]: (m1_subset_1(C_2590, k1_zfmisc_1(k2_zfmisc_1(A_2591, B_2592))) | ~r1_tarski(k2_relat_1(C_2590), B_2592) | ~r1_tarski(k1_relat_1(C_2590), A_2591) | ~v1_relat_1(C_2590))), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.98/5.20  tff(c_22017, plain, (![C_2666, B_2667]: (m1_subset_1(C_2666, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_2666), B_2667) | ~r1_tarski(k1_relat_1(C_2666), k1_xboole_0) | ~v1_relat_1(C_2666))), inference(superposition, [status(thm), theory('equality')], [c_12, c_20672])).
% 12.98/5.20  tff(c_22544, plain, (![C_2700]: (m1_subset_1(C_2700, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(C_2700), k1_xboole_0) | ~v1_relat_1(C_2700))), inference(resolution, [status(thm)], [c_6, c_22017])).
% 12.98/5.20  tff(c_22550, plain, (![B_2125]: (m1_subset_1(k2_zfmisc_1('#skF_1', B_2125), k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_1', k1_xboole_0) | ~v1_relat_1(k2_zfmisc_1('#skF_1', B_2125)))), inference(superposition, [status(thm), theory('equality')], [c_21118, c_22544])).
% 12.98/5.20  tff(c_22607, plain, (![B_2704]: (m1_subset_1(k2_zfmisc_1('#skF_1', B_2704), k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_21129, c_22550])).
% 12.98/5.20  tff(c_22670, plain, (![B_2707]: (r1_tarski(k2_zfmisc_1('#skF_1', B_2707), k1_xboole_0))), inference(resolution, [status(thm)], [c_22607, c_14])).
% 12.98/5.20  tff(c_21119, plain, (k1_relat_1(k1_xboole_0)='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_21099, c_20394])).
% 12.98/5.20  tff(c_12353, plain, (![A_2110, B_2111, A_2112]: (v5_relat_1(A_2110, B_2111) | ~r1_tarski(A_2110, k2_zfmisc_1(A_2112, B_2111)))), inference(resolution, [status(thm)], [c_16, c_3335])).
% 12.98/5.20  tff(c_12370, plain, (![A_2113, B_2114]: (v5_relat_1(k2_zfmisc_1(A_2113, B_2114), B_2114))), inference(resolution, [status(thm)], [c_6, c_12353])).
% 12.98/5.20  tff(c_12376, plain, (![B_4]: (v5_relat_1(k1_xboole_0, B_4))), inference(superposition, [status(thm), theory('equality')], [c_12, c_12370])).
% 12.98/5.20  tff(c_20251, plain, (![B_2571]: (k2_relat_1(B_2571)='#skF_3' | ~v5_relat_1(B_2571, '#skF_3') | ~v1_relat_1(B_2571))), inference(resolution, [status(thm)], [c_26, c_20207])).
% 12.98/5.20  tff(c_20263, plain, (k2_relat_1(k1_xboole_0)='#skF_3' | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_12376, c_20251])).
% 12.98/5.20  tff(c_20280, plain, (k2_relat_1(k1_xboole_0)='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_79, c_20263])).
% 12.98/5.20  tff(c_21123, plain, (k2_relat_1(k1_xboole_0)='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_21099, c_20280])).
% 12.98/5.20  tff(c_22371, plain, (![C_2681, A_2682, B_2683]: (r1_tarski(C_2681, k2_zfmisc_1(A_2682, B_2683)) | ~r1_tarski(k2_relat_1(C_2681), B_2683) | ~r1_tarski(k1_relat_1(C_2681), A_2682) | ~v1_relat_1(C_2681))), inference(resolution, [status(thm)], [c_20672, c_14])).
% 12.98/5.20  tff(c_22379, plain, (![A_2682, B_2683]: (r1_tarski(k1_xboole_0, k2_zfmisc_1(A_2682, B_2683)) | ~r1_tarski('#skF_1', B_2683) | ~r1_tarski(k1_relat_1(k1_xboole_0), A_2682) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_21123, c_22371])).
% 12.98/5.20  tff(c_22403, plain, (![A_2684, B_2685]: (r1_tarski(k1_xboole_0, k2_zfmisc_1(A_2684, B_2685)))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_21129, c_21119, c_21129, c_22379])).
% 12.98/5.20  tff(c_22441, plain, (![A_2684, B_2685]: (k2_zfmisc_1(A_2684, B_2685)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_2684, B_2685), k1_xboole_0))), inference(resolution, [status(thm)], [c_22403, c_2])).
% 12.98/5.20  tff(c_22806, plain, (![B_2709]: (k2_zfmisc_1('#skF_1', B_2709)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22670, c_22441])).
% 12.98/5.20  tff(c_22876, plain, (![B_2709]: (k1_xboole_0=B_2709 | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_22806, c_8])).
% 12.98/5.20  tff(c_22912, plain, (![B_2710]: (k1_xboole_0=B_2710)), inference(negUnitSimplification, [status(thm)], [c_21744, c_22876])).
% 12.98/5.20  tff(c_16831, plain, (![A_2385, B_2386, A_5]: (k1_relset_1(A_2385, B_2386, A_5)=k1_relat_1(A_5) | ~r1_tarski(A_5, k2_zfmisc_1(A_2385, B_2386)))), inference(resolution, [status(thm)], [c_16, c_16817])).
% 12.98/5.20  tff(c_22409, plain, (![A_2684, B_2685]: (k1_relset_1(A_2684, B_2685, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_22403, c_16831])).
% 12.98/5.20  tff(c_22431, plain, (![A_2684, B_2685]: (k1_relset_1(A_2684, B_2685, k1_xboole_0)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_21119, c_22409])).
% 12.98/5.20  tff(c_22935, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_22912, c_22431])).
% 12.98/5.20  tff(c_23330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21744, c_22935])).
% 12.98/5.20  tff(c_23332, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_21412])).
% 12.98/5.20  tff(c_20189, plain, (k1_xboole_0='#skF_4' | ~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_20140, c_2])).
% 12.98/5.20  tff(c_20230, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(splitLeft, [status(thm)], [c_20189])).
% 12.98/5.20  tff(c_23354, plain, (~r1_tarski('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_23332, c_20230])).
% 12.98/5.20  tff(c_23382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21129, c_23354])).
% 12.98/5.20  tff(c_23383, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_20189])).
% 12.98/5.20  tff(c_23404, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_23383, c_74])).
% 12.98/5.20  tff(c_23392, plain, (![A_3]: (v4_relat_1('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_23383, c_12454])).
% 12.98/5.20  tff(c_23441, plain, (![B_3858]: (k1_relat_1(B_3858)='#skF_3' | ~v4_relat_1(B_3858, '#skF_3') | ~v1_relat_1(B_3858))), inference(resolution, [status(thm)], [c_22, c_20207])).
% 12.98/5.20  tff(c_23445, plain, (k1_relat_1('#skF_4')='#skF_3' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_23392, c_23441])).
% 12.98/5.20  tff(c_23456, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_138, c_23445])).
% 12.98/5.20  tff(c_23463, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_23456, c_16832])).
% 12.98/5.20  tff(c_52, plain, (![B_32, A_31, C_33]: (k1_xboole_0=B_32 | k1_relset_1(A_31, B_32, C_33)=A_31 | ~v1_funct_2(C_33, A_31, B_32) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.98/5.20  tff(c_23897, plain, (![B_3888, A_3889, C_3890]: (B_3888='#skF_4' | k1_relset_1(A_3889, B_3888, C_3890)=A_3889 | ~v1_funct_2(C_3890, A_3889, B_3888) | ~m1_subset_1(C_3890, k1_zfmisc_1(k2_zfmisc_1(A_3889, B_3888))))), inference(demodulation, [status(thm), theory('equality')], [c_23383, c_52])).
% 12.98/5.20  tff(c_23913, plain, ('#skF_2'='#skF_4' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_23897])).
% 12.98/5.20  tff(c_23919, plain, ('#skF_2'='#skF_4' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_23463, c_23913])).
% 12.98/5.20  tff(c_23920, plain, ('#skF_3'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_23404, c_23919])).
% 12.98/5.20  tff(c_23935, plain, (![B_279]: (r1_tarski('#skF_1', B_279))), inference(demodulation, [status(thm), theory('equality')], [c_23920, c_20139])).
% 12.98/5.20  tff(c_23453, plain, (![B_2125]: (k1_relat_1(k2_zfmisc_1('#skF_3', B_2125))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_3', B_2125)))), inference(resolution, [status(thm)], [c_12418, c_23441])).
% 12.98/5.20  tff(c_23462, plain, (![B_2125]: (k1_relat_1(k2_zfmisc_1('#skF_3', B_2125))='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_23453])).
% 12.98/5.20  tff(c_23927, plain, (![B_2125]: (k1_relat_1(k2_zfmisc_1('#skF_1', B_2125))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_23920, c_23920, c_23462])).
% 12.98/5.20  tff(c_23403, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_23383, c_23383, c_12])).
% 12.98/5.20  tff(c_23697, plain, (![C_3872, A_3873, B_3874]: (m1_subset_1(C_3872, k1_zfmisc_1(k2_zfmisc_1(A_3873, B_3874))) | ~r1_tarski(k2_relat_1(C_3872), B_3874) | ~r1_tarski(k1_relat_1(C_3872), A_3873) | ~v1_relat_1(C_3872))), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.98/5.20  tff(c_25153, plain, (![C_3975, A_3976, B_3977]: (r1_tarski(C_3975, k2_zfmisc_1(A_3976, B_3977)) | ~r1_tarski(k2_relat_1(C_3975), B_3977) | ~r1_tarski(k1_relat_1(C_3975), A_3976) | ~v1_relat_1(C_3975))), inference(resolution, [status(thm)], [c_23697, c_14])).
% 12.98/5.20  tff(c_26953, plain, (![C_4066, A_4067]: (r1_tarski(C_4066, k2_zfmisc_1(A_4067, k2_relat_1(C_4066))) | ~r1_tarski(k1_relat_1(C_4066), A_4067) | ~v1_relat_1(C_4066))), inference(resolution, [status(thm)], [c_6, c_25153])).
% 12.98/5.20  tff(c_27137, plain, (![C_4071]: (r1_tarski(C_4071, '#skF_4') | ~r1_tarski(k1_relat_1(C_4071), '#skF_4') | ~v1_relat_1(C_4071))), inference(superposition, [status(thm), theory('equality')], [c_23403, c_26953])).
% 12.98/5.20  tff(c_27152, plain, (![B_2125]: (r1_tarski(k2_zfmisc_1('#skF_1', B_2125), '#skF_4') | ~r1_tarski('#skF_1', '#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', B_2125)))), inference(superposition, [status(thm), theory('equality')], [c_23927, c_27137])).
% 12.98/5.20  tff(c_27172, plain, (![B_2125]: (r1_tarski(k2_zfmisc_1('#skF_1', B_2125), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_23935, c_27152])).
% 12.98/5.20  tff(c_103, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | ~m1_subset_1(A_41, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.98/5.20  tff(c_111, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_103])).
% 12.98/5.20  tff(c_119, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_111, c_112])).
% 12.98/5.20  tff(c_12395, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_4')), inference(splitLeft, [status(thm)], [c_119])).
% 12.98/5.20  tff(c_27248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27172, c_12395])).
% 12.98/5.20  tff(c_27249, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_4'), inference(splitRight, [status(thm)], [c_119])).
% 12.98/5.20  tff(c_27252, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_27249, c_60])).
% 12.98/5.20  tff(c_27269, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_27249, c_8])).
% 12.98/5.20  tff(c_27279, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_74, c_27269])).
% 12.98/5.20  tff(c_27293, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_27279])).
% 12.98/5.20  tff(c_27628, plain, (![A_4117, B_4118, C_4119]: (k2_relset_1(A_4117, B_4118, C_4119)=k2_relat_1(C_4119) | ~m1_subset_1(C_4119, k1_zfmisc_1(k2_zfmisc_1(A_4117, B_4118))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.98/5.20  tff(c_27662, plain, (![C_4125]: (k2_relset_1('#skF_1', '#skF_2', C_4125)=k2_relat_1(C_4125) | ~m1_subset_1(C_4125, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_27249, c_27628])).
% 12.98/5.20  tff(c_27665, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_27252, c_27662])).
% 12.98/5.20  tff(c_27671, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12341, c_27665])).
% 12.98/5.20  tff(c_27685, plain, (![A_12]: (r1_tarski('#skF_3', A_12) | ~v5_relat_1('#skF_4', A_12) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_27671, c_26])).
% 12.98/5.20  tff(c_27707, plain, (![A_4126]: (r1_tarski('#skF_3', A_4126) | ~v5_relat_1('#skF_4', A_4126))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_27685])).
% 12.98/5.20  tff(c_27731, plain, (![B_279]: (r1_tarski('#skF_3', B_279) | ~r1_tarski('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_3369, c_27707])).
% 12.98/5.20  tff(c_27787, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_27731])).
% 12.98/5.20  tff(c_27745, plain, (![A_4127, B_4128, C_4129]: (k1_relset_1(A_4127, B_4128, C_4129)=k1_relat_1(C_4129) | ~m1_subset_1(C_4129, k1_zfmisc_1(k2_zfmisc_1(A_4127, B_4128))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.98/5.20  tff(c_27773, plain, (![C_4131]: (k1_relset_1('#skF_1', '#skF_2', C_4131)=k1_relat_1(C_4131) | ~m1_subset_1(C_4131, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_27249, c_27745])).
% 12.98/5.20  tff(c_27781, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_27252, c_27773])).
% 12.98/5.20  tff(c_28151, plain, (![B_4173, A_4174, C_4175]: (k1_xboole_0=B_4173 | k1_relset_1(A_4174, B_4173, C_4175)=A_4174 | ~v1_funct_2(C_4175, A_4174, B_4173) | ~m1_subset_1(C_4175, k1_zfmisc_1(k2_zfmisc_1(A_4174, B_4173))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.98/5.20  tff(c_28157, plain, (![C_4175]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_4175)='#skF_1' | ~v1_funct_2(C_4175, '#skF_1', '#skF_2') | ~m1_subset_1(C_4175, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_27249, c_28151])).
% 12.98/5.20  tff(c_28247, plain, (![C_4184]: (k1_relset_1('#skF_1', '#skF_2', C_4184)='#skF_1' | ~v1_funct_2(C_4184, '#skF_1', '#skF_2') | ~m1_subset_1(C_4184, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_74, c_28157])).
% 12.98/5.20  tff(c_28250, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_27252, c_28247])).
% 12.98/5.20  tff(c_28257, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_27781, c_28250])).
% 12.98/5.20  tff(c_27990, plain, (![C_4158, A_4159, B_4160]: (m1_subset_1(C_4158, k1_zfmisc_1(k2_zfmisc_1(A_4159, B_4160))) | ~r1_tarski(k2_relat_1(C_4158), B_4160) | ~r1_tarski(k1_relat_1(C_4158), A_4159) | ~v1_relat_1(C_4158))), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.98/5.20  tff(c_29621, plain, (![A_4273, B_4274, C_4275]: (k1_relset_1(A_4273, B_4274, C_4275)=k1_relat_1(C_4275) | ~r1_tarski(k2_relat_1(C_4275), B_4274) | ~r1_tarski(k1_relat_1(C_4275), A_4273) | ~v1_relat_1(C_4275))), inference(resolution, [status(thm)], [c_27990, c_36])).
% 12.98/5.20  tff(c_29623, plain, (![A_4273, B_4274]: (k1_relset_1(A_4273, B_4274, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_3', B_4274) | ~r1_tarski(k1_relat_1('#skF_4'), A_4273) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_27671, c_29621])).
% 12.98/5.20  tff(c_30002, plain, (![A_4292, B_4293]: (k1_relset_1(A_4292, B_4293, '#skF_4')='#skF_1' | ~r1_tarski('#skF_3', B_4293) | ~r1_tarski('#skF_1', A_4292))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_28257, c_28257, c_29623])).
% 12.98/5.20  tff(c_30054, plain, (![A_4300]: (k1_relset_1(A_4300, '#skF_3', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_4300))), inference(resolution, [status(thm)], [c_6, c_30002])).
% 12.98/5.20  tff(c_30059, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_6, c_30054])).
% 12.98/5.20  tff(c_28329, plain, (![B_4186, C_4187, A_4188]: (k1_xboole_0=B_4186 | v1_funct_2(C_4187, A_4188, B_4186) | k1_relset_1(A_4188, B_4186, C_4187)!=A_4188 | ~m1_subset_1(C_4187, k1_zfmisc_1(k2_zfmisc_1(A_4188, B_4186))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.98/5.20  tff(c_30035, plain, (![B_4296, C_4297, A_4298]: (k1_xboole_0=B_4296 | v1_funct_2(C_4297, A_4298, B_4296) | k1_relset_1(A_4298, B_4296, C_4297)!=A_4298 | ~r1_tarski(k2_relat_1(C_4297), B_4296) | ~r1_tarski(k1_relat_1(C_4297), A_4298) | ~v1_relat_1(C_4297))), inference(resolution, [status(thm)], [c_40, c_28329])).
% 12.98/5.20  tff(c_30037, plain, (![B_4296, A_4298]: (k1_xboole_0=B_4296 | v1_funct_2('#skF_4', A_4298, B_4296) | k1_relset_1(A_4298, B_4296, '#skF_4')!=A_4298 | ~r1_tarski('#skF_3', B_4296) | ~r1_tarski(k1_relat_1('#skF_4'), A_4298) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_27671, c_30035])).
% 12.98/5.20  tff(c_32106, plain, (![B_4343, A_4344]: (k1_xboole_0=B_4343 | v1_funct_2('#skF_4', A_4344, B_4343) | k1_relset_1(A_4344, B_4343, '#skF_4')!=A_4344 | ~r1_tarski('#skF_3', B_4343) | ~r1_tarski('#skF_1', A_4344))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_28257, c_30037])).
% 12.98/5.20  tff(c_32125, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_32106, c_152])).
% 12.98/5.20  tff(c_32142, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_30059, c_32125])).
% 12.98/5.20  tff(c_24, plain, (![B_13, A_12]: (v5_relat_1(B_13, A_12) | ~r1_tarski(k2_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.98/5.20  tff(c_27691, plain, (![A_12]: (v5_relat_1('#skF_4', A_12) | ~r1_tarski('#skF_3', A_12) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_27671, c_24])).
% 12.98/5.20  tff(c_27705, plain, (![A_12]: (v5_relat_1('#skF_4', A_12) | ~r1_tarski('#skF_3', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_27691])).
% 12.98/5.20  tff(c_27370, plain, (![B_4085, A_4086]: (r1_tarski(k2_relat_1(B_4085), A_4086) | ~v5_relat_1(B_4085, A_4086) | ~v1_relat_1(B_4085))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.98/5.20  tff(c_3349, plain, (![A_5, B_271, A_272]: (v5_relat_1(A_5, B_271) | ~r1_tarski(A_5, k2_zfmisc_1(A_272, B_271)))), inference(resolution, [status(thm)], [c_16, c_3335])).
% 12.98/5.20  tff(c_28218, plain, (![B_4181, B_4182, A_4183]: (v5_relat_1(k2_relat_1(B_4181), B_4182) | ~v5_relat_1(B_4181, k2_zfmisc_1(A_4183, B_4182)) | ~v1_relat_1(B_4181))), inference(resolution, [status(thm)], [c_27370, c_3349])).
% 12.98/5.20  tff(c_28677, plain, (![B_4211, B_4212]: (v5_relat_1(k2_relat_1(B_4211), B_4212) | ~v5_relat_1(B_4211, k1_xboole_0) | ~v1_relat_1(B_4211))), inference(superposition, [status(thm), theory('equality')], [c_12, c_28218])).
% 12.98/5.20  tff(c_28689, plain, (![B_4212]: (v5_relat_1('#skF_3', B_4212) | ~v5_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_27671, c_28677])).
% 12.98/5.20  tff(c_28694, plain, (![B_4212]: (v5_relat_1('#skF_3', B_4212) | ~v5_relat_1('#skF_4', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_28689])).
% 12.98/5.20  tff(c_28695, plain, (~v5_relat_1('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_28694])).
% 12.98/5.20  tff(c_28711, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_27705, c_28695])).
% 12.98/5.20  tff(c_32244, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32142, c_28711])).
% 12.98/5.20  tff(c_32303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_32244])).
% 12.98/5.20  tff(c_32305, plain, (v5_relat_1('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_28694])).
% 12.98/5.20  tff(c_27701, plain, (![A_12]: (r1_tarski('#skF_3', A_12) | ~v5_relat_1('#skF_4', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_27685])).
% 12.98/5.20  tff(c_32337, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_32305, c_27701])).
% 12.98/5.20  tff(c_32422, plain, (![C_4351, A_4352]: (m1_subset_1(C_4351, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_4351), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_4351), A_4352) | ~v1_relat_1(C_4351))), inference(superposition, [status(thm), theory('equality')], [c_10, c_27990])).
% 12.98/5.20  tff(c_32424, plain, (![A_4352]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_4'), A_4352) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_27671, c_32422])).
% 12.98/5.20  tff(c_32429, plain, (![A_4352]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_1', A_4352))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_28257, c_32337, c_32424])).
% 12.98/5.20  tff(c_32448, plain, (![A_4355]: (~r1_tarski('#skF_1', A_4355))), inference(splitLeft, [status(thm)], [c_32429])).
% 12.98/5.20  tff(c_32453, plain, $false, inference(resolution, [status(thm)], [c_6, c_32448])).
% 12.98/5.20  tff(c_32454, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_32429])).
% 12.98/5.20  tff(c_32477, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_32454, c_14])).
% 12.98/5.20  tff(c_32497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27787, c_32477])).
% 12.98/5.20  tff(c_32499, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_27731])).
% 12.98/5.20  tff(c_32548, plain, (k1_xboole_0='#skF_4' | ~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_32499, c_2])).
% 12.98/5.20  tff(c_32556, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_27293, c_32548])).
% 12.98/5.20  tff(c_32498, plain, (![B_279]: (r1_tarski('#skF_3', B_279))), inference(splitRight, [status(thm)], [c_27731])).
% 12.98/5.20  tff(c_27414, plain, (![A_4089, A_4090, B_4091]: (v4_relat_1(A_4089, A_4090) | ~r1_tarski(A_4089, k2_zfmisc_1(A_4090, B_4091)))), inference(resolution, [status(thm)], [c_16, c_12377])).
% 12.98/5.20  tff(c_27440, plain, (![A_4093, B_4094]: (v4_relat_1(k2_zfmisc_1(A_4093, B_4094), A_4093))), inference(resolution, [status(thm)], [c_6, c_27414])).
% 12.98/5.20  tff(c_27446, plain, (![A_3]: (v4_relat_1(k1_xboole_0, A_3))), inference(superposition, [status(thm), theory('equality')], [c_10, c_27440])).
% 12.98/5.20  tff(c_32504, plain, (![B_4356]: (r1_tarski('#skF_3', B_4356))), inference(splitRight, [status(thm)], [c_27731])).
% 12.98/5.20  tff(c_32618, plain, (![B_4363]: (B_4363='#skF_3' | ~r1_tarski(B_4363, '#skF_3'))), inference(resolution, [status(thm)], [c_32504, c_2])).
% 12.98/5.20  tff(c_32851, plain, (![B_4371]: (k1_relat_1(B_4371)='#skF_3' | ~v4_relat_1(B_4371, '#skF_3') | ~v1_relat_1(B_4371))), inference(resolution, [status(thm)], [c_22, c_32618])).
% 12.98/5.20  tff(c_32859, plain, (k1_relat_1(k1_xboole_0)='#skF_3' | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_27446, c_32851])).
% 12.98/5.20  tff(c_32873, plain, (k1_relat_1(k1_xboole_0)='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_79, c_32859])).
% 12.98/5.20  tff(c_32654, plain, (![B_4366]: (k2_relat_1(B_4366)='#skF_3' | ~v5_relat_1(B_4366, '#skF_3') | ~v1_relat_1(B_4366))), inference(resolution, [status(thm)], [c_26, c_32618])).
% 12.98/5.20  tff(c_32666, plain, (k2_relat_1(k1_xboole_0)='#skF_3' | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_12376, c_32654])).
% 12.98/5.20  tff(c_32683, plain, (k2_relat_1(k1_xboole_0)='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_79, c_32666])).
% 12.98/5.20  tff(c_32878, plain, (![C_4372, A_4373, B_4374]: (m1_subset_1(C_4372, k1_zfmisc_1(k2_zfmisc_1(A_4373, B_4374))) | ~r1_tarski(k2_relat_1(C_4372), B_4374) | ~r1_tarski(k1_relat_1(C_4372), A_4373) | ~v1_relat_1(C_4372))), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.98/5.20  tff(c_32995, plain, (![C_4375]: (m1_subset_1(C_4375, k1_zfmisc_1('#skF_4')) | ~r1_tarski(k2_relat_1(C_4375), '#skF_2') | ~r1_tarski(k1_relat_1(C_4375), '#skF_1') | ~v1_relat_1(C_4375))), inference(superposition, [status(thm), theory('equality')], [c_27249, c_32878])).
% 12.98/5.20  tff(c_33001, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_4')) | ~r1_tarski('#skF_3', '#skF_2') | ~r1_tarski(k1_relat_1(k1_xboole_0), '#skF_1') | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32683, c_32995])).
% 12.98/5.20  tff(c_33015, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_32498, c_32873, c_32498, c_33001])).
% 12.98/5.20  tff(c_33041, plain, (r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_33015, c_14])).
% 12.98/5.20  tff(c_33058, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32556, c_33041])).
% 12.98/5.20  tff(c_33060, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_27279])).
% 12.98/5.20  tff(c_33059, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_27279])).
% 12.98/5.20  tff(c_33075, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_33060, c_33059])).
% 12.98/5.20  tff(c_33069, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_33059, c_33059, c_12])).
% 12.98/5.20  tff(c_33117, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_33075, c_33075, c_33069])).
% 12.98/5.20  tff(c_33278, plain, (![A_4394, B_4395, C_4396]: (k1_relset_1(A_4394, B_4395, C_4396)=k1_relat_1(C_4396) | ~m1_subset_1(C_4396, k1_zfmisc_1(k2_zfmisc_1(A_4394, B_4395))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.98/5.20  tff(c_33565, plain, (![B_4443, C_4444]: (k1_relset_1('#skF_4', B_4443, C_4444)=k1_relat_1(C_4444) | ~m1_subset_1(C_4444, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_33117, c_33278])).
% 12.98/5.20  tff(c_33573, plain, (![B_4445]: (k1_relset_1('#skF_4', B_4445, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_27252, c_33565])).
% 12.98/5.20  tff(c_33108, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_33075, c_62])).
% 12.98/5.20  tff(c_50, plain, (![B_32, C_33]: (k1_relset_1(k1_xboole_0, B_32, C_33)=k1_xboole_0 | ~v1_funct_2(C_33, k1_xboole_0, B_32) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_32))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.98/5.20  tff(c_67, plain, (![B_32, C_33]: (k1_relset_1(k1_xboole_0, B_32, C_33)=k1_xboole_0 | ~v1_funct_2(C_33, k1_xboole_0, B_32) | ~m1_subset_1(C_33, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_50])).
% 12.98/5.20  tff(c_33547, plain, (![B_4440, C_4441]: (k1_relset_1('#skF_4', B_4440, C_4441)='#skF_4' | ~v1_funct_2(C_4441, '#skF_4', B_4440) | ~m1_subset_1(C_4441, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_33060, c_33060, c_33060, c_33060, c_67])).
% 12.98/5.20  tff(c_33552, plain, (k1_relset_1('#skF_4', '#skF_2', '#skF_4')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_33108, c_33547])).
% 12.98/5.20  tff(c_33559, plain, (k1_relset_1('#skF_4', '#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_27252, c_33552])).
% 12.98/5.20  tff(c_33577, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_33573, c_33559])).
% 12.98/5.20  tff(c_33571, plain, (![B_4443]: (k1_relset_1('#skF_4', B_4443, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_27252, c_33565])).
% 12.98/5.20  tff(c_33584, plain, (![B_4443]: (k1_relset_1('#skF_4', B_4443, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_33577, c_33571])).
% 12.98/5.20  tff(c_68, plain, (![C_33, B_32]: (v1_funct_2(C_33, k1_xboole_0, B_32) | k1_relset_1(k1_xboole_0, B_32, C_33)!=k1_xboole_0 | ~m1_subset_1(C_33, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_46])).
% 12.98/5.20  tff(c_33682, plain, (![C_4449, B_4450]: (v1_funct_2(C_4449, '#skF_4', B_4450) | k1_relset_1('#skF_4', B_4450, C_4449)!='#skF_4' | ~m1_subset_1(C_4449, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_33060, c_33060, c_33060, c_33060, c_68])).
% 12.98/5.20  tff(c_33684, plain, (![B_4450]: (v1_funct_2('#skF_4', '#skF_4', B_4450) | k1_relset_1('#skF_4', B_4450, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_27252, c_33682])).
% 12.98/5.20  tff(c_33690, plain, (![B_4450]: (v1_funct_2('#skF_4', '#skF_4', B_4450))), inference(demodulation, [status(thm), theory('equality')], [c_33584, c_33684])).
% 12.98/5.20  tff(c_33107, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_33075, c_152])).
% 12.98/5.20  tff(c_33695, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33690, c_33107])).
% 12.98/5.20  tff(c_33696, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_66])).
% 12.98/5.20  tff(c_34137, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34119, c_33696])).
% 12.98/5.20  tff(c_34159, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_34065, c_34137])).
% 12.98/5.20  tff(c_34164, plain, (~v4_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_34159])).
% 12.98/5.20  tff(c_34168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138, c_33773, c_34164])).
% 12.98/5.20  tff(c_34169, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_56])).
% 12.98/5.20  tff(c_34182, plain, (![B_4527]: (k2_zfmisc_1('#skF_1', B_4527)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34169, c_34169, c_12])).
% 12.98/5.20  tff(c_34186, plain, (v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_34182, c_28])).
% 12.98/5.20  tff(c_34181, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34169, c_34169, c_12])).
% 12.98/5.20  tff(c_34170, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_56])).
% 12.98/5.20  tff(c_34175, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34169, c_34170])).
% 12.98/5.20  tff(c_34210, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34181, c_34175, c_60])).
% 12.98/5.20  tff(c_34224, plain, (![B_4533, A_4534]: (v1_relat_1(B_4533) | ~m1_subset_1(B_4533, k1_zfmisc_1(A_4534)) | ~v1_relat_1(A_4534))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.98/5.20  tff(c_34230, plain, (v1_relat_1('#skF_4') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_34210, c_34224])).
% 12.98/5.20  tff(c_34234, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34186, c_34230])).
% 12.98/5.20  tff(c_34191, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34169, c_34169, c_10])).
% 12.98/5.20  tff(c_34320, plain, (![C_4549, A_4550, B_4551]: (v4_relat_1(C_4549, A_4550) | ~m1_subset_1(C_4549, k1_zfmisc_1(k2_zfmisc_1(A_4550, B_4551))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.98/5.20  tff(c_34333, plain, (![C_4552, A_4553]: (v4_relat_1(C_4552, A_4553) | ~m1_subset_1(C_4552, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_34191, c_34320])).
% 12.98/5.20  tff(c_34340, plain, (![A_4553]: (v4_relat_1('#skF_4', A_4553))), inference(resolution, [status(thm)], [c_34210, c_34333])).
% 12.98/5.20  tff(c_34457, plain, (![A_4579, B_4580, C_4581]: (k1_relset_1(A_4579, B_4580, C_4581)=k1_relat_1(C_4581) | ~m1_subset_1(C_4581, k1_zfmisc_1(k2_zfmisc_1(A_4579, B_4580))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.98/5.20  tff(c_34576, plain, (![A_4601, C_4602]: (k1_relset_1(A_4601, '#skF_1', C_4602)=k1_relat_1(C_4602) | ~m1_subset_1(C_4602, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_34191, c_34457])).
% 12.98/5.20  tff(c_34586, plain, (![A_4601]: (k1_relset_1(A_4601, '#skF_1', '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_34210, c_34576])).
% 12.98/5.20  tff(c_34176, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34175, c_62])).
% 12.98/5.20  tff(c_34697, plain, (![B_4614, C_4615]: (k1_relset_1('#skF_1', B_4614, C_4615)='#skF_1' | ~v1_funct_2(C_4615, '#skF_1', B_4614) | ~m1_subset_1(C_4615, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34169, c_34169, c_34169, c_34169, c_67])).
% 12.98/5.20  tff(c_34702, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')='#skF_1' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_34176, c_34697])).
% 12.98/5.20  tff(c_34709, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34210, c_34586, c_34702])).
% 12.98/5.20  tff(c_34717, plain, (![A_10]: (r1_tarski('#skF_1', A_10) | ~v4_relat_1('#skF_4', A_10) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_34709, c_22])).
% 12.98/5.20  tff(c_34729, plain, (![A_10]: (r1_tarski('#skF_1', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_34234, c_34340, c_34717])).
% 12.98/5.20  tff(c_34214, plain, (![A_4529, B_4530]: (r1_tarski(A_4529, B_4530) | ~m1_subset_1(A_4529, k1_zfmisc_1(B_4530)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.98/5.20  tff(c_34218, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_34210, c_34214])).
% 12.98/5.20  tff(c_34307, plain, (![B_4547, A_4548]: (B_4547=A_4548 | ~r1_tarski(B_4547, A_4548) | ~r1_tarski(A_4548, B_4547))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.98/5.20  tff(c_34314, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_34218, c_34307])).
% 12.98/5.20  tff(c_34332, plain, (~r1_tarski('#skF_1', '#skF_4')), inference(splitLeft, [status(thm)], [c_34314])).
% 12.98/5.20  tff(c_34737, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34729, c_34332])).
% 12.98/5.20  tff(c_34738, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_34314])).
% 12.98/5.20  tff(c_34746, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34738, c_34210])).
% 12.98/5.20  tff(c_34750, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34738, c_34738, c_34181])).
% 12.98/5.20  tff(c_34987, plain, (![A_4653, B_4654, C_4655]: (k1_relset_1(A_4653, B_4654, C_4655)=k1_relat_1(C_4655) | ~m1_subset_1(C_4655, k1_zfmisc_1(k2_zfmisc_1(A_4653, B_4654))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.98/5.20  tff(c_35237, plain, (![B_4691, C_4692]: (k1_relset_1('#skF_4', B_4691, C_4692)=k1_relat_1(C_4692) | ~m1_subset_1(C_4692, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_34750, c_34987])).
% 12.98/5.20  tff(c_35243, plain, (![B_4691]: (k1_relset_1('#skF_4', B_4691, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_34746, c_35237])).
% 12.98/5.20  tff(c_34752, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34738, c_34169])).
% 12.98/5.20  tff(c_35284, plain, (![C_4699, B_4700]: (v1_funct_2(C_4699, '#skF_4', B_4700) | k1_relset_1('#skF_4', B_4700, C_4699)!='#skF_4' | ~m1_subset_1(C_4699, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_34752, c_34752, c_34752, c_34752, c_68])).
% 12.98/5.20  tff(c_35286, plain, (![B_4700]: (v1_funct_2('#skF_4', '#skF_4', B_4700) | k1_relset_1('#skF_4', B_4700, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_34746, c_35284])).
% 12.98/5.20  tff(c_35291, plain, (![B_4700]: (v1_funct_2('#skF_4', '#skF_4', B_4700) | k1_relat_1('#skF_4')!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35243, c_35286])).
% 12.98/5.20  tff(c_35307, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_35291])).
% 12.98/5.20  tff(c_34747, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34738, c_34738, c_34176])).
% 12.98/5.20  tff(c_35360, plain, (![B_4708, C_4709]: (k1_relset_1('#skF_4', B_4708, C_4709)='#skF_4' | ~v1_funct_2(C_4709, '#skF_4', B_4708) | ~m1_subset_1(C_4709, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_34752, c_34752, c_34752, c_34752, c_67])).
% 12.98/5.20  tff(c_35365, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_4')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_34747, c_35360])).
% 12.98/5.20  tff(c_35373, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34746, c_35243, c_35365])).
% 12.98/5.20  tff(c_35375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35307, c_35373])).
% 12.98/5.20  tff(c_35376, plain, (![B_4700]: (v1_funct_2('#skF_4', '#skF_4', B_4700))), inference(splitRight, [status(thm)], [c_35291])).
% 12.98/5.20  tff(c_34213, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34210, c_34181, c_66])).
% 12.98/5.20  tff(c_34744, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34738, c_34213])).
% 12.98/5.20  tff(c_35451, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35376, c_34744])).
% 12.98/5.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.98/5.20  
% 12.98/5.20  Inference rules
% 12.98/5.20  ----------------------
% 12.98/5.20  #Ref     : 0
% 12.98/5.20  #Sup     : 7300
% 12.98/5.20  #Fact    : 0
% 12.98/5.20  #Define  : 0
% 12.98/5.20  #Split   : 77
% 12.98/5.20  #Chain   : 0
% 12.98/5.20  #Close   : 0
% 12.98/5.20  
% 12.98/5.20  Ordering : KBO
% 12.98/5.20  
% 12.98/5.20  Simplification rules
% 12.98/5.20  ----------------------
% 12.98/5.20  #Subsume      : 832
% 12.98/5.20  #Demod        : 9036
% 12.98/5.20  #Tautology    : 3320
% 12.98/5.20  #SimpNegUnit  : 228
% 12.98/5.20  #BackRed      : 1065
% 12.98/5.20  
% 12.98/5.20  #Partial instantiations: 868
% 12.98/5.20  #Strategies tried      : 1
% 12.98/5.20  
% 12.98/5.20  Timing (in seconds)
% 12.98/5.20  ----------------------
% 12.98/5.20  Preprocessing        : 0.34
% 12.98/5.20  Parsing              : 0.19
% 12.98/5.20  CNF conversion       : 0.02
% 12.98/5.20  Main loop            : 3.97
% 12.98/5.20  Inferencing          : 1.22
% 12.98/5.20  Reduction            : 1.58
% 12.98/5.20  Demodulation         : 1.16
% 12.98/5.20  BG Simplification    : 0.10
% 12.98/5.20  Subsumption          : 0.78
% 12.98/5.20  Abstraction          : 0.13
% 12.98/5.20  MUC search           : 0.00
% 12.98/5.20  Cooper               : 0.00
% 12.98/5.20  Total                : 4.46
% 12.98/5.20  Index Insertion      : 0.00
% 12.98/5.20  Index Deletion       : 0.00
% 12.98/5.20  Index Matching       : 0.00
% 12.98/5.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
