%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:24 EST 2020

% Result     : Theorem 8.35s
% Output     : CNFRefutation 8.66s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 799 expanded)
%              Number of leaves         :   53 ( 289 expanded)
%              Depth                    :   15
%              Number of atoms          :  335 (2026 expanded)
%              Number of equality atoms :   82 ( 374 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_171,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_130,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_89,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_134,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_122,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_126,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_152,axiom,(
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

tff(f_107,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_52,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_112,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_84,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_353,plain,(
    ! [C_110,B_111,A_112] :
      ( v5_relat_1(C_110,B_111)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_112,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_357,plain,(
    v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_84,c_353])).

tff(c_689,plain,(
    ! [A_153,B_154,C_155] :
      ( k2_relset_1(A_153,B_154,C_155) = k2_relat_1(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_698,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_84,c_689])).

tff(c_82,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_699,plain,(
    k2_relat_1('#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_698,c_82])).

tff(c_48,plain,(
    ! [A_29,B_30] : v1_relat_1(k2_zfmisc_1(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_198,plain,(
    ! [B_91,A_92] :
      ( v1_relat_1(B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_92))
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_201,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_84,c_198])).

tff(c_204,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_201])).

tff(c_358,plain,(
    ! [C_113,A_114,B_115] :
      ( v4_relat_1(C_113,A_114)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_362,plain,(
    v4_relat_1('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_84,c_358])).

tff(c_52,plain,(
    ! [B_34,A_33] :
      ( k7_relat_1(B_34,A_33) = B_34
      | ~ v4_relat_1(B_34,A_33)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_377,plain,
    ( k7_relat_1('#skF_9','#skF_7') = '#skF_9'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_362,c_52])).

tff(c_380,plain,(
    k7_relat_1('#skF_9','#skF_7') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_377])).

tff(c_50,plain,(
    ! [B_32,A_31] :
      ( k2_relat_1(k7_relat_1(B_32,A_31)) = k9_relat_1(B_32,A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_384,plain,
    ( k9_relat_1('#skF_9','#skF_7') = k2_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_380,c_50])).

tff(c_388,plain,(
    k9_relat_1('#skF_9','#skF_7') = k2_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_384])).

tff(c_3359,plain,(
    ! [A_288,B_289,C_290,D_291] :
      ( k7_relset_1(A_288,B_289,C_290,D_291) = k9_relat_1(C_290,D_291)
      | ~ m1_subset_1(C_290,k1_zfmisc_1(k2_zfmisc_1(A_288,B_289))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_3366,plain,(
    ! [D_291] : k7_relset_1('#skF_7','#skF_8','#skF_9',D_291) = k9_relat_1('#skF_9',D_291) ),
    inference(resolution,[status(thm)],[c_84,c_3359])).

tff(c_3631,plain,(
    ! [A_300,B_301,C_302,D_303] :
      ( m1_subset_1(k7_relset_1(A_300,B_301,C_302,D_303),k1_zfmisc_1(B_301))
      | ~ m1_subset_1(C_302,k1_zfmisc_1(k2_zfmisc_1(A_300,B_301))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_3663,plain,(
    ! [D_291] :
      ( m1_subset_1(k9_relat_1('#skF_9',D_291),k1_zfmisc_1('#skF_8'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3366,c_3631])).

tff(c_3674,plain,(
    ! [D_304] : m1_subset_1(k9_relat_1('#skF_9',D_304),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_3663])).

tff(c_3682,plain,(
    m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_3674])).

tff(c_38,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1('#skF_6'(A_19,B_20),A_19)
      | B_20 = A_19
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_40,plain,(
    ! [A_22,B_23] :
      ( r2_hidden(A_22,B_23)
      | v1_xboole_0(B_23)
      | ~ m1_subset_1(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_92,plain,(
    ! [D_62] :
      ( r2_hidden('#skF_10'(D_62),'#skF_7')
      | ~ r2_hidden(D_62,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_86,plain,(
    v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_646,plain,(
    ! [A_146,B_147,C_148] :
      ( k1_relset_1(A_146,B_147,C_148) = k1_relat_1(C_148)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_655,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_84,c_646])).

tff(c_4445,plain,(
    ! [B_326,A_327,C_328] :
      ( k1_xboole_0 = B_326
      | k1_relset_1(A_327,B_326,C_328) = A_327
      | ~ v1_funct_2(C_328,A_327,B_326)
      | ~ m1_subset_1(C_328,k1_zfmisc_1(k2_zfmisc_1(A_327,B_326))) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_4456,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_84,c_4445])).

tff(c_4461,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_655,c_4456])).

tff(c_4462,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_4461])).

tff(c_88,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_90,plain,(
    ! [D_62] :
      ( k1_funct_1('#skF_9','#skF_10'(D_62)) = D_62
      | ~ r2_hidden(D_62,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_1358,plain,(
    ! [B_205,A_206] :
      ( r2_hidden(k1_funct_1(B_205,A_206),k2_relat_1(B_205))
      | ~ r2_hidden(A_206,k1_relat_1(B_205))
      | ~ v1_funct_1(B_205)
      | ~ v1_relat_1(B_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1370,plain,(
    ! [D_62] :
      ( r2_hidden(D_62,k2_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_10'(D_62),k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_62,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_1358])).

tff(c_1374,plain,(
    ! [D_62] :
      ( r2_hidden(D_62,k2_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_10'(D_62),k1_relat_1('#skF_9'))
      | ~ r2_hidden(D_62,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_88,c_1370])).

tff(c_4486,plain,(
    ! [D_329] :
      ( r2_hidden(D_329,k2_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_10'(D_329),'#skF_7')
      | ~ r2_hidden(D_329,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4462,c_1374])).

tff(c_4504,plain,(
    ! [D_330] :
      ( r2_hidden(D_330,k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_330,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_92,c_4486])).

tff(c_36,plain,(
    ! [A_19,B_20] :
      ( ~ r2_hidden('#skF_6'(A_19,B_20),B_20)
      | B_20 = A_19
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4653,plain,(
    ! [A_336] :
      ( k2_relat_1('#skF_9') = A_336
      | ~ m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1(A_336))
      | ~ r2_hidden('#skF_6'(A_336,k2_relat_1('#skF_9')),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_4504,c_36])).

tff(c_4657,plain,(
    ! [A_336] :
      ( k2_relat_1('#skF_9') = A_336
      | ~ m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1(A_336))
      | v1_xboole_0('#skF_8')
      | ~ m1_subset_1('#skF_6'(A_336,k2_relat_1('#skF_9')),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_40,c_4653])).

tff(c_6185,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_4657])).

tff(c_22,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_109,plain,(
    ! [A_73] :
      ( v1_xboole_0(A_73)
      | r2_hidden('#skF_1'(A_73),A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ! [B_38,A_37] :
      ( ~ r1_tarski(B_38,A_37)
      | ~ r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_118,plain,(
    ! [A_74] :
      ( ~ r1_tarski(A_74,'#skF_1'(A_74))
      | v1_xboole_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_109,c_56])).

tff(c_123,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_118])).

tff(c_704,plain,(
    ! [A_156,B_157] :
      ( r2_hidden('#skF_2'(A_156,B_157),B_157)
      | r2_hidden('#skF_3'(A_156,B_157),A_156)
      | B_157 = A_156 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_773,plain,(
    ! [B_160,A_161] :
      ( ~ v1_xboole_0(B_160)
      | r2_hidden('#skF_3'(A_161,B_160),A_161)
      | B_160 = A_161 ) ),
    inference(resolution,[status(thm)],[c_704,c_2])).

tff(c_793,plain,(
    ! [A_162,B_163] :
      ( ~ v1_xboole_0(A_162)
      | ~ v1_xboole_0(B_163)
      | B_163 = A_162 ) ),
    inference(resolution,[status(thm)],[c_773,c_2])).

tff(c_799,plain,(
    ! [B_163] :
      ( ~ v1_xboole_0(B_163)
      | k1_xboole_0 = B_163 ) ),
    inference(resolution,[status(thm)],[c_123,c_793])).

tff(c_6207,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_6185,c_799])).

tff(c_46,plain,(
    ! [B_28,A_27] :
      ( r1_tarski(k2_relat_1(B_28),A_27)
      | ~ v5_relat_1(B_28,A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_318,plain,(
    ! [A_103,C_104,B_105] :
      ( r1_tarski(A_103,C_104)
      | ~ r1_tarski(B_105,C_104)
      | ~ r1_tarski(A_103,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_331,plain,(
    ! [A_106,A_107] :
      ( r1_tarski(A_106,A_107)
      | ~ r1_tarski(A_106,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_318])).

tff(c_411,plain,(
    ! [B_121,A_122] :
      ( r1_tarski(k2_relat_1(B_121),A_122)
      | ~ v5_relat_1(B_121,k1_xboole_0)
      | ~ v1_relat_1(B_121) ) ),
    inference(resolution,[status(thm)],[c_46,c_331])).

tff(c_116,plain,(
    ! [A_73] :
      ( ~ r1_tarski(A_73,'#skF_1'(A_73))
      | v1_xboole_0(A_73) ) ),
    inference(resolution,[status(thm)],[c_109,c_56])).

tff(c_442,plain,(
    ! [B_121] :
      ( v1_xboole_0(k2_relat_1(B_121))
      | ~ v5_relat_1(B_121,k1_xboole_0)
      | ~ v1_relat_1(B_121) ) ),
    inference(resolution,[status(thm)],[c_411,c_116])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1375,plain,(
    ! [B_207,A_208] :
      ( ~ v1_xboole_0(k2_relat_1(B_207))
      | ~ r2_hidden(A_208,k1_relat_1(B_207))
      | ~ v1_funct_1(B_207)
      | ~ v1_relat_1(B_207) ) ),
    inference(resolution,[status(thm)],[c_1358,c_2])).

tff(c_1421,plain,(
    ! [B_209] :
      ( ~ v1_xboole_0(k2_relat_1(B_209))
      | ~ v1_funct_1(B_209)
      | ~ v1_relat_1(B_209)
      | v1_xboole_0(k1_relat_1(B_209)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1375])).

tff(c_1428,plain,(
    ! [B_121] :
      ( ~ v1_funct_1(B_121)
      | v1_xboole_0(k1_relat_1(B_121))
      | ~ v5_relat_1(B_121,k1_xboole_0)
      | ~ v1_relat_1(B_121) ) ),
    inference(resolution,[status(thm)],[c_442,c_1421])).

tff(c_99,plain,(
    ! [D_72] :
      ( r2_hidden('#skF_10'(D_72),'#skF_7')
      | ~ r2_hidden(D_72,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_107,plain,(
    ! [D_72] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ r2_hidden(D_72,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_99,c_2])).

tff(c_108,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_1447,plain,(
    ! [D_211] :
      ( r2_hidden(D_211,k2_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_10'(D_211),k1_relat_1('#skF_9'))
      | ~ r2_hidden(D_211,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_88,c_1370])).

tff(c_1451,plain,(
    ! [D_211] :
      ( r2_hidden(D_211,k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_211,'#skF_8')
      | v1_xboole_0(k1_relat_1('#skF_9'))
      | ~ m1_subset_1('#skF_10'(D_211),k1_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_40,c_1447])).

tff(c_1770,plain,(
    v1_xboole_0(k1_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_1451])).

tff(c_1786,plain,(
    k1_relat_1('#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1770,c_799])).

tff(c_1790,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1786,c_655])).

tff(c_2415,plain,(
    ! [B_249,A_250,C_251] :
      ( k1_xboole_0 = B_249
      | k1_relset_1(A_250,B_249,C_251) = A_250
      | ~ v1_funct_2(C_251,A_250,B_249)
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(A_250,B_249))) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_2426,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_84,c_2415])).

tff(c_2431,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1790,c_2426])).

tff(c_2432,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_2431])).

tff(c_2474,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2432,c_123])).

tff(c_2477,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_2474])).

tff(c_2478,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_2431])).

tff(c_1372,plain,(
    ! [B_205,A_206] :
      ( ~ v1_xboole_0(k2_relat_1(B_205))
      | ~ r2_hidden(A_206,k1_relat_1(B_205))
      | ~ v1_funct_1(B_205)
      | ~ v1_relat_1(B_205) ) ),
    inference(resolution,[status(thm)],[c_1358,c_2])).

tff(c_1798,plain,(
    ! [A_206] :
      ( ~ v1_xboole_0(k2_relat_1('#skF_9'))
      | ~ r2_hidden(A_206,k1_xboole_0)
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1786,c_1372])).

tff(c_1804,plain,(
    ! [A_206] :
      ( ~ v1_xboole_0(k2_relat_1('#skF_9'))
      | ~ r2_hidden(A_206,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_88,c_1798])).

tff(c_1825,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_1804])).

tff(c_1828,plain,
    ( ~ v5_relat_1('#skF_9',k1_xboole_0)
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_442,c_1825])).

tff(c_1831,plain,(
    ~ v5_relat_1('#skF_9',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_1828])).

tff(c_2486,plain,(
    ~ v5_relat_1('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2478,c_1831])).

tff(c_2526,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_2486])).

tff(c_2528,plain,(
    v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_1804])).

tff(c_2601,plain,(
    k2_relat_1('#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2528,c_799])).

tff(c_2604,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2601,c_699])).

tff(c_3260,plain,(
    ! [B_282,A_283,C_284] :
      ( k1_xboole_0 = B_282
      | k1_relset_1(A_283,B_282,C_284) = A_283
      | ~ v1_funct_2(C_284,A_283,B_282)
      | ~ m1_subset_1(C_284,k1_zfmisc_1(k2_zfmisc_1(A_283,B_282))) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_3271,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_84,c_3260])).

tff(c_3276,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1790,c_3271])).

tff(c_3277,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_2604,c_3276])).

tff(c_3328,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3277,c_123])).

tff(c_3331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_3328])).

tff(c_3333,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_1451])).

tff(c_3336,plain,
    ( ~ v1_funct_1('#skF_9')
    | ~ v5_relat_1('#skF_9',k1_xboole_0)
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_1428,c_3333])).

tff(c_3339,plain,(
    ~ v5_relat_1('#skF_9',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_88,c_3336])).

tff(c_6249,plain,(
    ~ v5_relat_1('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6207,c_3339])).

tff(c_6287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_6249])).

tff(c_7581,plain,(
    ! [A_475] :
      ( k2_relat_1('#skF_9') = A_475
      | ~ m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1(A_475))
      | ~ m1_subset_1('#skF_6'(A_475,k2_relat_1('#skF_9')),'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_4657])).

tff(c_7585,plain,
    ( k2_relat_1('#skF_9') = '#skF_8'
    | ~ m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_38,c_7581])).

tff(c_7588,plain,(
    k2_relat_1('#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3682,c_7585])).

tff(c_7590,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_699,c_7588])).

tff(c_7591,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_4461])).

tff(c_7611,plain,(
    ~ v5_relat_1('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7591,c_3339])).

tff(c_7649,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_7611])).

tff(c_7651,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_8163,plain,(
    ! [A_546,B_547] :
      ( r2_hidden('#skF_2'(A_546,B_547),B_547)
      | r2_hidden('#skF_3'(A_546,B_547),A_546)
      | B_547 = A_546 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_7650,plain,(
    ! [D_72] : ~ r2_hidden(D_72,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_8197,plain,(
    ! [B_548] :
      ( r2_hidden('#skF_2'('#skF_8',B_548),B_548)
      | B_548 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_8163,c_7650])).

tff(c_8217,plain,(
    ! [B_549] :
      ( ~ v1_xboole_0(B_549)
      | B_549 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_8197,c_2])).

tff(c_8234,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_7651,c_8217])).

tff(c_8266,plain,(
    k2_relset_1('#skF_8','#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8234,c_82])).

tff(c_7752,plain,(
    ! [B_494,A_495] :
      ( v1_relat_1(B_494)
      | ~ m1_subset_1(B_494,k1_zfmisc_1(A_495))
      | ~ v1_relat_1(A_495) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_7755,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_84,c_7752])).

tff(c_7758,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_7755])).

tff(c_7874,plain,(
    ! [C_513,B_514,A_515] :
      ( v5_relat_1(C_513,B_514)
      | ~ m1_subset_1(C_513,k1_zfmisc_1(k2_zfmisc_1(A_515,B_514))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_7878,plain,(
    v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_84,c_7874])).

tff(c_7662,plain,(
    ! [A_478] :
      ( v1_xboole_0(A_478)
      | r2_hidden('#skF_1'(A_478),A_478) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_7676,plain,(
    ! [A_479] :
      ( ~ r1_tarski(A_479,'#skF_1'(A_479))
      | v1_xboole_0(A_479) ) ),
    inference(resolution,[status(thm)],[c_7662,c_56])).

tff(c_7681,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_7676])).

tff(c_8231,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_7681,c_8217])).

tff(c_7890,plain,(
    ! [A_518,C_519,B_520] :
      ( r1_tarski(A_518,C_519)
      | ~ r1_tarski(B_520,C_519)
      | ~ r1_tarski(A_518,B_520) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_7930,plain,(
    ! [A_523,A_524] :
      ( r1_tarski(A_523,A_524)
      | ~ r1_tarski(A_523,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_7890])).

tff(c_7951,plain,(
    ! [B_525,A_526] :
      ( r1_tarski(k2_relat_1(B_525),A_526)
      | ~ v5_relat_1(B_525,k1_xboole_0)
      | ~ v1_relat_1(B_525) ) ),
    inference(resolution,[status(thm)],[c_46,c_7930])).

tff(c_7674,plain,(
    ! [A_478] :
      ( ~ r1_tarski(A_478,'#skF_1'(A_478))
      | v1_xboole_0(A_478) ) ),
    inference(resolution,[status(thm)],[c_7662,c_56])).

tff(c_7982,plain,(
    ! [B_525] :
      ( v1_xboole_0(k2_relat_1(B_525))
      | ~ v5_relat_1(B_525,k1_xboole_0)
      | ~ v1_relat_1(B_525) ) ),
    inference(resolution,[status(thm)],[c_7951,c_7674])).

tff(c_8230,plain,(
    ! [B_525] :
      ( k2_relat_1(B_525) = '#skF_8'
      | ~ v5_relat_1(B_525,k1_xboole_0)
      | ~ v1_relat_1(B_525) ) ),
    inference(resolution,[status(thm)],[c_7982,c_8217])).

tff(c_8474,plain,(
    ! [B_561] :
      ( k2_relat_1(B_561) = '#skF_8'
      | ~ v5_relat_1(B_561,'#skF_8')
      | ~ v1_relat_1(B_561) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8231,c_8230])).

tff(c_8477,plain,
    ( k2_relat_1('#skF_9') = '#skF_8'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_7878,c_8474])).

tff(c_8480,plain,(
    k2_relat_1('#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7758,c_8477])).

tff(c_8265,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8234,c_84])).

tff(c_8546,plain,(
    ! [A_566,B_567,C_568] :
      ( k2_relset_1(A_566,B_567,C_568) = k2_relat_1(C_568)
      | ~ m1_subset_1(C_568,k1_zfmisc_1(k2_zfmisc_1(A_566,B_567))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_8549,plain,(
    k2_relset_1('#skF_8','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_8265,c_8546])).

tff(c_8555,plain,(
    k2_relset_1('#skF_8','#skF_8','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8480,c_8549])).

tff(c_8557,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8266,c_8555])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:36:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.35/2.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.35/2.85  
% 8.35/2.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.35/2.85  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_4
% 8.35/2.85  
% 8.35/2.85  %Foreground sorts:
% 8.35/2.85  
% 8.35/2.85  
% 8.35/2.85  %Background operators:
% 8.35/2.85  
% 8.35/2.85  
% 8.35/2.85  %Foreground operators:
% 8.35/2.85  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.35/2.85  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 8.35/2.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.35/2.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.35/2.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.35/2.85  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.35/2.85  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.35/2.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.35/2.85  tff('#skF_7', type, '#skF_7': $i).
% 8.35/2.85  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.35/2.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.35/2.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.35/2.85  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 8.35/2.85  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.35/2.85  tff('#skF_10', type, '#skF_10': $i > $i).
% 8.35/2.85  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.35/2.85  tff('#skF_9', type, '#skF_9': $i).
% 8.35/2.85  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.35/2.85  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.35/2.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.35/2.85  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.35/2.85  tff('#skF_8', type, '#skF_8': $i).
% 8.35/2.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.35/2.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.35/2.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.35/2.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.35/2.85  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.35/2.85  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.35/2.85  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.35/2.85  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.35/2.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.35/2.85  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.35/2.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.35/2.85  
% 8.66/2.88  tff(f_171, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 8.66/2.88  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.66/2.88  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.66/2.88  tff(f_89, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.66/2.88  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.66/2.88  tff(f_99, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 8.66/2.88  tff(f_93, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 8.66/2.88  tff(f_134, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 8.66/2.88  tff(f_122, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 8.66/2.88  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_subset_1)).
% 8.66/2.88  tff(f_74, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 8.66/2.88  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.66/2.88  tff(f_152, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 8.66/2.88  tff(f_107, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 8.66/2.88  tff(f_52, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.66/2.88  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.66/2.88  tff(f_112, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.66/2.88  tff(f_38, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 8.66/2.88  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 8.66/2.88  tff(f_50, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.66/2.88  tff(c_84, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 8.66/2.88  tff(c_353, plain, (![C_110, B_111, A_112]: (v5_relat_1(C_110, B_111) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_112, B_111))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.66/2.88  tff(c_357, plain, (v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_84, c_353])).
% 8.66/2.88  tff(c_689, plain, (![A_153, B_154, C_155]: (k2_relset_1(A_153, B_154, C_155)=k2_relat_1(C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.66/2.88  tff(c_698, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_84, c_689])).
% 8.66/2.88  tff(c_82, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_171])).
% 8.66/2.88  tff(c_699, plain, (k2_relat_1('#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_698, c_82])).
% 8.66/2.88  tff(c_48, plain, (![A_29, B_30]: (v1_relat_1(k2_zfmisc_1(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.66/2.88  tff(c_198, plain, (![B_91, A_92]: (v1_relat_1(B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(A_92)) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.66/2.88  tff(c_201, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_84, c_198])).
% 8.66/2.88  tff(c_204, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_201])).
% 8.66/2.88  tff(c_358, plain, (![C_113, A_114, B_115]: (v4_relat_1(C_113, A_114) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.66/2.88  tff(c_362, plain, (v4_relat_1('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_84, c_358])).
% 8.66/2.88  tff(c_52, plain, (![B_34, A_33]: (k7_relat_1(B_34, A_33)=B_34 | ~v4_relat_1(B_34, A_33) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.66/2.88  tff(c_377, plain, (k7_relat_1('#skF_9', '#skF_7')='#skF_9' | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_362, c_52])).
% 8.66/2.88  tff(c_380, plain, (k7_relat_1('#skF_9', '#skF_7')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_204, c_377])).
% 8.66/2.88  tff(c_50, plain, (![B_32, A_31]: (k2_relat_1(k7_relat_1(B_32, A_31))=k9_relat_1(B_32, A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.66/2.88  tff(c_384, plain, (k9_relat_1('#skF_9', '#skF_7')=k2_relat_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_380, c_50])).
% 8.66/2.88  tff(c_388, plain, (k9_relat_1('#skF_9', '#skF_7')=k2_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_384])).
% 8.66/2.88  tff(c_3359, plain, (![A_288, B_289, C_290, D_291]: (k7_relset_1(A_288, B_289, C_290, D_291)=k9_relat_1(C_290, D_291) | ~m1_subset_1(C_290, k1_zfmisc_1(k2_zfmisc_1(A_288, B_289))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 8.66/2.88  tff(c_3366, plain, (![D_291]: (k7_relset_1('#skF_7', '#skF_8', '#skF_9', D_291)=k9_relat_1('#skF_9', D_291))), inference(resolution, [status(thm)], [c_84, c_3359])).
% 8.66/2.88  tff(c_3631, plain, (![A_300, B_301, C_302, D_303]: (m1_subset_1(k7_relset_1(A_300, B_301, C_302, D_303), k1_zfmisc_1(B_301)) | ~m1_subset_1(C_302, k1_zfmisc_1(k2_zfmisc_1(A_300, B_301))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.66/2.88  tff(c_3663, plain, (![D_291]: (m1_subset_1(k9_relat_1('#skF_9', D_291), k1_zfmisc_1('#skF_8')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8'))))), inference(superposition, [status(thm), theory('equality')], [c_3366, c_3631])).
% 8.66/2.88  tff(c_3674, plain, (![D_304]: (m1_subset_1(k9_relat_1('#skF_9', D_304), k1_zfmisc_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_3663])).
% 8.66/2.88  tff(c_3682, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_388, c_3674])).
% 8.66/2.88  tff(c_38, plain, (![A_19, B_20]: (m1_subset_1('#skF_6'(A_19, B_20), A_19) | B_20=A_19 | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.66/2.88  tff(c_40, plain, (![A_22, B_23]: (r2_hidden(A_22, B_23) | v1_xboole_0(B_23) | ~m1_subset_1(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.66/2.88  tff(c_92, plain, (![D_62]: (r2_hidden('#skF_10'(D_62), '#skF_7') | ~r2_hidden(D_62, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 8.66/2.88  tff(c_86, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_171])).
% 8.66/2.88  tff(c_646, plain, (![A_146, B_147, C_148]: (k1_relset_1(A_146, B_147, C_148)=k1_relat_1(C_148) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.66/2.88  tff(c_655, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_84, c_646])).
% 8.66/2.88  tff(c_4445, plain, (![B_326, A_327, C_328]: (k1_xboole_0=B_326 | k1_relset_1(A_327, B_326, C_328)=A_327 | ~v1_funct_2(C_328, A_327, B_326) | ~m1_subset_1(C_328, k1_zfmisc_1(k2_zfmisc_1(A_327, B_326))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 8.66/2.88  tff(c_4456, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_7' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_84, c_4445])).
% 8.66/2.88  tff(c_4461, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_655, c_4456])).
% 8.66/2.88  tff(c_4462, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(splitLeft, [status(thm)], [c_4461])).
% 8.66/2.88  tff(c_88, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_171])).
% 8.66/2.88  tff(c_90, plain, (![D_62]: (k1_funct_1('#skF_9', '#skF_10'(D_62))=D_62 | ~r2_hidden(D_62, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 8.66/2.88  tff(c_1358, plain, (![B_205, A_206]: (r2_hidden(k1_funct_1(B_205, A_206), k2_relat_1(B_205)) | ~r2_hidden(A_206, k1_relat_1(B_205)) | ~v1_funct_1(B_205) | ~v1_relat_1(B_205))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.66/2.88  tff(c_1370, plain, (![D_62]: (r2_hidden(D_62, k2_relat_1('#skF_9')) | ~r2_hidden('#skF_10'(D_62), k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_62, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_1358])).
% 8.66/2.88  tff(c_1374, plain, (![D_62]: (r2_hidden(D_62, k2_relat_1('#skF_9')) | ~r2_hidden('#skF_10'(D_62), k1_relat_1('#skF_9')) | ~r2_hidden(D_62, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_88, c_1370])).
% 8.66/2.88  tff(c_4486, plain, (![D_329]: (r2_hidden(D_329, k2_relat_1('#skF_9')) | ~r2_hidden('#skF_10'(D_329), '#skF_7') | ~r2_hidden(D_329, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_4462, c_1374])).
% 8.66/2.88  tff(c_4504, plain, (![D_330]: (r2_hidden(D_330, k2_relat_1('#skF_9')) | ~r2_hidden(D_330, '#skF_8'))), inference(resolution, [status(thm)], [c_92, c_4486])).
% 8.66/2.88  tff(c_36, plain, (![A_19, B_20]: (~r2_hidden('#skF_6'(A_19, B_20), B_20) | B_20=A_19 | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.66/2.88  tff(c_4653, plain, (![A_336]: (k2_relat_1('#skF_9')=A_336 | ~m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1(A_336)) | ~r2_hidden('#skF_6'(A_336, k2_relat_1('#skF_9')), '#skF_8'))), inference(resolution, [status(thm)], [c_4504, c_36])).
% 8.66/2.88  tff(c_4657, plain, (![A_336]: (k2_relat_1('#skF_9')=A_336 | ~m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1(A_336)) | v1_xboole_0('#skF_8') | ~m1_subset_1('#skF_6'(A_336, k2_relat_1('#skF_9')), '#skF_8'))), inference(resolution, [status(thm)], [c_40, c_4653])).
% 8.66/2.88  tff(c_6185, plain, (v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_4657])).
% 8.66/2.88  tff(c_22, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.66/2.88  tff(c_109, plain, (![A_73]: (v1_xboole_0(A_73) | r2_hidden('#skF_1'(A_73), A_73))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.66/2.88  tff(c_56, plain, (![B_38, A_37]: (~r1_tarski(B_38, A_37) | ~r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.66/2.88  tff(c_118, plain, (![A_74]: (~r1_tarski(A_74, '#skF_1'(A_74)) | v1_xboole_0(A_74))), inference(resolution, [status(thm)], [c_109, c_56])).
% 8.66/2.88  tff(c_123, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_118])).
% 8.66/2.88  tff(c_704, plain, (![A_156, B_157]: (r2_hidden('#skF_2'(A_156, B_157), B_157) | r2_hidden('#skF_3'(A_156, B_157), A_156) | B_157=A_156)), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.66/2.88  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.66/2.88  tff(c_773, plain, (![B_160, A_161]: (~v1_xboole_0(B_160) | r2_hidden('#skF_3'(A_161, B_160), A_161) | B_160=A_161)), inference(resolution, [status(thm)], [c_704, c_2])).
% 8.66/2.88  tff(c_793, plain, (![A_162, B_163]: (~v1_xboole_0(A_162) | ~v1_xboole_0(B_163) | B_163=A_162)), inference(resolution, [status(thm)], [c_773, c_2])).
% 8.66/2.88  tff(c_799, plain, (![B_163]: (~v1_xboole_0(B_163) | k1_xboole_0=B_163)), inference(resolution, [status(thm)], [c_123, c_793])).
% 8.66/2.88  tff(c_6207, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_6185, c_799])).
% 8.66/2.88  tff(c_46, plain, (![B_28, A_27]: (r1_tarski(k2_relat_1(B_28), A_27) | ~v5_relat_1(B_28, A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.66/2.88  tff(c_318, plain, (![A_103, C_104, B_105]: (r1_tarski(A_103, C_104) | ~r1_tarski(B_105, C_104) | ~r1_tarski(A_103, B_105))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.66/2.88  tff(c_331, plain, (![A_106, A_107]: (r1_tarski(A_106, A_107) | ~r1_tarski(A_106, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_318])).
% 8.66/2.88  tff(c_411, plain, (![B_121, A_122]: (r1_tarski(k2_relat_1(B_121), A_122) | ~v5_relat_1(B_121, k1_xboole_0) | ~v1_relat_1(B_121))), inference(resolution, [status(thm)], [c_46, c_331])).
% 8.66/2.88  tff(c_116, plain, (![A_73]: (~r1_tarski(A_73, '#skF_1'(A_73)) | v1_xboole_0(A_73))), inference(resolution, [status(thm)], [c_109, c_56])).
% 8.66/2.88  tff(c_442, plain, (![B_121]: (v1_xboole_0(k2_relat_1(B_121)) | ~v5_relat_1(B_121, k1_xboole_0) | ~v1_relat_1(B_121))), inference(resolution, [status(thm)], [c_411, c_116])).
% 8.66/2.88  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.66/2.88  tff(c_1375, plain, (![B_207, A_208]: (~v1_xboole_0(k2_relat_1(B_207)) | ~r2_hidden(A_208, k1_relat_1(B_207)) | ~v1_funct_1(B_207) | ~v1_relat_1(B_207))), inference(resolution, [status(thm)], [c_1358, c_2])).
% 8.66/2.88  tff(c_1421, plain, (![B_209]: (~v1_xboole_0(k2_relat_1(B_209)) | ~v1_funct_1(B_209) | ~v1_relat_1(B_209) | v1_xboole_0(k1_relat_1(B_209)))), inference(resolution, [status(thm)], [c_4, c_1375])).
% 8.66/2.88  tff(c_1428, plain, (![B_121]: (~v1_funct_1(B_121) | v1_xboole_0(k1_relat_1(B_121)) | ~v5_relat_1(B_121, k1_xboole_0) | ~v1_relat_1(B_121))), inference(resolution, [status(thm)], [c_442, c_1421])).
% 8.66/2.88  tff(c_99, plain, (![D_72]: (r2_hidden('#skF_10'(D_72), '#skF_7') | ~r2_hidden(D_72, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 8.66/2.88  tff(c_107, plain, (![D_72]: (~v1_xboole_0('#skF_7') | ~r2_hidden(D_72, '#skF_8'))), inference(resolution, [status(thm)], [c_99, c_2])).
% 8.66/2.88  tff(c_108, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_107])).
% 8.66/2.88  tff(c_1447, plain, (![D_211]: (r2_hidden(D_211, k2_relat_1('#skF_9')) | ~r2_hidden('#skF_10'(D_211), k1_relat_1('#skF_9')) | ~r2_hidden(D_211, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_88, c_1370])).
% 8.66/2.88  tff(c_1451, plain, (![D_211]: (r2_hidden(D_211, k2_relat_1('#skF_9')) | ~r2_hidden(D_211, '#skF_8') | v1_xboole_0(k1_relat_1('#skF_9')) | ~m1_subset_1('#skF_10'(D_211), k1_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_40, c_1447])).
% 8.66/2.88  tff(c_1770, plain, (v1_xboole_0(k1_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_1451])).
% 8.66/2.88  tff(c_1786, plain, (k1_relat_1('#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_1770, c_799])).
% 8.66/2.88  tff(c_1790, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1786, c_655])).
% 8.66/2.88  tff(c_2415, plain, (![B_249, A_250, C_251]: (k1_xboole_0=B_249 | k1_relset_1(A_250, B_249, C_251)=A_250 | ~v1_funct_2(C_251, A_250, B_249) | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(A_250, B_249))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 8.66/2.88  tff(c_2426, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_7' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_84, c_2415])).
% 8.66/2.88  tff(c_2431, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1790, c_2426])).
% 8.66/2.88  tff(c_2432, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_2431])).
% 8.66/2.88  tff(c_2474, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2432, c_123])).
% 8.66/2.88  tff(c_2477, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_2474])).
% 8.66/2.88  tff(c_2478, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_2431])).
% 8.66/2.88  tff(c_1372, plain, (![B_205, A_206]: (~v1_xboole_0(k2_relat_1(B_205)) | ~r2_hidden(A_206, k1_relat_1(B_205)) | ~v1_funct_1(B_205) | ~v1_relat_1(B_205))), inference(resolution, [status(thm)], [c_1358, c_2])).
% 8.66/2.88  tff(c_1798, plain, (![A_206]: (~v1_xboole_0(k2_relat_1('#skF_9')) | ~r2_hidden(A_206, k1_xboole_0) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1786, c_1372])).
% 8.66/2.88  tff(c_1804, plain, (![A_206]: (~v1_xboole_0(k2_relat_1('#skF_9')) | ~r2_hidden(A_206, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_88, c_1798])).
% 8.66/2.88  tff(c_1825, plain, (~v1_xboole_0(k2_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_1804])).
% 8.66/2.88  tff(c_1828, plain, (~v5_relat_1('#skF_9', k1_xboole_0) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_442, c_1825])).
% 8.66/2.88  tff(c_1831, plain, (~v5_relat_1('#skF_9', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_204, c_1828])).
% 8.66/2.88  tff(c_2486, plain, (~v5_relat_1('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2478, c_1831])).
% 8.66/2.88  tff(c_2526, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_357, c_2486])).
% 8.66/2.88  tff(c_2528, plain, (v1_xboole_0(k2_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_1804])).
% 8.66/2.88  tff(c_2601, plain, (k2_relat_1('#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_2528, c_799])).
% 8.66/2.88  tff(c_2604, plain, (k1_xboole_0!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2601, c_699])).
% 8.66/2.88  tff(c_3260, plain, (![B_282, A_283, C_284]: (k1_xboole_0=B_282 | k1_relset_1(A_283, B_282, C_284)=A_283 | ~v1_funct_2(C_284, A_283, B_282) | ~m1_subset_1(C_284, k1_zfmisc_1(k2_zfmisc_1(A_283, B_282))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 8.66/2.88  tff(c_3271, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_7' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_84, c_3260])).
% 8.66/2.88  tff(c_3276, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1790, c_3271])).
% 8.66/2.88  tff(c_3277, plain, (k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_2604, c_3276])).
% 8.66/2.88  tff(c_3328, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3277, c_123])).
% 8.66/2.88  tff(c_3331, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_3328])).
% 8.66/2.88  tff(c_3333, plain, (~v1_xboole_0(k1_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_1451])).
% 8.66/2.88  tff(c_3336, plain, (~v1_funct_1('#skF_9') | ~v5_relat_1('#skF_9', k1_xboole_0) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_1428, c_3333])).
% 8.66/2.88  tff(c_3339, plain, (~v5_relat_1('#skF_9', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_204, c_88, c_3336])).
% 8.66/2.88  tff(c_6249, plain, (~v5_relat_1('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_6207, c_3339])).
% 8.66/2.88  tff(c_6287, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_357, c_6249])).
% 8.66/2.88  tff(c_7581, plain, (![A_475]: (k2_relat_1('#skF_9')=A_475 | ~m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1(A_475)) | ~m1_subset_1('#skF_6'(A_475, k2_relat_1('#skF_9')), '#skF_8'))), inference(splitRight, [status(thm)], [c_4657])).
% 8.66/2.88  tff(c_7585, plain, (k2_relat_1('#skF_9')='#skF_8' | ~m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8'))), inference(resolution, [status(thm)], [c_38, c_7581])).
% 8.66/2.88  tff(c_7588, plain, (k2_relat_1('#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3682, c_7585])).
% 8.66/2.88  tff(c_7590, plain, $false, inference(negUnitSimplification, [status(thm)], [c_699, c_7588])).
% 8.66/2.88  tff(c_7591, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_4461])).
% 8.66/2.88  tff(c_7611, plain, (~v5_relat_1('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_7591, c_3339])).
% 8.66/2.88  tff(c_7649, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_357, c_7611])).
% 8.66/2.88  tff(c_7651, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_107])).
% 8.66/2.88  tff(c_8163, plain, (![A_546, B_547]: (r2_hidden('#skF_2'(A_546, B_547), B_547) | r2_hidden('#skF_3'(A_546, B_547), A_546) | B_547=A_546)), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.66/2.88  tff(c_7650, plain, (![D_72]: (~r2_hidden(D_72, '#skF_8'))), inference(splitRight, [status(thm)], [c_107])).
% 8.66/2.88  tff(c_8197, plain, (![B_548]: (r2_hidden('#skF_2'('#skF_8', B_548), B_548) | B_548='#skF_8')), inference(resolution, [status(thm)], [c_8163, c_7650])).
% 8.66/2.88  tff(c_8217, plain, (![B_549]: (~v1_xboole_0(B_549) | B_549='#skF_8')), inference(resolution, [status(thm)], [c_8197, c_2])).
% 8.66/2.88  tff(c_8234, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_7651, c_8217])).
% 8.66/2.88  tff(c_8266, plain, (k2_relset_1('#skF_8', '#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_8234, c_82])).
% 8.66/2.88  tff(c_7752, plain, (![B_494, A_495]: (v1_relat_1(B_494) | ~m1_subset_1(B_494, k1_zfmisc_1(A_495)) | ~v1_relat_1(A_495))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.66/2.88  tff(c_7755, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_84, c_7752])).
% 8.66/2.88  tff(c_7758, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_7755])).
% 8.66/2.88  tff(c_7874, plain, (![C_513, B_514, A_515]: (v5_relat_1(C_513, B_514) | ~m1_subset_1(C_513, k1_zfmisc_1(k2_zfmisc_1(A_515, B_514))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.66/2.88  tff(c_7878, plain, (v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_84, c_7874])).
% 8.66/2.88  tff(c_7662, plain, (![A_478]: (v1_xboole_0(A_478) | r2_hidden('#skF_1'(A_478), A_478))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.66/2.88  tff(c_7676, plain, (![A_479]: (~r1_tarski(A_479, '#skF_1'(A_479)) | v1_xboole_0(A_479))), inference(resolution, [status(thm)], [c_7662, c_56])).
% 8.66/2.88  tff(c_7681, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_7676])).
% 8.66/2.88  tff(c_8231, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_7681, c_8217])).
% 8.66/2.88  tff(c_7890, plain, (![A_518, C_519, B_520]: (r1_tarski(A_518, C_519) | ~r1_tarski(B_520, C_519) | ~r1_tarski(A_518, B_520))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.66/2.88  tff(c_7930, plain, (![A_523, A_524]: (r1_tarski(A_523, A_524) | ~r1_tarski(A_523, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_7890])).
% 8.66/2.88  tff(c_7951, plain, (![B_525, A_526]: (r1_tarski(k2_relat_1(B_525), A_526) | ~v5_relat_1(B_525, k1_xboole_0) | ~v1_relat_1(B_525))), inference(resolution, [status(thm)], [c_46, c_7930])).
% 8.66/2.88  tff(c_7674, plain, (![A_478]: (~r1_tarski(A_478, '#skF_1'(A_478)) | v1_xboole_0(A_478))), inference(resolution, [status(thm)], [c_7662, c_56])).
% 8.66/2.88  tff(c_7982, plain, (![B_525]: (v1_xboole_0(k2_relat_1(B_525)) | ~v5_relat_1(B_525, k1_xboole_0) | ~v1_relat_1(B_525))), inference(resolution, [status(thm)], [c_7951, c_7674])).
% 8.66/2.88  tff(c_8230, plain, (![B_525]: (k2_relat_1(B_525)='#skF_8' | ~v5_relat_1(B_525, k1_xboole_0) | ~v1_relat_1(B_525))), inference(resolution, [status(thm)], [c_7982, c_8217])).
% 8.66/2.88  tff(c_8474, plain, (![B_561]: (k2_relat_1(B_561)='#skF_8' | ~v5_relat_1(B_561, '#skF_8') | ~v1_relat_1(B_561))), inference(demodulation, [status(thm), theory('equality')], [c_8231, c_8230])).
% 8.66/2.88  tff(c_8477, plain, (k2_relat_1('#skF_9')='#skF_8' | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_7878, c_8474])).
% 8.66/2.88  tff(c_8480, plain, (k2_relat_1('#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_7758, c_8477])).
% 8.66/2.88  tff(c_8265, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_8234, c_84])).
% 8.66/2.88  tff(c_8546, plain, (![A_566, B_567, C_568]: (k2_relset_1(A_566, B_567, C_568)=k2_relat_1(C_568) | ~m1_subset_1(C_568, k1_zfmisc_1(k2_zfmisc_1(A_566, B_567))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.66/2.88  tff(c_8549, plain, (k2_relset_1('#skF_8', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_8265, c_8546])).
% 8.66/2.88  tff(c_8555, plain, (k2_relset_1('#skF_8', '#skF_8', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_8480, c_8549])).
% 8.66/2.88  tff(c_8557, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8266, c_8555])).
% 8.66/2.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.66/2.88  
% 8.66/2.88  Inference rules
% 8.66/2.88  ----------------------
% 8.66/2.88  #Ref     : 0
% 8.66/2.88  #Sup     : 1749
% 8.66/2.88  #Fact    : 0
% 8.66/2.88  #Define  : 0
% 8.66/2.88  #Split   : 40
% 8.66/2.88  #Chain   : 0
% 8.66/2.88  #Close   : 0
% 8.66/2.88  
% 8.66/2.88  Ordering : KBO
% 8.66/2.88  
% 8.66/2.88  Simplification rules
% 8.66/2.88  ----------------------
% 8.66/2.88  #Subsume      : 411
% 8.66/2.88  #Demod        : 1130
% 8.66/2.88  #Tautology    : 381
% 8.66/2.88  #SimpNegUnit  : 157
% 8.66/2.88  #BackRed      : 328
% 8.66/2.88  
% 8.66/2.88  #Partial instantiations: 0
% 8.66/2.88  #Strategies tried      : 1
% 8.66/2.88  
% 8.66/2.88  Timing (in seconds)
% 8.66/2.88  ----------------------
% 8.66/2.88  Preprocessing        : 0.37
% 8.66/2.88  Parsing              : 0.19
% 8.66/2.88  CNF conversion       : 0.03
% 8.66/2.88  Main loop            : 1.72
% 8.66/2.88  Inferencing          : 0.53
% 8.66/2.88  Reduction            : 0.52
% 8.66/2.88  Demodulation         : 0.33
% 8.66/2.88  BG Simplification    : 0.06
% 8.66/2.88  Subsumption          : 0.46
% 8.66/2.88  Abstraction          : 0.08
% 8.66/2.88  MUC search           : 0.00
% 8.66/2.88  Cooper               : 0.00
% 8.66/2.88  Total                : 2.14
% 8.66/2.88  Index Insertion      : 0.00
% 8.66/2.88  Index Deletion       : 0.00
% 8.66/2.88  Index Matching       : 0.00
% 8.66/2.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
