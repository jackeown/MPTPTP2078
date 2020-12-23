%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:51 EST 2020

% Result     : Theorem 7.43s
% Output     : CNFRefutation 7.63s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 766 expanded)
%              Number of leaves         :   50 ( 256 expanded)
%              Depth                    :   21
%              Number of atoms          :  290 (2372 expanded)
%              Number of equality atoms :   49 ( 618 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_179,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_125,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_139,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_156,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_104,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1('#skF_1'(A_2),A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_74,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_792,plain,(
    ! [A_207,B_208,C_209,D_210] :
      ( r2_relset_1(A_207,B_208,C_209,C_209)
      | ~ m1_subset_1(D_210,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208)))
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_892,plain,(
    ! [C_218] :
      ( r2_relset_1('#skF_7','#skF_8',C_218,C_218)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ) ),
    inference(resolution,[status(thm)],[c_74,c_792])).

tff(c_908,plain,(
    r2_relset_1('#skF_7','#skF_8','#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_80,c_892])).

tff(c_70,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_108,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_78,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_76,plain,(
    v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_678,plain,(
    ! [C_191,A_192,B_193] :
      ( v1_partfun1(C_191,A_192)
      | ~ v1_funct_2(C_191,A_192,B_193)
      | ~ v1_funct_1(C_191)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193)))
      | v1_xboole_0(B_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_685,plain,
    ( v1_partfun1('#skF_10','#skF_7')
    | ~ v1_funct_2('#skF_10','#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_10')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_74,c_678])).

tff(c_700,plain,
    ( v1_partfun1('#skF_10','#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_685])).

tff(c_706,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_700])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_709,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_706,c_2])).

tff(c_713,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_709])).

tff(c_715,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_700])).

tff(c_84,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_82,plain,(
    v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_688,plain,
    ( v1_partfun1('#skF_9','#skF_7')
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_9')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_80,c_678])).

tff(c_703,plain,
    ( v1_partfun1('#skF_9','#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_688])).

tff(c_716,plain,(
    v1_partfun1('#skF_9','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_715,c_703])).

tff(c_714,plain,(
    v1_partfun1('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_700])).

tff(c_72,plain,(
    r1_partfun1('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1591,plain,(
    ! [D_273,C_274,A_275,B_276] :
      ( D_273 = C_274
      | ~ r1_partfun1(C_274,D_273)
      | ~ v1_partfun1(D_273,A_275)
      | ~ v1_partfun1(C_274,A_275)
      | ~ m1_subset_1(D_273,k1_zfmisc_1(k2_zfmisc_1(A_275,B_276)))
      | ~ v1_funct_1(D_273)
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_zfmisc_1(A_275,B_276)))
      | ~ v1_funct_1(C_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1593,plain,(
    ! [A_275,B_276] :
      ( '#skF_10' = '#skF_9'
      | ~ v1_partfun1('#skF_10',A_275)
      | ~ v1_partfun1('#skF_9',A_275)
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(A_275,B_276)))
      | ~ v1_funct_1('#skF_10')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(A_275,B_276)))
      | ~ v1_funct_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_72,c_1591])).

tff(c_1596,plain,(
    ! [A_275,B_276] :
      ( '#skF_10' = '#skF_9'
      | ~ v1_partfun1('#skF_10',A_275)
      | ~ v1_partfun1('#skF_9',A_275)
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(A_275,B_276)))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(A_275,B_276))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_78,c_1593])).

tff(c_1869,plain,(
    ! [A_294,B_295] :
      ( ~ v1_partfun1('#skF_10',A_294)
      | ~ v1_partfun1('#skF_9',A_294)
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(A_294,B_295)))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(A_294,B_295))) ) ),
    inference(splitLeft,[status(thm)],[c_1596])).

tff(c_1875,plain,
    ( ~ v1_partfun1('#skF_10','#skF_7')
    | ~ v1_partfun1('#skF_9','#skF_7')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(resolution,[status(thm)],[c_74,c_1869])).

tff(c_1880,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_716,c_714,c_1875])).

tff(c_1881,plain,(
    '#skF_10' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1596])).

tff(c_68,plain,(
    ~ r2_relset_1('#skF_7','#skF_8','#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1893,plain,(
    ~ r2_relset_1('#skF_7','#skF_8','#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1881,c_68])).

tff(c_1906,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_908,c_1893])).

tff(c_1908,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1907,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1915,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1908,c_1907])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1909,plain,(
    ! [A_4] : m1_subset_1('#skF_7',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1907,c_6])).

tff(c_1926,plain,(
    ! [A_4] : m1_subset_1('#skF_8',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1915,c_1909])).

tff(c_1935,plain,(
    ! [A_302,B_303] :
      ( r1_tarski(A_302,B_303)
      | ~ m1_subset_1(A_302,k1_zfmisc_1(B_303)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1955,plain,(
    ! [A_4] : r1_tarski('#skF_8',A_4) ),
    inference(resolution,[status(thm)],[c_1926,c_1935])).

tff(c_1932,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1915,c_80])).

tff(c_8072,plain,(
    ! [A_813,B_814,C_815,D_816] :
      ( r2_relset_1(A_813,B_814,C_815,C_815)
      | ~ m1_subset_1(D_816,k1_zfmisc_1(k2_zfmisc_1(A_813,B_814)))
      | ~ m1_subset_1(C_815,k1_zfmisc_1(k2_zfmisc_1(A_813,B_814))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_8100,plain,(
    ! [C_819] :
      ( r2_relset_1('#skF_8','#skF_8',C_819,C_819)
      | ~ m1_subset_1(C_819,k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_8'))) ) ),
    inference(resolution,[status(thm)],[c_1932,c_8072])).

tff(c_8115,plain,(
    r2_relset_1('#skF_8','#skF_8','#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_1932,c_8100])).

tff(c_44,plain,(
    ! [A_58] : v1_relat_1(k6_relat_1(A_58)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_46,plain,(
    ! [A_58] : v1_funct_1(k6_relat_1(A_58)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24,plain,(
    ! [A_17] : k2_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    ! [A_17] : k1_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8315,plain,(
    ! [A_842,B_843] :
      ( r2_hidden('#skF_3'(A_842,B_843),k1_relat_1(A_842))
      | r2_hidden('#skF_4'(A_842,B_843),B_843)
      | k2_relat_1(A_842) = B_843
      | ~ v1_funct_1(A_842)
      | ~ v1_relat_1(A_842) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_8342,plain,(
    ! [A_17,B_843] :
      ( r2_hidden('#skF_3'(k6_relat_1(A_17),B_843),A_17)
      | r2_hidden('#skF_4'(k6_relat_1(A_17),B_843),B_843)
      | k2_relat_1(k6_relat_1(A_17)) = B_843
      | ~ v1_funct_1(k6_relat_1(A_17))
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_8315])).

tff(c_9054,plain,(
    ! [A_907,B_908] :
      ( r2_hidden('#skF_3'(k6_relat_1(A_907),B_908),A_907)
      | r2_hidden('#skF_4'(k6_relat_1(A_907),B_908),B_908)
      | B_908 = A_907 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_24,c_8342])).

tff(c_2037,plain,(
    ! [C_320,B_321,A_322] :
      ( ~ v1_xboole_0(C_320)
      | ~ m1_subset_1(B_321,k1_zfmisc_1(C_320))
      | ~ r2_hidden(A_322,B_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2052,plain,(
    ! [A_4,A_322] :
      ( ~ v1_xboole_0(A_4)
      | ~ r2_hidden(A_322,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1926,c_2037])).

tff(c_2054,plain,(
    ! [A_322] : ~ r2_hidden(A_322,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2052])).

tff(c_9095,plain,(
    ! [B_908] :
      ( r2_hidden('#skF_4'(k6_relat_1('#skF_8'),B_908),B_908)
      | B_908 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_9054,c_2054])).

tff(c_1958,plain,(
    ! [C_305,A_306,B_307] :
      ( v1_relat_1(C_305)
      | ~ m1_subset_1(C_305,k1_zfmisc_1(k2_zfmisc_1(A_306,B_307))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1978,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_1932,c_1958])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2055,plain,(
    ! [A_323] : ~ r2_hidden(A_323,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2052])).

tff(c_2060,plain,(
    ! [A_5] :
      ( v1_xboole_0('#skF_8')
      | ~ m1_subset_1(A_5,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_8,c_2055])).

tff(c_2062,plain,(
    ! [A_324] : ~ m1_subset_1(A_324,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2060])).

tff(c_2067,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_4,c_2062])).

tff(c_2068,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_2060])).

tff(c_2012,plain,(
    ! [C_316,B_317,A_318] :
      ( v5_relat_1(C_316,B_317)
      | ~ m1_subset_1(C_316,k1_zfmisc_1(k2_zfmisc_1(A_318,B_317))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2032,plain,(
    v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_1932,c_2012])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v5_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_9102,plain,(
    ! [B_909] :
      ( r2_hidden('#skF_4'(k6_relat_1('#skF_8'),B_909),B_909)
      | B_909 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_9054,c_2054])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2049,plain,(
    ! [B_8,A_322,A_7] :
      ( ~ v1_xboole_0(B_8)
      | ~ r2_hidden(A_322,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(resolution,[status(thm)],[c_12,c_2037])).

tff(c_9129,plain,(
    ! [B_910,B_911] :
      ( ~ v1_xboole_0(B_910)
      | ~ r1_tarski(B_911,B_910)
      | B_911 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_9102,c_2049])).

tff(c_9179,plain,(
    ! [A_915,B_916] :
      ( ~ v1_xboole_0(A_915)
      | k2_relat_1(B_916) = '#skF_8'
      | ~ v5_relat_1(B_916,A_915)
      | ~ v1_relat_1(B_916) ) ),
    inference(resolution,[status(thm)],[c_20,c_9129])).

tff(c_9197,plain,
    ( ~ v1_xboole_0('#skF_8')
    | k2_relat_1('#skF_9') = '#skF_8'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_2032,c_9179])).

tff(c_9215,plain,(
    k2_relat_1('#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1978,c_2068,c_9197])).

tff(c_26,plain,(
    ! [A_18,D_57] :
      ( r2_hidden(k1_funct_1(A_18,D_57),k2_relat_1(A_18))
      | ~ r2_hidden(D_57,k1_relat_1(A_18))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_9287,plain,(
    ! [D_57] :
      ( r2_hidden(k1_funct_1('#skF_9',D_57),'#skF_8')
      | ~ r2_hidden(D_57,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9215,c_26])).

tff(c_9309,plain,(
    ! [D_57] :
      ( r2_hidden(k1_funct_1('#skF_9',D_57),'#skF_8')
      | ~ r2_hidden(D_57,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1978,c_84,c_9287])).

tff(c_9423,plain,(
    ! [D_921] : ~ r2_hidden(D_921,k1_relat_1('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_2054,c_9309])).

tff(c_9466,plain,(
    k1_relat_1('#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_9095,c_9423])).

tff(c_1931,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1915,c_74])).

tff(c_1979,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_1931,c_1958])).

tff(c_2033,plain,(
    v5_relat_1('#skF_10','#skF_8') ),
    inference(resolution,[status(thm)],[c_1931,c_2012])).

tff(c_9194,plain,
    ( ~ v1_xboole_0('#skF_8')
    | k2_relat_1('#skF_10') = '#skF_8'
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_2033,c_9179])).

tff(c_9212,plain,(
    k2_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1979,c_2068,c_9194])).

tff(c_2271,plain,(
    ! [A_368,D_369] :
      ( r2_hidden(k1_funct_1(A_368,D_369),k2_relat_1(A_368))
      | ~ r2_hidden(D_369,k1_relat_1(A_368))
      | ~ v1_funct_1(A_368)
      | ~ v1_relat_1(A_368) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_52,plain,(
    ! [B_66,A_65] :
      ( ~ r1_tarski(B_66,A_65)
      | ~ r2_hidden(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_9316,plain,(
    ! [A_917,D_918] :
      ( ~ r1_tarski(k2_relat_1(A_917),k1_funct_1(A_917,D_918))
      | ~ r2_hidden(D_918,k1_relat_1(A_917))
      | ~ v1_funct_1(A_917)
      | ~ v1_relat_1(A_917) ) ),
    inference(resolution,[status(thm)],[c_2271,c_52])).

tff(c_9322,plain,(
    ! [D_918] :
      ( ~ r1_tarski('#skF_8',k1_funct_1('#skF_10',D_918))
      | ~ r2_hidden(D_918,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9212,c_9316])).

tff(c_9517,plain,(
    ! [D_924] : ~ r2_hidden(D_924,k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1979,c_78,c_1955,c_9322])).

tff(c_9560,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_9095,c_9517])).

tff(c_50,plain,(
    ! [A_59,B_63] :
      ( r2_hidden('#skF_6'(A_59,B_63),k1_relat_1(A_59))
      | B_63 = A_59
      | k1_relat_1(B_63) != k1_relat_1(A_59)
      | ~ v1_funct_1(B_63)
      | ~ v1_relat_1(B_63)
      | ~ v1_funct_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_9580,plain,(
    ! [B_63] :
      ( r2_hidden('#skF_6'('#skF_10',B_63),'#skF_8')
      | B_63 = '#skF_10'
      | k1_relat_1(B_63) != k1_relat_1('#skF_10')
      | ~ v1_funct_1(B_63)
      | ~ v1_relat_1(B_63)
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9560,c_50])).

tff(c_9590,plain,(
    ! [B_63] :
      ( r2_hidden('#skF_6'('#skF_10',B_63),'#skF_8')
      | B_63 = '#skF_10'
      | k1_relat_1(B_63) != '#skF_8'
      | ~ v1_funct_1(B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1979,c_78,c_9560,c_9580])).

tff(c_9881,plain,(
    ! [B_944] :
      ( B_944 = '#skF_10'
      | k1_relat_1(B_944) != '#skF_8'
      | ~ v1_funct_1(B_944)
      | ~ v1_relat_1(B_944) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2054,c_9590])).

tff(c_9902,plain,
    ( '#skF_10' = '#skF_9'
    | k1_relat_1('#skF_9') != '#skF_8'
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_1978,c_9881])).

tff(c_9917,plain,(
    '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_9466,c_9902])).

tff(c_1930,plain,(
    ~ r2_relset_1('#skF_8','#skF_8','#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1915,c_68])).

tff(c_9939,plain,(
    ~ r2_relset_1('#skF_8','#skF_8','#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9917,c_1930])).

tff(c_9953,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8115,c_9939])).

tff(c_9954,plain,(
    ! [A_4] : ~ v1_xboole_0(A_4) ),
    inference(splitRight,[status(thm)],[c_2052])).

tff(c_9957,plain,(
    ! [A_946,B_947] :
      ( r2_hidden(A_946,B_947)
      | ~ m1_subset_1(A_946,B_947) ) ),
    inference(negUnitSimplification,[status(thm)],[c_9954,c_8])).

tff(c_9987,plain,(
    ! [B_952,A_953] :
      ( ~ r1_tarski(B_952,A_953)
      | ~ m1_subset_1(A_953,B_952) ) ),
    inference(resolution,[status(thm)],[c_9957,c_52])).

tff(c_10004,plain,(
    ! [A_954] : ~ m1_subset_1(A_954,'#skF_8') ),
    inference(resolution,[status(thm)],[c_1955,c_9987])).

tff(c_10009,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_4,c_10004])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:37:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.43/2.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.43/2.68  
% 7.43/2.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.43/2.68  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4
% 7.43/2.68  
% 7.43/2.68  %Foreground sorts:
% 7.43/2.68  
% 7.43/2.68  
% 7.43/2.68  %Background operators:
% 7.43/2.68  
% 7.43/2.68  
% 7.43/2.68  %Foreground operators:
% 7.43/2.68  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 7.43/2.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.43/2.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.43/2.68  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.43/2.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.43/2.68  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.43/2.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.43/2.68  tff('#skF_7', type, '#skF_7': $i).
% 7.43/2.68  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.43/2.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.43/2.68  tff('#skF_10', type, '#skF_10': $i).
% 7.43/2.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.43/2.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.43/2.68  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.43/2.68  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.43/2.68  tff('#skF_9', type, '#skF_9': $i).
% 7.43/2.68  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.43/2.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.43/2.68  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.43/2.68  tff('#skF_8', type, '#skF_8': $i).
% 7.43/2.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.43/2.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.43/2.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.43/2.68  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.43/2.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.43/2.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.43/2.68  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.43/2.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.43/2.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.43/2.68  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 7.43/2.68  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.43/2.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.43/2.68  
% 7.63/2.70  tff(f_32, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 7.63/2.70  tff(f_179, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 7.63/2.70  tff(f_125, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 7.63/2.70  tff(f_139, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 7.63/2.70  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 7.63/2.70  tff(f_156, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 7.63/2.70  tff(f_34, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 7.63/2.70  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.63/2.70  tff(f_86, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 7.63/2.70  tff(f_67, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.63/2.70  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 7.63/2.70  tff(f_57, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 7.63/2.70  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.63/2.70  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 7.63/2.70  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.63/2.70  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 7.63/2.70  tff(f_109, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.63/2.70  tff(f_104, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 7.63/2.70  tff(c_4, plain, (![A_2]: (m1_subset_1('#skF_1'(A_2), A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.63/2.70  tff(c_80, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.63/2.70  tff(c_74, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.63/2.70  tff(c_792, plain, (![A_207, B_208, C_209, D_210]: (r2_relset_1(A_207, B_208, C_209, C_209) | ~m1_subset_1(D_210, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.63/2.70  tff(c_892, plain, (![C_218]: (r2_relset_1('#skF_7', '#skF_8', C_218, C_218) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8'))))), inference(resolution, [status(thm)], [c_74, c_792])).
% 7.63/2.70  tff(c_908, plain, (r2_relset_1('#skF_7', '#skF_8', '#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_80, c_892])).
% 7.63/2.70  tff(c_70, plain, (k1_xboole_0='#skF_7' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.63/2.70  tff(c_108, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_70])).
% 7.63/2.70  tff(c_78, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.63/2.70  tff(c_76, plain, (v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.63/2.70  tff(c_678, plain, (![C_191, A_192, B_193]: (v1_partfun1(C_191, A_192) | ~v1_funct_2(C_191, A_192, B_193) | ~v1_funct_1(C_191) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))) | v1_xboole_0(B_193))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.63/2.70  tff(c_685, plain, (v1_partfun1('#skF_10', '#skF_7') | ~v1_funct_2('#skF_10', '#skF_7', '#skF_8') | ~v1_funct_1('#skF_10') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_74, c_678])).
% 7.63/2.70  tff(c_700, plain, (v1_partfun1('#skF_10', '#skF_7') | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_685])).
% 7.63/2.70  tff(c_706, plain, (v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_700])).
% 7.63/2.70  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.63/2.70  tff(c_709, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_706, c_2])).
% 7.63/2.70  tff(c_713, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_709])).
% 7.63/2.70  tff(c_715, plain, (~v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_700])).
% 7.63/2.70  tff(c_84, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.63/2.70  tff(c_82, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.63/2.70  tff(c_688, plain, (v1_partfun1('#skF_9', '#skF_7') | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_1('#skF_9') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_80, c_678])).
% 7.63/2.70  tff(c_703, plain, (v1_partfun1('#skF_9', '#skF_7') | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_688])).
% 7.63/2.70  tff(c_716, plain, (v1_partfun1('#skF_9', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_715, c_703])).
% 7.63/2.70  tff(c_714, plain, (v1_partfun1('#skF_10', '#skF_7')), inference(splitRight, [status(thm)], [c_700])).
% 7.63/2.70  tff(c_72, plain, (r1_partfun1('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.63/2.70  tff(c_1591, plain, (![D_273, C_274, A_275, B_276]: (D_273=C_274 | ~r1_partfun1(C_274, D_273) | ~v1_partfun1(D_273, A_275) | ~v1_partfun1(C_274, A_275) | ~m1_subset_1(D_273, k1_zfmisc_1(k2_zfmisc_1(A_275, B_276))) | ~v1_funct_1(D_273) | ~m1_subset_1(C_274, k1_zfmisc_1(k2_zfmisc_1(A_275, B_276))) | ~v1_funct_1(C_274))), inference(cnfTransformation, [status(thm)], [f_156])).
% 7.63/2.70  tff(c_1593, plain, (![A_275, B_276]: ('#skF_10'='#skF_9' | ~v1_partfun1('#skF_10', A_275) | ~v1_partfun1('#skF_9', A_275) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(A_275, B_276))) | ~v1_funct_1('#skF_10') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(A_275, B_276))) | ~v1_funct_1('#skF_9'))), inference(resolution, [status(thm)], [c_72, c_1591])).
% 7.63/2.70  tff(c_1596, plain, (![A_275, B_276]: ('#skF_10'='#skF_9' | ~v1_partfun1('#skF_10', A_275) | ~v1_partfun1('#skF_9', A_275) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(A_275, B_276))) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(A_275, B_276))))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_78, c_1593])).
% 7.63/2.70  tff(c_1869, plain, (![A_294, B_295]: (~v1_partfun1('#skF_10', A_294) | ~v1_partfun1('#skF_9', A_294) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))))), inference(splitLeft, [status(thm)], [c_1596])).
% 7.63/2.70  tff(c_1875, plain, (~v1_partfun1('#skF_10', '#skF_7') | ~v1_partfun1('#skF_9', '#skF_7') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(resolution, [status(thm)], [c_74, c_1869])).
% 7.63/2.70  tff(c_1880, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_716, c_714, c_1875])).
% 7.63/2.70  tff(c_1881, plain, ('#skF_10'='#skF_9'), inference(splitRight, [status(thm)], [c_1596])).
% 7.63/2.70  tff(c_68, plain, (~r2_relset_1('#skF_7', '#skF_8', '#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.63/2.70  tff(c_1893, plain, (~r2_relset_1('#skF_7', '#skF_8', '#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1881, c_68])).
% 7.63/2.70  tff(c_1906, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_908, c_1893])).
% 7.63/2.70  tff(c_1908, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_70])).
% 7.63/2.70  tff(c_1907, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_70])).
% 7.63/2.70  tff(c_1915, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1908, c_1907])).
% 7.63/2.70  tff(c_6, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.63/2.70  tff(c_1909, plain, (![A_4]: (m1_subset_1('#skF_7', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_1907, c_6])).
% 7.63/2.70  tff(c_1926, plain, (![A_4]: (m1_subset_1('#skF_8', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_1915, c_1909])).
% 7.63/2.70  tff(c_1935, plain, (![A_302, B_303]: (r1_tarski(A_302, B_303) | ~m1_subset_1(A_302, k1_zfmisc_1(B_303)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.63/2.70  tff(c_1955, plain, (![A_4]: (r1_tarski('#skF_8', A_4))), inference(resolution, [status(thm)], [c_1926, c_1935])).
% 7.63/2.70  tff(c_1932, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_1915, c_80])).
% 7.63/2.70  tff(c_8072, plain, (![A_813, B_814, C_815, D_816]: (r2_relset_1(A_813, B_814, C_815, C_815) | ~m1_subset_1(D_816, k1_zfmisc_1(k2_zfmisc_1(A_813, B_814))) | ~m1_subset_1(C_815, k1_zfmisc_1(k2_zfmisc_1(A_813, B_814))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.63/2.70  tff(c_8100, plain, (![C_819]: (r2_relset_1('#skF_8', '#skF_8', C_819, C_819) | ~m1_subset_1(C_819, k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_8'))))), inference(resolution, [status(thm)], [c_1932, c_8072])).
% 7.63/2.70  tff(c_8115, plain, (r2_relset_1('#skF_8', '#skF_8', '#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_1932, c_8100])).
% 7.63/2.70  tff(c_44, plain, (![A_58]: (v1_relat_1(k6_relat_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.63/2.70  tff(c_46, plain, (![A_58]: (v1_funct_1(k6_relat_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.63/2.70  tff(c_24, plain, (![A_17]: (k2_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.63/2.70  tff(c_22, plain, (![A_17]: (k1_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.63/2.70  tff(c_8315, plain, (![A_842, B_843]: (r2_hidden('#skF_3'(A_842, B_843), k1_relat_1(A_842)) | r2_hidden('#skF_4'(A_842, B_843), B_843) | k2_relat_1(A_842)=B_843 | ~v1_funct_1(A_842) | ~v1_relat_1(A_842))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.63/2.70  tff(c_8342, plain, (![A_17, B_843]: (r2_hidden('#skF_3'(k6_relat_1(A_17), B_843), A_17) | r2_hidden('#skF_4'(k6_relat_1(A_17), B_843), B_843) | k2_relat_1(k6_relat_1(A_17))=B_843 | ~v1_funct_1(k6_relat_1(A_17)) | ~v1_relat_1(k6_relat_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_8315])).
% 7.63/2.70  tff(c_9054, plain, (![A_907, B_908]: (r2_hidden('#skF_3'(k6_relat_1(A_907), B_908), A_907) | r2_hidden('#skF_4'(k6_relat_1(A_907), B_908), B_908) | B_908=A_907)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_24, c_8342])).
% 7.63/2.70  tff(c_2037, plain, (![C_320, B_321, A_322]: (~v1_xboole_0(C_320) | ~m1_subset_1(B_321, k1_zfmisc_1(C_320)) | ~r2_hidden(A_322, B_321))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.63/2.70  tff(c_2052, plain, (![A_4, A_322]: (~v1_xboole_0(A_4) | ~r2_hidden(A_322, '#skF_8'))), inference(resolution, [status(thm)], [c_1926, c_2037])).
% 7.63/2.70  tff(c_2054, plain, (![A_322]: (~r2_hidden(A_322, '#skF_8'))), inference(splitLeft, [status(thm)], [c_2052])).
% 7.63/2.70  tff(c_9095, plain, (![B_908]: (r2_hidden('#skF_4'(k6_relat_1('#skF_8'), B_908), B_908) | B_908='#skF_8')), inference(resolution, [status(thm)], [c_9054, c_2054])).
% 7.63/2.70  tff(c_1958, plain, (![C_305, A_306, B_307]: (v1_relat_1(C_305) | ~m1_subset_1(C_305, k1_zfmisc_1(k2_zfmisc_1(A_306, B_307))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.63/2.70  tff(c_1978, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_1932, c_1958])).
% 7.63/2.70  tff(c_8, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.63/2.70  tff(c_2055, plain, (![A_323]: (~r2_hidden(A_323, '#skF_8'))), inference(splitLeft, [status(thm)], [c_2052])).
% 7.63/2.70  tff(c_2060, plain, (![A_5]: (v1_xboole_0('#skF_8') | ~m1_subset_1(A_5, '#skF_8'))), inference(resolution, [status(thm)], [c_8, c_2055])).
% 7.63/2.70  tff(c_2062, plain, (![A_324]: (~m1_subset_1(A_324, '#skF_8'))), inference(splitLeft, [status(thm)], [c_2060])).
% 7.63/2.70  tff(c_2067, plain, $false, inference(resolution, [status(thm)], [c_4, c_2062])).
% 7.63/2.70  tff(c_2068, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_2060])).
% 7.63/2.70  tff(c_2012, plain, (![C_316, B_317, A_318]: (v5_relat_1(C_316, B_317) | ~m1_subset_1(C_316, k1_zfmisc_1(k2_zfmisc_1(A_318, B_317))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.63/2.70  tff(c_2032, plain, (v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_1932, c_2012])).
% 7.63/2.70  tff(c_20, plain, (![B_16, A_15]: (r1_tarski(k2_relat_1(B_16), A_15) | ~v5_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.63/2.70  tff(c_9102, plain, (![B_909]: (r2_hidden('#skF_4'(k6_relat_1('#skF_8'), B_909), B_909) | B_909='#skF_8')), inference(resolution, [status(thm)], [c_9054, c_2054])).
% 7.63/2.70  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.63/2.70  tff(c_2049, plain, (![B_8, A_322, A_7]: (~v1_xboole_0(B_8) | ~r2_hidden(A_322, A_7) | ~r1_tarski(A_7, B_8))), inference(resolution, [status(thm)], [c_12, c_2037])).
% 7.63/2.70  tff(c_9129, plain, (![B_910, B_911]: (~v1_xboole_0(B_910) | ~r1_tarski(B_911, B_910) | B_911='#skF_8')), inference(resolution, [status(thm)], [c_9102, c_2049])).
% 7.63/2.70  tff(c_9179, plain, (![A_915, B_916]: (~v1_xboole_0(A_915) | k2_relat_1(B_916)='#skF_8' | ~v5_relat_1(B_916, A_915) | ~v1_relat_1(B_916))), inference(resolution, [status(thm)], [c_20, c_9129])).
% 7.63/2.70  tff(c_9197, plain, (~v1_xboole_0('#skF_8') | k2_relat_1('#skF_9')='#skF_8' | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_2032, c_9179])).
% 7.63/2.70  tff(c_9215, plain, (k2_relat_1('#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1978, c_2068, c_9197])).
% 7.63/2.70  tff(c_26, plain, (![A_18, D_57]: (r2_hidden(k1_funct_1(A_18, D_57), k2_relat_1(A_18)) | ~r2_hidden(D_57, k1_relat_1(A_18)) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.63/2.70  tff(c_9287, plain, (![D_57]: (r2_hidden(k1_funct_1('#skF_9', D_57), '#skF_8') | ~r2_hidden(D_57, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_9215, c_26])).
% 7.63/2.70  tff(c_9309, plain, (![D_57]: (r2_hidden(k1_funct_1('#skF_9', D_57), '#skF_8') | ~r2_hidden(D_57, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_1978, c_84, c_9287])).
% 7.63/2.70  tff(c_9423, plain, (![D_921]: (~r2_hidden(D_921, k1_relat_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_2054, c_9309])).
% 7.63/2.70  tff(c_9466, plain, (k1_relat_1('#skF_9')='#skF_8'), inference(resolution, [status(thm)], [c_9095, c_9423])).
% 7.63/2.70  tff(c_1931, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_1915, c_74])).
% 7.63/2.70  tff(c_1979, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_1931, c_1958])).
% 7.63/2.70  tff(c_2033, plain, (v5_relat_1('#skF_10', '#skF_8')), inference(resolution, [status(thm)], [c_1931, c_2012])).
% 7.63/2.70  tff(c_9194, plain, (~v1_xboole_0('#skF_8') | k2_relat_1('#skF_10')='#skF_8' | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_2033, c_9179])).
% 7.63/2.70  tff(c_9212, plain, (k2_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1979, c_2068, c_9194])).
% 7.63/2.70  tff(c_2271, plain, (![A_368, D_369]: (r2_hidden(k1_funct_1(A_368, D_369), k2_relat_1(A_368)) | ~r2_hidden(D_369, k1_relat_1(A_368)) | ~v1_funct_1(A_368) | ~v1_relat_1(A_368))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.63/2.70  tff(c_52, plain, (![B_66, A_65]: (~r1_tarski(B_66, A_65) | ~r2_hidden(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.63/2.70  tff(c_9316, plain, (![A_917, D_918]: (~r1_tarski(k2_relat_1(A_917), k1_funct_1(A_917, D_918)) | ~r2_hidden(D_918, k1_relat_1(A_917)) | ~v1_funct_1(A_917) | ~v1_relat_1(A_917))), inference(resolution, [status(thm)], [c_2271, c_52])).
% 7.63/2.70  tff(c_9322, plain, (![D_918]: (~r1_tarski('#skF_8', k1_funct_1('#skF_10', D_918)) | ~r2_hidden(D_918, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_9212, c_9316])).
% 7.63/2.70  tff(c_9517, plain, (![D_924]: (~r2_hidden(D_924, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_1979, c_78, c_1955, c_9322])).
% 7.63/2.70  tff(c_9560, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(resolution, [status(thm)], [c_9095, c_9517])).
% 7.63/2.70  tff(c_50, plain, (![A_59, B_63]: (r2_hidden('#skF_6'(A_59, B_63), k1_relat_1(A_59)) | B_63=A_59 | k1_relat_1(B_63)!=k1_relat_1(A_59) | ~v1_funct_1(B_63) | ~v1_relat_1(B_63) | ~v1_funct_1(A_59) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.63/2.70  tff(c_9580, plain, (![B_63]: (r2_hidden('#skF_6'('#skF_10', B_63), '#skF_8') | B_63='#skF_10' | k1_relat_1(B_63)!=k1_relat_1('#skF_10') | ~v1_funct_1(B_63) | ~v1_relat_1(B_63) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_9560, c_50])).
% 7.63/2.70  tff(c_9590, plain, (![B_63]: (r2_hidden('#skF_6'('#skF_10', B_63), '#skF_8') | B_63='#skF_10' | k1_relat_1(B_63)!='#skF_8' | ~v1_funct_1(B_63) | ~v1_relat_1(B_63))), inference(demodulation, [status(thm), theory('equality')], [c_1979, c_78, c_9560, c_9580])).
% 7.63/2.70  tff(c_9881, plain, (![B_944]: (B_944='#skF_10' | k1_relat_1(B_944)!='#skF_8' | ~v1_funct_1(B_944) | ~v1_relat_1(B_944))), inference(negUnitSimplification, [status(thm)], [c_2054, c_9590])).
% 7.63/2.70  tff(c_9902, plain, ('#skF_10'='#skF_9' | k1_relat_1('#skF_9')!='#skF_8' | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_1978, c_9881])).
% 7.63/2.70  tff(c_9917, plain, ('#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_9466, c_9902])).
% 7.63/2.70  tff(c_1930, plain, (~r2_relset_1('#skF_8', '#skF_8', '#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1915, c_68])).
% 7.63/2.70  tff(c_9939, plain, (~r2_relset_1('#skF_8', '#skF_8', '#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_9917, c_1930])).
% 7.63/2.70  tff(c_9953, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8115, c_9939])).
% 7.63/2.70  tff(c_9954, plain, (![A_4]: (~v1_xboole_0(A_4))), inference(splitRight, [status(thm)], [c_2052])).
% 7.63/2.70  tff(c_9957, plain, (![A_946, B_947]: (r2_hidden(A_946, B_947) | ~m1_subset_1(A_946, B_947))), inference(negUnitSimplification, [status(thm)], [c_9954, c_8])).
% 7.63/2.70  tff(c_9987, plain, (![B_952, A_953]: (~r1_tarski(B_952, A_953) | ~m1_subset_1(A_953, B_952))), inference(resolution, [status(thm)], [c_9957, c_52])).
% 7.63/2.70  tff(c_10004, plain, (![A_954]: (~m1_subset_1(A_954, '#skF_8'))), inference(resolution, [status(thm)], [c_1955, c_9987])).
% 7.63/2.70  tff(c_10009, plain, $false, inference(resolution, [status(thm)], [c_4, c_10004])).
% 7.63/2.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.63/2.70  
% 7.63/2.70  Inference rules
% 7.63/2.70  ----------------------
% 7.63/2.70  #Ref     : 4
% 7.63/2.70  #Sup     : 1914
% 7.63/2.70  #Fact    : 0
% 7.63/2.70  #Define  : 0
% 7.63/2.70  #Split   : 29
% 7.63/2.70  #Chain   : 0
% 7.63/2.70  #Close   : 0
% 7.63/2.70  
% 7.63/2.70  Ordering : KBO
% 7.63/2.70  
% 7.63/2.70  Simplification rules
% 7.63/2.70  ----------------------
% 7.63/2.70  #Subsume      : 457
% 7.63/2.70  #Demod        : 2378
% 7.63/2.70  #Tautology    : 580
% 7.63/2.70  #SimpNegUnit  : 28
% 7.63/2.70  #BackRed      : 285
% 7.63/2.70  
% 7.63/2.70  #Partial instantiations: 0
% 7.63/2.70  #Strategies tried      : 1
% 7.63/2.70  
% 7.63/2.70  Timing (in seconds)
% 7.63/2.70  ----------------------
% 7.63/2.71  Preprocessing        : 0.36
% 7.63/2.71  Parsing              : 0.19
% 7.63/2.71  CNF conversion       : 0.03
% 7.63/2.71  Main loop            : 1.57
% 7.63/2.71  Inferencing          : 0.52
% 7.63/2.71  Reduction            : 0.59
% 7.63/2.71  Demodulation         : 0.43
% 7.63/2.71  BG Simplification    : 0.05
% 7.63/2.71  Subsumption          : 0.27
% 7.63/2.71  Abstraction          : 0.06
% 7.63/2.71  MUC search           : 0.00
% 7.63/2.71  Cooper               : 0.00
% 7.63/2.71  Total                : 1.97
% 7.63/2.71  Index Insertion      : 0.00
% 7.63/2.71  Index Deletion       : 0.00
% 7.63/2.71  Index Matching       : 0.00
% 7.63/2.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
