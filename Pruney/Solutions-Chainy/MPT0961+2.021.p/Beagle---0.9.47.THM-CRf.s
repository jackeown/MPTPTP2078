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
% DateTime   : Thu Dec  3 10:10:44 EST 2020

% Result     : Theorem 5.15s
% Output     : CNFRefutation 5.30s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 775 expanded)
%              Number of leaves         :   27 ( 274 expanded)
%              Depth                    :   12
%              Number of atoms          :  232 (2192 expanded)
%              Number of equality atoms :   67 ( 588 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_85,axiom,(
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

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4359,plain,(
    ! [C_449,A_450,B_451] :
      ( m1_subset_1(C_449,k1_zfmisc_1(k2_zfmisc_1(A_450,B_451)))
      | ~ r1_tarski(k2_relat_1(C_449),B_451)
      | ~ r1_tarski(k1_relat_1(C_449),A_450)
      | ~ v1_relat_1(C_449) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2007,plain,(
    ! [C_238,A_239,B_240] :
      ( m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_239,B_240)))
      | ~ r1_tarski(k2_relat_1(C_238),B_240)
      | ~ r1_tarski(k1_relat_1(C_238),A_239)
      | ~ v1_relat_1(C_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2630,plain,(
    ! [C_322,A_323,B_324] :
      ( r1_tarski(C_322,k2_zfmisc_1(A_323,B_324))
      | ~ r1_tarski(k2_relat_1(C_322),B_324)
      | ~ r1_tarski(k1_relat_1(C_322),A_323)
      | ~ v1_relat_1(C_322) ) ),
    inference(resolution,[status(thm)],[c_2007,c_16])).

tff(c_2635,plain,(
    ! [C_325,A_326] :
      ( r1_tarski(C_325,k2_zfmisc_1(A_326,k2_relat_1(C_325)))
      | ~ r1_tarski(k1_relat_1(C_325),A_326)
      | ~ v1_relat_1(C_325) ) ),
    inference(resolution,[status(thm)],[c_6,c_2630])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_238,plain,(
    ! [A_65,B_66,C_67] :
      ( k1_relset_1(A_65,B_66,C_67) = k1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_249,plain,(
    ! [A_65,B_66,A_6] :
      ( k1_relset_1(A_65,B_66,A_6) = k1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_65,B_66)) ) ),
    inference(resolution,[status(thm)],[c_18,c_238])).

tff(c_2683,plain,(
    ! [A_328,C_329] :
      ( k1_relset_1(A_328,k2_relat_1(C_329),C_329) = k1_relat_1(C_329)
      | ~ r1_tarski(k1_relat_1(C_329),A_328)
      | ~ v1_relat_1(C_329) ) ),
    inference(resolution,[status(thm)],[c_2635,c_249])).

tff(c_2701,plain,(
    ! [C_329] :
      ( k1_relset_1(k1_relat_1(C_329),k2_relat_1(C_329),C_329) = k1_relat_1(C_329)
      | ~ v1_relat_1(C_329) ) ),
    inference(resolution,[status(thm)],[c_6,c_2683])).

tff(c_30,plain,(
    ! [C_18,A_16,B_17] :
      ( m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17)))
      | ~ r1_tarski(k2_relat_1(C_18),B_17)
      | ~ r1_tarski(k1_relat_1(C_18),A_16)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2252,plain,(
    ! [B_273,C_274,A_275] :
      ( k1_xboole_0 = B_273
      | v1_funct_2(C_274,A_275,B_273)
      | k1_relset_1(A_275,B_273,C_274) != A_275
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_zfmisc_1(A_275,B_273))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3347,plain,(
    ! [B_378,C_379,A_380] :
      ( k1_xboole_0 = B_378
      | v1_funct_2(C_379,A_380,B_378)
      | k1_relset_1(A_380,B_378,C_379) != A_380
      | ~ r1_tarski(k2_relat_1(C_379),B_378)
      | ~ r1_tarski(k1_relat_1(C_379),A_380)
      | ~ v1_relat_1(C_379) ) ),
    inference(resolution,[status(thm)],[c_30,c_2252])).

tff(c_3656,plain,(
    ! [C_400,A_401] :
      ( k2_relat_1(C_400) = k1_xboole_0
      | v1_funct_2(C_400,A_401,k2_relat_1(C_400))
      | k1_relset_1(A_401,k2_relat_1(C_400),C_400) != A_401
      | ~ r1_tarski(k1_relat_1(C_400),A_401)
      | ~ v1_relat_1(C_400) ) ),
    inference(resolution,[status(thm)],[c_6,c_3347])).

tff(c_46,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_44,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_50,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44])).

tff(c_96,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_3672,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3656,c_96])).

tff(c_3683,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_6,c_3672])).

tff(c_3684,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3683])).

tff(c_3690,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2701,c_3684])).

tff(c_3697,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3690])).

tff(c_3698,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3683])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2667,plain,(
    ! [A_326,C_325] :
      ( k2_zfmisc_1(A_326,k2_relat_1(C_325)) = C_325
      | ~ r1_tarski(k2_zfmisc_1(A_326,k2_relat_1(C_325)),C_325)
      | ~ r1_tarski(k1_relat_1(C_325),A_326)
      | ~ v1_relat_1(C_325) ) ),
    inference(resolution,[status(thm)],[c_2635,c_2])).

tff(c_3707,plain,(
    ! [A_326] :
      ( k2_zfmisc_1(A_326,k2_relat_1('#skF_1')) = '#skF_1'
      | ~ r1_tarski(k2_zfmisc_1(A_326,k1_xboole_0),'#skF_1')
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_326)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3698,c_2667])).

tff(c_3735,plain,(
    ! [A_326] :
      ( k1_xboole_0 = '#skF_1'
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_326) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_8,c_12,c_12,c_3698,c_3707])).

tff(c_3756,plain,(
    ! [A_402] : ~ r1_tarski(k1_relat_1('#skF_1'),A_402) ),
    inference(splitLeft,[status(thm)],[c_3735])).

tff(c_3780,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_3756])).

tff(c_3781,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3735])).

tff(c_301,plain,(
    ! [C_72,A_73,B_74] :
      ( m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74)))
      | ~ r1_tarski(k2_relat_1(C_72),B_74)
      | ~ r1_tarski(k1_relat_1(C_72),A_73)
      | ~ v1_relat_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_935,plain,(
    ! [C_167,A_168,B_169] :
      ( r1_tarski(C_167,k2_zfmisc_1(A_168,B_169))
      | ~ r1_tarski(k2_relat_1(C_167),B_169)
      | ~ r1_tarski(k1_relat_1(C_167),A_168)
      | ~ v1_relat_1(C_167) ) ),
    inference(resolution,[status(thm)],[c_301,c_16])).

tff(c_940,plain,(
    ! [C_170,A_171] :
      ( r1_tarski(C_170,k2_zfmisc_1(A_171,k2_relat_1(C_170)))
      | ~ r1_tarski(k1_relat_1(C_170),A_171)
      | ~ v1_relat_1(C_170) ) ),
    inference(resolution,[status(thm)],[c_6,c_935])).

tff(c_983,plain,(
    ! [A_173,C_174] :
      ( k1_relset_1(A_173,k2_relat_1(C_174),C_174) = k1_relat_1(C_174)
      | ~ r1_tarski(k1_relat_1(C_174),A_173)
      | ~ v1_relat_1(C_174) ) ),
    inference(resolution,[status(thm)],[c_940,c_249])).

tff(c_997,plain,(
    ! [C_174] :
      ( k1_relset_1(k1_relat_1(C_174),k2_relat_1(C_174),C_174) = k1_relat_1(C_174)
      | ~ v1_relat_1(C_174) ) ),
    inference(resolution,[status(thm)],[c_6,c_983])).

tff(c_416,plain,(
    ! [B_89,C_90,A_91] :
      ( k1_xboole_0 = B_89
      | v1_funct_2(C_90,A_91,B_89)
      | k1_relset_1(A_91,B_89,C_90) != A_91
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1463,plain,(
    ! [B_210,C_211,A_212] :
      ( k1_xboole_0 = B_210
      | v1_funct_2(C_211,A_212,B_210)
      | k1_relset_1(A_212,B_210,C_211) != A_212
      | ~ r1_tarski(k2_relat_1(C_211),B_210)
      | ~ r1_tarski(k1_relat_1(C_211),A_212)
      | ~ v1_relat_1(C_211) ) ),
    inference(resolution,[status(thm)],[c_30,c_416])).

tff(c_1744,plain,(
    ! [C_235,A_236] :
      ( k2_relat_1(C_235) = k1_xboole_0
      | v1_funct_2(C_235,A_236,k2_relat_1(C_235))
      | k1_relset_1(A_236,k2_relat_1(C_235),C_235) != A_236
      | ~ r1_tarski(k1_relat_1(C_235),A_236)
      | ~ v1_relat_1(C_235) ) ),
    inference(resolution,[status(thm)],[c_6,c_1463])).

tff(c_1764,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1744,c_96])).

tff(c_1776,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_6,c_1764])).

tff(c_1777,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1776])).

tff(c_1783,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_997,c_1777])).

tff(c_1790,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1783])).

tff(c_1791,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1776])).

tff(c_972,plain,(
    ! [A_171,C_170] :
      ( k2_zfmisc_1(A_171,k2_relat_1(C_170)) = C_170
      | ~ r1_tarski(k2_zfmisc_1(A_171,k2_relat_1(C_170)),C_170)
      | ~ r1_tarski(k1_relat_1(C_170),A_171)
      | ~ v1_relat_1(C_170) ) ),
    inference(resolution,[status(thm)],[c_940,c_2])).

tff(c_1800,plain,(
    ! [A_171] :
      ( k2_zfmisc_1(A_171,k2_relat_1('#skF_1')) = '#skF_1'
      | ~ r1_tarski(k2_zfmisc_1(A_171,k1_xboole_0),'#skF_1')
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_171)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1791,c_972])).

tff(c_1828,plain,(
    ! [A_171] :
      ( k1_xboole_0 = '#skF_1'
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_8,c_12,c_12,c_1791,c_1800])).

tff(c_1849,plain,(
    ! [A_237] : ~ r1_tarski(k1_relat_1('#skF_1'),A_237) ),
    inference(splitLeft,[status(thm)],[c_1828])).

tff(c_1873,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_1849])).

tff(c_1874,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1828])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_152,plain,(
    ! [C_45,A_46,B_47] :
      ( v4_relat_1(C_45,A_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_216,plain,(
    ! [A_62,A_63,B_64] :
      ( v4_relat_1(A_62,A_63)
      | ~ r1_tarski(A_62,k2_zfmisc_1(A_63,B_64)) ) ),
    inference(resolution,[status(thm)],[c_18,c_152])).

tff(c_236,plain,(
    ! [A_63,B_64] : v4_relat_1(k2_zfmisc_1(A_63,B_64),A_63) ),
    inference(resolution,[status(thm)],[c_6,c_216])).

tff(c_188,plain,(
    ! [B_57,A_58] :
      ( r1_tarski(k1_relat_1(B_57),A_58)
      | ~ v4_relat_1(B_57,A_58)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_86,plain,(
    ! [B_30,A_31] :
      ( B_30 = A_31
      | ~ r1_tarski(B_30,A_31)
      | ~ r1_tarski(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_86])).

tff(c_260,plain,(
    ! [B_71] :
      ( k1_relat_1(B_71) = k1_xboole_0
      | ~ v4_relat_1(B_71,k1_xboole_0)
      | ~ v1_relat_1(B_71) ) ),
    inference(resolution,[status(thm)],[c_188,c_95])).

tff(c_264,plain,(
    ! [B_64] :
      ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,B_64)) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,B_64)) ) ),
    inference(resolution,[status(thm)],[c_236,c_260])).

tff(c_274,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_264])).

tff(c_277,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_274])).

tff(c_1941,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1874,c_277])).

tff(c_1956,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1941])).

tff(c_1957,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_274])).

tff(c_2160,plain,(
    ! [A_258,B_259,A_260] :
      ( k1_relset_1(A_258,B_259,A_260) = k1_relat_1(A_260)
      | ~ r1_tarski(A_260,k2_zfmisc_1(A_258,B_259)) ) ),
    inference(resolution,[status(thm)],[c_18,c_238])).

tff(c_2178,plain,(
    ! [A_258,B_259] : k1_relset_1(A_258,B_259,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_2160])).

tff(c_2182,plain,(
    ! [A_258,B_259] : k1_relset_1(A_258,B_259,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1957,c_2178])).

tff(c_32,plain,(
    ! [A_19] :
      ( v1_funct_2(k1_xboole_0,A_19,k1_xboole_0)
      | k1_xboole_0 = A_19
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_19,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_53,plain,(
    ! [A_19] :
      ( v1_funct_2(k1_xboole_0,A_19,k1_xboole_0)
      | k1_xboole_0 = A_19
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_32])).

tff(c_1959,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_1981,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_1959])).

tff(c_1985,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1981])).

tff(c_1987,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_36,plain,(
    ! [C_21,B_20] :
      ( v1_funct_2(C_21,k1_xboole_0,B_20)
      | k1_relset_1(k1_xboole_0,B_20,C_21) != k1_xboole_0
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2209,plain,(
    ! [C_265,B_266] :
      ( v1_funct_2(C_265,k1_xboole_0,B_266)
      | k1_relset_1(k1_xboole_0,B_266,C_265) != k1_xboole_0
      | ~ m1_subset_1(C_265,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_36])).

tff(c_2211,plain,(
    ! [B_266] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_266)
      | k1_relset_1(k1_xboole_0,B_266,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1987,c_2209])).

tff(c_2217,plain,(
    ! [B_266] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_266) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2182,c_2211])).

tff(c_3834,plain,(
    ! [B_266] : v1_funct_2('#skF_1','#skF_1',B_266) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3781,c_3781,c_2217])).

tff(c_3846,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3781,c_3781,c_1957])).

tff(c_3700,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3698,c_96])).

tff(c_3783,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3781,c_3700])).

tff(c_3964,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3846,c_3783])).

tff(c_4180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3834,c_3964])).

tff(c_4181,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_4371,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4359,c_4181])).

tff(c_4387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_6,c_6,c_4371])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n019.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 20:33:22 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.15/2.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.15/2.11  
% 5.15/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.15/2.11  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 5.15/2.11  
% 5.15/2.11  %Foreground sorts:
% 5.15/2.11  
% 5.15/2.11  
% 5.15/2.11  %Background operators:
% 5.15/2.11  
% 5.15/2.11  
% 5.15/2.11  %Foreground operators:
% 5.15/2.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.15/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.15/2.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.15/2.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.15/2.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.15/2.11  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.15/2.11  tff('#skF_1', type, '#skF_1': $i).
% 5.15/2.11  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.15/2.11  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.15/2.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.15/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.15/2.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.15/2.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.15/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.15/2.11  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.15/2.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.15/2.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.15/2.11  
% 5.30/2.13  tff(f_96, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 5.30/2.13  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.30/2.13  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 5.30/2.13  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.30/2.13  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.30/2.13  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.30/2.13  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.30/2.13  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.30/2.13  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.30/2.13  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 5.30/2.13  tff(c_48, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.30/2.13  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.30/2.13  tff(c_4359, plain, (![C_449, A_450, B_451]: (m1_subset_1(C_449, k1_zfmisc_1(k2_zfmisc_1(A_450, B_451))) | ~r1_tarski(k2_relat_1(C_449), B_451) | ~r1_tarski(k1_relat_1(C_449), A_450) | ~v1_relat_1(C_449))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.30/2.13  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.30/2.13  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.30/2.13  tff(c_2007, plain, (![C_238, A_239, B_240]: (m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_239, B_240))) | ~r1_tarski(k2_relat_1(C_238), B_240) | ~r1_tarski(k1_relat_1(C_238), A_239) | ~v1_relat_1(C_238))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.30/2.13  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.30/2.13  tff(c_2630, plain, (![C_322, A_323, B_324]: (r1_tarski(C_322, k2_zfmisc_1(A_323, B_324)) | ~r1_tarski(k2_relat_1(C_322), B_324) | ~r1_tarski(k1_relat_1(C_322), A_323) | ~v1_relat_1(C_322))), inference(resolution, [status(thm)], [c_2007, c_16])).
% 5.30/2.13  tff(c_2635, plain, (![C_325, A_326]: (r1_tarski(C_325, k2_zfmisc_1(A_326, k2_relat_1(C_325))) | ~r1_tarski(k1_relat_1(C_325), A_326) | ~v1_relat_1(C_325))), inference(resolution, [status(thm)], [c_6, c_2630])).
% 5.30/2.13  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.30/2.13  tff(c_238, plain, (![A_65, B_66, C_67]: (k1_relset_1(A_65, B_66, C_67)=k1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.30/2.13  tff(c_249, plain, (![A_65, B_66, A_6]: (k1_relset_1(A_65, B_66, A_6)=k1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_65, B_66)))), inference(resolution, [status(thm)], [c_18, c_238])).
% 5.30/2.13  tff(c_2683, plain, (![A_328, C_329]: (k1_relset_1(A_328, k2_relat_1(C_329), C_329)=k1_relat_1(C_329) | ~r1_tarski(k1_relat_1(C_329), A_328) | ~v1_relat_1(C_329))), inference(resolution, [status(thm)], [c_2635, c_249])).
% 5.30/2.13  tff(c_2701, plain, (![C_329]: (k1_relset_1(k1_relat_1(C_329), k2_relat_1(C_329), C_329)=k1_relat_1(C_329) | ~v1_relat_1(C_329))), inference(resolution, [status(thm)], [c_6, c_2683])).
% 5.30/2.13  tff(c_30, plain, (![C_18, A_16, B_17]: (m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))) | ~r1_tarski(k2_relat_1(C_18), B_17) | ~r1_tarski(k1_relat_1(C_18), A_16) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.30/2.13  tff(c_2252, plain, (![B_273, C_274, A_275]: (k1_xboole_0=B_273 | v1_funct_2(C_274, A_275, B_273) | k1_relset_1(A_275, B_273, C_274)!=A_275 | ~m1_subset_1(C_274, k1_zfmisc_1(k2_zfmisc_1(A_275, B_273))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.30/2.13  tff(c_3347, plain, (![B_378, C_379, A_380]: (k1_xboole_0=B_378 | v1_funct_2(C_379, A_380, B_378) | k1_relset_1(A_380, B_378, C_379)!=A_380 | ~r1_tarski(k2_relat_1(C_379), B_378) | ~r1_tarski(k1_relat_1(C_379), A_380) | ~v1_relat_1(C_379))), inference(resolution, [status(thm)], [c_30, c_2252])).
% 5.30/2.13  tff(c_3656, plain, (![C_400, A_401]: (k2_relat_1(C_400)=k1_xboole_0 | v1_funct_2(C_400, A_401, k2_relat_1(C_400)) | k1_relset_1(A_401, k2_relat_1(C_400), C_400)!=A_401 | ~r1_tarski(k1_relat_1(C_400), A_401) | ~v1_relat_1(C_400))), inference(resolution, [status(thm)], [c_6, c_3347])).
% 5.30/2.13  tff(c_46, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.30/2.13  tff(c_44, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.30/2.13  tff(c_50, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44])).
% 5.30/2.13  tff(c_96, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_50])).
% 5.30/2.13  tff(c_3672, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_3656, c_96])).
% 5.30/2.13  tff(c_3683, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_6, c_3672])).
% 5.30/2.13  tff(c_3684, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_3683])).
% 5.30/2.13  tff(c_3690, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2701, c_3684])).
% 5.30/2.13  tff(c_3697, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_3690])).
% 5.30/2.13  tff(c_3698, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3683])).
% 5.30/2.13  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.30/2.13  tff(c_2667, plain, (![A_326, C_325]: (k2_zfmisc_1(A_326, k2_relat_1(C_325))=C_325 | ~r1_tarski(k2_zfmisc_1(A_326, k2_relat_1(C_325)), C_325) | ~r1_tarski(k1_relat_1(C_325), A_326) | ~v1_relat_1(C_325))), inference(resolution, [status(thm)], [c_2635, c_2])).
% 5.30/2.13  tff(c_3707, plain, (![A_326]: (k2_zfmisc_1(A_326, k2_relat_1('#skF_1'))='#skF_1' | ~r1_tarski(k2_zfmisc_1(A_326, k1_xboole_0), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), A_326) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3698, c_2667])).
% 5.30/2.13  tff(c_3735, plain, (![A_326]: (k1_xboole_0='#skF_1' | ~r1_tarski(k1_relat_1('#skF_1'), A_326))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_8, c_12, c_12, c_3698, c_3707])).
% 5.30/2.13  tff(c_3756, plain, (![A_402]: (~r1_tarski(k1_relat_1('#skF_1'), A_402))), inference(splitLeft, [status(thm)], [c_3735])).
% 5.30/2.13  tff(c_3780, plain, $false, inference(resolution, [status(thm)], [c_6, c_3756])).
% 5.30/2.13  tff(c_3781, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_3735])).
% 5.30/2.13  tff(c_301, plain, (![C_72, A_73, B_74]: (m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))) | ~r1_tarski(k2_relat_1(C_72), B_74) | ~r1_tarski(k1_relat_1(C_72), A_73) | ~v1_relat_1(C_72))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.30/2.13  tff(c_935, plain, (![C_167, A_168, B_169]: (r1_tarski(C_167, k2_zfmisc_1(A_168, B_169)) | ~r1_tarski(k2_relat_1(C_167), B_169) | ~r1_tarski(k1_relat_1(C_167), A_168) | ~v1_relat_1(C_167))), inference(resolution, [status(thm)], [c_301, c_16])).
% 5.30/2.13  tff(c_940, plain, (![C_170, A_171]: (r1_tarski(C_170, k2_zfmisc_1(A_171, k2_relat_1(C_170))) | ~r1_tarski(k1_relat_1(C_170), A_171) | ~v1_relat_1(C_170))), inference(resolution, [status(thm)], [c_6, c_935])).
% 5.30/2.13  tff(c_983, plain, (![A_173, C_174]: (k1_relset_1(A_173, k2_relat_1(C_174), C_174)=k1_relat_1(C_174) | ~r1_tarski(k1_relat_1(C_174), A_173) | ~v1_relat_1(C_174))), inference(resolution, [status(thm)], [c_940, c_249])).
% 5.30/2.13  tff(c_997, plain, (![C_174]: (k1_relset_1(k1_relat_1(C_174), k2_relat_1(C_174), C_174)=k1_relat_1(C_174) | ~v1_relat_1(C_174))), inference(resolution, [status(thm)], [c_6, c_983])).
% 5.30/2.13  tff(c_416, plain, (![B_89, C_90, A_91]: (k1_xboole_0=B_89 | v1_funct_2(C_90, A_91, B_89) | k1_relset_1(A_91, B_89, C_90)!=A_91 | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_89))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.30/2.13  tff(c_1463, plain, (![B_210, C_211, A_212]: (k1_xboole_0=B_210 | v1_funct_2(C_211, A_212, B_210) | k1_relset_1(A_212, B_210, C_211)!=A_212 | ~r1_tarski(k2_relat_1(C_211), B_210) | ~r1_tarski(k1_relat_1(C_211), A_212) | ~v1_relat_1(C_211))), inference(resolution, [status(thm)], [c_30, c_416])).
% 5.30/2.13  tff(c_1744, plain, (![C_235, A_236]: (k2_relat_1(C_235)=k1_xboole_0 | v1_funct_2(C_235, A_236, k2_relat_1(C_235)) | k1_relset_1(A_236, k2_relat_1(C_235), C_235)!=A_236 | ~r1_tarski(k1_relat_1(C_235), A_236) | ~v1_relat_1(C_235))), inference(resolution, [status(thm)], [c_6, c_1463])).
% 5.30/2.13  tff(c_1764, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1744, c_96])).
% 5.30/2.13  tff(c_1776, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_6, c_1764])).
% 5.30/2.13  tff(c_1777, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_1776])).
% 5.30/2.13  tff(c_1783, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_997, c_1777])).
% 5.30/2.13  tff(c_1790, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1783])).
% 5.30/2.13  tff(c_1791, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1776])).
% 5.30/2.13  tff(c_972, plain, (![A_171, C_170]: (k2_zfmisc_1(A_171, k2_relat_1(C_170))=C_170 | ~r1_tarski(k2_zfmisc_1(A_171, k2_relat_1(C_170)), C_170) | ~r1_tarski(k1_relat_1(C_170), A_171) | ~v1_relat_1(C_170))), inference(resolution, [status(thm)], [c_940, c_2])).
% 5.30/2.13  tff(c_1800, plain, (![A_171]: (k2_zfmisc_1(A_171, k2_relat_1('#skF_1'))='#skF_1' | ~r1_tarski(k2_zfmisc_1(A_171, k1_xboole_0), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), A_171) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1791, c_972])).
% 5.30/2.13  tff(c_1828, plain, (![A_171]: (k1_xboole_0='#skF_1' | ~r1_tarski(k1_relat_1('#skF_1'), A_171))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_8, c_12, c_12, c_1791, c_1800])).
% 5.30/2.13  tff(c_1849, plain, (![A_237]: (~r1_tarski(k1_relat_1('#skF_1'), A_237))), inference(splitLeft, [status(thm)], [c_1828])).
% 5.30/2.13  tff(c_1873, plain, $false, inference(resolution, [status(thm)], [c_6, c_1849])).
% 5.30/2.13  tff(c_1874, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_1828])).
% 5.30/2.13  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.30/2.13  tff(c_152, plain, (![C_45, A_46, B_47]: (v4_relat_1(C_45, A_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.30/2.13  tff(c_216, plain, (![A_62, A_63, B_64]: (v4_relat_1(A_62, A_63) | ~r1_tarski(A_62, k2_zfmisc_1(A_63, B_64)))), inference(resolution, [status(thm)], [c_18, c_152])).
% 5.30/2.13  tff(c_236, plain, (![A_63, B_64]: (v4_relat_1(k2_zfmisc_1(A_63, B_64), A_63))), inference(resolution, [status(thm)], [c_6, c_216])).
% 5.30/2.13  tff(c_188, plain, (![B_57, A_58]: (r1_tarski(k1_relat_1(B_57), A_58) | ~v4_relat_1(B_57, A_58) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.30/2.13  tff(c_86, plain, (![B_30, A_31]: (B_30=A_31 | ~r1_tarski(B_30, A_31) | ~r1_tarski(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.30/2.13  tff(c_95, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_86])).
% 5.30/2.13  tff(c_260, plain, (![B_71]: (k1_relat_1(B_71)=k1_xboole_0 | ~v4_relat_1(B_71, k1_xboole_0) | ~v1_relat_1(B_71))), inference(resolution, [status(thm)], [c_188, c_95])).
% 5.30/2.13  tff(c_264, plain, (![B_64]: (k1_relat_1(k2_zfmisc_1(k1_xboole_0, B_64))=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0, B_64)))), inference(resolution, [status(thm)], [c_236, c_260])).
% 5.30/2.13  tff(c_274, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_264])).
% 5.30/2.13  tff(c_277, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_274])).
% 5.30/2.13  tff(c_1941, plain, (~v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1874, c_277])).
% 5.30/2.13  tff(c_1956, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1941])).
% 5.30/2.13  tff(c_1957, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_274])).
% 5.30/2.13  tff(c_2160, plain, (![A_258, B_259, A_260]: (k1_relset_1(A_258, B_259, A_260)=k1_relat_1(A_260) | ~r1_tarski(A_260, k2_zfmisc_1(A_258, B_259)))), inference(resolution, [status(thm)], [c_18, c_238])).
% 5.30/2.13  tff(c_2178, plain, (![A_258, B_259]: (k1_relset_1(A_258, B_259, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_2160])).
% 5.30/2.13  tff(c_2182, plain, (![A_258, B_259]: (k1_relset_1(A_258, B_259, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1957, c_2178])).
% 5.30/2.13  tff(c_32, plain, (![A_19]: (v1_funct_2(k1_xboole_0, A_19, k1_xboole_0) | k1_xboole_0=A_19 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_19, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.30/2.13  tff(c_53, plain, (![A_19]: (v1_funct_2(k1_xboole_0, A_19, k1_xboole_0) | k1_xboole_0=A_19 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_32])).
% 5.30/2.13  tff(c_1959, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_53])).
% 5.30/2.13  tff(c_1981, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_1959])).
% 5.30/2.13  tff(c_1985, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1981])).
% 5.30/2.13  tff(c_1987, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_53])).
% 5.30/2.13  tff(c_36, plain, (![C_21, B_20]: (v1_funct_2(C_21, k1_xboole_0, B_20) | k1_relset_1(k1_xboole_0, B_20, C_21)!=k1_xboole_0 | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_20))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.30/2.13  tff(c_2209, plain, (![C_265, B_266]: (v1_funct_2(C_265, k1_xboole_0, B_266) | k1_relset_1(k1_xboole_0, B_266, C_265)!=k1_xboole_0 | ~m1_subset_1(C_265, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_36])).
% 5.30/2.13  tff(c_2211, plain, (![B_266]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_266) | k1_relset_1(k1_xboole_0, B_266, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1987, c_2209])).
% 5.30/2.13  tff(c_2217, plain, (![B_266]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_266))), inference(demodulation, [status(thm), theory('equality')], [c_2182, c_2211])).
% 5.30/2.13  tff(c_3834, plain, (![B_266]: (v1_funct_2('#skF_1', '#skF_1', B_266))), inference(demodulation, [status(thm), theory('equality')], [c_3781, c_3781, c_2217])).
% 5.30/2.13  tff(c_3846, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3781, c_3781, c_1957])).
% 5.30/2.13  tff(c_3700, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3698, c_96])).
% 5.30/2.13  tff(c_3783, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3781, c_3700])).
% 5.30/2.13  tff(c_3964, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3846, c_3783])).
% 5.30/2.13  tff(c_4180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3834, c_3964])).
% 5.30/2.13  tff(c_4181, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_50])).
% 5.30/2.13  tff(c_4371, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4359, c_4181])).
% 5.30/2.13  tff(c_4387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_6, c_6, c_4371])).
% 5.30/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.30/2.13  
% 5.30/2.13  Inference rules
% 5.30/2.13  ----------------------
% 5.30/2.13  #Ref     : 0
% 5.30/2.13  #Sup     : 881
% 5.30/2.13  #Fact    : 0
% 5.30/2.13  #Define  : 0
% 5.30/2.13  #Split   : 11
% 5.30/2.13  #Chain   : 0
% 5.30/2.13  #Close   : 0
% 5.30/2.13  
% 5.30/2.13  Ordering : KBO
% 5.30/2.13  
% 5.30/2.13  Simplification rules
% 5.30/2.13  ----------------------
% 5.30/2.13  #Subsume      : 226
% 5.30/2.13  #Demod        : 1112
% 5.30/2.13  #Tautology    : 306
% 5.30/2.13  #SimpNegUnit  : 12
% 5.30/2.13  #BackRed      : 160
% 5.30/2.13  
% 5.30/2.13  #Partial instantiations: 0
% 5.30/2.13  #Strategies tried      : 1
% 5.30/2.13  
% 5.30/2.13  Timing (in seconds)
% 5.30/2.13  ----------------------
% 5.30/2.13  Preprocessing        : 0.34
% 5.30/2.13  Parsing              : 0.17
% 5.30/2.13  CNF conversion       : 0.02
% 5.30/2.13  Main loop            : 0.91
% 5.30/2.13  Inferencing          : 0.31
% 5.30/2.13  Reduction            : 0.28
% 5.30/2.13  Demodulation         : 0.20
% 5.30/2.13  BG Simplification    : 0.04
% 5.30/2.13  Subsumption          : 0.21
% 5.30/2.13  Abstraction          : 0.05
% 5.30/2.13  MUC search           : 0.00
% 5.30/2.13  Cooper               : 0.00
% 5.30/2.13  Total                : 1.28
% 5.30/2.13  Index Insertion      : 0.00
% 5.30/2.13  Index Deletion       : 0.00
% 5.30/2.13  Index Matching       : 0.00
% 5.30/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
